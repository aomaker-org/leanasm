#!/usr/bin/env python3
# Path: leanasm/tools/incremental_build.py
"""Time-boxed incremental Lake build runner for interruptible Lean 4 builds."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
from typing import Dict, List, Optional, Set, Tuple

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")
DEFAULT_BUDGET_SECS = 900  # 15 minutes per collectible increment


def utc_now_iso() -> str:
    """Return ISO 8601 UTC timestamp."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def discover_modules(repo_root: Path) -> List[Tuple[str, Path]]:
    """Return workspace Lean modules in topological dependency order."""
    src_dir = repo_root / "src"
    files: Dict[str, Path] = {}
    for p in sorted(src_dir.rglob("*.lean")):
        rel = p.relative_to(src_dir).with_suffix("")
        mod = ".".join(rel.parts)
        files[mod] = p

    main_file = repo_root / "Main.lean"
    if main_file.is_file():
        files["Main"] = main_file

    deps: Dict[str, List[str]] = {}
    for mod, path in files.items():
        mod_deps: List[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            m = IMPORT_RE.match(line)
            if m and m.group(1) in files:
                mod_deps.append(m.group(1))
        deps[mod] = mod_deps

    visited: Set[str] = set()
    ordered: List[Tuple[str, Path]] = []

    def visit(mod: str) -> None:
        if mod in visited:
            return
        visited.add(mod)
        for dep in deps.get(mod, []):
            visit(dep)
        ordered.append((mod, files[mod]))

    for mod in sorted(files):
        visit(mod)
    return ordered


def lake_target_for(mod: str) -> str:
    """Map discovered module name to a Lake build target."""
    if mod == "Main":
        return "leanasm"
    return f"+{mod}"


def is_target_cached(repo_root: Path, target: str) -> Tuple[bool, str]:
    """Query whether a Lake target is already up to date without building."""
    proc = subprocess.run(
        ["lake", "--no-build", "build", target],
        cwd=str(repo_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode == 0:
        return True, ""
    detail = (proc.stderr or proc.stdout).strip()
    return False, detail


def run_module_build(
    repo_root: Path,
    target: str,
    timeout_secs: float,
    lean_mem_mb: Optional[int],
) -> Tuple[str, int, float, str]:
    """Build a single Lake target with a strict wall-clock cap and group cleanup."""
    cmd = ["lake", "build", "-v", target]
    if lean_mem_mb is not None:
        os_env = dict(os.environ)
        existing = os_env.get("LEAN_OPTS", "").strip()
        mem_flag = f"-M{lean_mem_mb}"
        os_env["LEAN_OPTS"] = f"{existing} {mem_flag}".strip()
    else:
        os_env = None

    t0 = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=str(repo_root),
        env=os_env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    )
    output_lines: List[str] = []

    def kill_group() -> None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
            proc.wait(timeout=5)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()

    try:
        stdout_data, _ = proc.communicate(timeout=timeout_secs)
        elapsed = time.monotonic() - t0
        if stdout_data:
            output_lines.append(stdout_data)
        text = "".join(output_lines)
        sys.stdout.write(text)
        sys.stdout.flush()
        status = "built" if proc.returncode == 0 else "failed"
        return status, proc.returncode, elapsed, text
    except subprocess.TimeoutExpired as exc:
        kill_group()
        elapsed = time.monotonic() - t0
        partial = exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        if partial:
            sys.stdout.write(partial)
            sys.stdout.flush()
        return "timeout", 124, elapsed, partial
    except KeyboardInterrupt:
        kill_group()
        elapsed = time.monotonic() - t0
        return "interrupted", 130, elapsed, ""


def save_progress(progress_path: Path, payload: dict) -> None:
    """Persist incremental build checkpoint state under .lake/."""
    progress_path.parent.mkdir(parents=True, exist_ok=True)
    progress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def print_status_report(repo_root: Path, ordered: List[Tuple[str, Path]], progress_path: Path) -> int:
    """Display cached vs pending status for every module in topological order."""
    prior_timings: Dict[str, float] = {}
    if progress_path.is_file():
        data = json.loads(progress_path.read_text(encoding="utf-8"))
        prior_timings = data.get("timings", {})

    cached_count = 0
    pending: List[str] = []
    print("=== Incremental Build Module Status ===")
    for mod, _ in ordered:
        target = lake_target_for(mod)
        ok, _ = is_target_cached(repo_root, target)
        state = "CACHED" if ok else "PENDING"
        if ok:
            cached_count += 1
        else:
            pending.append(target)
        t_str = f" ({prior_timings[target]:.2f}s)" if target in prior_timings else ""
        print(f"  [{state:7s}] {target}{t_str}")

    print(f"Summary: {cached_count}/{len(ordered)} targets cached, {len(pending)} pending.")
    if prior_timings:
        slowest = sorted(prior_timings.items(), key=lambda kv: kv[1], reverse=True)[:5]
        print("Slowest recorded builds: " + ", ".join(f"{k}={v:.2f}s" for k, v in slowest))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build LeanAsm modules incrementally in time-bounded slices."
    )
    parser.add_argument(
        "--budget-secs",
        type=int,
        default=DEFAULT_BUDGET_SECS,
        help="Total wall-clock budget for this slice in seconds (default: 900 = 15 min).",
    )
    parser.add_argument(
        "--module-timeout",
        type=int,
        default=DEFAULT_BUDGET_SECS,
        help="Max wall-clock seconds for any single module (default: 900).",
    )
    parser.add_argument(
        "--lean-mem-mb",
        type=int,
        default=None,
        help="Optional Lean -M heap cap in MB exported via LEAN_OPTS.",
    )
    parser.add_argument(
        "--require-complete",
        action="store_true",
        help="Exit non-zero if time budget pauses the build before all targets finish.",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="Print per-module .olean cache status and exit.",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    progress_path = repo_root / ".lake" / "incremental_build_state.json"
    ordered = discover_modules(repo_root)

    if args.status:
        return print_status_report(repo_root, ordered, progress_path)

    timings: Dict[str, float] = {}
    if progress_path.is_file():
        old_data = json.loads(progress_path.read_text(encoding="utf-8"))
        timings.update(old_data.get("timings", {}))

    slice_start = time.monotonic()
    built: List[str] = []
    cached: List[str] = []
    remaining: List[str] = []
    paused = False
    failure_code = 0

    print(
        f"[*] Incremental build started at {utc_now_iso()} "
        f"(budget={args.budget_secs}s, modules={len(ordered)})"
    )

    for idx, (mod, _) in enumerate(ordered):
        target = lake_target_for(mod)
        is_cached, _ = is_target_cached(repo_root, target)
        if is_cached:
            cached.append(target)
            print(f"  [CACHED]  {target}")
            continue

        elapsed_total = time.monotonic() - slice_start
        rem_budget = args.budget_secs - elapsed_total
        if rem_budget <= 1.0:
            paused = True
            remaining = [lake_target_for(m) for m, _ in ordered[idx:]]
            break

        cap = min(float(args.module_timeout), rem_budget)
        print(f"  [BUILD]   {target} (budget remaining: {rem_budget:.1f}s)")
        status, rc, mod_elapsed, _ = run_module_build(
            repo_root, target, cap, args.lean_mem_mb
        )
        timings[target] = round(mod_elapsed, 3)

        if status == "built":
            built.append(target)
            print(f"  [DONE]    {target} in {mod_elapsed:.2f}s")
        elif status == "timeout":
            paused = True
            remaining = [lake_target_for(m) for m, _ in ordered[idx:]]
            print(
                f"  [TIMEOUT] {target} exceeded {cap:.1f}s slice cap; "
                f"prior {len(cached) + len(built)} targets remain cached."
            )
            break
        elif status == "interrupted":
            paused = True
            remaining = [lake_target_for(m) for m, _ in ordered[idx:]]
            failure_code = rc
            break
        else:
            remaining = [lake_target_for(m) for m, _ in ordered[idx:]]
            failure_code = rc if rc != 0 else 1
            print(f"  [FAILED]  {target} exited with code {failure_code} after {mod_elapsed:.2f}s")
            break

        save_progress(
            progress_path,
            {
                "updated_at": utc_now_iso(),
                "budget_secs": args.budget_secs,
                "cached": cached,
                "built": built,
                "remaining": [lake_target_for(m) for m, _ in ordered[idx + 1 :]],
                "timings": timings,
            },
        )

    save_progress(
        progress_path,
        {
            "updated_at": utc_now_iso(),
            "budget_secs": args.budget_secs,
            "cached": cached,
            "built": built,
            "remaining": remaining,
            "timings": timings,
        },
    )

    total_elapsed = time.monotonic() - slice_start
    print(
        f"=== Slice Summary ({total_elapsed:.2f}s) ===\n"
        f"  Cached: {len(cached)} | Newly built: {len(built)} | Remaining: {len(remaining)}"
    )
    if built:
        slowest = sorted(((t, timings[t]) for t in built), key=lambda kv: kv[1], reverse=True)[:5]
        print("  Built timings: " + ", ".join(f"{k}={v:.2f}s" for k, v in slowest))

    if failure_code != 0:
        return failure_code
    if paused:
        print(f"[CHECKPOINT] Next module to resume: {remaining[0] if remaining else 'none'}")
        return 2 if args.require_complete else 0
    print("[+] All targets up to date.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

# end of file: leanasm/tools/incremental_build.py
