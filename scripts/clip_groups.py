#!/usr/bin/env python3
# Path: leanasm/scripts/clip_groups.py
# Automatic bundle splitter (<240 KB), tree scanner, and clipboard dispatcher
# Max Column: 80 Columns

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

MAX_BYTES = 240 * 1024  # 240 KB limit per bundle
STATE_FILE = Path(".lake/clip_state.json")

GROUP_META = [
    ("0_constants", "Immutable constants & certified lookup tables"),
    ("1_core", "Architecture, toolchain, configs, scripts, and Main"),
    ("2_minivm", "MiniVM bytecode interpreter and NTT assembly bridge"),
    ("3_crt_rns", "RNS arithmetic and multi-prime CRT-NTT engines"),
    ("4_chudnovsky", "100-digit Chudnovsky Pi constructive calculation"),
    ("5_yangmills", "Yang-Mills SU(2)/Q8 gauge toy models & OpenAI bridge"),
    ("6_qrh_core", "Quasi-Riemann hypothesis core, sweeps & asymptotic ZFR"),
    ("7_qrh_deep", "Quasi-Riemann UltraDeep zero-free sweeps (N=72,90,108)"),
    ("8_valuation", "p-adic valuation, Eisenstein, and preperiodic dynamics"),
    ("9_bridges", "Arithmetic & L-function bridges (Artin, Weil, Collatz)"),
    ("10_proofs", "Provenance summary, axiom audits, and test suites"),
    ("11_docs", "Scanned submission docs & architecture notes"),
]

INCLUDE_EXTS = {".lean", ".py", ".sh", ".toml", ".mk", ".md"}
INCLUDE_NAMES = {"Makefile", "lean-toolchain", "config_env"}
EXCLUDE_DIRS = {".git", ".lake", ".venv", "__pycache__", "subrepos"}


def discover_repo_files() -> list[str]:
    """Return sorted tracked/workspace files eligible for clip bundles."""
    try:
        out = subprocess.check_output(
            ["git", "ls-files", "-co", "--exclude-standard"],
            stderr=subprocess.DEVNULL,
            text=True,
        )
        candidates = [ln.strip() for ln in out.splitlines() if ln.strip()]
    except Exception:
        candidates = []
        for root, dirs, names in os.walk("."):
            dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS]
            for name in names:
                candidates.append(os.path.normpath(os.path.join(root, name)))

    files: set[str] = set()
    for rel in candidates:
        p = Path(rel)
        if any(
            part.startswith(".") or part in EXCLUDE_DIRS for part in p.parts
        ):
            continue
        if p.parts[0] == "docs" and "--include-docs" not in sys.argv:
            continue
        if not p.is_file():
            continue
        if p.name in INCLUDE_NAMES or p.suffix in INCLUDE_EXTS:
            files.add(p.as_posix())
    return sorted(files)


def classify_file(path: str) -> str:
    """Assign a workspace file path to its semantic group key."""
    if path.startswith("src/LeanAsm/Constants/"):
        return "0_constants"
    if path in {
        "AI.md",
        "README.md",
        "lakefile.toml",
        "lean-toolchain",
        "Makefile",
        "config_env",
        "Main.lean",
        "src/LeanAsm.lean",
    } or path.startswith(("mk/", "tools/", "scripts/")):
        return "1_core"
    if path in {
        "src/LeanAsm/MiniVM.lean",
        "src/LeanAsm/MiniVMNttBridge.lean",
        "src/LeanAsm/NttArithmetic.lean",
    }:
        return "2_minivm"
    if path in {
        "src/LeanAsm/RnsArithmetic.lean",
        "src/LeanAsm/CrtNtt.lean",
        "src/LeanAsm/CrtNttUniversal.lean",
    }:
        return "3_crt_rns"
    if path == "src/LeanAsm/PiChudnovsky.lean" or path.startswith(
        "src/LeanAsm/PiChudnovsky/"
    ):
        return "4_chudnovsky"
    if path in {
        "src/LeanAsm/YangMillsToy.lean",
        "src/LeanAsm/YangMillsQ8.lean",
        "src/LeanAsm/ConstructiveOpenaiBridge.lean",
    }:
        return "5_yangmills"
    if path in {
        "src/LeanAsm/QuasiRiemann.lean",
        "src/LeanAsm/QuasiRiemann/Rat.lean",
        "src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean",
        "src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean",
    } or path.startswith("src/LeanAsm/QuasiRiemann/QR/"):
        return "6_qrh_core"
    if path.startswith("src/LeanAsm/QuasiRiemann/UltraDeep"):
        return "7_qrh_deep"
    if path.startswith("src/LeanAsm/QuasiRiemann/Valuation/"):
        return "8_valuation"
    if path == "src/LeanAsm/ProvenanceSummary.lean" or path.startswith(
        "tests/"
    ):
        return "10_proofs"
    if path.startswith("docs/"):
        return "11_docs"
    if path.startswith("src/LeanAsm/") and path.endswith(".lean"):
        return "9_bridges"
    return "1_core"


def compute_tree_hash(files: list[str]) -> str:
    h = hashlib.sha256()
    for f in files:
        h.update(f.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()[:16]


def build_batches_from_files(files: list[str]) -> list[dict]:
    """Group discovered files and split each group under MAX_BYTES."""
    grouped: dict[str, list[str]] = {k: [] for k, _ in GROUP_META}
    for f in files:
        grouped[classify_file(f)].append(f)

    batches: list[dict] = []
    for gname, gdesc in GROUP_META:
        flist = grouped.get(gname, [])
        cur_batch: list[str] = []
        cur_size = 0
        part = 1
        for f in flist:
            sz = os.path.getsize(f)
            if cur_batch and (cur_size + sz > MAX_BYTES):
                batches.append(
                    {
                        "name": f"{gname}.{part}",
                        "desc": gdesc,
                        "files": cur_batch,
                        "size": cur_size,
                    }
                )
                part += 1
                cur_batch = [f]
                cur_size = sz
            else:
                cur_batch.append(f)
                cur_size += sz
        if cur_batch:
            lbl = f"{gname}.{part}" if part > 1 else gname
            batches.append(
                {
                    "name": lbl,
                    "desc": gdesc,
                    "files": cur_batch,
                    "size": cur_size,
                }
            )
    return batches


def load_raw_state() -> dict:
    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as fp:
                data = json.load(fp)
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
    return {}


def save_raw_state(state: dict) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    with open(STATE_FILE, "w", encoding="utf-8") as fp:
        json.dump(state, fp, indent=2)


def sync_manifest(force_rebuild: bool = False) -> tuple[dict, bool]:
    """Load cached manifest or rebuild from current repository file tree."""
    state = load_raw_state()
    files = discover_repo_files()
    tree_hash = compute_tree_hash(files)

    if force_rebuild or "batches" not in state:
        old_files = set(state.get("files", []))
        new_files = set(files)
        added = sorted(new_files - old_files)
        removed = sorted(old_files - new_files)
        batches = build_batches_from_files(files)
        last_idx = 0 if force_rebuild else int(state.get("last_index", 0))
        if last_idx > len(batches):
            last_idx = 0
        state = {
            "last_index": last_idx,
            "tree_hash": tree_hash,
            "files": files,
            "batches": batches,
        }
        save_raw_state(state)
        if force_rebuild:
            print(
                f"[+] Rebuilt manifest: {len(files)} files across "
                f"{len(batches)} batches."
            )
            for f in added:
                print(f"    + {f}")
            for f in removed:
                print(f"    - {f}")
        return state, False

    stale = state.get("tree_hash") != tree_hash
    return state, stale


def print_list(state: dict, stale: bool) -> None:
    batches = state.get("batches", [])
    last_idx = int(state.get("last_index", 0))
    print("=" * 78)
    print(" leanasm files2clip Review Batches (Auto-split under 240 KB)")
    print("=" * 78)
    for i, b in enumerate(batches, 1):
        marker = "-> [LAST SENT]" if i == last_idx else "  "
        bfiles = b["files"]
        bsz = b["size"]
        print(
            f"{marker} {i:2d}. {b['name']:16s} ({len(bfiles):2d} files, "
            f"{bsz/1024:5.1f} KB) - {b['desc']}"
        )
    print("=" * 78)
    if stale:
        print(
            "[!] Tree changed since last manifest; run "
            "'./scripts/clip_groups.py rebuild' to sync."
        )
    print("Quick Shortcuts:")
    print("  ./scripts/clip_groups.py next     (send next sequential batch)")
    print(f"  ./scripts/clip_groups.py 1        (send batch 1..{len(batches)})")
    print("  ./scripts/clip_groups.py rebuild  (rescan tree & update manifest)")
    print("  ./scripts/clip_groups.py reset    (reset next counter to 1)")
    print("=" * 78)


def send_batch(state: dict, stale: bool, idx: int) -> None:
    batches = state.get("batches", [])
    if idx < 1 or idx > len(batches):
        print(f"[-] Error: Batch index {idx} out of range (1..{len(batches)}).")
        sys.exit(1)

    if stale:
        print(
            "[!] Warning: Tree changed since last manifest; consider "
            "'./scripts/clip_groups.py rebuild'."
        )

    b = batches[idx - 1]
    bfiles = [f for f in b["files"] if os.path.exists(f)]
    bsz = sum(os.path.getsize(f) for f in bfiles)
    print(
        f"[+] Batch {idx}/{len(batches)}: '{b['name']}' "
        f"({len(bfiles)} files, {bsz/1024:.1f} KB)"
    )
    for f in bfiles:
        print(f"    - {f} ({os.path.getsize(f)/1024:.1f} KB)")

    cmd = ["files2clip"] + bfiles
    try:
        res = subprocess.run(cmd, check=True)
        if res.returncode == 0:
            state["last_index"] = idx
            save_raw_state(state)
            next_idx = idx + 1 if idx < len(batches) else 1
            print(f"[+] Successfully copied batch {idx} to clipboard!")
            print(
                f"[+] Run './scripts/clip_groups.py next' to copy "
                f"batch {next_idx}."
            )
    except Exception as e:
        print(f"[-] Error running files2clip: {e}")
        sys.exit(1)


def main() -> None:
    args = [a for a in sys.argv[1:] if a != "--include-docs"]
    target = args[0].strip().lower() if args else "list"

    if target in ("rebuild", "--rebuild", "-r"):
        state, stale = sync_manifest(force_rebuild=True)
        print_list(state, stale)
        sys.exit(0)

    state, stale = sync_manifest(force_rebuild=False)
    batches = state.get("batches", [])

    if target in ("-h", "--help", "help", "list", "-l"):
        print_list(state, stale)
        sys.exit(0)

    if target == "reset":
        state["last_index"] = 0
        save_raw_state(state)
        print("[+] Reset next batch counter to 1.")
        sys.exit(0)

    if target in ("next", "n"):
        last_idx = int(state.get("last_index", 0))
        target_idx = last_idx + 1 if last_idx < len(batches) else 1
        send_batch(state, stale, target_idx)
        sys.exit(0)

    if target.isdigit():
        send_batch(state, stale, int(target))
        sys.exit(0)

    matches = [
        (i + 1)
        for i, b in enumerate(batches)
        if target in b["name"].lower()
    ]
    if len(matches) == 1:
        send_batch(state, stale, matches[0])
    elif len(matches) > 1:
        print(f"[-] Ambiguous name '{target}'. Matches batches: {matches}")
        sys.exit(1)
    else:
        print(f"[-] Unknown target or batch: '{target}'")
        print_list(state, stale)
        sys.exit(1)


if __name__ == "__main__":
    main()

# end of file: leanasm/scripts/clip_groups.py
