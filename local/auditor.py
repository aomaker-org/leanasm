#!/usr/bin/env python3
# Path: leanasm/local/auditor.py
"""Long-running Qwen + DeepSeek-Prover codebase auditor with full profiling."""

import argparse
import asyncio
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import urllib.error
import urllib.request
from typing import Any, Dict, List, Optional, Tuple

from google.antigravity import Agent, BuiltinTools, CapabilitiesConfig, types
from google.antigravity.connections.local.local_openai_connection_config import (
    LocalOpenAIAgentConfig,
)


DEFAULT_ORCHESTRATOR_MODEL = "qwen2.5-coder:7b"
DEFAULT_PROVER_MODEL = "deepseek-prover:7b"
DEFAULT_BASE_URL = "http://localhost:11434"
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]*$")
SORRY_RE = re.compile(r"\bsorry\b")
AXIOM_RE = re.compile(r"^\s*axiom\b")
CHOICE_RE = re.compile(r"\bClassical\.choice\b")
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|instance|structure|inductive|class|abbrev|opaque)\b"
)

AUDITOR_INSTRUCTIONS = (
    "You are a read-only Lean 4 (v4.35.0) codebase reviewer and auditor for "
    "leanasm.\n"
    "For each assigned module:\n"
    "1. Use view_file to read the module source.\n"
    "2. Use run_lean_check to verify 'lake build +<Module>' compiles.\n"
    "3. Select 1-2 flagship theorems or non-trivial proofs in the module and "
    "call ask_deepseek_prover with the exact Lean snippet to audit proof "
    "constructiveness, edge cases, and tactic quality.\n"
    "4. Return a concise audit summary with:\n"
    "   - Verdict: PASS | WARN | FAIL\n"
    "   - Build & Hygiene observations\n"
    "   - DeepSeek-Prover mathematical review findings\n"
    "Never modify files."
)


def utc_now_iso() -> str:
    """Return ISO 8601 UTC timestamp."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def normalize_urls(raw_url: Optional[str]) -> Tuple[str, str]:
    """Return (ollama_root_url, openai_v1_url) from CLI arg or env vars."""
    raw = (
        raw_url
        or os.environ.get("AGY_OLLAMA_BASE_URL")
        or os.environ.get("OLLAMA_HOST")
        or DEFAULT_BASE_URL
    ).rstrip("/")
    root = raw[:-3] if raw.endswith("/v1") else raw
    return root, f"{root}/v1"


def discover_lean_modules(repo_root: Path) -> List[Tuple[str, Path]]:
    """Discover Lean modules under src/ plus Main.lean."""
    modules: List[Tuple[str, Path]] = []
    src_dir = repo_root / "src"
    if src_dir.is_dir():
        for path in sorted(src_dir.rglob("*.lean")):
            rel = path.relative_to(src_dir).with_suffix("")
            modules.append((".".join(rel.parts), path))
    main_file = repo_root / "Main.lean"
    if main_file.is_file():
        modules.append(("Main", main_file))
    return modules


def scan_module_hygiene(repo_root: Path, mod_name: str, path: Path) -> Dict[str, Any]:
    """Run fast deterministic static checks on a single Lean file."""
    t0 = time.monotonic()
    rel_path = path.relative_to(repo_root).as_posix()
    lines = path.read_text(encoding="utf-8").splitlines()
    long_lines = [i for i, ln in enumerate(lines, 1) if len(ln) > 100]
    sorry_lines = [i for i, ln in enumerate(lines, 1) if SORRY_RE.search(ln)]
    axiom_lines = [i for i, ln in enumerate(lines, 1) if AXIOM_RE.search(ln)]
    choice_lines = [i for i, ln in enumerate(lines, 1) if CHOICE_RE.search(ln)]

    first_line = lines[0] if lines else ""
    last_line = lines[-1] if lines else ""
    has_header = f"Path: leanasm/{rel_path}" in first_line
    has_footer = f"end of file: leanasm/{rel_path}" in last_line

    elapsed_ms = round((time.monotonic() - t0) * 1000.0, 2)
    return {
        "module": mod_name,
        "rel_path": rel_path,
        "line_count": len(lines),
        "has_header": has_header,
        "has_footer": has_footer,
        "long_lines_gt_100": long_lines,
        "sorry_lines": sorry_lines,
        "axiom_lines": axiom_lines,
        "choice_lines": choice_lines,
        "duration_ms": elapsed_ms,
    }


def sample_process_and_wsl_memory() -> Dict[str, Any]:
    """Read WSL2 /proc/meminfo and process/child max RSS in MB."""
    meminfo: Dict[str, int] = {}
    proc_mem = Path("/proc/meminfo")
    if proc_mem.is_file():
        for line in proc_mem.read_text(encoding="utf-8").splitlines():
            parts = line.split(":")
            if len(parts) == 2:
                val_parts = parts[1].strip().split()
                if val_parts and val_parts[0].isdigit():
                    meminfo[parts[0]] = int(val_parts[0])  # kB

    total_kb = meminfo.get("MemTotal", 0)
    avail_kb = meminfo.get("MemAvailable", 0)
    swap_total_kb = meminfo.get("SwapTotal", 0)
    swap_free_kb = meminfo.get("SwapFree", 0)

    self_rss_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    child_rss_kb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss

    return {
        "wsl_ram_total_mb": round(total_kb / 1024.0, 2),
        "wsl_ram_used_mb": round(max(0, total_kb - avail_kb) / 1024.0, 2),
        "wsl_ram_avail_mb": round(avail_kb / 1024.0, 2),
        "wsl_swap_used_mb": round(max(0, swap_total_kb - swap_free_kb) / 1024.0, 2),
        "python_max_rss_mb": round(self_rss_kb / 1024.0, 2),
        "child_max_rss_mb": round(child_rss_kb / 1024.0, 2),
    }


def sample_ollama_ps(ollama_root: str, timeout_secs: int = 10) -> Dict[str, Any]:
    """Query Ollama GET /api/ps for loaded model VRAM, CPU spill, and context_length."""
    endpoint = f"{ollama_root}/api/ps"
    req = urllib.request.Request(endpoint, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout_secs) as resp:
            body = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, urllib.error.HTTPError, json.JSONDecodeError) as exc:
        return {"status": "error", "error": str(exc), "models": []}

    mb = 1024.0 * 1024.0
    parsed_models: List[Dict[str, Any]] = []
    for item in body.get("models", []):
        size_b = int(item.get("size", 0) or 0)
        vram_b = int(item.get("size_vram", 0) or 0)
        spill_b = max(0, size_b - vram_b)
        details = item.get("details", {}) or {}
        parsed_models.append(
            {
                "name": item.get("name", item.get("model", "")),
                "size_mb": round(size_b / mb, 2),
                "size_vram_mb": round(vram_b / mb, 2),
                "cpu_spill_mb": round(spill_b / mb, 2),
                "vram_pct": round((100.0 * vram_b / size_b), 1) if size_b > 0 else 0.0,
                "context_length": int(item.get("context_length", 0) or 0),
                "parameter_size": details.get("parameter_size", ""),
                "quantization_level": details.get("quantization_level", ""),
                "expires_at": item.get("expires_at", ""),
            }
        )

    return {
        "status": "ok",
        "total_loaded_models": len(parsed_models),
        "total_model_mem_mb": round(sum(m["size_mb"] for m in parsed_models), 2),
        "total_vram_mb": round(sum(m["size_vram_mb"] for m in parsed_models), 2),
        "total_cpu_spill_mb": round(sum(m["cpu_spill_mb"] for m in parsed_models), 2),
        "models": parsed_models,
    }


def extract_ollama_metrics(body: Dict[str, Any]) -> Dict[str, Any]:
    """Convert Ollama /api/chat nanosecond counters into ms and tok/s."""
    ns_to_ms = 1_000_000.0
    ns_to_s = 1_000_000_000.0
    total_ns = int(body.get("total_duration", 0) or 0)
    load_ns = int(body.get("load_duration", 0) or 0)
    prompt_cnt = int(body.get("prompt_eval_count", 0) or 0)
    prompt_ns = int(body.get("prompt_eval_duration", 0) or 0)
    eval_cnt = int(body.get("eval_count", 0) or 0)
    eval_ns = int(body.get("eval_duration", 0) or 0)

    return {
        "total_duration_ms": round(total_ns / ns_to_ms, 2),
        "load_duration_ms": round(load_ns / ns_to_ms, 2),
        "prompt_eval_count": prompt_cnt,
        "prompt_eval_duration_ms": round(prompt_ns / ns_to_ms, 2),
        "prompt_eval_tok_s": round(prompt_cnt / (prompt_ns / ns_to_s), 2)
        if prompt_ns > 0
        else 0.0,
        "eval_count": eval_cnt,
        "eval_duration_ms": round(eval_ns / ns_to_ms, 2),
        "eval_tok_s": round(eval_cnt / (eval_ns / ns_to_s), 2)
        if eval_ns > 0
        else 0.0,
    }


class AuditProfiler:
    """Thread-safe additive JSONL event and timing collector."""

    def __init__(self, out_dir: Path) -> None:
        self.out_dir = out_dir
        self.out_dir.mkdir(parents=True, exist_ok=True)
        self.events_path = self.out_dir / "events.jsonl"
        self.events: List[Dict[str, Any]] = []
        self.started_monotonic = time.monotonic()

    def record(self, kind: str, **fields: Any) -> Dict[str, Any]:
        """Append a timestamped event to memory and events.jsonl immediately."""
        entry = {
            "timestamp": utc_now_iso(),
            "elapsed_s": round(time.monotonic() - self.started_monotonic, 3),
            "kind": kind,
            **fields,
        }
        self.events.append(entry)
        with open(self.events_path, "a", encoding="utf-8") as ef:
            ef.write(json.dumps(entry) + "\n")
        return entry

    def record_snapshot(
        self,
        phase: str,
        ollama_root: Optional[str],
        module_name: Optional[str] = None,
    ) -> Dict[str, Any]:
        """Record WSL2/process memory and optional Ollama /api/ps VRAM/context state."""
        sys_mem = sample_process_and_wsl_memory()
        ps_info = sample_ollama_ps(ollama_root) if ollama_root else None
        return self.record(
            "memory_snapshot",
            phase=phase,
            module=module_name,
            **sys_mem,
            ollama_ps=ps_info,
        )

    def build_summary(self) -> Dict[str, Any]:
        """Aggregate timing, token, context, memory, and load-swap telemetry."""
        lake_events = [e for e in self.events if e["kind"] == "lake_check"]
        deepseek_events = [e for e in self.events if e["kind"] == "deepseek_call"]
        qwen_events = [
            e for e in self.events if e["kind"] in ("qwen_review", "qwen_call")
        ]
        tool_call_events = [e for e in self.events if e["kind"] == "tool_call"]
        tool_res_events = [e for e in self.events if e["kind"] == "tool_result"]
        snap_events = [e for e in self.events if e["kind"] == "memory_snapshot"]

        ds_eval_tokens = sum(e.get("eval_count", 0) for e in deepseek_events)
        ds_eval_ms = sum(e.get("eval_duration_ms", 0.0) for e in deepseek_events)
        ds_load_ms = sum(e.get("load_duration_ms", 0.0) for e in deepseek_events)

        qwen_prompt_tok = sum(
            e.get("prompt_token_count", e.get("prompt_eval_count", 0))
            for e in qwen_events
        )
        qwen_cand_tok = sum(
            e.get("candidates_token_count", e.get("eval_count", 0))
            for e in qwen_events
        )
        qwen_thought_tok = sum(e.get("thoughts_token_count", 0) for e in qwen_events)
        qwen_cached_tok = sum(
            e.get("cached_content_token_count", 0) for e in qwen_events
        )
        qwen_total_ms = sum(
            e.get("duration_ms", e.get("wall_ms", 0.0)) for e in qwen_events
        )
        ctx_utils = [
            e["context_utilization_pct"]
            for e in qwen_events
            if e.get("context_utilization_pct") is not None
        ]

        lake_total_ms = sum(e.get("duration_ms", 0.0) for e in lake_events)
        lake_failures = sum(1 for e in lake_events if e.get("exit_code", 1) != 0)
        tool_errors = sum(1 for e in tool_res_events if e.get("is_error"))

        max_wsl_used = max((e.get("wsl_ram_used_mb", 0.0) for e in snap_events), default=0.0)
        max_py_rss = max((e.get("python_max_rss_mb", 0.0) for e in snap_events), default=0.0)
        max_child_rss = max((e.get("child_max_rss_mb", 0.0) for e in snap_events), default=0.0)

        ps_ok = [
            e["ollama_ps"]
            for e in snap_events
            if isinstance(e.get("ollama_ps"), dict) and e["ollama_ps"].get("status") == "ok"
        ]
        max_vram_mb = max((p.get("total_vram_mb", 0.0) for p in ps_ok), default=0.0)
        max_spill_mb = max((p.get("total_cpu_spill_mb", 0.0) for p in ps_ok), default=0.0)
        max_loaded = max((p.get("total_loaded_models", 0) for p in ps_ok), default=0)

        seen_models: Dict[str, Dict[str, Any]] = {}
        for ps in ps_ok:
            for m in ps.get("models", []):
                name = m.get("name", "")
                if not name:
                    continue
                prev = seen_models.get(name, {})
                seen_models[name] = {
                    "max_size_mb": max(prev.get("max_size_mb", 0.0), m.get("size_mb", 0.0)),
                    "max_vram_mb": max(prev.get("max_vram_mb", 0.0), m.get("size_vram_mb", 0.0)),
                    "max_cpu_spill_mb": max(
                        prev.get("max_cpu_spill_mb", 0.0), m.get("cpu_spill_mb", 0.0)
                    ),
                    "context_length": max(
                        prev.get("context_length", 0), m.get("context_length", 0)
                    ),
                    "quantization": m.get("quantization_level") or prev.get("quantization", ""),
                }

        return {
            "total_wall_s": round(time.monotonic() - self.started_monotonic, 3),
            "event_count": len(self.events),
            "lake_checks": {
                "count": len(lake_events),
                "failures": lake_failures,
                "total_ms": round(lake_total_ms, 2),
            },
            "qwen_reviews": {
                "count": len(qwen_events),
                "total_ms": round(qwen_total_ms, 2),
                "prompt_tokens": qwen_prompt_tok,
                "candidate_tokens": qwen_cand_tok,
                "thought_tokens": qwen_thought_tok,
                "cached_tokens": qwen_cached_tok,
                "max_context_utilization_pct": max(ctx_utils, default=None),
            },
            "deepseek_calls": {
                "count": len(deepseek_events),
                "total_load_swap_ms": round(ds_load_ms, 2),
                "total_eval_tokens": ds_eval_tokens,
                "avg_eval_tok_s": round(ds_eval_tokens / (ds_eval_ms / 1000.0), 2)
                if ds_eval_ms > 0
                else 0.0,
            },
            "tool_trace": {
                "total_tool_calls": len(tool_call_events),
                "total_tool_results": len(tool_res_events),
                "tool_errors": tool_errors,
            },
            "memory_telemetry": {
                "snapshots": len(snap_events),
                "peak_wsl_ram_used_mb": max_wsl_used,
                "peak_python_max_rss_mb": max_py_rss,
                "peak_child_max_rss_mb": max_child_rss,
                "peak_ollama_vram_mb": max_vram_mb,
                "peak_ollama_cpu_spill_mb": max_spill_mb,
                "max_concurrent_models_loaded": max_loaded,
                "models_observed": seen_models,
            },
        }

    def write_checkpoint(
        self,
        hygiene_rows: List[Dict[str, Any]],
        ai_reviews: List[Dict[str, Any]],
        completed_modules: List[str],
        axiom_result: Optional[Dict[str, Any]],
        status: str,
    ) -> None:
        """Persist checkpoint.json atomically for interruptible --resume."""
        payload = {
            "updated_at": utc_now_iso(),
            "status": status,
            "completed_modules": completed_modules,
            "hygiene_rows": hygiene_rows,
            "ai_reviews": ai_reviews,
            "axiom_result": axiom_result,
        }
        tmp_path = self.out_dir / "checkpoint.json.tmp"
        ckpt_path = self.out_dir / "checkpoint.json"
        tmp_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        tmp_path.replace(ckpt_path)


def run_lake_command(
    repo_root: Path,
    cmd: List[str],
    profiler: AuditProfiler,
    label: str,
) -> Tuple[int, str, float]:
    """Execute a lake/lean command with exact timing logged to AuditProfiler."""
    elan_bin = str(Path.home() / ".elan" / "bin")
    env = dict(os.environ)
    if elan_bin not in env.get("PATH", ""):
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    t0 = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=str(repo_root),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    duration_ms = round((time.monotonic() - t0) * 1000.0, 2)
    profiler.record(
        "lake_check",
        label=label,
        command=" ".join(cmd),
        exit_code=proc.returncode,
        duration_ms=duration_ms,
    )
    return proc.returncode, proc.stdout.strip(), duration_ms


def call_ollama_chat(
    ollama_root: str,
    model: str,
    system_msg: str,
    user_msg: str,
    profiler: AuditProfiler,
    event_kind: str,
    module_name: str,
    num_ctx: int = 4096,
    num_predict: int = 384,
    num_threads: Optional[int] = None,
    temperature: float = 0.2,
    repeat_penalty: float = 1.18,
    timeout_secs: int = 900,
) -> Tuple[str, Dict[str, Any]]:
    """Invoke Ollama /api/chat and record full hardware, timing, and VRAM metrics."""
    endpoint = f"{ollama_root}/api/chat"
    options: Dict[str, Any] = {
        "temperature": temperature,
        "repeat_penalty": repeat_penalty,
        "num_ctx": num_ctx,
        "num_predict": num_predict,
    }
    if num_threads is not None and num_threads > 0:
        options["num_thread"] = num_threads
    payload = json.dumps(
        {
            "model": model,
            "messages": [
                {"role": "system", "content": system_msg},
                {"role": "user", "content": user_msg},
            ],
            "options": options,
            "stream": False,
        }
    ).encode("utf-8")

    t0 = time.monotonic()
    req = urllib.request.Request(
        endpoint,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_secs) as resp:
            body = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        wall_ms = round((time.monotonic() - t0) * 1000.0, 2)
        ev = profiler.record(
            event_kind,
            module=module_name,
            model=model,
            status="http_error",
            http_code=exc.code,
            wall_ms=wall_ms,
        )
        return f"Error: Ollama HTTP {exc.code} querying {model}: {detail}", ev
    except urllib.error.URLError as exc:
        wall_ms = round((time.monotonic() - t0) * 1000.0, 2)
        ev = profiler.record(
            event_kind,
            module=module_name,
            model=model,
            status="url_error",
            error=str(exc.reason),
            wall_ms=wall_ms,
        )
        return f"Error: Cannot reach Ollama at {endpoint}: {exc.reason}", ev
    except TimeoutError as exc:
        wall_ms = round((time.monotonic() - t0) * 1000.0, 2)
        ev = profiler.record(
            event_kind,
            module=module_name,
            model=model,
            status="timeout",
            error=str(exc),
            wall_ms=wall_ms,
        )
        return f"Error: Ollama request timed out after {timeout_secs}s on {model}.", ev

    wall_ms = round((time.monotonic() - t0) * 1000.0, 2)
    metrics = extract_ollama_metrics(body)
    reply = body.get("message", {}).get("content", "")
    ctx_pct = (
        round(100.0 * metrics["prompt_eval_count"] / num_ctx, 2)
        if num_ctx > 0 and metrics["prompt_eval_count"] > 0
        else None
    )
    ev = profiler.record(
        event_kind,
        module=module_name,
        model=model,
        status="ok",
        wall_ms=wall_ms,
        num_ctx=num_ctx,
        context_utilization_pct=ctx_pct,
        prompt_chars=len(user_msg),
        reply_chars=len(reply),
        **metrics,
    )
    profiler.record_snapshot(f"after_{event_kind}", ollama_root, module_name)
    return reply, ev


def make_deepseek_audit_tool(
    ollama_root: str,
    prover_model: str,
    profiler: AuditProfiler,
    module_name: str,
    num_ctx: int = 4096,
    num_predict: int = 384,
    num_threads: Optional[int] = None,
):
    """Create profiled tool calling Ollama native /api/chat for DeepSeek-Prover."""

    def ask_deepseek_prover(lean_snippet: str, audit_question: str) -> str:
        """Ask DeepSeek-Prover to audit or critique a Lean 4 theorem/proof snippet.

        Args:
            lean_snippet: Exact Lean 4 theorem and definitions from the file.
            audit_question: Specific mathematical or constructiveness question.
        """
        reply, _ = call_ollama_chat(
            ollama_root=ollama_root,
            model=prover_model,
            system_msg=(
                "You are a Lean 4 (v4.35.0) mathematical proof auditor. "
                "Write concise English technical bullets ONLY. Never copy or "
                "reprint the input Lean source code."
            ),
            user_msg=(
                f"Module: `{module_name}`\n\n"
                f"```lean4\n{lean_snippet}\n```\n\n"
                f"Question: {audit_question}\n\n"
                "Respond ONLY with short markdown bullets covering:\n"
                "- Verdict: PASS | WARN | FAIL\n"
                "- Hidden assumptions / domain preconditions\n"
                "- Edge cases or proof-simplification ideas\n"
                "Do NOT repeat or rewrite the source file."
            ),
            profiler=profiler,
            event_kind="deepseek_call",
            module_name=module_name,
            num_ctx=num_ctx,
            num_predict=num_predict,
            num_threads=num_threads,
        )
        return reply

    return ask_deepseek_prover


def make_lean_check_tool(repo_root: Path, profiler: AuditProfiler):
    """Create profiled read-only Lean build and axiom-audit tool."""

    def run_lean_check(module_name: str, check_axioms: bool = False) -> str:
        """Build a Lean 4 module via lake and optionally audit axioms.

        Args:
            module_name: Dotted module name (e.g. LeanAsm.MiniVM or Main).
            check_axioms: If true, also run lake env lean tests/TestAxioms.lean.
        """
        if not MODULE_RE.match(module_name):
            return f"Error: Invalid Lean module name '{module_name}'."

        target = "leanasm" if module_name == "Main" else f"+{module_name}"
        rc, out, ms = run_lake_command(
            repo_root, ["lake", "build", target], profiler, label=module_name
        )
        lines = [f"$ lake build {target} -> exit={rc} ({ms} ms)"]
        if out:
            lines.append(out)

        if rc == 0 and check_axioms:
            ax_rc, ax_out, ax_ms = run_lake_command(
                repo_root,
                ["lake", "env", "lean", "tests/TestAxioms.lean"],
                profiler,
                label="tests/TestAxioms.lean",
            )
            lines.append(
                f"$ lake env lean tests/TestAxioms.lean -> exit={ax_rc} ({ax_ms} ms)"
            )
            if ax_out:
                lines.append(ax_out)
        return "\n".join(lines)

    return run_lean_check


def slice_module_source(mod_path: Path, max_source_chars: int) -> Tuple[str, str]:
    """Read and bound module source text (head + middle decl index + tail) for /api/chat."""
    raw_text = mod_path.read_text(encoding="utf-8")
    if len(raw_text) <= max_source_chars:
        return raw_text, ""
    head_budget = int(max_source_chars * 0.45)
    tail_budget = int(max_source_chars * 0.30)
    mid_budget = max(200, max_source_chars - head_budget - tail_budget - 160)
    head = raw_text[:head_budget]
    tail = raw_text[-tail_budget:]
    middle = raw_text[head_budget : len(raw_text) - tail_budget]
    mid_decls = [line.strip() for line in middle.splitlines() if DECL_RE.match(line)]
    mid_summary = "\n".join(mid_decls)[:mid_budget]
    source_slice = (
        f"{head}\n\n"
        f"-- [Middle declarations summary ({len(mid_decls)} items)]:\n"
        f"{mid_summary}\n\n"
        f"-- [Tail of module]:\n{tail}"
    )
    trunc_note = (
        f"\n(Note: condensed {len(raw_text)} chars -> {len(source_slice)} chars "
        f"via head + {len(mid_decls)} middle decl headers + tail.)"
    )
    return source_slice, trunc_note


def has_proof_items(mod_path: Path) -> bool:
    """Return True if a Lean module contains theorems, lemmas, defs, or types."""
    text = mod_path.read_text(encoding="utf-8")
    return any(DECL_RE.match(line) for line in text.splitlines())


def run_qwen_direct(
    mod_name: str,
    hygiene: Dict[str, Any],
    source_slice: str,
    trunc_note: str,
    orchestrator_model: str,
    ollama_root: str,
    profiler: AuditProfiler,
    num_ctx: int,
    num_predict: int,
    num_threads: Optional[int],
) -> Tuple[str, Dict[str, Any]]:
    """Run direct Qwen review on bounded module source via /api/chat."""
    qwen_prompt = (
        f"Review Lean 4 module `{mod_name}` (`{hygiene['rel_path']}`).\n"
        f"Pre-scan: lines={hygiene['line_count']}, header={hygiene['has_header']}, "
        f"footer={hygiene['has_footer']}, >100cols={len(hygiene['long_lines_gt_100'])}, "
        f"sorry={hygiene['sorry_lines']}, axiom={hygiene['axiom_lines']}, "
        f"choice={hygiene['choice_lines']}.\n"
        f"Provide a short Verdict (PASS/WARN/FAIL), any code/doc issues, "
        f"and 1-2 key theorems for DeepSeek-Prover to audit.{trunc_note}\n\n"
        f"```lean4\n{source_slice}\n```"
    )
    qwen_reply, q_ev = call_ollama_chat(
        ollama_root=ollama_root,
        model=orchestrator_model,
        system_msg=(
            "You are a concise Lean 4 (v4.35.0) code reviewer for leanasm. "
            "Output short, concrete bullet points."
        ),
        user_msg=qwen_prompt,
        profiler=profiler,
        event_kind="qwen_call",
        module_name=mod_name,
        num_ctx=num_ctx,
        num_predict=num_predict,
        num_threads=num_threads,
    )
    print(
        f"    [qwen-direct] {mod_name}: {q_ev.get('wall_ms')} ms, "
        f"eval={q_ev.get('eval_tok_s')} tok/s, ctx={q_ev.get('context_utilization_pct')}%"
    )
    return qwen_reply, q_ev


def run_deepseek_direct(
    mod_name: str,
    hygiene: Dict[str, Any],
    source_slice: str,
    trunc_note: str,
    prover_model: str,
    prover_root: str,
    profiler: AuditProfiler,
    num_ctx: int,
    num_predict: int,
    num_threads: Optional[int],
    qwen_reply: str = "",
) -> Tuple[str, Dict[str, Any]]:
    """Run direct DeepSeek-Prover audit on bounded module source via /api/chat."""
    qwen_note = (
        f"\n\nQwen focus notes:\n{qwen_reply[:450]}"
        if qwen_reply and not qwen_reply.startswith("Error:")
        else ""
    )
    hygiene_line = (
        f"Static scan: lines={hygiene['line_count']}, "
        f"unresolved_placeholders={len(hygiene['sorry_lines'])}, "
        f"custom_axioms={len(hygiene['axiom_lines'])}, "
        f"choice_refs={len(hygiene['choice_lines'])}."
    )
    ds_prompt = (
        f"Here is Lean 4 module `{mod_name}` (`{hygiene['rel_path']}`). "
        f"{hygiene_line}{trunc_note}\n\n"
        f"```lean4\n{source_slice}\n```{qwen_note}\n\n"
        "Perform a concise mathematical & proof audit of the declarations above.\n"
        "Respond ONCE with these 4 short markdown bullets (never repeat headings):\n"
        "- **Proof Verdict**: PASS | WARN | FAIL\n"
        "- **Preconditions & Edge Cases**: key hypotheses or domain guards\n"
        "- **Constructiveness & Soundness**: constructiveness vs. classical assumptions\n"
        "- **Simplifications / Follow-ups**: concrete Lean 4 (no Mathlib) ideas\n\n"
        "IMPORTANT: State each bullet once, never repeat lines, and do NOT echo source code."
    )
    ds_reply, ds_ev = call_ollama_chat(
        ollama_root=prover_root,
        model=prover_model,
        system_msg=(
            "You are a Lean 4 (v4.35.0) mathematical proof auditor for leanasm. "
            "Write 4 short non-repeating English bullets once and stop. "
            "Never repeat headings or echo input Lean code."
        ),
        user_msg=ds_prompt,
        profiler=profiler,
        event_kind="deepseek_call",
        module_name=mod_name,
        num_ctx=num_ctx,
        num_predict=num_predict,
        num_threads=num_threads,
    )
    print(
        f"    [deepseek-direct] {mod_name}: {ds_ev.get('wall_ms')} ms "
        f"(load={ds_ev.get('load_duration_ms')} ms), "
        f"eval={ds_ev.get('eval_tok_s')} tok/s, ctx={ds_ev.get('context_utilization_pct')}%"
    )
    return ds_reply, ds_ev


def append_direct_step(
    entry: Optional[Dict[str, Any]],
    mod_name: str,
    tool_tag: str,
    heading: str,
    reply: str,
    ev: Dict[str, Any],
) -> Dict[str, Any]:
    """Initialize or merge a direct Qwen/DeepSeek step into an ai_reviews record."""
    if entry is None:
        entry = {
            "module": mod_name,
            "duration_ms": 0.0,
            "tool_calls": [],
            "usage": {
                "prompt_token_count": 0,
                "candidates_token_count": 0,
                "total_token_count": 0,
            },
            "context_utilization_pct": None,
            "review": "",
        }
    entry["duration_ms"] = round(entry["duration_ms"] + ev.get("wall_ms", 0.0), 2)
    entry["tool_calls"].append(tool_tag)
    u = entry["usage"]
    u["prompt_token_count"] += ev.get("prompt_eval_count", 0)
    u["candidates_token_count"] += ev.get("eval_count", 0)
    u["total_token_count"] = u["prompt_token_count"] + u["candidates_token_count"]
    ctx_pct = ev.get("context_utilization_pct")
    if ctx_pct is not None:
        prev = entry["context_utilization_pct"]
        entry["context_utilization_pct"] = ctx_pct if prev is None else max(prev, ctx_pct)
    block = f"#### {heading}\n\n{reply}"
    entry["review"] = f"{entry['review']}\n\n{block}" if entry["review"] else block
    return entry


def maybe_run_deepseek_direct(
    mod_name: str,
    mod_path: Path,
    hygiene: Dict[str, Any],
    source_slice: str,
    trunc_note: str,
    prover_model: str,
    prover_root: str,
    profiler: AuditProfiler,
    num_ctx: int,
    num_predict: int,
    num_threads: Optional[int],
    qwen_reply: str = "",
) -> Tuple[str, str, Dict[str, Any]]:
    """Run DeepSeek-Prover unless module is an import-only barrel."""
    if not has_proof_items(mod_path):
        print(f"    [deepseek-skip] {mod_name}: import-only barrel (no declarations)")
        profiler.record(
            "deepseek_skip", module=mod_name, reason="import_only_barrel"
        )
        return (
            "skip:import-only",
            "_(Skipped DeepSeek-Prover: import-only barrel module with no declarations.)_",
            {},
        )
    ds_reply, ds_ev = run_deepseek_direct(
        mod_name,
        hygiene,
        source_slice,
        trunc_note,
        prover_model,
        prover_root,
        profiler,
        num_ctx,
        num_predict,
        num_threads,
        qwen_reply=qwen_reply,
    )
    return f"direct:{prover_model}", ds_reply, ds_ev


def review_module_direct(
    mod_name: str,
    mod_path: Path,
    hygiene: Dict[str, Any],
    orchestrator_model: str,
    prover_model: str,
    ollama_root: str,
    prover_root: str,
    profiler: AuditProfiler,
    num_ctx: int,
    num_predict: int,
    max_source_chars: int,
    num_threads: Optional[int],
    prover_only: bool,
    qwen_only: bool = False,
) -> Dict[str, Any]:
    """Run deterministic source injection into Qwen and/or DeepSeek via /api/chat."""
    source_slice, trunc_note = slice_module_source(mod_path, max_source_chars)
    entry: Optional[Dict[str, Any]] = None
    qwen_reply = ""
    if not prover_only:
        qwen_reply, q_ev = run_qwen_direct(
            mod_name,
            hygiene,
            source_slice,
            trunc_note,
            orchestrator_model,
            ollama_root,
            profiler,
            num_ctx,
            num_predict,
            num_threads,
        )
        entry = append_direct_step(
            entry,
            mod_name,
            f"direct:{orchestrator_model}",
            f"Qwen (`{orchestrator_model}`) Review",
            qwen_reply,
            q_ev,
        )
        if qwen_only:
            return entry

    ds_tag, ds_reply, ds_ev = maybe_run_deepseek_direct(
        mod_name,
        mod_path,
        hygiene,
        source_slice,
        trunc_note,
        prover_model,
        prover_root,
        profiler,
        num_ctx,
        num_predict,
        num_threads,
        qwen_reply=qwen_reply,
    )
    return append_direct_step(
        entry,
        mod_name,
        ds_tag,
        f"DeepSeek-Prover (`{prover_model}`) Audit",
        ds_reply,
        ds_ev,
    )


async def review_single_module(
    repo_root: Path,
    mod_name: str,
    hygiene: Dict[str, Any],
    orchestrator_model: str,
    prover_model: str,
    ollama_root: str,
    prover_root: str,
    v1_url: str,
    profiler: AuditProfiler,
    num_threads: Optional[int],
    lightweight: bool,
) -> Dict[str, Any]:
    """Run a bounded read-only Qwen + DeepSeek audit on one Lean module."""
    prover_tool = make_deepseek_audit_tool(
        prover_root, prover_model, profiler, mod_name, num_threads=num_threads
    )
    check_tool = make_lean_check_tool(repo_root, profiler)

    capabilities = CapabilitiesConfig(
        enable_subagents=False,
        enabled_tools=[
            BuiltinTools.LIST_DIR,
            BuiltinTools.SEARCH_DIR,
            BuiltinTools.FIND_FILE,
            BuiltinTools.VIEW_FILE,
            BuiltinTools.FINISH,
        ],
    )
    config = LocalOpenAIAgentConfig(
        model=orchestrator_model,
        base_url=v1_url,
        system_instructions=AUDITOR_INSTRUCTIONS,
        capabilities=capabilities,
        tools=[prover_tool, check_tool],
        workspaces=[str(repo_root)],
    )
    if lightweight:
        config = config.lightweight()

    prompt = (
        f"Audit Lean 4 module `{mod_name}` at `{hygiene['rel_path']}`.\n"
        f"Pre-scan facts: lines={hygiene['line_count']}, "
        f"header={hygiene['has_header']}, footer={hygiene['has_footer']}, "
        f"sorry_lines={hygiene['sorry_lines']}, "
        f"axiom_lines={hygiene['axiom_lines']}, "
        f"choice_lines={hygiene['choice_lines']}, "
        f"long_lines_gt_100={len(hygiene['long_lines_gt_100'])}.\n"
        f"1. Read `{hygiene['rel_path']}` with view_file.\n"
        f"2. Run `run_lean_check(module_name='{mod_name}')`.\n"
        f"3. Call `ask_deepseek_prover` on 1-2 key theorems.\n"
        f"4. Summarize Verdict (PASS/WARN/FAIL) and key findings concisely."
    )

    t0 = time.monotonic()
    tool_names: List[str] = []
    text_chunks: List[str] = []
    thought_chars = 0
    call_start_times: Dict[str, float] = {}
    usage_dict: Dict[str, int] = {}

    async with Agent(config) as agent:
        response = await agent.chat(prompt)
        async for chunk in response.chunks:
            if isinstance(chunk, types.ToolCall):
                tool_names.append(chunk.name)
                call_id = str(getattr(chunk, "id", "") or f"{chunk.name}:{len(tool_names)}")
                call_start_times[call_id] = time.monotonic()
                args_json = json.dumps(getattr(chunk, "args", None), default=str)
                profiler.record(
                    "tool_call",
                    module=mod_name,
                    call_id=call_id,
                    tool=chunk.name,
                    args_chars=len(args_json),
                    args_preview=args_json[:240],
                )
                print(f"    [tool] {mod_name} -> {chunk.name} ({len(args_json)} chars)")
            elif isinstance(chunk, types.ToolResult):
                call_id = str(getattr(chunk, "id", "") or "")
                started = call_start_times.pop(call_id, t0)
                tool_ms = round((time.monotonic() - started) * 1000.0, 2)
                raw_res = getattr(chunk, "result", "")
                res_str = raw_res if isinstance(raw_res, str) else json.dumps(raw_res, default=str)
                err_val = getattr(chunk, "error", None) or getattr(chunk, "exception", None)
                profiler.record(
                    "tool_result",
                    module=mod_name,
                    call_id=call_id,
                    tool=getattr(chunk, "name", ""),
                    duration_ms=tool_ms,
                    result_chars=len(res_str),
                    is_error=bool(err_val),
                    error=str(err_val) if err_val else None,
                )
            elif isinstance(chunk, types.Thought):
                thought_chars += len(chunk.text)
            elif isinstance(chunk, types.Text):
                text_chunks.append(chunk.text)
        if response.usage_metadata is not None:
            um = response.usage_metadata
            usage_dict = {
                "prompt_token_count": int(um.prompt_token_count or 0),
                "candidates_token_count": int(um.candidates_token_count or 0),
                "thoughts_token_count": int(um.thoughts_token_count or 0),
                "cached_content_token_count": int(um.cached_content_token_count or 0),
                "total_token_count": int(um.total_token_count or 0),
            }

    duration_ms = round((time.monotonic() - t0) * 1000.0, 2)
    review_text = "".join(text_chunks).strip()
    snap = profiler.record_snapshot("after_qwen_module", ollama_root, mod_name)

    ctx_util_pct: Optional[float] = None
    ps_models = (snap.get("ollama_ps") or {}).get("models", [])
    for m in ps_models:
        if orchestrator_model in m.get("name", "") and m.get("context_length", 0) > 0:
            ptok = usage_dict.get("prompt_token_count", 0)
            if ptok > 0:
                ctx_util_pct = round(100.0 * ptok / m["context_length"], 2)
            break

    profiler.record(
        "qwen_review",
        module=mod_name,
        model=orchestrator_model,
        duration_ms=duration_ms,
        tool_calls=tool_names,
        thought_chars=thought_chars,
        review_chars=len(review_text),
        context_utilization_pct=ctx_util_pct,
        **usage_dict,
    )
    return {
        "module": mod_name,
        "duration_ms": duration_ms,
        "tool_calls": tool_names,
        "usage": usage_dict,
        "context_utilization_pct": ctx_util_pct,
        "review": review_text,
    }


def load_checkpoint(out_dir: Path) -> Dict[str, Any]:
    """Load checkpoint.json from an interrupted or paused audit directory."""
    ckpt_path = out_dir / "checkpoint.json"
    if not ckpt_path.is_file():
        raise FileNotFoundError(f"No checkpoint.json found in {out_dir}")
    return json.loads(ckpt_path.read_text(encoding="utf-8"))


def write_outputs(
    out_dir: Path,
    summary: Dict[str, Any],
    hygiene_rows: List[Dict[str, Any]],
    ai_reviews: List[Dict[str, Any]],
    axiom_result: Optional[Dict[str, Any]],
) -> None:
    """Persist profile_summary.json and report.md in out_dir."""
    summary_path = out_dir / "profile_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    lines = [
        "# LeanAsm Codebase Audit & Profiling Report",
        "",
        f"- **Generated (UTC)**: {utc_now_iso()}",
        f"- **Total Wall Time**: {summary['total_wall_s']} s",
        f"- **Modules Audited**: {len(hygiene_rows)}",
        f"- **Lake Checks**: {summary['lake_checks']['count']} "
        f"(failures={summary['lake_checks']['failures']}, "
        f"total={summary['lake_checks']['total_ms']} ms)",
        f"- **Qwen Reviews**: {summary['qwen_reviews']['count']} "
        f"(total={summary['qwen_reviews']['total_ms']} ms, "
        f"prompt_tok={summary['qwen_reviews']['prompt_tokens']}, "
        f"cand_tok={summary['qwen_reviews']['candidate_tokens']}, "
        f"max_ctx_pct={summary['qwen_reviews']['max_context_utilization_pct']})",
        f"- **DeepSeek Calls**: {summary['deepseek_calls']['count']} "
        f"(load_swap={summary['deepseek_calls']['total_load_swap_ms']} ms, "
        f"eval_tok={summary['deepseek_calls']['total_eval_tokens']}, "
        f"avg_tok_s={summary['deepseek_calls']['avg_eval_tok_s']})",
        f"- **Tool Trace**: calls={summary['tool_trace']['total_tool_calls']}, "
        f"errors={summary['tool_trace']['tool_errors']}",
        "",
        "## Memory, VRAM & Context Telemetry",
        "",
        f"- **WSL2 Peak RAM Used**: "
        f"{summary['memory_telemetry']['peak_wsl_ram_used_mb']} MB",
        f"- **Python / Child (lake) Peak RSS**: "
        f"{summary['memory_telemetry']['peak_python_max_rss_mb']} MB / "
        f"{summary['memory_telemetry']['peak_child_max_rss_mb']} MB",
        f"- **Ollama Peak VRAM / CPU Spill**: "
        f"{summary['memory_telemetry']['peak_ollama_vram_mb']} MB / "
        f"{summary['memory_telemetry']['peak_ollama_cpu_spill_mb']} MB "
        f"(max_concurrent_models="
        f"{summary['memory_telemetry']['max_concurrent_models_loaded']})",
        "",
    ]
    models_obs = summary["memory_telemetry"].get("models_observed", {})
    if models_obs:
        lines.extend(
            [
                "| Model | Quant | Max Size (MB) | Max VRAM (MB) | CPU Spill (MB) | Context Len |",
                "| :--- | :---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for mname, mstats in models_obs.items():
            lines.append(
                f"| `{mname}` | {mstats.get('quantization', '')} | "
                f"{mstats.get('max_size_mb', 0.0)} | "
                f"{mstats.get('max_vram_mb', 0.0)} | "
                f"{mstats.get('max_cpu_spill_mb', 0.0)} | "
                f"{mstats.get('context_length', 0)} |"
            )
        lines.append("")

    lines.extend(
        [
            "## Static Hygiene Summary",
            "",
            "| Module | Lines | Header/Footer | >100 Cols | sorry | axiom | choice |",
            "| :--- | ---: | :---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for h in hygiene_rows:
        hf = f"{'Y' if h['has_header'] else 'N'}/{'Y' if h['has_footer'] else 'N'}"
        lines.append(
            f"| `{h['module']}` | {h['line_count']} | {hf} | "
            f"{len(h['long_lines_gt_100'])} | {len(h['sorry_lines'])} | "
            f"{len(h['axiom_lines'])} | {len(h['choice_lines'])} |"
        )

    if axiom_result is not None:
        lines.extend(
            [
                "",
                "## Axiom Audit (`tests/TestAxioms.lean`)",
                "",
                f"- **Exit Code**: {axiom_result['exit_code']}",
                f"- **Duration**: {axiom_result['duration_ms']} ms",
            ]
        )

    if ai_reviews:
        lines.extend(["", "## Qwen + DeepSeek Module Reviews", ""])
        for item in ai_reviews:
            lines.extend(
                [
                    f"### `{item['module']}` ({item['duration_ms']} ms)",
                    f"- **Tools Called**: {', '.join(item['tool_calls']) or 'none'}",
                    f"- **Tokens**: {item['usage']}",
                    f"- **Context Utilization**: {item.get('context_utilization_pct')}%",
                    "",
                    item["review"] or "*(No textual summary emitted)*",
                    "",
                ]
            )

    (out_dir / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    """Build CLI argument parser for codebase auditor."""
    parser = argparse.ArgumentParser(
        description="Run Qwen + DeepSeek codebase audit with full profiling."
    )
    parser.add_argument(
        "--modules",
        nargs="*",
        default=None,
        help="Optional subset of dotted module names (e.g. LeanAsm.MiniVM).",
    )
    parser.add_argument(
        "--offset",
        type=int,
        default=0,
        help="Start index in discovered module list (default: 0).",
    )
    parser.add_argument(
        "--max-modules",
        type=int,
        default=None,
        help="Optional cap on number of modules to audit.",
    )
    parser.add_argument(
        "--build-each",
        action="store_true",
        help="Run deterministic 'lake build +<Module>' per module before AI review.",
    )
    parser.add_argument(
        "--check-axioms",
        action="store_true",
        help="Run 'lake env lean tests/TestAxioms.lean' and profile it.",
    )
    parser.add_argument(
        "--deterministic-only",
        action="store_true",
        help="Skip Qwen/DeepSeek LLM calls; run static + lake checks only.",
    )
    parser.add_argument(
        "--orchestrator-model",
        default=DEFAULT_ORCHESTRATOR_MODEL,
        help=f"Tool-calling orchestrator model (default: {DEFAULT_ORCHESTRATOR_MODEL}).",
    )
    parser.add_argument(
        "--prover-model",
        default=DEFAULT_PROVER_MODEL,
        help=f"Lean 4 proof auditor model (default: {DEFAULT_PROVER_MODEL}).",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override Ollama URL (default: $AGY_OLLAMA_BASE_URL or $OLLAMA_HOST).",
    )
    parser.add_argument(
        "--prover-base-url",
        default=None,
        help="Optional separate Ollama URL for DeepSeek-Prover (e.g. remote SSH tunnel).",
    )
    parser.add_argument(
        "--no-lightweight",
        action="store_true",
        help="Disable SDK .lightweight() presets.",
    )
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Optional explicit output directory under logs/traces/.",
    )
    parser.add_argument(
        "--resume",
        default=None,
        help="Resume a paused/interrupted audit from an existing audit directory.",
    )
    parser.add_argument(
        "--direct",
        action="store_true",
        help="Send exact .lean source directly to Qwen & DeepSeek via /api/chat (best for CPU).",
    )
    parser.add_argument(
        "--prover-only",
        action="store_true",
        help="With --direct, skip Qwen and run DeepSeek-Prover only (avoids CPU model swaps).",
    )
    parser.add_argument(
        "--qwen-only",
        action="store_true",
        help="With --direct, skip DeepSeek and run Qwen only (fast review, zero model swap).",
    )
    parser.add_argument(
        "--two-phase",
        action="store_true",
        help="With --direct, run Qwen across all modules first, then DeepSeek (avoids swaps).",
    )
    parser.add_argument(
        "--num-ctx",
        type=int,
        default=4096,
        help="Context window passed to Ollama in --direct mode (default: 4096).",
    )
    parser.add_argument(
        "--num-predict",
        type=int,
        default=384,
        help="Max generated tokens per model call in --direct mode (default: 384).",
    )
    parser.add_argument(
        "--max-source-chars",
        type=int,
        default=8000,
        help="Max source characters sent per module in --direct mode (default: 8000).",
    )
    parser.add_argument(
        "--num-threads",
        type=int,
        default=None,
        help="Optional Ollama CPU thread count (options.num_thread) in /api/chat calls.",
    )
    parser.add_argument(
        "--cooldown-secs",
        type=float,
        default=0.0,
        help="Optional pause in seconds between modules/calls for laptop cooling.",
    )
    parser.add_argument(
        "--budget-secs",
        type=float,
        default=None,
        help="Optional wall-clock budget in seconds; pauses cleanly between modules.",
    )
    return parser


def _budget_exceeded(args: argparse.Namespace, run_t0: float, mod_name: str) -> bool:
    """Return True and log if optional wall-clock budget has elapsed."""
    if args.budget_secs is None:
        return False
    elapsed_run = time.monotonic() - run_t0
    if elapsed_run >= args.budget_secs:
        print(f"[*] Budget ({args.budget_secs}s) reached; pausing before {mod_name}.")
        return True
    return False


def _cooldown_pause(cooldown_secs: float, has_more: bool) -> None:
    """Sleep briefly between inference turns when thermal cooldown is configured."""
    if cooldown_secs > 0 and has_more:
        print(f"    [cooldown] sleeping {cooldown_secs}s...")
        time.sleep(cooldown_secs)


def _run_deterministic_step(
    repo_root: Path,
    mod_name: str,
    mod_path: Path,
    args: argparse.Namespace,
    profiler: AuditProfiler,
    hygiene_rows: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """Run static hygiene scan and optional lake build for a module."""
    hygiene = scan_module_hygiene(repo_root, mod_name, mod_path)
    hygiene_rows.append(hygiene)
    profiler.record("hygiene_scan", **hygiene)
    if args.build_each:
        target = "leanasm" if mod_name == "Main" else f"+{mod_name}"
        rc, _, ms = run_lake_command(
            repo_root, ["lake", "build", target], profiler, label=mod_name
        )
        print(f"    [lake] {target} exit={rc} ({ms} ms)")
        if args.deterministic_only:
            profiler.record_snapshot("after_lake_build", None, mod_name)
    return hygiene


async def async_main(args: argparse.Namespace) -> int:
    """Execute deterministic scan, optional lake builds, and AI audit."""
    repo_root = Path(__file__).resolve().parent.parent
    ollama_root, v1_url = normalize_urls(args.base_url)
    prover_root = (
        normalize_urls(args.prover_base_url)[0]
        if args.prover_base_url
        else ollama_root
    )

    if args.resume:
        out_dir = Path(args.resume).resolve()
        ckpt = load_checkpoint(out_dir)
        hygiene_rows: List[Dict[str, Any]] = list(ckpt.get("hygiene_rows", []))
        ai_reviews: List[Dict[str, Any]] = list(ckpt.get("ai_reviews", []))
        completed_list: List[str] = list(ckpt.get("completed_modules", []))
        completed_set = set(completed_list)
        axiom_result: Optional[Dict[str, Any]] = ckpt.get("axiom_result")
    else:
        slug = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        out_dir = (
            Path(args.out_dir).resolve()
            if args.out_dir
            else repo_root / "logs" / "traces" / f"audit_{slug}"
        )
        hygiene_rows = []
        ai_reviews = []
        completed_list = []
        completed_set = set()
        axiom_result = None

    profiler = AuditProfiler(out_dir)

    discovered = discover_lean_modules(repo_root)
    if args.modules:
        wanted = set(args.modules)
        discovered = [(m, p) for m, p in discovered if m in wanted]
        missing = sorted(wanted - {m for m, _ in discovered})
        if missing:
            print(f"[!] Unknown module(s): {', '.join(missing)}", file=sys.stderr)
            return 1

    if args.offset > 0:
        discovered = discovered[args.offset :]
    if args.max_modules is not None:
        discovered = discovered[: args.max_modules]

    pending = [(m, p) for m, p in discovered if m not in completed_set]

    print(
        f"[+] Audit run {'resumed' if args.resume else 'started'}: "
        f"total={len(discovered)}, completed={len(completed_set)}, "
        f"pending={len(pending)}, deterministic_only={args.deterministic_only}, "
        f"out_dir={out_dir}"
    )
    profiler.record_snapshot(
        "audit_start", None if args.deterministic_only else ollama_root
    )

    paused = False
    interrupted = False
    run_t0 = time.monotonic()

    def save_progress() -> None:
        summary_so_far = profiler.build_summary()
        write_outputs(out_dir, summary_so_far, hygiene_rows, ai_reviews, axiom_result)
        profiler.write_checkpoint(
            hygiene_rows,
            ai_reviews,
            completed_list,
            axiom_result,
            status="in_progress",
        )

    try:
        use_two_phase = (
            not args.deterministic_only
            and args.direct
            and args.two_phase
            and not args.prover_only
            and not args.qwen_only
        )
        if use_two_phase:
            hygiene_map = {h["module"]: h for h in hygiene_rows}
            review_map = {r["module"]: r for r in ai_reviews}
            print("[+] Two-phase mode: Phase 1/2 (deterministic + Qwen across pending)")
            for idx, (mod_name, mod_path) in enumerate(pending, 1):
                if _budget_exceeded(args, run_t0, mod_name):
                    paused = True
                    break
                print(f"[1/2 {idx}/{len(pending)}] Scanning/Qwen {mod_name}...")
                hygiene = hygiene_map.get(mod_name)
                if hygiene is None:
                    hygiene = _run_deterministic_step(
                        repo_root, mod_name, mod_path, args, profiler, hygiene_rows
                    )
                    hygiene_map[mod_name] = hygiene
                if mod_name not in review_map:
                    source_slice, trunc_note = slice_module_source(
                        mod_path, args.max_source_chars
                    )
                    qwen_reply, q_ev = run_qwen_direct(
                        mod_name,
                        hygiene,
                        source_slice,
                        trunc_note,
                        args.orchestrator_model,
                        ollama_root,
                        profiler,
                        args.num_ctx,
                        args.num_predict,
                        args.num_threads,
                    )
                    entry = append_direct_step(
                        None,
                        mod_name,
                        f"direct:{args.orchestrator_model}",
                        f"Qwen (`{args.orchestrator_model}`) Review",
                        qwen_reply,
                        q_ev,
                    )
                    entry["qwen_reply"] = qwen_reply
                    ai_reviews.append(entry)
                    review_map[mod_name] = entry
                    save_progress()
                    _cooldown_pause(args.cooldown_secs, True)

            if not paused:
                print("[+] Two-phase mode: Phase 2/2 (DeepSeek-Prover across pending)")
                for idx, (mod_name, mod_path) in enumerate(pending, 1):
                    if _budget_exceeded(args, run_t0, mod_name):
                        paused = True
                        break
                    print(f"[2/2 {idx}/{len(pending)}] DeepSeek {mod_name}...")
                    hygiene = hygiene_map[mod_name]
                    entry = review_map.get(mod_name)
                    qwen_reply = str((entry or {}).pop("qwen_reply", ""))
                    source_slice, trunc_note = slice_module_source(
                        mod_path, args.max_source_chars
                    )
                    ds_tag, ds_reply, ds_ev = maybe_run_deepseek_direct(
                        mod_name,
                        mod_path,
                        hygiene,
                        source_slice,
                        trunc_note,
                        args.prover_model,
                        prover_root,
                        profiler,
                        args.num_ctx,
                        args.num_predict,
                        args.num_threads,
                        qwen_reply=qwen_reply,
                    )
                    updated = append_direct_step(
                        entry,
                        mod_name,
                        ds_tag,
                        f"DeepSeek-Prover (`{args.prover_model}`) Audit",
                        ds_reply,
                        ds_ev,
                    )
                    if entry is None:
                        ai_reviews.append(updated)
                        review_map[mod_name] = updated
                    completed_list.append(mod_name)
                    completed_set.add(mod_name)
                    save_progress()
                    _cooldown_pause(
                        args.cooldown_secs,
                        idx < len(pending) and ds_tag != "skip:import-only",
                    )
        else:
            for idx, (mod_name, mod_path) in enumerate(pending, 1):
                if _budget_exceeded(args, run_t0, mod_name):
                    paused = True
                    break

                print(f"[{idx}/{len(pending)}] Auditing {mod_name}...")
                hygiene = _run_deterministic_step(
                    repo_root, mod_name, mod_path, args, profiler, hygiene_rows
                )

                if not args.deterministic_only:
                    if args.direct:
                        review = review_module_direct(
                            mod_name=mod_name,
                            mod_path=mod_path,
                            hygiene=hygiene,
                            orchestrator_model=args.orchestrator_model,
                            prover_model=args.prover_model,
                            ollama_root=ollama_root,
                            prover_root=prover_root,
                            profiler=profiler,
                            num_ctx=args.num_ctx,
                            num_predict=args.num_predict,
                            max_source_chars=args.max_source_chars,
                            num_threads=args.num_threads,
                            prover_only=args.prover_only,
                            qwen_only=args.qwen_only,
                        )
                    else:
                        review = await review_single_module(
                            repo_root=repo_root,
                            mod_name=mod_name,
                            hygiene=hygiene,
                            orchestrator_model=args.orchestrator_model,
                            prover_model=args.prover_model,
                            ollama_root=ollama_root,
                            prover_root=prover_root,
                            v1_url=v1_url,
                            profiler=profiler,
                            num_threads=args.num_threads,
                            lightweight=not args.no_lightweight,
                        )
                        print(
                            f"    [qwen] {mod_name} finished in {review['duration_ms']} ms "
                            f"(tools={len(review['tool_calls'])})"
                        )
                    ai_reviews.append(review)

                completed_list.append(mod_name)
                completed_set.add(mod_name)
                save_progress()
                if not args.deterministic_only:
                    _cooldown_pause(args.cooldown_secs, idx < len(pending))

        if not paused and args.check_axioms:
            print("[*] Running tests/TestAxioms.lean...")
            ax_rc, _, ax_ms = run_lake_command(
                repo_root,
                ["lake", "env", "lean", "tests/TestAxioms.lean"],
                profiler,
                label="tests/TestAxioms.lean",
            )
            axiom_result = {"exit_code": ax_rc, "duration_ms": ax_ms}
            print(f"    [axioms] exit={ax_rc} ({ax_ms} ms)")
    except (KeyboardInterrupt, asyncio.CancelledError):
        interrupted = True
        print("\n[!] Audit interrupted; saving checkpoint and partial report...")

    final_status = (
        "interrupted" if interrupted else ("paused" if paused else "completed")
    )
    summary = profiler.build_summary()
    write_outputs(out_dir, summary, hygiene_rows, ai_reviews, axiom_result)
    profiler.write_checkpoint(
        hygiene_rows, ai_reviews, completed_list, axiom_result, status=final_status
    )

    print(f"[+] Audit {final_status} in {summary['total_wall_s']}s.")
    print(f"    Report:     {out_dir / 'report.md'}")
    print(f"    Profile:    {out_dir / 'profile_summary.json'}")
    print(f"    Events:     {out_dir / 'events.jsonl'}")
    print(f"    Checkpoint: {out_dir / 'checkpoint.json'}")
    if interrupted or paused:
        print(f"    Resume with: python local/auditor.py --resume {out_dir}")
        return 130 if interrupted else 2
    return 0


def main() -> int:
    """CLI entrypoint."""
    args = build_parser().parse_args()
    try:
        return asyncio.run(async_main(args))
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    raise SystemExit(main())

# end of file: leanasm/local/auditor.py
