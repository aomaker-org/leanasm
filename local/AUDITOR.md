<!-- Path: leanasm/local/AUDITOR.md -->
<!-- Max Column: 80 Columns -->

# Qwen + DeepSeek Codebase Auditor & Profiler

`local/auditor.py` runs a read-only, profiled codebase review across `leanasm`
modules using **`qwen2.5-coder:7b`**, **`deepseek-prover:7b`**, and
**`lake`**.

- **`--direct` (recommended on CPU-only laptops)**: Injects deterministic
  static/build results and bounded source (`--max-source-chars`) straight into
  Ollama `/api/chat` without SDK tool schemas (~2.5k tokens saved per module),
  bounding generation with `--num-predict` (default `384`) and `--num-ctx`
  (default `4096`).
- **SDK tool-calling mode (default in `auditor.py`, opt-in via `--sdk` in
  `usingQwenPlusDeepseek.sh`)**: Runs Qwen with `view_file` /
  `search_directory` / `run_lean_check` / `ask_deepseek_prover`. Requires larger
  context/VRAM; 7B models on 4k CPU context often exceed context or misemit
  tool JSON.
- **`--prover-only` / `--qwen-only`**: With `--direct`, runs only
  `deepseek-prover:7b` (`--prover-only`) or only `qwen2.5-coder:7b`
  (`--qwen-only`) so a CPU-only host avoids swapping two ~4.5–6 GB GGUF
  models in RAM.
- **`--two-phase`**: With `--direct`, runs Qwen across all pending modules
  first, then DeepSeek across them — keeping 1 model warm per phase (~2 loads
  total instead of `2*N` swaps/SSD reads). Supports `--cooldown-secs` (thermal
  pauses), `--num-threads` (`options.num_thread`), and `--prover-base-url`
  (optional separate Ollama node for DeepSeek, e.g. over SSH tunnel).

## Profiling Outputs

Every run writes additive artifacts to `logs/traces/audit_<timestamp>/`:

- `events.jsonl` — Flushed after every check/call (safe across long runs).
  Captures wall-clock `duration_ms`, `lake` exit codes, verbose per-tool
  `tool_call`/`tool_result` timings and payload sizes, Qwen token counts and
  context utilization, Ollama `/api/chat` hardware timings (`load_duration_ms`,
  `prompt_eval_tok_s`, `eval_tok_s`), and `memory_snapshot` events (WSL2
  `/proc/meminfo`, Python/`lake` peak RSS, and Ollama `/api/ps` VRAM, CPU
  spill, and `context_length`).
- `profile_summary.json` — Aggregated timings, token totals, context usage,
  peak WSL2/child RSS, peak Ollama VRAM/CPU spill, and swap overhead.
- `report.md` — Memory/VRAM/context table, static hygiene table (`sorry`,
  `axiom`, `Classical.choice`, `>100` col lines, headers/footers), and
  per-module Qwen + DeepSeek reviews.

## Usage Examples

```bash
. config_env

# 1. Fast deterministic baseline (static scan + lake build + TestAxioms.lean)
python local/auditor.py --deterministic-only --build-each --check-axioms \
  --max-modules 3

# 2. CPU-friendly direct Qwen + DeepSeek 1-module trial
python local/auditor.py --direct \
  --modules LeanAsm.QuasiRiemann.MollifierVariationalBridge \
  --no-check-axioms

# 3. Single-model DeepSeek-Prover audit (no Qwen<->DeepSeek RAM swap on CPU)
python local/auditor.py --direct --prover-only --build-each --check-axioms

# 4. Two-phase CPU sweep (avoids Qwen<->DeepSeek RAM/SSD swaps) + cooldown
python local/auditor.py --direct --two-phase --cooldown-secs 15 \
  --build-each --check-axioms --max-modules 5

# 5. Full codebase sweep (long-running; log stdout too per Directive 02)
python3 tools/run_with_logging.py -l full-audit \
  ".venv/bin/python local/auditor.py --direct --two-phase --check-axioms"

# 6. Resume / slice a sweep with --budget-secs or Ctrl+C checkpointing
python local/auditor.py --direct --two-phase --budget-secs 600 \
  --build-each --check-axioms
python local/auditor.py --direct --two-phase \
  --resume logs/traces/audit_<timestamp> --build-each --check-axioms
```

## Hardware Profiling Notes (CPU-Only Laptops vs. GPUs)

- `vram_mb = 0.0` with `cpu_spill_mb` ~4200–4850 MB in `memory_snapshot`
  confirms CPU-only execution (`~4–5 tok/s` prompt eval, `~2–4 tok/s` decode).
  Use `--direct` (and optionally `--prover-only` or `--num-predict 256`) to
  keep per-module time around ~2–5 minutes on CPU.
- `load_duration_ms` in `events.jsonl` and `total_load_swap_ms` in
  `profile_summary.json` measure whether Ollama keeps both 7B models resident
  or reloads weights between Qwen and DeepSeek turns.
- On 12+ GB VRAM Windows hosts, setting `OLLAMA_MAX_LOADED_MODELS=2` avoids
  repeatedly reloading weights during long audits.

<!-- end of file: leanasm/local/AUDITOR.md -->
