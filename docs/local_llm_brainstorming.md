<!-- Path: leanasm/docs/local_llm_brainstorming.md -->
<!-- Max Column: 80 Columns -->

# Local LLM Experiment Notes & Brainstorming

Working notes from local Ollama (`qwen2.5-coder:7b` + `deepseek-prover:7b`)
codebase auditing and profiling experiments on CPU-only laptop hardware.

## 1. Observed Hardware & Runtime Baseline

- **Primary node (`core12`)**: Windows Ollama + WSL2 (`i7-1255U`, `4` WSL2
  vCPUs, `7944.55 MB` WSL2 RAM cap, `0.0 MB` GPU VRAM).
- **Context lengths**: Both models natively support `32768` (`32K`) tokens,
  while Ollama defaults runtime KV cache to `4096` unless `--num-ctx` or
  `OLLAMA_CONTEXT_LENGTH` is set.
- **CPU throughput (`4096` ctx)**:
  - `qwen2.5-coder:7b` (`Q4_K_M`, `4835.05 MB`): ~16–20 tok/s prompt eval,
    ~5–7 tok/s decode.
  - `deepseek-prover:7b` (`6052.82 MB` resident): ~14–15 tok/s prompt eval,
    ~3.8–5.1 tok/s decode.
  - Cold swap load between models: ~27–37 s per reload.

## 2. Key Architecture Lessons (`local/auditor.py`)

- **Direct `/api/chat` (`--direct`) beats SDK tool-calling on 7B CPU**:
  - SDK tool schemas consumed `61.91%` of `4096` context, and 7B Qwen emitted
    raw JSON text (`tool_calls=[]`) instead of executing structured tool calls.
  - Injecting deterministic hygiene + bounded `.lean` source directly cut
    prompt usage (`~10–44%` of 4k ctx) and delivered reliable reviews.
- **Avoid SSD write wear (`pagefile.sys` thrash)**:
  - Model weight reads are read-only; SSD write pressure comes from Windows
    `pagefile.sys` when Qwen (`4835 MB`) and DeepSeek (`6053 MB`) sit loaded
    concurrently (`10887.87 MB` combined) alongside Windows + WSL2.
  - Solution: `--two-phase` runs all Qwen passes first, then all DeepSeek
    passes (~2 model loads total instead of `2*N` swaps), optionally paired
    with Windows `OLLAMA_MAX_LOADED_MODELS=1` and `--cooldown-secs`.
- **DeepSeek-Prover prompt discipline**:
  - Placing instructions *after* the code fence stopped source-file echoing.
  - Adding `repeat_penalty=1.18`, `temperature=0.2`, removing `` `sorry` ``
    trigger wording, and skipping import-only barrels (`has_proof_items`)
    addressed 7B repetition loops and hallucinated critiques on stub barrels.

## 3. Thermals, Scheduling & Distributed Offload Ideas

- **Windows 90% thermal cap (optional)**: Setting AC Maximum Processor State
  to `90%` (`powercfg ... PROCTHROTTLEMAX 90`) prevents sustained Turbo heat
  across both Windows Ollama and WSL2 during overnight runs.
- **Burst + rest + resume**: Combine `--budget-secs`, `--cooldown-secs`, and
  `--resume logs/traces/audit_<timestamp>` for interruptible multi-day sweeps.
- **Secondary node (`core11` / `core11-local` at `10.0.0.213`)**:
  - `i7-1165G7`, `16 GB` Windows RAM, Intel Iris Xe (no NVIDIA GPU);
    `~/src/leanasm` updated cleanly to `79fd1e6` (`main`), no Ollama yet.
  - If Ollama + AC stay-awake are configured later, `--prover-base-url` allows
    keeping Qwen + `lake` on `core12` and DeepSeek-Prover warm on `core11`
    with zero model swapping on either laptop.

## 4. Zero-Quota Local Utilities & `openai-20261028` Triage

Target corpus: `subrepos/YM/submissions/openai-20261028` (already indexed in
`docs/openai-20261028/` via `scripts/scan_openai_submission.py`: `9,564` Lean
files, `100,680` declarations, and `782` candidate matches in
`QRH_7_8_CANDIDATES.md`).

- **Live trace/heartbeat viewer**: Lightweight Python CLI tailing
  `events.jsonl`, `checkpoint.json`, `/api/ps`, and Windows Ollama `server.log`
  during long unattended runs.
- **Structural RAG / QRH 7/8 candidate filter**: Instead of burning `agy`
  tokens scanning raw trees, use `LEAN_TOC.json` + `QRH_7_8_CANDIDATES.md`
  to retrieve exact lemma snippets and score constructive/cleared-denominator
  portability locally with Qwen + DeepSeek overnight, handing `agy` a compact
  shortlist.
- **Fine-tuning vs. retrieval on CPU hardware**:
  - Full 7B training or QLoRA is impractical on CPU-only `16 GB` laptops
    (best done via `LEAN_TOC.json` JSONL export + external 24 GB GPU if ever
    desired to adapt Lean naming/tactic style).
  - Structural lookup (`LEAN_TOC.json`) + targeted Ollama `Modelfile` system
    context run locally on CPU with zero GPU needed and stay 100% current.

## 5. `agy` Quota & Routing Strategy (Through Nov 20)

With `gemini-weekly` at `5.89%`, avoid **Gemini 4 Hydrogen** and **Gemini 3.8
Flash** completely and route onto untouched pools:

1. **Gemini 4 Argon at `--effort medium` or `low` ONLY (never `high`)**:
   - **Routing bug**: Setting Gemini 4 Argon with `--effort high` diverts
     requests into `gemini-weekly` instead of `gemini-argon-wtu-weekly`.
   - **Safe preset (`source config_env argon`)**: Sets
     `AGY_CLI_MODEL=gemini-4-argon-medium` and `AGY_CLI_EFFORT=medium` (or
     `argon-low` for `low`), deducting cleanly from `gemini-argon-wtu-weekly`.
2. **Claude Sonnet 5.5 (`source config_env sonnet`) for `lake` & file edits**:
   - Uses the untouched `3p-weekly` / `3p-5h` buckets (`100%`) for multi-file
     Lean 4 edits and compiler loops, keeping **Claude Opus 5.5** (`opus`) in
     reserve for hard proof roadblocks.
3. **Warm interactive `agy` sessions + local Ollama (`./local/`)**:
   - Stay inside a single warm interactive `agy` session (rather than repeated
     `agy -p` one-shots) to preserve prompt cache hits, while offloading routine
     `omega` / `decide` searches and codebase audits to local Ollama.

<!-- end of file: leanasm/docs/local_llm_brainstorming.md -->
