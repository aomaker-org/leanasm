<!-- Path: leanasm/local/PROVER_ORCHESTRATOR.md -->
<!-- Max Column: 80 Columns -->

# Hierarchical Qwen + DeepSeek-Prover Orchestrator

`local/prover_orchestrator.py` pairs **`qwen2.5-coder:7b`** (tool-calling
orchestrator) with **`deepseek-prover:7b`** (Lean 4 tactic synthesis) and
**`lake build`** inside the Antigravity Python SDK (`LocalOpenAIAgentConfig`).

## Architecture

1. **Orchestrator (`qwen2.5-coder:7b`)**: Reads `.lean` files using focused
   workspace tools (`view_file`, `search_directory`, `find_file`,
   `list_directory`, plus `edit_file`/`create_file`/`run_command` when
   `--write` is passed).
2. **Prover Tool (`synthesize_lean_prover_tactic`)**: Custom Python tool
   bound to the agent that calls `deepseek-prover:7b` at
   `http://localhost:11434/v1/chat/completions` with the exact theorem context
   and compiler feedback.
3. **Kernel Verifier (`verify_lean_module`)**: Custom Python tool that runs
   `lake build +<module>` (and optionally `lake env lean tests/TestAxioms.lean`)
   so every candidate proof is checked by the Lean 4 (`v4.35.0`) kernel.

## Prerequisites

1. Run `./local/setup.sh` once to install `google-antigravity` into `.venv`.
2. Pull both local models on Windows Ollama (`qwen2.5-coder:7b` and aliased
   `deepseek-prover:7b`).
3. **VRAM Note**: Two 7B `Q4_K_M` models need ~9 GB+ VRAM (plus KV cache) to
   stay resident together. On Windows PowerShell, set
   `OLLAMA_MAX_LOADED_MODELS=2` if you have >= 12 GB VRAM; on 8 GB GPUs, Ollama
   will automatically swap models between orchestration and proof-synthesis
   turns.

## Usage

```bash
. config_env

# Read-only inspection + verification (safe default)
python local/prover_orchestrator.py \
  -p "Inspect src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean and
verify LeanAsm.QuasiRiemann.MollifierVariationalBridge."

# Interactive orchestrator with write tools enabled
python local/prover_orchestrator.py --write

# Custom models or explicit base URL
python local/prover_orchestrator.py --write \
  --orchestrator-model qwen2.5-coder:7b \
  --prover-model deepseek-prover:7b \
  --base-url http://localhost:11434/v1
```

<!-- end of file: leanasm/local/PROVER_ORCHESTRATOR.md -->
