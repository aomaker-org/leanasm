<!-- Path: leanasm/local/README.md -->
<!-- Max Column: 80 Columns -->

# Local Quota-Free Agent Runner (`./local`)

This directory provides a quota-free local Ollama runner for `leanasm` when
cloud `agy` quota is exhausted or when testing local models
(`deepseek-prover:7b` and `qwen2.5-coder:7b`) on Windows via WSL2 mirrored
networking.

## Files

- [setup.sh](setup.sh) — Creates `.venv` via `uv` and installs
  `google-antigravity`.
- [requirements.txt](requirements.txt) — Python dependencies for SDK mode.
- [agent.py](agent.py) — Local interactive/one-shot agent runner supporting
  both Antigravity Python SDK (`LocalOpenAIAgentConfig`) and zero-dependency
  Ollama HTTP mode (`--http`).

## 1. One-Time Setup

Run `./local/setup.sh` from the repository root to install `google-antigravity`
into `.venv`, then re-source `config_env`:

```bash
chmod +x local/setup.sh local/agent.py
./local/setup.sh
source config_env dev
```

If you want to skip installing the Python SDK, `local/agent.py --http` works
immediately using only the Python standard library.

## 2. Selecting a Local Model via `config_env`

`local/agent.py` reads `AGY_MODEL` and `AGY_OLLAMA_BASE_URL` (or `OLLAMA_HOST`)
exported by `config_env`. After `./local/setup.sh`, `source config_env`
auto-activates `.venv` so `python local/agent.py` uses `google-antigravity`
directly (or use `uv run --with-requirements local/requirements.txt ...`):

- **Multi-step agentic / tool-calling loops** (`qwen2.5-coder:7b` handles tool
  JSON more reliably):

  ```bash
  source config_env qwen
  python local/agent.py --write
  ```

- **Lean 4 tactic / theorem sketching** (`deepseek-prover:7b`):

  ```bash
  source config_env deepseek
  python local/agent.py --http
  ```

## 3. Usage Examples

```bash
# Interactive SDK agent (read-only by default, uses activated .venv)
python local/agent.py

# Or run SDK mode via uv without manually creating .venv
uv run --with-requirements local/requirements.txt python local/agent.py

# Interactive SDK agent with workspace write/command tools enabled
python local/agent.py --write

# One-shot SDK prompt with custom model override
python local/agent.py --model qwen2.5-coder:7b \
    -p "Summarize the theorems in src/LeanAsm/MiniVM.lean."

# Zero-dependency HTTP chat directly against Ollama /v1/chat/completions
python3 local/agent.py --http \
    -p "Draft a constructive Lean 4 proof outline for Nat.add_comm."

# Load AI.md as explicit system context
python3 local/agent.py --http --system-file AI.md
```

## 4. Verification Discipline

After applying any locally generated Lean 4 edits, always verify with Lean 4
and the zero-axiom gate before committing:

```bash
lake build +LeanAsm.<Module>
lake env lean tests/TestAxioms.lean
make sync
```

<!-- end of file: leanasm/local/README.md -->
