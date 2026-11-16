<!-- Path: leanasm/docs/ollama_local.md -->
<!-- Max Column: 80 Columns -->

# Local Hybrid Ollama Architecture (`leanasm` + WSL2 + Windows)

## Overview

This guide specifies the local hybrid LLM setup for `leanasm`, pairing a
native **Windows Ollama service** (direct host GPU access and NTFS weight
storage) with the **WSL2 Ubuntu** Lean 4 (`leanprover/lean4:v4.35.0`)
development environment and `agy` agentic workflows.

Running Ollama natively on Windows avoids duplicating multi-gigabyte model
weights inside the WSL2 virtual disk (`ext4.vhdx`) while allowing WSL2 tools
to reach the inference server seamlessly over `http://localhost:11434` using
**WSL2 mirrored networking**.

## Hybrid Architecture

```text
+-------------------------------------------------------------------------+
| Windows 11 Host                                                         |
|                                                                         |
|  +------------------------+         +--------------------------------+  |
|  | Model Store            |         | Native Ollama Service          |  |
|  | C:\AI_models           | <-----> | 127.0.0.1:11434                |  |
|  | (OLLAMA_MODELS env)    |         | Model: deepseek-prover:7b      |  |
|  +------------------------+         +--------------------------------+  |
|                                                    ^                    |
+----------------------------------------------------|--------------------+
                                                     | Loopback
                                                     | (networkingMode=
                                                     |  mirrored)
+----------------------------------------------------|--------------------+
| WSL2 Ubuntu (leanasm workspace)                    v                    |
|                                                                         |
|  +-------------------------------------------------------------------+  |
|  | config_env (LEANASM_USE_OLLAMA=1)                                 |  |
|  |   OLLAMA_HOST=http://localhost:11434                              |  |
|  |   AGY_LLM_PROVIDER=ollama                                         |  |
|  |   AGY_MODEL=deepseek-prover:7b                                    |  |
|  |   AGY_OLLAMA_BASE_URL=http://localhost:11434                      |  |
|  +-------------------------------------------------------------------+  |
|                    |                               ^                    |
|                    v                               |                    |
|  +--------------------------------+   +------------------------------+  |
|  | agy / Proof-Search Loop        |-->| lake build / lake env lean   |  |
|  | (Tactic & Lemma Synthesis)     |<--| tests/TestAxioms.lean Audit  |  |
|  +--------------------------------+   +------------------------------+  |
+-------------------------------------------------------------------------+
```

## 1. Windows Model Storage (`C:\AI_models`)

Store all Ollama blobs and manifests under `C:\AI_models` on the Windows NTFS
filesystem so weights remain independent of WSL2 disk images and persist across
WSL2 resets.

1. Create the directory in Windows PowerShell:

   ```powershell
   New-Item -ItemType Directory -Force -Path "C:\AI_models"
   ```

2. Set `OLLAMA_MODELS` permanently on Windows (use `"Machine"` if running
   Ollama as a system service, or `"User"` for a user-session tray app):

   ```powershell
   [System.Environment]::SetEnvironmentVariable(
       "OLLAMA_MODELS",
       "C:\AI_models",
       "User"
   )
   ```

3. Restart the Ollama application or service on Windows so it picks up the
   updated `OLLAMA_MODELS` path, then pull your local models.

   Note that `qwen2.5-coder:7b` is in the official Ollama library, whereas
   `deepseek-prover:7b` is not an official top-level library tag. Pull a
   community DeepSeek-Prover GGUF/Ollama build (or import a local GGUF via
   `Modelfile`) and alias it to `deepseek-prover:7b` so `config_env` resolves
   it automatically:

   ```powershell
   # Official coding/reasoning baseline (optional comparison model)
   ollama pull qwen2.5-coder:7b

   # Community DeepSeek-Prover-V2-7B GGUF (Q4_K_M ~4.2 GB) aliased to default
   ollama pull yothgewalt/DeepSeek-Prover-V2-7B-GGUF:Q4_K_M
   ollama cp yothgewalt/DeepSeek-Prover-V2-7B-GGUF:Q4_K_M deepseek-prover:7b
   ollama list
   ```

4. Confirm that `C:\AI_models\blobs` and `C:\AI_models\manifests` are
   populated.

## 2. WSL2 Mirrored Networking Setup

WSL2's default NAT networking isolates WSL2 `localhost` from Windows loopback
services. Enabling **mirrored networking** shares the host loopback interface
between Windows and WSL2 Ubuntu so `http://localhost:11434` resolves directly
without exposing Ollama on external network interfaces (`0.0.0.0`).

1. Edit or create `%UserProfile%\.wslconfig` on Windows:

   ```ini
   [wsl2]
   networkingMode=mirrored
   ```

2. Restart WSL2 from Windows PowerShell to apply the configuration:

   ```powershell
   wsl --shutdown
   ```

3. Reopen your WSL2 Ubuntu terminal and verify connectivity to the Windows
   Ollama instance:

   ```bash
   curl -sS http://localhost:11434/api/tags
   curl -sS http://localhost:11434/v1/models
   ```

   Both endpoints should return JSON listing `deepseek-prover:7b`.

## 3. Repository Environment Configuration (`config_env`)

Sourcing `config_env` configures `elan`/`lake`, optional `.venv`, and the
local Ollama / `agy` environment variables.

```bash
source config_env dev
```

### Exported Variables (Ollama Enabled by Default)

When `LEANASM_USE_OLLAMA` is `1` (the default), `config_env` exports:

| Variable | Default Value | Purpose |
| :--- | :--- | :--- |
| `LEANASM_USE_OLLAMA` | `1` | Master toggle (`1` enabled, `0` disabled) |
| `OLLAMA_HOST` | `http://localhost:11434` | Ollama CLI / API endpoint |
| `AGY_LLM_PROVIDER` | `ollama` | Selects Ollama provider for local SDK |
| `AGY_MODEL` | `deepseek-prover:7b` | Default local Ollama prover model |
| `AGY_OLLAMA_BASE_URL` | `http://localhost:11434` | Local Ollama base URL |
| `AGY_CLI_MODEL` | *(unset)* | Optional `agy_session` `--model` override |

Note: `config_env` intentionally does **not** mutate
`~/.gemini/antigravity-cli/settings.json` so repo-local settings never
clobber other workspaces or concurrent `agy` sessions. Use `agy_session`
with `--flash`, `--hydrogen`, `--argon`, or `--cli-model <id>` to pass
session-only `--model` overrides to `agy`.

### Enabling, Disabling, and Switching via Tags, Flags, or Env Vars

You can switch providers or models directly with `config_env` tags/flags or
via `export LEANASM_USE_OLLAMA=...`:

```bash
# 1. Default local Ollama with deepseek-prover:7b
source config_env dev
source config_env deepseek      # explicit tag alias (also: prover)
source config_env hum --prover  # keep custom run tag 'hum'

# 2. Switch local Ollama to qwen2.5-coder:7b
source config_env qwen          # sets tag='qwen', AGY_MODEL=qwen2.5-coder:7b
source config_env hum --qwen    # keeps tag='hum', AGY_MODEL=qwen2.5-coder:7b
source config_env dev --model qwen2.5-coder:7b

# 3. Disable local Ollama and select a session agy CLI model (non-mutating)
source config_env gemini        # unsets OLLAMA_HOST / AGY_*
source config_env argon         # gemini-4-argon-medium (--effort medium ONLY)
source config_env sonnet        # claude-sonnet-5-5-high (3p-weekly / 3p-5h)
agy_session                     # runs: agy --model "$AGY_CLI_MODEL" ...

# 4. Override host URL, clear AGY_CLI_MODEL, or inspect all flags
source config_env dev --host http://localhost:11434 --reset-cli-model
source config_env --help
```

If using environment variables instead of flags, `export LEANASM_USE_OLLAMA=...`
before sourcing `config_env` (avoid `VAR=0 source config_env`, because bash
restores `VAR` after `source` returns if it was already exported):

```bash
export LEANASM_USE_OLLAMA=0
source config_env dev
```

Accepted `LEANASM_USE_OLLAMA` truthy values: `1`, `true`, `yes`, `on`,
`enable`, `enabled`. Falsy values: `0`, `false`, `no`, `off`, `disable`,
`disabled`.

## 4. Agentic Theorem-Proving Loops on Lean 4 Modules

Follow the `AI.md` directives when running local prover loops against modules
in `src/LeanAsm/` (for example `MiniVM.lean`, `RnsArithmetic.lean`,
`CrtNtt.lean`, `FiniteFieldRH.lean`, `YangMillsQ8.lean`, or
`src/LeanAsm/QuasiRiemann/*`).

### Step 1: Prepare Branch and Environment

```bash
git checkout -b feature/<prover-task>
source config_env dev
make status
curl -sS http://localhost:11434/api/tags
```

### Step 2: Launch Local SDK / `agy_session` Against Target Modules

- **Antigravity CLI (`agy`)**: Run `agy_session` (which passes
  `--model "$AGY_CLI_MODEL"` and optional `--effort "$AGY_CLI_EFFORT"` when
  set, e.g., `gemini-4-argon-medium` at `--effort medium` or
  `claude-sonnet-5-5-high`) scoped to a single module and its direct imports.
  Never use `--effort high` with Gemini 4 Argon, as it diverts requests into
  `gemini-weekly` instead of `gemini-argon-wtu-weekly`.
- **Antigravity Python SDK (Local Ollama)**: Connect Python agents directly to
  Ollama's OpenAI-compatible endpoint using `LocalOpenAIAgentConfig`:

```python
import os
from google.antigravity import Agent, LocalOpenAIAgentConfig

config = LocalOpenAIAgentConfig(
    model=os.environ["AGY_MODEL"],
    base_url=f"{os.environ['AGY_OLLAMA_BASE_URL']}/v1",
).lightweight()
agent = Agent(config=config)
```

Recommended prompting and loop discipline for `deepseek-prover:7b`:

- **Target one theorem or helper lemma per iteration**: Keep context focused on
  the theorem signature, local helper definitions, and exact `lake` errors.
- **Keep proofs constructive**: `leanasm` requires zero `sorryAx` and zero
  `Classical.choice` across `LeanAsm.leanasm_full_provenance_certified`.
- **Use targeted module builds during search**: Compile only the active module
  instead of rebuilding the whole tree on every tactic candidate:

  ```bash
  lake build +LeanAsm.MiniVM
  lake env lean src/LeanAsm/MiniVM.lean
  ```

- **Log long-running autonomous loops**: Wrap scripted proof searches with
  `tools/run_with_logging.py` to preserve full stdout/stderr audit trails in
  `logs/tasks/` (Directive 02):

  ```bash
  python3 tools/run_with_logging.py -l prover-loop \
      "lake build +LeanAsm.QuasiRiemann.DyadicAbelBridge"
  ```

- **Stateful REPL / Best-First Search**: For automated tactic-tree search
  against `leanprover-community/repl` or Pantograph, reuse the OpenAI-
  compatible endpoint `http://localhost:11434/v1/chat/completions` with model
  `deepseek-prover:7b`. See the
  [llama.cpp prover architecture](llama_cpp_prover_architecture.md)
  for the REPL JSON-lines protocol and search loop topology.

### Step 3: Post-Proof Verification and Zero-Axiom Gate

After splicing a candidate proof into `src/LeanAsm/`, run the full verification
gate before committing:

```bash
# 1. Incremental cached build of all workspace modules
make build-incremental

# 2. Audit transitive axiom closures (must show 0 Classical.choice, 0 sorryAx)
lake env lean tests/TestAxioms.lean

# 3. Handover sync check (status + build + executable test)
make sync
```

## 5. Troubleshooting

- **Connection refused on `http://localhost:11434`**:
  - Verify Ollama is running on Windows (`Get-Process ollama` in PowerShell).
  - Verify `%UserProfile%\.wslconfig` contains `networkingMode=mirrored` under
    `[wsl2]` and run `wsl --shutdown` from PowerShell.
  - Check Windows Defender Firewall rules if loopback traffic is blocked.
- **Model `deepseek-prover:7b` not found**:
  - Run `ollama list` on Windows to verify the exact tag.
  - Confirm `OLLAMA_MODELS=C:\AI_models` is set in the same Windows scope
    (User vs Machine) under which the Ollama process runs, then restart Ollama.
- **Slow generation or CPU fallback**:
  - Run `ollama ps` on Windows while generating to confirm GPU layer offload.
  - Ensure no competing GPU workloads hold VRAM during proof-search loops.
- **Switching back to non-Ollama providers**:
  - Run `source config_env gemini` (or `source config_env --no-ollama`) to
    clear `OLLAMA_HOST`, `AGY_LLM_PROVIDER`, `AGY_MODEL`, and
    `AGY_OLLAMA_BASE_URL`.

<!-- end of file: leanasm/docs/ollama_local.md -->
