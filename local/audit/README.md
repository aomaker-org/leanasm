<!-- Path: leanasm/local/audit/README.md -->
<!-- Max Column: 80 Columns -->

# Qwen + DeepSeek Codebase Audit Runner (`local/audit`)

[usingQwenPlusDeepseek.sh](usingQwenPlusDeepseek.sh) wraps
[../auditor.py](../auditor.py) with `config_env` activation, Ollama
connectivity preflight, and Directive 02 I/O logging
(`tools/run_with_logging.py`).

By default it passes `--direct --build-each --check-axioms`, avoiding SDK
tool-schema overhead on CPU-only laptops (pass `--sdk` to opt back into
Antigravity SDK tool-calling, or `--prover-only` to run only DeepSeek-Prover
without swapping models in RAM).

## Examples

```bash
# Show wrapper and auditor options
./local/audit/usingQwenPlusDeepseek.sh --help

# Quick 1-module direct Qwen + DeepSeek + Lake trial (CPU-friendly)
./local/audit/usingQwenPlusDeepseek.sh --no-check-axioms \
  --modules LeanAsm.QuasiRiemann.MollifierVariationalBridge

# Two-phase direct batch with cooling pauses (avoids model-swap SSD thrash)
./local/audit/usingQwenPlusDeepseek.sh --two-phase --cooldown-secs 15 \
  --no-check-axioms --modules LeanAsm.MiniVM LeanAsm.YangMillsQ8

# Split Qwen (local Ollama) and DeepSeek (remote Ollama on port 11435)
./local/audit/usingQwenPlusDeepseek.sh \
  --prover-base-url http://localhost:11435 --modules LeanAsm.MiniVM

# Single-model Qwen-only direct audit (fast code/doc review, zero swap)
./local/audit/usingQwenPlusDeepseek.sh --qwen-only \
  --modules LeanAsm.MiniVM

# Single-model DeepSeek-Prover direct audit (no Qwen/DeepSeek RAM swap)
./local/audit/usingQwenPlusDeepseek.sh --prover-only \
  --modules LeanAsm.MiniVM

# Opt back into SDK tool-calling mode (best on GPU / >=8k ctx)
./local/audit/usingQwenPlusDeepseek.sh --sdk --modules LeanAsm.MiniVM

# Fast deterministic hygiene + build check (no Ollama calls)
./local/audit/usingQwenPlusDeepseek.sh --deterministic-only --max-modules 3

# Full codebase audit (long-running; logs to logs/tasks/ and logs/traces/)
./local/audit/usingQwenPlusDeepseek.sh
```

<!-- end of file: leanasm/local/audit/README.md -->
