# Path: leanasm/README.md
# leanasm: Lean 4 & Neural Prover Exploration Workspace

An exploration workspace for Lean 4 theorem proving, verified algorithms,
and assembly / systems-level verification paired with local quantized neural
prover models (`llama.cpp`).

## Prerequisites & Toolchain

The Lean toolchain is managed via [elan](https://github.com/leanprover/elan):

- **Lean Version**: Lean 4 (pinned in `lean-toolchain`)
- **Build Manager**: Lake (Lean's package and build manager)
- **Local Neural Prover Engine**: `llama.cpp` (`llama-server`)

To activate `elan`, `lake`, and your workspace environment, source `config_env`:
```bash
# Optional tag argument: hum, dev, test, etc.
source config_env hum
```

## Quick Start

```bash
# Check toolchain and workspace status
make status

# Build the Lean executable
make build

# Run the Lean program
make run

# Run workspace verification
make test

# Check submodule hydration status
make hydrate-status
```

## Prover Integration & Submodule Hydration

- **Local `llama.cpp` Prover**: Details on wiring `llama-server` to a Lean 4
  REPL (`leanprover-community/repl` or `Pantograph`) for tactic search are
  documented in [`docs/llama_cpp_prover_architecture.md`](docs/llama_cpp_prover_architecture.md).
- **Lazy Submodule Hydration**: Modeled on `clouds-labs`, subrepos can be
  hydrated on-demand (`make hydrate SUB=<name>`) or dehydrated to reclaim disk
  space (`make dehydrate SUB=<name>`). See [`docs/lazy_hydration_guide.md`](docs/lazy_hydration_guide.md).

## Project Structure

```
leanasm/
├── .editorconfig       # Code formatting standards
├── .gitignore          # Lake artifacts & transient log rules
├── AGENTS.md           # Governance pointer for AI assistants
├── AI.md               # Workspace directives and coding standards
├── config_env          # Shell environment setup with run tags
├── docs/               # Architecture guides and specifications
│   ├── lazy_hydration_guide.md
│   └── llama_cpp_prover_architecture.md
├── inbox/              # Ingested research notes and reference memos
├── lake-manifest.json  # Lake dependency manifest
├── lakefile.toml       # Lake package configuration
├── lean-toolchain      # Active Lean toolchain pinned version
├── Makefile            # Convenience targets (build, run, test, sync, hydrate)
├── mk/                 # Modular makefile extensions (hydrate.mk)
├── Main.lean           # Entrypoint Lean module
├── src/                # Reusable Lean libraries
├── tests/              # Verification suites and proofs
└── tools/              # Utilities (run_with_logging.py)
```

<!-- end of file: leanasm/README.md -->
