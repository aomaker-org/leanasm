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

# Run the verified MiniVM and Collatz demo
make run

# Run workspace verification
make test

# Check submodule hydration status
make hydrate-status
```

## Architecture & Mathematical Exploration

- **Yang–Mills QFT Formalization**: Comprehensive analysis of the 2026 4D pure
  Yang–Mills scaling limit formalization and independent verification suite:
  [`docs/yang_mills_formalization_overview.md`](docs/yang_mills_formalization_overview.md).
  - Check package integrity: `make ym-integrity`
  - Inspect YM subrepo status: `make ym-status`
- **Local `llama.cpp` Prover**: Wiring `llama-server` to a Lean 4 REPL
  (`leanprover-community/repl` or `Pantograph`) for automated tactic search:
  [`docs/llama_cpp_prover_architecture.md`](docs/llama_cpp_prover_architecture.md).
- **Lazy Submodule Hydration**: On-demand hydration (`make hydrate SUB=<name>`)
  or dehydration (`make dehydrate SUB=<name>`) modeled on `clouds-labs`:
  [`docs/lazy_hydration_guide.md`](docs/lazy_hydration_guide.md).
- **External Verification & Benchmarks**: External typecheckers (`comparator`,
  `nanoda`), axiom audits, and formalization benchmark suites:
  [`docs/external_verification_and_benchmarks.md`](docs/external_verification_and_benchmarks.md).

## Project Structure

```
leanasm/
├── .editorconfig       # Code formatting standards
├── .gitignore          # Lake artifacts & transient log rules
├── AGENTS.md           # Governance pointer for AI assistants
├── AI.md               # Workspace directives and coding standards
├── config_env          # Shell environment setup with run tags
├── docs/               # Architecture guides and specifications
│   ├── external_verification_and_benchmarks.md
│   ├── lazy_hydration_guide.md
│   ├── llama_cpp_prover_architecture.md
│   └── yang_mills_formalization_overview.md
├── inbox/              # Ingested research notes (gemweb001 - gemweb004)
├── lake-manifest.json  # Lake dependency manifest
├── lakefile.toml       # Lake package configuration
├── lean-toolchain      # Active Lean toolchain pinned version
├── Makefile            # Convenience targets (build, run, test, sync, hydrate, ym-*)
├── mk/                 # Modular makefile extensions (hydrate.mk)
├── Main.lean           # Entrypoint Lean module (runs MiniVM & Collatz)
├── src/                # Reusable Lean libraries
│   ├── LeanAsm.lean
│   └── LeanAsm/
│       ├── Conjectures.lean
│       └── MiniVM.lean
├── tests/              # Verification suites and proofs (TestAxioms.lean)
└── tools/              # Utilities (run_with_logging.py)
```

<!-- end of file: leanasm/README.md -->
