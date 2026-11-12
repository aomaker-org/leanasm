# Path: leanasm/README.md
# leanasm: Lean 4 Exploration Workspace

An exploration workspace for Lean 4 theorem proving, verified algorithms,
and assembly / systems-level verification.

## Prerequisites & Toolchain

The Lean toolchain is managed via [elan](https://github.com/leanprover/elan):

- **Lean Version**: Lean 4 (defined in `lean-toolchain`)
- **Build Manager**: Lake (Lean's build tool and package manager)

To ensure `elan` and `lake` are in your active shell path, source `config_env`:
```bash
source config_env
```

## Quick Start

```bash
# Check toolchain status
make status

# Build the Lean executable
make build

# Run the Lean program
make run

# Run workspace verification
make test
```

## Project Structure

```
leanasm/
├── .editorconfig       # Code formatting standards
├── .gitignore          # Lake artifacts & transient log rules
├── AGENTS.md           # Governance pointer for AI assistants
├── AI.md               # Workspace directives and coding standards
├── config_env          # Shell environment setup
├── lake-manifest.json  # Lake dependency manifest
├── lakefile.toml       # Lake package configuration
├── lean-toolchain      # Active Lean toolchain pinned version
├── Makefile            # Convenience targets (build, run, test, status)
├── Main.lean           # Entrypoint Lean module
├── src/                # Reusable Lean libraries
├── tests/              # Verification suites and proofs
└── tools/              # Utilities (run_with_logging.py)
```

<!-- end of file: leanasm/README.md -->
