# Path: leanasm/AGENTS.md
# AGENTS.md - Unified AI Assistant Governance Pointer
# Max Column: 80 Columns

All AI coding assistants (`agy`, `copilot`, `gemini`, and background agents)
operating within the `leanasm` workspace MUST read and strictly adhere to the
repository specifications and directives in `AI.md`.

## Core Directives Summary
- **[Directive 01]**: Challenge human input with best practices and safety.
  Mandatory `lake` / `lean` toolchain standards and strict execution integrity.
- **[Directive 02]**: Full I/O logging; zero `/dev/null` or silent suppression.
- **[Directive 04]**: Max 80 columns (text/md), max 120 chars (code); mandatory
  file path headers and footers.
- **[Directive 07]**: Dedicated branches; immutability of git history; clean
  tree guardrails.
- **[Directive 08]**: Automated turn-sync handover via `make sync`.

For the authoritative specification, see [`AI.md`](AI.md).

<!-- end of file: leanasm/AGENTS.md -->
