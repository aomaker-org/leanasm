# Path: leanasm/AI.md
# Workspace Specification & Consolidated AI Directives (`AI.md`)
# Max Column: 80 Columns

Notice to AI Agents: This document defines operational directives, environment
boundaries, and repository hygiene for all assistants operating within the
`leanasm` workspace.

---

## Level-1 Executive Directives Kernel

### [Directive 01] OPERATIONAL BOUNDARIES & COMMAND INTEGRITY
- **Constructive Pushback**: AI assistants are strictly forbidden from acting
  as blind "yes-men". Challenge input with industry best practices and
  architectural integrity.
- **Mandatory Toolchain Hygiene**: Use `lake` and `lean` via `elan` for all
  Lean package builds, verification, and executions. If Python scripts are
  used, execute via `uv` or standard virtual environments.
- **Safe Shell Usage**: Always use standard Linux bash.

### [Directive 02] LOGGING & DIAGNOSTIC OBSERVABILITY
- **Zero Silent Suppression**: NEVER redirect diagnostic streams to `/dev/null`
  or suppress command failures with `|| true` unless strictly required.
- **Structured Logging**: Use `tools/run_with_logging.py` for audit trails and
  long-running tasks when running outside interactive terminals.

### [Directive 04] FILE FORMATTING, LINE WRAPPING, & HEADER/FOOTER RULES
- **Line Wrapping**:
  - Text and Markdown (`.md`): Maximum **80 columns**.
  - Code files (`.lean`, `.py`, `.sh`): Target **80 columns**; max **120 chars**.
- **File Headers & Footers**:
  - Every file MUST contain a clear header identifying the file path.
  - Every file MUST contain a footer comment specifying the relative file path.
    - Markdown: `<!-- end of file: leanasm/AI.md -->`
    - Lean / Shell / Python: `# end of file: leanasm/AI.md` or `-- end of file`

### [Directive 07] GIT BRANCHING & WORKFLOW STANDARDS
- **Branch-Per-Feature Mandate**: Work in dedicated feature branches
  (`feature/*`, `fix/*`).
- **History Immutability**: Git history must NEVER be overwritten, squashed,
  or destroyed (`git reset --hard` and `git clean -fd` are prohibited).
- **Additive Artifact Operations**: Generated traces and execution logs
  are strictly additive.

### [Directive 08] AUTOMATED TURN-SYNC HANDOVER
- Run `make sync` at turn completion to verify git status, run tests, and check
  cleanliness.

<!-- end of file: leanasm/AI.md -->
