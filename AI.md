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
- **Constructive Axiom & Zero-Mathlib Invariant**: Keep the package strictly
  free of Mathlib dependencies; all proven theorems MUST reduce solely to
  `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`), verified
  via `make axioms` (`lake env lean tests/TestAxioms.lean`).
- **Preferred Build Strategy**: To prevent RAM thrashing and OOM terminations
  on heavy modules (e.g., `UltraDeep108N2048Part1/2`, `UltraDeep108N1024`,
  `CrtNtt`), assistants MUST prefer sequential, heap-capped elaboration via
  `make build-seq` or `python3 tools/incremental_build.py` (enforcing
  `-M 4096` / `LEAN_OPTS="-M4096"` and checking rolling build telemetry
  regression against `.lake/build-history.json` or via
  `python3 scripts/inspect_build_history.py`). Full unbounded concurrent builds
  (`lake build`) risk exhausting system memory; when running direct or ad-hoc
  `lake build <target>` tool commands, assistants MUST explicitly prefix them
  with `LEAN_OPTS="-M4096"` (or host-appropriate cap). Ongoing architecture
  work targets finer-grained modularization so units stay fast and lightweight.
- **Background Task & Timer Hygiene**: NEVER call `Schedule` or polling loops
  to watch long-running `make` or `lake` background tasks, and do not
  repeatedly call `ManageTask` on the same task ID (check/update a task ID at
  most once per step and proceed directly); run builds synchronously or end
  your turn and let the CLI harness auto-wake on task completion.
- **Safe Shell Usage**: Always use standard Linux bash.

### [Directive 02] LOGGING & DIAGNOSTIC OBSERVABILITY
- **Zero Silent Suppression**: NEVER redirect diagnostic streams to `/dev/null`
  or suppress command failures with `|| true` unless strictly required.
- **Structured Logging**: Use `tools/run_with_logging.py` for audit trails and
  long-running tasks when running outside interactive terminals.
- **Trial Helper-Script Logging**: When creating or executing any non-trivial
  helper script, append a single-line log entry recording timestamp, script
  path, and intent to `/tmp/agy_helper_scripts.log`; avoid refactoring or
  generalizing scripts prematurely and do not modify tracked files unless
  explicitly requested.

### [Directive 04] FILE FORMATTING, LINE WRAPPING, & HEADER/FOOTER RULES
- **Line Wrapping**:
  - Text and Markdown (`.md`): Maximum **80 columns**.
  - Code files (`.lean`, `.py`, `.sh`): Target **80 cols**; max **120 chars**.
- **File Headers & Footers**:
  - Every file MUST contain a clear header identifying the file path.
  - Every file MUST contain a footer comment specifying the relative file path.
    - Markdown: `<!-- end of file: leanasm/AI.md -->`
    - Lean / Shell / Python: `# end of file: leanasm/AI.md` or `-- end of file`

### [Directive 07] GIT BRANCHING & WORKFLOW STANDARDS
- **Branch-Per-Feature Mandate**: Work in dedicated feature branches
  (`feature/*`, `refactor/*`, `fix/*`, `chore/*`).
- **Issue-Before-PR Default**: Always check for or create a tracking GitHub
  issue before opening a pull request. Every PR must reference its tracking
  issue (e.g. `fixes #N` or `(#N)`), with narrow exceptions only for urgent
  hotfixes or explicit user override.
- **History Immutability**: Git history must NEVER be overwritten, squashed,
  or destroyed (`git reset --hard` and `git clean -fd` are prohibited).
- **Additive Artifact Operations**: Generated traces and execution logs
  are strictly additive.

### [Directive 08] AUTOMATED TURN-SYNC HANDOVER
- Run `make sync` at turn completion to verify git status, run tests, and check
  cleanliness.

<!-- end of file: leanasm/AI.md -->
