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
- **Background Task & Timer Hygiene**: One-shot 1-to-2-minute `Schedule`
  wake-up check-ins (`maxIterations=1`) are permitted during or between heavy
  `make` / `lake` steps to provide signs of life and check `free -h`, swap,
  `uptime`, and build log progress, with proactive replanning or decomposition
  on high load (never spawning overlapping builds). Sub-minute polling loops,
  repeated `ManageTask` calls on the same task ID (check/update at most once
  per step and proceed directly), `> /dev/null`, `|| true`, and running
  `lake build` inside read-only `subrepos/alpo-rh` remain strictly banned.
  Otherwise, run builds synchronously or end your turn and let the CLI harness
  auto-wake on task completion.
- **Safe Shell Usage**: Always use standard Linux bash.
- **Dry & Read-Only Subrepos**: Keep `subrepos/*` unhydrated ("dry") by default
  on new/secondary checkouts (do NOT run `git submodule update --init`).
  Whenever a subrepo is hydrated (such as `subrepos/alpo-rh`), treat it as
  strictly read-only—never edit files, cut branches, or run `lake build` inside
  `subrepos/*`.

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
- **Issue-Before-PR Mandate**: Tracking GitHub issues are strictly
  mandatory before opening a pull request, with zero exceptions. Always check
  for or create a tracking GitHub issue first, and ensure every PR references
  its tracking issue (e.g. `fixes #N`, `closes #N`, or `(#N)`).
- **History Immutability**: Git history must NEVER be overwritten, squashed,
  or destroyed (`git reset --hard` and `git clean -fd` are prohibited).
- **Additive Artifact Operations**: Generated traces and execution logs
  are strictly additive.

### [Directive 08] AUTOMATED TURN-SYNC HANDOVER
- Run `make sync` at turn completion when Lean code or build targets change;
  skip redundant runs on merge-only or docs-only turns unless requested.

<!-- end of file: leanasm/AI.md -->
