# Path: leanasm/agy/agy-startup.md
# agy-startup.md - Local Agent Context & Workflow Directives
# Max Column: 80 Columns

Notice to AI Agents: This document captures runtime context, workflow
conventions, and operational guardrails for assistants operating within the
`leanasm` workspace on core12 (`LAPTOP-AJPE53SG`, `10.99.0.12`).

---

## 1. Zero-Trust Verification Baseline
- **Zero-Trust Baseline**: Always verify local system, repository, and remote
  state directly with explicit commands rather than trusting unverified or
  mobile claims.
- **Never Silently Suppress Errors**: Never use `|| true`, `|| :`, or redirect
  output to `/dev/null` (`> /dev/null`, `2> /dev/null`). All diagnostic and
  error streams must remain visible in execution logs.
- **History Immutability**: Never overwrite, rebase, or squash git history.
  Strictly preserve history (`git reset --hard` and `git clean -fd` are
  strictly prohibited).
- **Dry & Read-Only Subrepos**: Keep `subrepos/*` dry/unhydrated per
  `[Directive 01]`. Treat hydrated subrepos as strictly read-only.

---

## 2. Workload & Host Boundary Guardrails
- **Silicon Validation Engineer Interview Boundary**:
  - Defer heavy `leanasm` proof development, large-scale refactoring, and WSL2
    RAM or host configuration changes until after the Dec 2, 2026 Microsoft
    Silicon Validation Engineer interview.
  - Keep repository operations bounded, verified, and low-risk.
- **Heavy Builds & Build-Timing Test Boundaries**:
  - Bound any Lean build with sequential execution and heap caps
    (`LEAN_OPTS="-M2048"` or `LEAN_OPTS="-M4096"` with `make build-seq`).
  - When conducting build timing tests (such as on core11 / `10.99.0.11` where
    `ridge-sled` runs with limited RAM ~3.3–3.5 GiB), maintain strict 5-minute
    check-in intervals.
  - Check WSL2 memory pressure (`free -h`, `vmstat`, `df -h / /tmp`) and Windows
    host disk/memory pressure every 5 minutes.
  - Monitor Google Drive for any `"stop work"` signal and halt immediately and
    cleanly if detected or if thrashing occurs.
  - Ensure graceful shutdown receipts are recorded; do not leave runaway builds.

---

## 3. Backlog Notes & Future Conventions (No Immediate Churn / No Emails)

### File Versioning and Timestamping Convention
- Follow standard timestamping and file versioning across working, staged,
  and archive directories:
  - **Date-First Canonical Prefix**: `YYMMDD` or `YYYYMMDD` (e.g. `261125_` or
    `20261125_`) for directories, sessions, and log bundles.
  - **ISO 8601 UTC / Local Snapshot Suffix**: `YYYYMMDD_HHMMSS` (e.g.
    `settings.json.bak.20261125_153837` or `AI.md.bak.20261125_164100`) for
    pre-change backup snapshots.
  - **Staged vs. Active vs. Archive Separation**:
    - Working / Active: working repository trees and active configs.
    - Staged: isolated test and validation staging directories (e.g.
      `261125_pods_sleds_stage/active`, `baseline`).
    - Archive: immutable historical logs, audits, and retired snapshots under
      dated archive paths.
  - **Immutable Append-Only Logging**: Generated metrics, audit logs, and
    traces remain strictly additive.

### Follow-Up `fekerr-dev` GitHub Issues to File / Review Later
*(Note: Queue for later review; do not open issues or send emails during this
operational turn)*:
1. **File Versioning & Timestamping Specification**: Standardize automated
   snapshot naming (`YYYYMMDD_HHMMSS`), staged vs. working tree separation,
   and retention policies across core hosts.
2. **Scheduled Zero-Trust Audit & Secret-Leak Scan**: Automated regular checks
   for secrets, permissions, and zero-trust verification baselines
   (tracked as `fekerr-dev#43`).
3. **Backup Policies & Cross-Storage Coverage**: Verify automated backup
   integrity across local, OneDrive, and Google Drive mirrors
   (tracked as `fekerr-dev#44`).
4. **Post-Dec 2 Workspace & Google Drive Cleanup Pass**: Structured cleanup
   and retirement pass following the Dec 2 interview (tracked as
   `fekerr-dev#45`).
5. **Windows Handoff Worker & pwsh Daemon**: Implement a validated background
   queue daemon to avoid WSL2-to-pwsh execution stalls.
6. **Turn Context & Quota Observability**: Implement per-turn token and context
   telemetry reporting.
7. **Family Dashboard & Operations Backlog**: Track Jensen Kerr family/home
   dashboard and operational utilities.
8. **Graceful Sled Shutdown Receipts**: Automated generation of cryptographic
   or state-verified receipts on sled termination.

---

<!-- end of file: leanasm/agy/agy-startup.md -->
