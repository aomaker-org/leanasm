<!-- Path: leanasm/docs/ROADMAP_V1_5_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.5.0 Architecture Roadmap & Milestone Synthesis

This roadmap documents the formal achievements and architectural expansion of
`aomaker-org/leanasm` on Lean `v4.35.0` (Lake `5.0.0-src+eb6cafb`), tracking the
synthesis weaves, variational bridge certificates, and ladder parameterizations
landed since `v1.4.0` (PRs `#116`–`#210`).

The repository scales to **106 verified Lean source modules** (97 imported in
[`src/LeanAsm.lean`](../src/LeanAsm.lean)), spanning **Parts 1–85** in
[`tests/TestAxioms.lean`](../tests/TestAxioms.lean) with strict zero-Mathlib,
zero `Classical.choice`, and zero `sorryAx` (`[propext, Quot.sound]` only).

---

## 1. Verified Inventory & State Probe (`v1.5.0`)

- **106 Lean Modules / 97 Top-Level Exports**:
  Complete zero-Mathlib formalization spanning MiniVM, Yang-Mills SU(2)/Q8 gauge
  models, Quasi-Riemann zero-free sweeps, Garner CRT / NTT towers, Chudnovsky
  105-digit $\pi$, Genus 2 Jacobian arithmetic, QSD[1-4] nilpotent algebras and
  Hensel prime-tower tangent lifts, generalized Beurling sieves (Lucky, Ludic,
  Hawkins, Ulam), and parametric reflection/mollifier bridges.
- **85 Axiom Audit Parts**:
  All 85 audit parts in [`tests/TestAxioms.lean`](../tests/TestAxioms.lean) pass
  strictly within `[propext, Quot.sound]` (or empty `[]`), free of `sorryAx`
  or classical choice.
- **Deterministic Incremental Build**:
  `tools/incremental_build.py` tracks 107 cache targets (106 modules + `leanasm`
  executable binary) executing sequentially under memory cap (`-M4096`).
- **Provenance Integrity**:
  [`src/LeanAsm/ProvenanceSummary.lean`](../src/LeanAsm/ProvenanceSummary.lean)
  synthesizes master zero-axiom certificates across all 11 CLI parts, including
  new bridge structures (`LeanAsmBridgeProvenance`,
  `ContractionReflectionBridgeProvenance`, and
  `MollifierVariationalBridgeProvenance`).

---

## 2. Landed Workstreams & PR Milestones (Post-`v1.4.0`)

### Workstream 1: Beurling Operators & Generalized Sieves (PR `#145`–`#197`)
- **Modules**:
  - `src/LeanAsm/QuasiRiemann/LuckySieve.lean` (Core & BeurlingCerts)
  - `src/LeanAsm/QuasiRiemann/SieveSequence.lean` (Core, BeurlingCerts,
    LuckyGenerators500)
  - `src/LeanAsm/QuasiRiemann/LuckyBeurlingStripWeave.lean`
  - `src/LeanAsm/QuasiRiemann/LuckyQrh78Strip.lean`
  - `src/LeanAsm/QuasiRiemann/SieveSequenceStripWeave.lean`
- **Scope & Issues**:
  - Landed Hawkins stochastic sieve models, Ulam recursive unique-sum sieves,
    logarithmic root-finding, and $N = 500$ Lucky prefix generators
    (resolving `#143` / `#146` / PR `#196`).
  - Proved rational Beurling kernel bounds and non-vanishing strip certificates
    under `[propext, Quot.sound]`.

### Workstream 2: QSD & Preperiodic Strip Weaves (PR `#193`–`#195`)
- **Modules**:
  - `src/LeanAsm/QuasiRiemann/PreperiodicQsd1StripWeave.lean`
  - `src/LeanAsm/QuasiRiemann/Qsd1IdempotentDyadicAbelWeave.lean`
  - `src/LeanAsm/QuasiRiemann/RnsGaussianNormBridge.lean`
- **Scope & Issues**:
  - Weaved `PreperiodicDynamics` rational partition and uniform divisibility
    bounds with `Qsd1LogDerivStripBridge` (PR `#193`, resolving `#128`).
  - Connected QSD[1] split idempotents ($(1 \pm L)/2$ with $L^2 = 1$) and
    $\text{logDeriv}$ strip bounds with high-truncation ($N = 1024, 2048$)
    dyadic-Abel rung contraction certificates (PR `#194`, resolving `#123`).
  - Extended `RnsInt` CRT channel bounds with `GaussianQsdBridge` norm bounds
    and multiplicativity (PR `#195`, resolving `#124`).

### Workstream 3: Parametric Rungs, Dyadic Gates & RNS (PR `#183`–`#190`)
- **Modules**:
  - `src/LeanAsm/QuasiRiemann/ParametricQrhLadder.lean`
  - `src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean`
  - `src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean`
- **Scope & Issues**:
  - Proved the parametric dyadic rung theorem for all $k \ge 5$ and verified
    explicit concrete rungs $k \in \{6, 7, 8, 9, 10, 11, 12, 13, 14\}$
    (PR `#184`, `#186`).
  - Coupled dyadic parametric rungs with $N = 1024, 2048, 4096$ RNS pair boxes
    (PR `#188`).
  - Parameterized short-interval gap exponent $e_{\text{gap}}$ and verified rung
    $k = 29$ with $e_{\text{gap}} = 24$, providing headroom up to
    $t \sim 10^{120}$ (PR `#190`, resolving `#203`).

### Workstream 4: Variational & Non-Degenerate Witnesses (PR `#198`–`#208`)
- **Modules**:
  - `src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean`
  - `src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean`
  - `tests/TestAxioms.lean` (Parts 82, 83, 84)
- **Scope & Issues**:
  - Added explicit `#print axioms` assertions for all contraction reflection and
    mollifier variational bridge structures (PR `#199`, resolving `#198`).
  - Weaved RNS `RnsPairBox` with `ContractionReflectionBridge` (PR `#200`,
    resolving `#129`).
  - Enforced constructive non-zero box/bridge witnesses: non-degenerate window
    boxes, non-zero channels, and positive variational mollifier energy
    (PR `#207`, resolving `#204`).
  - Verified explicit arithmetic bound compatibility across transforms without
    unconstrained definitional placeholders (resolving `#205`).
  - Wired bridge certificates into top-level `ProvenanceSummary.lean`
    verification and `TestAxioms.lean` (PR `#208`, resolving `#206`).

### Workstream 5: Constructive Stepanov Gain-vs.-Cost Lift Chain (PR `#210`)
- **Scope & Issues**:
  - Formalized multi-step Stepanov gain-vs.-cost lifting chains with accumulated
    strict dominance, positive net margins, and composition bounds
    (PR `#210`, resolving `#209`, Part 85).

---

## 3. Work In Flight & Open Items

1. **Tooling & PR File Dispatch (`#136`)**:
   - Extend `scripts/clip_groups.py` with `pr<N>` syntax, error validation,
     JSON parsing, and chunked dispatch via `files2clip`.
2. **Local Prover Audit (`#86`)**:
   - Track local Qwen and DeepSeek coding/prover performance across `lake`
     re-verifications.

---

## 4. Verification Invariants & Execution Gates

All code in `leanasm` satisfies repository governance rules per `AI.md`:
1. **Zero-Axiom Kernel Audit**:
   `lake env lean tests/TestAxioms.lean` passes all 85 parts strictly within
   `[]`, `[propext]`, or `[propext, Quot.sound]`, with zero `Classical.choice`
   and zero `sorryAx`.
2. **Build Stability**:
   `LEAN_OPTS="-M4096" make build-seq` succeeds with zero errors across all 107
   targets.
3. **Synchronization**:
   `make sync` executes and validates executable output cleanly.
4. **Formatting**:
   Markdown $\le 80$ columns; Lean source code $\le 120$ characters.

<!-- end of file: leanasm/docs/ROADMAP_V1_5_0.md -->
