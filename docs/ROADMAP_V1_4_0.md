<!-- Path: leanasm/docs/ROADMAP_V1_4_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.4.0 Architecture Roadmap & Release Retrospective

This roadmap documents the completed **v1.4.0 milestone** and release
achievements for `aomaker-org/leanasm` on Lean `v4.35.0` (lakefile version
`1.4.0`), tracking the landed workstreams and synthesis weaves through PRs
`#99`–`#115`.

The repository scales to **71 verified Lean modules** (60 imported in
`src/LeanAsm.lean`), spanning **Parts 1–63** in
[`tests/TestAxioms.lean`](../tests/TestAxioms.lean) with strict zero-Mathlib,
zero `Classical.choice`, and zero `sorryAx` (`[propext, Quot.sound]` only).

---

## 1. Release Architecture & Provenance Inventory (`v1.4.0`)

- **71 Verified Modules**: Complete zero-Mathlib formalization spanning MiniVM,
  Yang-Mills SU(2)/Q8 gauge models, Quasi-Riemann zero-free sweeps,
  Garner CRT / NTT towers, Chudnovsky 105-digit $\pi$, Genus 2 curve
  arithmetic, QSD[1-4] Hensel prime-tower tangent lifts, and multi-prime
  Weil certificates ($p \in \{7, 11, 13, 17, 19, 23\}$).
- **Strict Constructive Invariant**: Kernel checks pass strictly within
  `[propext, Quot.sound]` with zero `Classical.choice`, zero `sorryAx`, and
  zero compiler warnings across all 63 axiom audit parts.
- **Sequential Build & Memory Governance**: Clean sequential build execution
  (`LEAN_OPTS="-M4096"` / `make build-seq`) ensuring stable compilation on
  `core12` and resource-constrained environments without heap exhaustion.
- **Architectural Audit**:
  [`docs/ARCHITECTURE_AND_PROVENANCE.md`](ARCHITECTURE_AND_PROVENANCE.md)
  and `src/LeanAsm/ProvenanceSummary.lean` provide master top-level provenance
  synthesis across all 11 CLI parts.

---

## 2. Landed `v1.4.0` Workstreams & PR Milestones

### Workstream 1: Unicritical $p$-Adic Orbits & Escape Dynamics (PR `#99`)
- **Module**: `src/LeanAsm/QuasiRiemann/Valuation/PreperiodicDynamics.lean`
  (wired into `tests/TestAxioms.lean` **Part 54**).
- **Scope**:
  - Proved general $p$-adic escape dynamics for unicritical polynomials
    $f(x) = x^d + c$:
    $$\nu_p(f^n(x_0)) = d^n \nu_p(x_0) \quad \text{when } \nu_p(x_0) < 0$$
  - Established bounded-orbit integrality invariants for points with
    $\nu_p(x_0) \ge 0$ and $\nu_p(c) \ge 0$.
  - Formalized non-preperiodicity certificates ensuring escaping orbits never
    enter periodic cycles.

### Workstream 2: Prime-Tower RNS CRT Roundtrip (PR `#102`, `#104`)
- **Module**: `src/LeanAsm/QuasiRiemann/Valuation/RNS.lean`
- **Scope**:
  - Proved complete residue number system (RNS) reconstruction soundness
    (`RnsInt.reconstruct`) across arbitrary prime towers.
  - Formalized `RnsQRat` algebraic homomorphism soundness for addition and
    multiplication.
  - Wove RNS CRT soundness with valuation and orbit bounds.

### Workstream 3: Genus 2 Multi-Prime Frobenius & Weil RH (PR `#103`, `#106`)
- **Modules**: `src/LeanAsm/Genus2MultiPrimeWeil.lean` &
  `src/LeanAsm/Genus2WeilGSp4Weave.lean` (Parts 55, 57).
- **Scope**:
  - Constructed multi-prime Frobenius Euler polynomials $P_p(T)$ across good
    primes $p \in \{7, 11, 13, 17, 19, 23\}$.
  - Certified Weil Riemann Hypothesis bounds for roots of characteristic
    polynomials over each evaluated field.
  - Wove multi-prime Weil certificates with `WeilZetaBridge` and
    `GSp4FunctorialityBridge` standard Euler factors.

### Workstream 4: High-Truncation Strip & Dyadic-Abel Weave (PR `#105`)
- **Module**:
  `src/LeanAsm/QuasiRiemann/HighTruncDyadicAbelWeave.lean` (Part 56).
- **Scope**:
  - Wove high-truncation zero-free strip certificates ($N = 1024, 2048$) with
    dyadic-Abel summation bounds down to $\sigma = 0.5000625$ at
    $t \sim 10^{30}$.

### Workstream 5: Constructive QSD[1-4] Algebraic Weaves (PR `#107`–`#115`)
- **PR `#107`–`#111`**: Formalized QSD[1-4] nilpotent algebras
  (`QsdAlgebraBridge.lean`, Part 58), logarithmic derivative box contraction,
  and QSD[4] Hensel tangent lifts (`QsdHenselTower.lean`, Part 59).
- **PR `#112` (`MiniVMRnsHenselWeave`)**: Weaved MiniVM NTT assembly with
  RnsInt CRT reconstruction and QSD[4] Hensel prime-tower tangent lifts
  (`minivm_ntt_rns_hensel_weave_bridge`, Part 60).
- **PR `#113` (`Qsd1LogDerivStripBridge`)**: Bridged QSD[1] logarithmic
  derivatives with sub-7/8 strip contraction certificates at rung 32,000
  (`qsd1_logderiv_sub78_strip_bridge`, Part 61).
- **PR `#114` (`GaussianQsdBridge`)**: Established integral Gaussian
  QSD[1-4] slices, norm multiplicativity, truncation defect bounds, and
  Hensel tower links (`gaussian_qsd_hensel_tower_bridge`, Part 62).
- **PR `#115` (`Genus2HenselPreperiodicWeave`)**: Synthesized multi-prime
  genus-2 Frobenius traces ($p \in \{7, 11, 13, 17, 19, 23\}$) with QSD[4]
  Hensel tangent lifts and preperiodic dynamics bounds
  (`genus2_hensel_preperiodic_cert`, Part 63).

---

## 3. `v1.5.0` Forward Targets

1. **Higher Genus & Arithmetic Surface Weaves**:
   - Extend multi-prime Weil certificates to additional conductor families
     and hyperelliptic curves.
   - Formalize higher rank Artin L-function non-vanishing and Rankin-Selberg
     convolutions.
2. **QSD[4] Deep Analytic Continuation**:
   - Push QSD[4] Hensel tangent lifts into higher degree nilpotent rings
     mod $p^k$.
   - Couple Gaussian QSD norm multiplicativity with 2D Dirichlet L-function
     contour integrals.
3. **MiniVM Hardware-Target Assembly Synthesis**:
   - Verify native register allocation and instruction emission from MiniVM
     bytecode to RISC-V / ARM64 assembly formal models.
   - Extend Proth NTT tower bridges with certified AVX-512 vector execution.
4. **Tooling & Distributed Verification**:
   - Automated parallel axiom checkers and proof certification caching.
   - Distributed telemetry across multi-node Ollama prover swarms.

---

## 4. Verification & Governance Invariants

All modules and PRs satisfy repository governance rules per `AI.md`:
1. **Zero-Axiom Kernel Audit**: `lake env lean tests/TestAxioms.lean` passes all
   parts strictly within `[]`, `[propext]`, or `[propext, Quot.sound]`, with
   zero `Classical.choice` and zero `sorryAx`.
2. **Strict Line Lengths**: Markdown documentation $\le 80$ columns; Lean
   source code $\le 120$ characters.
3. **File Framing**: Explicit `-- Path:` / `<!-- Path:` headers and
   `-- end of file:` / `<!-- end of file:` footers on all files.
4. **Execution Integrity**: Zero stderr/stdout redirection to `/dev/null` or
   silent error masking (`|| true`).

<!-- end of file: leanasm/docs/ROADMAP_V1_4_0.md -->
