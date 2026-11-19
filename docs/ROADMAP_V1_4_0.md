<!-- Path: leanasm/docs/ROADMAP_V1_4_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.4.0 Architecture Roadmap

This roadmap defines the **4-workstream `v1.4.0` milestone** for
`aomaker-org/leanasm` on Lean `v4.35.0`, building on the `v1.3.0` baseline
and PRs `#94`–`#97`: **63 modules**, **Parts 1–53** in
[`tests/TestAxioms.lean`](../tests/TestAxioms.lean) (`[propext, Quot.sound]`,
`0` `Classical.choice`, `0` `sorryAx`), zero-import constant leaves
(`Constants/{PiAndSqrt,PrimeTowers,CurveTables}.lean`),
`Genus2/{PolyF5,Cantor}.lean`, `scripts/{files2clip,clip_groups.py}`, and
[`docs/ARCHITECTURE_AND_PROVENANCE.md`](ARCHITECTURE_AND_PROVENANCE.md).

---

## 1. Baseline Architecture & Provenance Inventory (`v1.3.0` + `#94`–`#97`)

- **63 Verified Modules**: Complete zero-Mathlib formalization spanning MiniVM,
  Yang-Mills SU(2)/Q8 gauge models, Quasi-Riemann zero-free sweeps,
  Garner CRT / NTT towers, Chudnovsky 105-digit $\pi$, and Genus 2 curve
  arithmetic over $\mathbb{F}_5$.
- **Strict Constructive Invariant**: Kernel checks pass strictly within
  `[propext, Quot.sound]` with zero `Classical.choice`, zero `sorryAx`, and
  zero compiler warnings across all 53 axiom audit parts.
- **Constant Subsystem Factorization**: Zero-import architectural leaf modules
  under `LeanAsm/Constants/` isolate fundamental numeric tables and constants
  (`PiAndSqrt.lean`, `PrimeTowers.lean`, `CurveTables.lean`).
- **Comprehensive Review Tooling**: `files2clip` and `clip_groups.py` automate
  chunked clipboard dispatch under the 240 KB context threshold.
- **Architectural Audit**: `docs/ARCHITECTURE_AND_PROVENANCE.md` provides full
  traceability into `LeanAsmFullProvenance` and its component certificates.

---

## 2. `v1.4.0` Workstreams & Scope

### Workstream 1: Unicritical $p$-Adic Orbits & Escape Dynamics
- **Branch / PR**: `feature/unicritical-padic-orbits`
- **Module**: `src/LeanAsm/QuasiRiemann/Valuation/PreperiodicDynamics.lean`
  (wired into `tests/TestAxioms.lean` **Part 54**).
- **Scope**:
  - Prove general $p$-adic escape dynamics for unicritical polynomials
    $f(x) = x^d + c$:
    $$\nu_p(f^n(x_0)) = d^n \nu_p(x_0) \quad \text{when } \nu_p(x_0) < 0$$
  - Establish bounded-orbit integrality invariants for points with
    $\nu_p(x_0) \ge 0$ and $\nu_p(c) \ge 0$.
  - Formalize non-preperiodicity certificates ensuring escaping orbits never
    enter periodic cycles.

### Workstream 2: Prime-Tower RNS CRT Roundtrip & Homomorphism Soundness
- **Branch / PR**: `feature/rns-crt-soundness`
- **Module**: `src/LeanAsm/QuasiRiemann/Valuation/RNS.lean`
- **Scope**:
  - Prove complete residue number system (RNS) reconstruction soundness
    (`RnsInt.reconstruct`) across arbitrary prime towers.
  - Formalize `RnsQRat` algebraic homomorphism soundness for addition and
    multiplication.
  - Bridge certified `Valuation/Hensel.lean` root lifting with high-order
    `QuasiRiemann` rational contraction mappings.

### Workstream 3: Genus 2 Multi-Prime Frobenius & Weil RH Certificates
- **Branch / PR**: `feature/genus2-multiprime-weil`
- **Modules**: `src/LeanAsm/Genus2/` & `src/LeanAsm/FiniteFieldRH.lean`
- **Scope**:
  - Extend Genus 2 Jacobian group and divisor arithmetic for curve
    $C : y^2 = x^5 - x + 1$ beyond $\mathbb{F}_5$.
  - Construct multi-prime Frobenius Euler polynomials $P_p(T)$ across good
    primes $p \in \{7, 11, 13, 17, 19, 23\}$.
  - Certify Weil Riemann Hypothesis bounds $|\alpha_i| = \sqrt{p}$ for roots of
    characteristic polynomials over each evaluated field.

### Workstream 4: Hygiene, Modularization & Tooling
- **Branch / PR**: `chore/v1-4-0-hygiene-and-tooling`
- **Scope**:
  - Restore missing `-- end of file:` footer in `MiniVMNttBridge.lean`.
  - Format and wrap lines to $\le 100$ columns in `UltraDeep*` modules
    (`UltraDeep72Core.lean`, `UltraDeep90.lean`).
  - Execute remaining batch review audits in `scripts/clip_groups.py`:
    `2_minivm`, `3_crt_rns.2`, `5_yangmills`, `6_qrh_core`, and `7_qrh_deep`.
  - Add Gemini 4 Neon presets to `config_env` for rapid local session binding.

---

## 3. Verification & Governance Invariants (`v1.4.0`)

All workstreams must satisfy repository governance rules per `AI.md`:
1. **Zero-Axiom Kernel Audit**: `lake env lean tests/TestAxioms.lean` passes all
   parts strictly within `[]`, `[propext]`, or `[propext, Quot.sound]`, with
   zero `Classical.choice` and zero `sorryAx`.
2. **Strict Line Lengths**: Markdown documentation $\le 80$ columns; Lean
   source code $\le 120$ characters (with $\le 100$ column target on sweeps).
3. **File Framing**: Explicit `-- Path:` / `<!-- Path:` headers and
   `-- end of file:` / `<!-- end of file:` footers on all files.
4. **Execution Integrity**: Zero stderr/stdout redirection to `/dev/null` or
   silent error masking (`|| true`).

<!-- end of file: leanasm/docs/ROADMAP_V1_4_0.md -->
