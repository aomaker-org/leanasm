<!-- Path: leanasm/docs/ROADMAP_V1_3_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.3.0 Architecture Roadmap (`#78`–`#81`)

This roadmap defines the **4-workstream `v1.3.0` milestone** (`#78`–`#81`)
for `aomaker-org/leanasm` on Lean `v4.35.0`, building on the `v1.2.0` baseline
([`ARCH_REVIEW_V1_2_0.md`](ARCH_REVIEW_V1_2_0.md),
[`V1_2_0_CODE_DIGEST.md`](V1_2_0_CODE_DIGEST.md)): **35 modules** (**72 Lake
jobs**), **Parts 1-46** (`513` `#print axioms` checks in
[`tests/TestAxioms.lean`](../tests/TestAxioms.lean)), zero Mathlib, zero
`Classical.choice`, zero `sorryAx`, and zero compiler warnings.

`v1.3.0` expands the theorem graph across **Parts 47-50** and adds dedicated
cross-pillar synthesis modules (`MollifierVariationalBridge`,
`LanglandsRankinSelbergBridge`, `ProthNttTowerBridge`, plus modularizing
`UltraDeep72.lean` into parallel submodules), reaching **38+ verified modules**
(**41** with the 3-way `UltraDeep72` split).

---

## 1. `v1.2.0` Baseline Gaps & Build Performance Bottlenecks (`32ea641`)

1. **Open-Loop Dyadic-Abel & Linear Mollifier**: `ParametricQrhLadder` (`#68`)
   and `DyadicAbelBridge` (`#71`) are decoupled from variational mollifier
   optimization, stopping concrete short-interval rungs at `k = 4` (`17/32`).
2. **`UltraDeep72.lean` Monolith Bottleneck (`271.55s`, `4,683` lines)**:
   `UltraDeep72.lean` is the second slowest build unit in `leanasm` (after
   `Genus2Jacobian` at `388.33s`), bundling Parts 15-19 in one file and
   stalling at `N = 512` (`sigma = 0.50025`, `t ~ 10^18`, `90`-digit phases).
   Meanwhile `MiniVMNttBridge` proves 4-point (`ntt4AsmFermat_sound`) but not
   8-point Fermat-tower NTT assembly (`ntt8AsmFermat_sound`).
3. **Unlinked `GL(1) x GL(2) -> GSp(4)` Lift**: `EllipticModularityBridge`
   (`E_{11a1}` / `f_{11}`), `ArtinShortIntervalBridge` (`chi_4`), and
   `GSp4FunctorialityBridge` remain separate pillars without a unified
   Rankin-Selberg `L_p(s, f_{11} x chi_4)` or `Sym^2(f_{11})` Euler bridge.
4. **31-Bit `M_4` Dynamic Range Cap**: The 4-prime Fermat tower
   `{5, 17, 257, 65537}` has modulus `M_4 = 1,431,655,765 < 2^31`, capping
   single-pass Garner CRT before 61+ bits; adding a 31-bit Proth NTT prime
   `P_5 = 15 * 2^27 + 1 = 2,013,265,921` raises `M_5 > 2^61`.

---

## 2. `v1.3.0` Workstreams & GitHub Issues (`#78`–`#81`)

### Issue #78: Closed-Loop Dyadic-Abel Rungs (`k = 5, 6`) & Mollifier
- **New Module**: `src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean`
  (exported in `src/LeanAsm.lean`, wired into `ProvenanceSummary.lean`,
  `Main.lean`, and `tests/TestAxioms.lean` **Part 47**).
- **Scope**:
  - Couple `DyadicAbelBridge` (`abel_monotone_weight_envelope_qrat`,
    `InvSqrtTailGateSpec`) with `ParametricQrhLadder` to certify short-interval
    prime positivity at **`k = 5`** (`theta = 33/64` on `[10^192, +10^108]`)
    and **`k = 6`** (`theta = 65/128` on `[10^384, +10^206]`).
  - Formalize two-piece `QRat` variational mollifier optimization
    `P(u) = c_1 u + c_2 u^2`, proving cleared-denominator quadratic variance
    dominance strictly beating linear mollifiers (`c_2 = 0`).

### Issue #79: `UltraDeep72` Split, `N = 1024, 2048` Contraction & 8-Pt NTT
- **Modules**: Split `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (`271.55s`,
  `4,683` lines) into focused submodules (e.g., `UltraDeep72Core.lean`,
  `UltraDeep90.lean`, `UltraDeep108.lean` / contraction module) re-exported by
  `UltraDeep72.lean` for drop-in import compatibility and parallel Lake builds;
  extend `PiChudnovsky`, `ZeroDensityBridge` (Part 8), `MiniVMNttBridge`,
  `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean`
  (**Part 48**).
- **Scope**:
  - Decompose Parts 15-19 of `UltraDeep72.lean` into smaller compilation units
    so `lake build` parallelizes cleanly and isolates heavy kernel checks.
  - Extend `PiChudnovsky` to 108-digit `twoPiInterval108`.
  - Certify Part 20 rational box contraction for **`N = 1024`** (`sigma =
    0.500125`, `t ~ 10^24`) and **`N = 2048`** (`sigma = 0.5000625`, `t ~
    10^30`), and export `certifiedStrip05000625_N2048` into `ZeroDensityBridge`
    Part 8.
  - Prove symbolic `MiniVM` 8-point NTT/INTT assembly soundness
    `ntt8AsmFermat_sound` in `MiniVMNttBridge.lean`.

### Issue #80: Unified `GL(1) x GL(2) -> GSp(4)` Rankin-Selberg & Hecke Bridge
- **New Module**: `src/LeanAsm/LanglandsRankinSelbergBridge.lean` (exported in
  `src/LeanAsm.lean`, wired into `ProvenanceSummary.lean`, `Main.lean`, and
  `tests/TestAxioms.lean` **Part 49**).
- **Scope**:
  - Link `EllipticModularityBridge` (`E_{11a1}` / `f_{11}`),
    `ArtinShortIntervalBridge` (`chi_4`), and `GSp4FunctorialityBridge`
    (`GSp(4) -> SO(5)`).
  - Prove cleared-denominator Rankin-Selberg `L_p(s, f_{11} x chi_4)` and
    `Sym^2(f_{11})` Euler-factor non-vanishing across `p <= 97`.
  - Certify `GL(2) x GL(2) -> GSp(4)` reciprocal-polynomial embeddings and
    Hecke-weighted short-interval `DyadicAbelBridge` bounds.

### Issue #81: 5-Prime Proth/Solinas NTT Tower & Dedekind Strip Bounds
- **New Module**: `src/LeanAsm/ProthNttTowerBridge.lean` (exported in
  `src/LeanAsm.lean`, wired into `EulerFactorNonVanishing.lean`,
  `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean`
  (**Part 50**).
- **Scope**:
  - Extend the 4-prime Fermat tower `{5, 17, 257, 65537}` with 31-bit Proth
    NTT prime `P_5 = 15 * 2^27 + 1 = 2,013,265,921` (`M_5 > 2^61`).
  - Prove 5-channel Garner CRT reconstruction (`garnerReconstruct5Asm_sound`)
    and 5-prime Dedekind Euler strip bounds in `EulerFactorNonVanishing`.

---

## 3. Architectural & Verification Invariants (`v1.3.0`)

Every `v1.3.0` PR must preserve all repository governance and kernel rules:
1. **Zero-Axiom Kernel Audit**: `lake env lean tests/TestAxioms.lean` passes
   **Parts 1-50** strictly within `[]`, `[propext]`, or `[propext, Quot.sound]`
   (`0` `Classical.choice`, `0` `sorryAx`, `0` warnings).
2. **Hygiene & Wrapping (`AI.md`)**: `-- Path:` / `-- end of file:` markers on
   every file, `<= 120` chars/line (`.lean`), `<= 80` cols (`.md`), zero
   `/dev/null` or silent suppression, and `make sync` clean on `main`.

<!-- end of file: leanasm/docs/ROADMAP_V1_3_0.md -->
