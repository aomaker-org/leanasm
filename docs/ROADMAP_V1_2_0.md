<!-- Path: leanasm/docs/ROADMAP_V1_2_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.2.0 Architecture Roadmap: Extending QRH Beyond 7/8

This document captures the read-only architectural scan on `main` (`d96e3d9`)
and defines the `v1.2.0` issue roadmap (`#68`–`#71`) connecting QRH analytic
descent, CRT-NTT 2D rectangles, Langlands bridges, and dyadic/Abel sums.
All designs preserve zero `Classical.choice`, zero `sorryAx`, zero warnings,
and cleared-denominator `Nat`/`Int`/`QRat` arithmetic.

## 1. Current Pillar Interfaces & Cross-Module Gaps (`d96e3d9`)

- **`QuasiRiemann`**: `qrhThresholdFromMollifier`, `ExpPair`,
  `zeroDensityGuthMaynard` (`30/13`). Static rungs; no dynamic `θ` step.
- **`ZeroDensityBridge`**: `ZeroDensitySpec.sublinearAt`,
  `zero_density_implies_qrh_threshold`, `qrh_chebyshev_savings_certs`.
  Unused by `UltraDeep72` and `ArtinFermatBridge`.
- **`ShortIntervalPrimes`**: `ShortIntervalChebyshevSpec`,
  `ApShortIntervalSpec`, `fermat_tower_ap_short_interval_certs`,
  `sub_three_quarters_qrh_ladder_certs`. No `GSp4` (`7/64`) or `ArtinFermat`
  link.
- **`UltraDeep72`**: `highTruncSpec_1e12_N256`, `highTruncSpec_1e18_N512`,
  `cauchy_box_interior_nonvanishing`, `telescoping_box_contraction_cert`
  (`σ = 0.50025`). Isolated from `ZeroDensityBridge` and `ShortIntervalPrimes`.
- **`EulerFactorNonVanishing`**: `fermatTowerPrimes`, `FermatTowerStripCert`,
  `fermat_tower_euler_product_strip_certs`. Feeds `ApShortIntervalSpec`, not
  `EllipticModularityBridge`.
- **`ArtinFermatBridge`**: `ArtinFermatCharacterSpec`,
  `artin_char_transform_eq_ntt4`, `artin_char_orthogonality_minivm`. Not
  connected to `ApShortIntervalSpec`.
- **`EllipticModularityBridge`**: `eichler_shimura_trace_eq_11a1`,
  `hasse_weil_ramanujan_11a1_certs`, `hecke_multiplicativity_11a1_certs`.
  Isolated from `QuasiRiemann`, `ZeroDensityBridge`, and `GSp4`.
- **`GSp4FunctorialityBridge`**: `gsp4_std_functional_equation`,
  `genus2_f5_so5_cyclotomic_lift`, `thetaKimSarnakSym4` (`7/64`),
  `kim_sarnak_ramanujan_ladder_strict`. Imports `ZeroDensityBridge`, never
  feeds back.
- **`MiniVMNttBridge`**: `FermatNtt4Spec`, `fermatTowerNtt4Specs`,
  `fermatTowerNtt4_asm_roundtrip_certs`. Only consumed by `ArtinFermatBridge`.
- **`ConstructiveOpenaiBridge`**: `slab_sum_foliation`,
  `q8_plaquette_holonomy_gauge_invariant`, `q8_send_price_trace_invariant`.
  Sum foliation unused by `ShortIntervalPrimes`.

### Key Structural Gaps Observed
1. **Unconnected Spectral-to-QRH Feedback**: `GSp4FunctorialityBridge` certifies
   `thetaKimSarnakSym4 = 7/64` and `selbergLambda1`, but `ShortIntervalPrimes`
   never consumes automorphic spectral gaps in `θ` descent or `ϑ` ascent.
2. **Hardcoded `UltraDeep72` Contraction**: `telescoping_box_contraction_cert`
   halves radii (`1/2`) across `nestedBox1e18_0..3` down to `σ = 0.50025`
   using literal `highTruncTiles_1e18_N512`, without linking the `N`-indexed
   Euler–Maclaurin budget back to `ZeroDensityBridge` strip exclusion.
3. **Unplugged `GL(1)` Character Twists**: `ArtinFermatBridge` proves symbolic
   order-4 orthogonality over `{5, 17, 257, 65537}` via `MiniVM`, while
   `ApShortIntervalSpec` only bounds unsigned `ψ(x; q, a)` without character
   twisting `ψ(x; χ_4)`.
4. **No Constructive Dyadic / Abel Helper**: `ShortIntervalPrimes` operates on
   single endpoints `(x, x+h)` without a reusable discrete dyadic-shell or
   Abel summation-by-parts identity adapted from `slab_sum_foliation`.

## 2. Candidate Lemmas From `docs/openai-20261028/LEAN_TOC.json`

Filtered scan (`2,305` non-colliding `Extension/UV`, `UVExtension`, `Contacts`,
`EveryPhase`, `RemainderComparison`, `RG08` matches; `subrepos/YM` read-only):

- `YM.Extension.UV.Holo.cauchy_bound` & `on_smaller_ball` (`Holo.lean:23,61`):
  Cauchy `M / (r - δ)` derivative control -> adapt in cleared `Nat`/`Int` as
  parameterized interior radius shrinkage in `UltraDeep72.lean`.
- `YM.UVExtension.Pier.cauchyInterior` & `zeroFree` (`Power.lean:45,49`):
  `r / 3` interior half-magnitude survival `b / 2 <= ‖f z‖` -> generalize
  `cauchy_box_interior_nonvanishing` for `N ∈ {256, 512}` sub-tile grids.
- `YM.Extension.UV.Tail.improve` & `Lipschitz` (`Tail.lean:43,80`):
  General `(1/3)^w + (3/2) * (K * b_m / radius_m)` contraction -> replace
  fixed `1/2` halving in `telescoping_squeezing_chain` with rational ratio
  `qNum / qDen < 1`.
- `YM.Contacts.Harvest.geometric_dyadic` & `EveryPhase.Light.dyadic`
  (`Absolute.lean:58`, `Light.lean:135`): dyadic shell partition `w_n = u*2^-n`
  -> port as constructive `[M, M * 2^k)` finite shell sums in `Int`/`QRat`.
- `YM.RG08.KContraction` (`KStep.lean:121,130`): `L^(-1/2)` thresholded
  contraction gate -> adapt as `N`-indexed Euler–Maclaurin `1/√N` tail gates
  for `ShortIntervalPrimes` / `UltraDeep72`.

## 3. Proposed `v1.2.0` Workstreams & GitHub Issues (`#68`–`#71`)

### Issue #68: Parametric QRH Ladder (`θ ↓ 1/2` & `ϑ ↑ 1` + `Kim–Sarnak 7/64`)
- **Modules**: `ZeroDensityBridge.lean`, `ShortIntervalPrimes.lean`,
  `GSp4FunctorialityBridge.lean` (new theorem + `ProvenanceSummary.lean`).
- **Scope**: Define parametric `ParametricQrhRungSpec (k : Nat)` producing
  monotone descent `θ(k) = (2^k + 1) / 2^(k+1) ↓ 1/2` (`9/16 -> 17/32 ->
  33/64`), dual mollifier ascent `ϑ(k) = 1 - 1/2^(k+1) ↑ 1`, and a cleared
  `QRat` transfer bridge tying `GSp4FunctorialityBridge.thetaKimSarnakSym4`
  (`7/64`) and `zdGuthMaynard` (`15/26`) to shifted prime-gap exponents in
  `ShortIntervalChebyshevSpec`.

### Issue #69: Higher-Truncation (`N = 256, 512`) 4-Prime CRT-NTT Contraction
- **Modules**: `UltraDeep72.lean`, `PiChudnovsky.lean`,
  `ZeroDensityBridge.lean`.
- **Scope**: Generalize `telescoping_squeezing_chain` from halving (`1/2`) to
  rational ratio `qNum / qDen < 1` (adapting `YM.Extension.UV.Tail.improve`),
  connect `highTruncSpec_1e12_N256` and `highTruncSpec_1e18_N512` (`σ =
  0.50025`, `t ~ 10^18`) to `ZeroDensityBridge.ZeroDensitySpec`, and certify
  explicit 4-prime CRT-NTT wrap-around margins for the `N = 512` derivative
  evaluation (`dirichletGradBoundScaled6_512`).

### Issue #70: `GL(1)` Artin Character-Twisted Short-Interval Prime Bounds
- **Modules**: `ArtinFermatBridge.lean`, `MiniVMNttBridge.lean`,
  `ShortIntervalPrimes.lean`.
- **Scope**: Define `ArtinTwistedShortIntervalSpec` combining
  `ApShortIntervalSpec` with `ArtinFermatCharacterSpec` (`q ∈ {5, 17, 257,
  65537}`), using `artin_char_orthogonality_minivm` to pass constructively from
  character-twisted Chebyshev sums `ψ(x; χ_4^r)` (`r ∈ {0..3}`) to
  `HasGuaranteedApPrime` positivity `0 < ϑ(x + h; q, a) - ϑ(x; q, a)`.

### Issue #71: Constructive Dyadic Shell & Abel Summation-by-Parts Bridge
- **Modules**: `ConstructiveOpenaiBridge.lean`, `ShortIntervalPrimes.lean` (or
  a dedicated `AbelSummationBridge.lean` imported by `ShortIntervalPrimes`).
- **Scope**: Generalize `ConstructiveOpenaiBridge.slab_sum_foliation` and
  `geometric_dyadic` into a zero-axiom integer `Finset`-free `List` identity
  for discrete Abel summation by parts (`∑_{n=M+1}^{N} a_n w_n` expressed via
  partial sums `A(k) - A(M)` and forward differences `w_k - w_{k+1}`), plus
  dyadic-shell `[2^j, 2^(j+1))` Chebyshev remainder aggregation for
  `short_interval_psi_diff_bound`.

<!-- end of file: leanasm/docs/ROADMAP_V1_2_0.md -->
