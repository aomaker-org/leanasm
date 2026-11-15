<!-- Path: leanasm/docs/V1_2_0_CODE_DIGEST.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.2.0 Digest of Oversized Modules (`6db78d7` / `32ea641`)

This companion digest summarizes the `v1.2.0` additions in the three largest
source files omitted from the `< 250 KB` clipboard subset (`UltraDeep72.lean`,
`ZeroDensityBridge.lean`, and `ProvenanceSummary.lean`) so the packed bundle
remains self-contained for external review.

Full 13-file bundle (`576.83 KB`):
`scratch/bundle_20261114_184003.txt`.

---

## 1. `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (Part 19, `#69` / PR `#74`)

Total file size: `4,683` lines (`239,121` B); `v1.2.0` added `461` lines
(`L4220`-`L4683`):

- **`RationalBoxContractionSpec` (`L4228`)**: Generalizes fixed `1/2` halving to
  arbitrary `0 < qNum < qDen`, with shrunk-ball Lipschitz margin
  `2 * lipNumerator * radius <= centerLower * (radius - deltaShrink)`.
- **`RationalBoxContractionSpec.lip_mul_radius_lt` (`L4243`)**: Proves
  `rSpec.lipNumerator * rSpec.radius < rSpec.centerLower * (radius - delta)`.
- **`rational_box_contraction_step` (`L4263`)**: Single-step interior lower
  bound (`centerLower / 2 <= pointMag`, `(centerLower + 1) / 2 <= pointMag`,
  `0 < pointMag`) and rational drift contraction `qDen * nextDrift <= qNum *
  currDrift` (`nextDrift < currDrift` for positive drift).
- **`nat_pow_contraction_le` & `rational_telescoping_chain_cert`**: Multi-step
  `n`-iteration drift contraction `qDen ^ n * drifts n <= qNum ^ n * drifts 0`
  and nested box inclusion `boxes n ⊆ boxes 0`.
- **`ultraDeep72_N256_rational_rect_cert` (`L4536`)**:
  - `N = 256`, `sigma = 0.5005 = 1001/2000`, `t ~ 10^12`, `q = 1/3`.
  - Proves `nestedBox1e12_2.SubBox nestedBox1e12_0`, `3^2 * drift 2 <= 1^2 *
    drift 0`, `dirichletGradBoundScaled6_512 500500 256 = 117284435`,
    `highTruncSpec_1e12_N256.HasCertifiedNonVanishing`, and `2 x 2` Lipschitz
    tile coverage over `nestedBox1e12_2`.
- **`ultraDeep72_N512_rational_rect_cert` (`L4612`)**:
  - `N = 512`, `sigma = 0.50025 = 1/2 + 1/4000`, `t ~ 10^18`, `q = 2/5`.
  - Proves `nestedBox1e18_3.SubBox nestedBox1e18_rat_0`, `5^2 * drift 2 <= 2^2 *
    drift 0`, `dirichletGradBoundScaled6_512 500250 512 = 195620879`,
    `eulerMaclaurinB2TailRect2DForN 512 ... <= ... 256`,
    `highTruncSpec_1e18_N512.HasCertifiedNonVanishing`, and `2 x 2` tile
    coverage over `nestedBox1e18_3`.

---

## 2. `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` (Part 7, `#69`)

Total file size: `933` lines (`51,478` B); `v1.2.0` added `218` lines
(`L720`-`L934`):

- **`exponent_strict_mono_sigma` (`L720`)**: Strictly monotone zero-density
  exponent `σ₁ < σ₂ -> spec.exponent σ₂ < spec.exponent σ₁`.
- **`CertifiedStripWidthSpec` (`L783`)**: Packages a
  `HighTruncZeroFreeRectSpec` anchored at `sigmaLo = 1/2 + halfWidth`
  (`0 < halfWidth.num`) together with `rectSpec.HasCertifiedNonVanishing`.
- **Concrete Instances (`L795`, `L806`)**:
  - `certifiedStrip05005_N256` (`1001/2000 = 1/2 + 1/2000`, `N = 256`).
  - `certifiedStrip050025_N512` (`2001/4000 = 1/2 + 1/4000`, `N = 512`).
- **`ultradeep72_strip_to_zero_density_bridge` (`L827`)**: Composes any
  `CertifiedStripWidthSpec` with `ZeroDensitySpec` and `θ ∈ (sigmaLo, 1)` to
  certify `1/2 < strip.sigmaLo`, strict exponent tightening, narrower width
  `θ - strip.sigmaLo < θ - 1/2`, and DVP strip exclusion `β <= θ` and
  `β <= 1 - c_dvp / octaveLnUpper36QRat t`.
- **`ultradeep72_N512_strip_zd_certs` (`L908`)**: Certifies `3/5200` saving on
  `zdGuthMaynard` (`30/13`), `3/5000` saving on `zdHuxley` (`12/5`),
  `dirichletGradBoundScaled6_512 500250 512 = 195620879`, and both
  `HasCertifiedNonVanishing` witnesses.

---

## 3. `src/LeanAsm/ProvenanceSummary.lean` (`v1.2.0` Synthesis)

Total file size: `1,549` lines (`90,948` B); `v1.2.0` added `282` diff lines
coupling all four new modules (`ParametricQrhLadder`, `UltraDeep72` Part 19,
`DyadicAbelBridge`, `ArtinShortIntervalBridge`) into the 8-pillar closure:

- **`ParametricQrhLadderProp` (`L617`)**: Bundles
  `qrhShortExponent_strict_anti`, `qrhShortExponent_density_benchmarks`,
  `qrhDualFraction_strict_mono`, `shortIntervalQrh1732Spec_has_prime`,
  `kim_sarnak_amplified_qrh_step`, and `parametric_qrh_kim_sarnak_certs`.
- **`HighTruncRationalContractionProp` (`L653`)**: Bundles
  `rational_box_contraction_step`, `rational_telescoping_chain_cert`,
  `ultraDeep72_N256_rational_rect_cert`, `ultraDeep72_N512_rational_rect_cert`,
  `ultradeep72_strip_to_zero_density_bridge`, and
  `ultradeep72_N512_strip_zd_certs`.
- **`DyadicAbelProvenanceProp` (`L689`)**: Bundles `dyadic_shell_sum_partition`,
  `dyadic_shell_sum_foliation`, `discrete_abel_summation_by_parts`,
  `abel_summation_by_parts_list`, `abel_monotone_weight_envelope`,
  `abel_monotone_weight_envelope_qrat`, `inv_sqrt_tail_gate_dyadic_step`,
  `short_interval_dyadic_abel_envelope`, and `dyadic_abel_short_interval_certs`.
- **`QuasiRiemannProvenance` (`L883`-`L885`)**: Conjoins those three props into
  the QRH pillar (`quasiRiemann_provenance_certified`).
- **`ArtinShortIntervalProvenanceProp` (`L969`, `L1182`)**: Bundles
  `artin_gaussian_char_orthogonality`, `artin_ntt4_residue_class_recovery`,
  `artin_twisted_ap_short_interval_pos`,
  `artin_twisted_coset_short_interval_pos`,
  and `fermat_tower_artin_short_interval_certs` into `EulerRnsProvenance`
  (`eulerRns_provenance_certified`).
- **Master Theorem (`L1529`)**: `LeanAsm.leanasm_full_provenance_certified`
  proves the explicit 8-way conjunction `MiniVmProvenance ∧ CollatzProvenance ∧
  YangMillsProvenance ∧ QuasiRiemannProvenance ∧ EulerRnsProvenance ∧
  FiniteFieldWeilProvenance ∧ CrtNttProvenance ∧ ChudnovskyPiProvenance`
  with zero `Classical.choice` and zero `sorryAx`.

<!-- end of file: leanasm/docs/V1_2_0_CODE_DIGEST.md -->
