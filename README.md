# Path: leanasm/README.md
# leanasm: Zero-Axiom Lean 4 Verification & Algorithmic Architecture

A constructive Lean 4 (`v4.35.0`) formalization workspace uniting verified
`MiniVM` assembly execution, Fermat-tower `{5, 17, 257, 65537}` NTT/INTT &
Garner CRT, 192-digit CRT-NTT arithmetic, 100-digit Chudnovsky `pi`, analytic
2D zero-free regions / QRH / Chebyshev envelopes, Collatz Diophantine
barriers, 4D lattice gauge invariance, and genus-2 Hasse-Weil / BSD /
Cantor-Mumford certificates.

All core proofs in `LeanAsm.leanasm_full_provenance_certified` audit strictly
to `[propext, Quot.sound]` (or zero axioms), with **zero** `Classical.choice`
and **zero** `sorryAx` across the full transitive dependency cone.

## Prerequisites & Toolchain

The Lean toolchain is managed via [elan](https://github.com/leanprover/elan):

- **Lean Version**: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`)
- **Build Manager**: Lake (Lean's package and build manager)
- **Local Neural Prover Engine**: `llama.cpp` (`llama-server`)

To activate `elan`, `lake`, and your workspace environment, source
`config_env`:
```bash
# Optional tag argument: hum, dev, test, etc.
source config_env hum
```

## Quick Start & Zero-Axiom Verification Workflow

```bash
# Check toolchain and workspace status
make status

# Build all 32 modules incrementally with timing budgets
make build-incremental

# Full build & execute Parts 1-11 + unified provenance CLI demo
make sync

# Audit transitive axiom closures across Parts 1-42 (0 choice, 0 sorryAx)
lake env lean tests/TestAxioms.lean

# Check submodule hydration status
make hydrate-status
```

## CLI Parts 1-11 Summary (`Main.lean`)

Running `lake exe leanasm` (or `make run`) executes and prints build-time
kernel-verified computations across all 11 parts:

1. **Part 1 (`MiniVM`, `MiniVMNttBridge`)**: Register machine execution,
   4-channel Garner CRT assembly (`M_4 = 1,431,655,765`), `F_17` (`289` /
   `83,521` states) & parametric `{5, 17, 257, 65537}` 4-pt NTT/INTT and
   CRT-NTT cyclic convolution soundness.
2. **Part 2 (`Conjectures`, `CollatzQrhBridge`)**: 144-digit CRT-NTT gap
   `2^485 - 3^306 > 0`, 318-digit `(1054, 665)` convergent bracket, 72-digit
   Baker measure, Steiner 1-cycle exclusions, Simons-de Weger `m >= 666`
   (`K >= 1721`) barrier, and constructive predecessor-tree density bounds.
3. **Part 3 (`YangMillsToy`)**: 4D `Z_2` Wilson plaquette action & local gauge
   invariance.
4. **Part 4 (`YangMillsQ8`, `ConstructiveOpenaiBridge`)**: Non-abelian
   `Q_8 subset SU(2)` quaternion gauge multiplication, trace cyclicity,
   conjugation invariance, 4D lattice walks, box/slab foliation, and
   `SignedSym4` face-holonomy trace invariance.
5. **Part 5 (`QuasiRiemann`, `UltraDeep72`, `AsymptoticZfr`,
   `ZeroDensityBridge`, `ShortIntervalPrimes`)**: Mollifier descent, 2D
   rectangles down to `sigma = 0.501` (`N = 128`) and compositional 2x2
   Lipschitz tiles down to `sigma = 0.5005` (`N = 256`, `t ~ 10^12`) and
   `sigma = 0.50025` (`N = 512`, `t ~ 10^18`) via 90-digit CRT-NTT phase
   reduction (`< 10^-60` rad), DVP asymptotic ZFR, Dirichlet `L^2` diagonal
   dominance, rational zero-density descent (`15/26 < 3/5 < 2/3`), QRH
   threshold ladder `theta in {3/4, 7/8, 11/12, 47/48}`, Chebyshev remainder
   envelopes (`10^12..10^336`), short-interval prime positivity
   (`10^336/10^308`), Fermat-tower AP short-interval primes
   (`q in {5, 17, 257, 65537}`), and the
   `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` sub-3/4 QRH ladder.
6. **Part 6 (`RnsArithmetic`, `EulerFactorNonVanishing`, `ArtinFermatBridge`)**:
   3-channel Garner CRT execution, Fermat-tower `{5, 17, 257, 65537}` strip
   bounds (`sigma in {1/2, 3/4, 1}`), cyclotomic Dedekind splitting across
   `32,906` split prime ideals, GL(1) Artin Euler collapse & order-4
   cyclotomic factorization, and MiniVM 4-pt NTT character orthogonality.
7. **Part 7 (`FiniteFieldRH`, `Genus2Jacobian`, `WeilZetaBridge`,
   `GSp4FunctorialityBridge`, `EllipticModularityBridge`)**: Hasse-Weil RH
   for `E/F_7`, genus-2 `C : y^2 = x^5 - x + 1` over `F_5`, `L(C, 1) = 71/25`,
   Cantor-Mumford group axioms on `J(C)(F_5) ~= Z/71Z`, punctured-strip zeta
   bounds, `Xi_C(1 - s) = Xi_C(s)`, `GSp(4) -> SO(5)` cyclotomic lift
   `5(1 - T) Phi_10(T)`, Selberg / Kim-Sarnak `Sym^k` ladder, and
   `E_{11a1}` / `f_{11}` Eichler-Shimura trace equality (`p <= 97`).
8. **Part 8 (`EulerFactorNonVanishing`)**: Local RNS channels `p in {7, 11,
   13}` non-vanishing at `sigma in {1/2, 7/8}`.
9. **Part 9 (`NttArithmetic`)**: `F_17` primitive roots, butterfly, and
   universal 4-pt invertibility & cyclic convolution (`F_5` and `F_17`).
10. **Part 10 (`CrtNtt`, `CrtNttUniversal`)**: 2-tier 192-digit Karatsuba
    CRT-NTT multiplication, 4-prime Garner (`M_4 = 1,431,655,765`, inverses
    `7, 127, 32767`), and sharp wrap-around bounds (`B <= 18918/13377/9459`).
11. **Part 11 (`PiChudnovsky`, `ProvenanceSummary`)**: 100-digit Chudnovsky
    `pi`, universal `m >= 8` truncation trap, and unified master certificate
    `LeanAsm.leanasm_full_provenance_certified`.

## 32-Module Theorem Inventory

Paths below `src/LeanAsm/` are relative to `src/LeanAsm/` (with `QR/` for
`QuasiRiemann/`, `PC/` for `PiChudnovsky/`, and `Main.lean` +
`src/LeanAsm.lean` at the root). `tests/TestAxioms.lean` audits Parts 1-42.
`NS` legend: `=` = filename stem, `QR` = `QuasiRiemann`, `PC` = `PiChudnovsky`.

| Module | NS | Flagship Theorem / Role |
| --- | --- | --- |
| `Main.lean` | `(root)` | CLI entrypoint (`Parts 1-11` + provenance) |
| `LeanAsm.lean` | `(root)` | Library root exporting all 30 submodules |
| `MiniVM.lean` | `=` | `exec_garner_crt_sound`, `mul_mod_reg_correct` |
| `MiniVMNttBridge.lean` | `=` | `crtNtt4ConvAsm_sound` |
| `Conjectures.lean` | `=` | `collatz_one_reaches_one` |
| `CollatzQrhBridge.lean` | `=` | `collatz_cycle_length_lower_bound_306` |
| `YangMillsToy.lean` | `=` | `plaquette_action_gauge_invariant` |
| `YangMillsQ8.lean` | `=` | `q8_trace_conjugation_invariant` |
| `ConstructiveOpenaiBridge.lean` | `=` | `holonomy_gauge_covariant` |
| `QR/Rat.lean` | `QR` | `QRat` constructive rational field core |
| `QuasiRiemann.lean` | `=` | `isValidLipTile2D_sound` |
| `QR/UltraDeep72.lean` | `QR` | `crtNtt_highTrunc_2d_zero_free_rect` |
| `QR/AsymptoticZfr.lean` | `QR` | `dvp_asymptotic_zero_free_region` |
| `QR/AsymptoticZfrBridge.lean` | `QR` | `ln2Upper36Scaled_eq_lnInterval36_hi` |
| `QR/ZeroDensityBridge.lean` | `QR` | `qrh_chebyshev_benchmark_certs` |
| `QR/ShortIntervalPrimes.lean` | `QR` | `qrh_short_interval_positivity_certs` |
| `RnsArithmetic.lean` | `=` | `garner_mul_concrete_soundness` |
| `EulerFactorNonVanishing.lean` | `=` | `local_euler_disk_nonvanishing` |
| `FiniteFieldRH.lean` | `=` | `hasse_weil_riemann_hypothesis` |
| `Genus2Jacobian.lean` | `=` | `jacobian_group_axioms_on_orbit` |
| `WeilZetaBridge.lean` | `=` | `genus2_completed_zeta_reflection` |
| `GSp4FunctorialityBridge.lean` | `=` | `gsp4_std_functional_equation` |
| `EllipticModularityBridge.lean` | `=` | `eichler_shimura_trace_eq_11a1` |
| `ArtinFermatBridge.lean` | `=` | `artin_char_orthogonality_minivm` |
| `NttArithmetic.lean` | `=` | `cyclic_conv4_ntt_universal_F17` |
| `CrtNtt.lean` | `=` | `crt_ntt16_exact_integer_convolution` |
| `CrtNttUniversal.lean` | `CrtNtt` | `karatsubaCrtNttMul192_universal_sound` |
| `PC/CrtMulBridge.lean` | `PC` | `intMulBigViaCrtNtt_eq_mul` |
| `PC/Sqrt10005.lean` | `PC` | `sqrt10005_scaled110_certified` |
| `PC/ChudnovskySeries.lean` | `PC` | `chudBinarySplit_eq_exact` |
| `PiChudnovsky.lean` | `=` | `pi_100_digits_certified` |
| `ProvenanceSummary.lean` | `LeanAsm` | `leanasm_full_provenance_certified` |

Additional headline theorems audited in `ProvenanceSummary.lean` and
`tests/TestAxioms.lean` include:

- `MiniVMNttBridge.fermatTowerNtt4_asm_roundtrip_certs`,
  `garnerReconstruct4Asm_sound`, & `crtNtt4ChannelConvAsm_sound`
- `CollatzQrhBridge.baker_effective_measure_485_306_verified`,
  `steiner_1cycle_excluded_at_convergents`, `log2_3_convergent_bracket_665`,
  `simons_de_weger_barrier_665`, `collatzPredTree_sound`, &
  `collatz_pred_tree_growth_certs`
- `ConstructiveOpenaiBridge.axisRoute_reverse`, `squareWalk_corners`,
  `slab_sum_foliation`, `q8_plaquette_holonomy_gauge_invariant`, &
  `q8_send_price_trace_invariant`
- `QuasiRiemann.qrh_full_descent_chain_certified`,
  `ultra_deep_rects_down_to_0501_certified`,
  `high_height_dirichlet_rects_1e12_certified`,
  `crtNtt_phase_reduction_512_sound`, `euler_maclaurin_tail_shrinks_with_N`,
  `crtNtt_highTrunc_2d_zero_free_rect`, `cauchy_box_interior_nonvanishing`,
  `telescoping_box_contraction_cert`, `dirichlet_l2_zeta_and_mobius_certs`,
  `zero_density_and_dvp_combined_region`, `qrh_chebyshev_savings_certs`,
  `short_interval_density_ladder_strict`, `qrh_maximal_prime_gap_bound`,
  `fermat_tower_ap_short_interval_certs`, &
  `sub_three_quarters_qrh_ladder_certs`
- `EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs` &
  `fermat_tower_dedekind_euler_strip_certs`
- `ArtinFermatBridge.artin_split_euler_factor_collapse`,
  `artin_order4_cyclotomic_factorization`, `artin_char_transform_eq_ntt4`,
  & `artin_char_orthogonality_minivm`
- `FiniteFieldRH.genus2_L_at_1_qrat`,
  `WeilZetaBridge.weil_zeta_punctured_strip_regular_and_nonzero`,
  `GSp4FunctorialityBridge.genus2_f5_so5_ramanujan_tempered`,
  `kim_sarnak_ramanujan_ladder_strict`, &
  `selberg_laplacian_eigenvalue_ladder`
- `EllipticModularityBridge.eichler_shimura_trace_eq_11a1`,
  `hasse_weil_ramanujan_11a1_certs`, &
  `hecke_multiplicativity_11a1_certs`
- `CrtNtt.garnerReconstruct4_sound` & `fermat_tower_conv_bound_certs`
- `PiChudnovsky.pi_105_traps_all_chudnovsky_truncations`

## Architecture Guides & External Verification

- **Yang-Mills QFT Formalization**: Analysis of 4D pure Yang-Mills scaling
  limits and independent verification suite:
  [Yang-Mills overview](docs/yang_mills_formalization_overview.md).
  Check integrity: `make ym-integrity`; status: `make ym-status`.
- **OpenAI-20261028 Constructive Audit**: Classification of all 21 pure
  constructive files:
  [Constructive audit](docs/openai-20261028/CONSTRUCTIVE_AUDIT.md).
- **Local `llama.cpp` Prover**: Wiring `llama-server` to a Lean 4 REPL:
  [llama.cpp prover guide](docs/llama_cpp_prover_architecture.md).
- **Lazy Submodule Hydration**: On-demand hydration (`make hydrate SUB=...`):
  [Lazy hydration guide](docs/lazy_hydration_guide.md).
- **External Verification & Benchmarks**: External typecheckers and axiom
  audits:
  [External verification](docs/external_verification_and_benchmarks.md).

## Project Structure

```
leanasm/
├── .editorconfig            # Code formatting standards
├── .gitignore               # Lake artifacts & transient log rules
├── AGENTS.md                # Governance pointer for AI assistants
├── AI.md                    # Workspace directives and coding standards
├── config_env               # Shell environment setup with run tags
├── docs/                    # Architecture guides and specifications
├── inbox/                   # Ingested research notes
├── lake-manifest.json       # Lake dependency manifest
├── lakefile.toml            # Lake package configuration
├── lean-toolchain           # Active Lean toolchain (v4.35.0)
├── Makefile                 # build, build-incremental, run, test, sync
├── mk/                      # Modular makefile extensions (hydrate.mk)
├── Main.lean                # CLI entrypoint (Parts 1-11 + provenance)
├── src/
│   ├── LeanAsm.lean         # Library root exporting 30 submodules
│   └── LeanAsm/             # 21 domain modules + PiChudnovsky/ + QuasiRiemann/
│       ├── ProvenanceSummary.lean
│       ├── PiChudnovsky/    # CrtMulBridge, Sqrt10005, ChudnovskySeries
│       └── QuasiRiemann/    # Rat, UltraDeep72, Zfr, Bridge, ZD, ShortInt
├── tests/                   # Axiom audit suite (TestAxioms.lean Parts 1-42)
└── tools/                   # Build and logging utilities
```

<!-- end of file: leanasm/README.md -->
