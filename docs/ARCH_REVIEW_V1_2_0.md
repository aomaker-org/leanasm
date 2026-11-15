<!-- Path: leanasm/docs/ARCH_REVIEW_V1_2_0.md -->
<!-- Max Column: 80 Columns -->

# `leanasm` v1.2.0 Architecture Review (`6db78d7`)

`aomaker-org/leanasm` **v1.2.0** (`main` commit `6db78d7`, Lean `v4.35.0`) is a
**35-module**, **72-Lake-job**, warning-free Lean 4 formalization whose theorem
graph resolves constructively over `Nat`, `Int`, and cleared-denominator `QRat`
arithmetic with **zero `Classical.choice`** and **zero `sorryAx`**. Across
**46 audit sections** (`513` `#print axioms` checks over `630` lines) in
[`tests/TestAxioms.lean`](../tests/TestAxioms.lean) and **8 provenance
pillars** in
[`src/LeanAsm/ProvenanceSummary.lean`](../src/LeanAsm/ProvenanceSummary.lean),
the repository connects analytic number theory beyond the `theta = 7/8`
Quasi-Riemann Hypothesis (`QRH`) threshold with the `GL(1) -> GL(2) -> GSp(4)`
Langlands functoriality trilogy, symbolic 4-prime CRT-NTT virtual-machine
compilation, multi-limb Chudnovsky `pi` binary splitting, higher Collatz
barriers, and non-abelian quaternion `Q_8` lattice gauge theory.

---

## 1. Constructive Foundations & Zero-Axiom Invariants

Conventional formalizations of analytic number theory and automorphic forms
depend on Mathlib's noncomputable real/complex analysis (`Real.sqrt`,
`Complex.exp`, classical `Finset`), pulling `Classical.choice` into every
downstream closure. `aomaker-org/leanasm` has **zero Mathlib dependency** and
enforces four constructive invariants:

1. **Pure Lean 4 Core & Decidable Combinatorics:**
   - All order comparisons and list partitions use core constructive primitives:
     `Nat.decLt`, `Int.decLt`, structural induction over `halfOpenRange`, core
     `List.nodup_range`, and explicit `Nodup` witnesses (`range_nodup`,
     `not_mem_erase_of_nodup` in `ConstructiveOpenaiBridge.lean`,
     `UltraDeep72.lean`, and `DyadicAbelBridge.lean`).
2. **Cleared-Denominator Polynomial & Quadratic Arithmetic:**
   - Square-root and local Euler unit-circle bounds are cleared of denominators
     into exact `Int` and `QRat` certificates: `m^2 * bound^2 <= N * num^2`
     for `1 / sqrt(N)` tails (`DyadicAbelBridge.lean`), and positive-definite
     quadratic forms `v^2 - a_p u v + p u^2 > 0` (`v > 0`) plus reciprocal
     discriminants (`EllipticModularityBridge.lean`,
     `GSp4FunctorialityBridge.lean`).
3. **4-Prime Fermat CRT-NTT Engine (`{5, 17, 257, 65537}`):**
   - Exact Garner CRT reconstruction operates over the four Fermat primes
     `F_1 = 5`, `F_2 = 17`, `F_3 = 257`, `F_4 = 65537`, whose product
     `M_4 = 1,431,655,765 = (2^32 - 1) / 3` (`3 * CrtNtt.fermatTowerMod4 =
     2^32 - 1`) fits in 31 bits while powering 192-digit Karatsuba
     multiplication (`CrtNttUniversal`), 90-digit `UltraDeep72` phase
     reductions (`t ln n mod 2pi`), 100-digit Chudnovsky `pi`, and order-4
     `MiniVM` NTT character transforms.
4. **Compiler Hygiene & Bounded Kernel Reduction:**
   - `.lean` modules keep `-- Path:` / `-- end of file:` markers and
     `<= 120` chars/line; `.md` docs wrap at `<= 80` columns; heavy power
     evaluations are scoped with `set_option exponentiation.threshold 2000 in`
     so `lake build` finishes all **72 jobs** with **0 warnings**.

---

## 2. Module Architecture Across 8 Provenance Pillars

The **35 verified modules** (`33` submodules under `src/LeanAsm/`,
[`src/LeanAsm.lean`](../src/LeanAsm.lean), and [`Main.lean`](../Main.lean))
organize into **8 domain provenance pillars** in `ProvenanceSummary.lean`:

1. **Quasi-Riemann Hypothesis & Beyond-`7/8` Primes** (`QuasiRiemannProvenance`)
   - *Core*: `QuasiRiemann`, `ZeroDensityBridge`, `ShortIntervalPrimes`,
     `UltraDeep72`, `ParametricQrhLadder`, `DyadicAbelBridge`.
   - *Scope*: Zero-density descent (`15/26 < 3/5 < 2/3`), unconditional
     `QRH(7/8)` short-interval positivity, inductive `theta(k) -> 1/2` /
     `vartheta(k) -> 1` ladder coupled to Kim-Sarnak `7/64`, `N in {256, 512}`
     rational box contractions down to `sigma = 0.50025` (`t ~ 10^18`), and
     `[M, M * 2^k)` dyadic-shell Abel summation-by-parts.
2. **Finite-Field RH, Weil Zeta & `GL(2) / GSp(4)`**
   (`FiniteFieldWeilProvenance`)
   - *Core*: `FiniteFieldRH`, `WeilZetaBridge`, `Genus2Jacobian`,
     `EllipticModularityBridge` (`#60`), `GSp4FunctorialityBridge` (`#61`).
   - *Scope*: Curve point-counting over `F_q`, Weil zeta rationality, genus-2
     Jacobian `L`-polynomials, `E_{11a1}` / `f_{11} in S_2(Gamma_0(11))`
     Eichler-Shimura trace equality and Ramanujan temperedness (`p <= 97`),
     and `GSp(4) -> SO(5)` lift (`0 < 7/64 < 1/9 < 1/5 < 1/4 < 1/2`).
3. **Euler Products, Fermat RNS & `GL(1)` Artin** (`EulerRnsProvenance`)
   - *Core*: `EulerFactorNonVanishing`, `ArtinFermatBridge` (`#59`),
     `ArtinShortIntervalBridge` (`#70`).
   - *Scope*: Cleared-denominator Euler non-vanishing, `{5, 17, 257, 65537}`
     strip certificates across `32,906` split primes, cyclotomic Artin
     collapse, exact `Z[i]` character orthogonality, and twisted short-interval
     prime positivity.
4. **Universal 4-Prime CRT-NTT Algebraic Engine** (`CrtNttProvenance`)
   - *Core*: `NttArithmetic`, `CrtNtt`, `CrtNttUniversal`.
   - *Scope*: Exact Garner CRT reconstruction, forward/inverse NTTs over
     `{5, 17, 257, 65537}`, and 192-digit Karatsuba CRT-NTT multiplication.
5. **Multi-Limb Chudnovsky `pi` & CRT Mul** (`ChudnovskyPiProvenance`)
   - *Core*: `PiChudnovsky`, `PiChudnovsky/CrtMulBridge`,
     `PiChudnovsky/Sqrt10005`, `PiChudnovsky/ChudnovskySeries`.
   - *Scope*: Chudnovsky binary splitting and arbitrary-size CRT-NTT integer
     multiplication certifying **100-digit** rational bounds for `pi`.
6. **Symbolic `MiniVM` Register Machine & Compiler** (`MiniVmProvenance`)
   - *Core*: `MiniVM`, `MiniVMNttBridge`.
   - *Scope*: Register-machine operational semantics and symbolic compiler
     soundness (`ntt4AsmFermat_sound`, `intt4_ntt4_asm_fermat_roundtrip`).
7. **Higher Collatz Cycle & Density Barriers** (`CollatzProvenance`)
   - *Core*: `Conjectures`, `CollatzQrhBridge`.
   - *Scope*: Constructive Diophantine parity-vector cycle exclusions
     (`m >= 666`, `K >= 1721`) and predecessor-tree density bounds.
8. **Constructive Lattice Gauge Theory & `openai-20261028`**
   (`YangMillsProvenance`)
   - *Core*: `YangMillsToy`, `YangMillsQ8`, `ConstructiveOpenaiBridge` (`#65`).
   - *Scope*: Constructive 4D `Cover4` box combinatorics, `Perm4` /
     `SignedSym4` route transport, `slab_sum_foliation`, `LatticeGroup`
     covariant holonomy, and `Q_8` Wilson-loop / plaquette gauge invariance.

[`Main.lean`](../Main.lean) executes **Parts 1-11** of runtime verification
and exercises `LeanAsm.leanasm_full_provenance_certified`.

---

## 3. Cross-Pillar `v1.2.0` Synthesis Beyond `theta = 7/8`

Building on [`docs/ROADMAP_V1_2_0.md`](ROADMAP_V1_2_0.md) (**Issues
`#68`-`#71`**, **PRs `#73`-`#76`**), `v1.2.0` transforms standalone pillars
into a coupled analytical pipeline feeding `ZeroDensityBridge` and
`ShortIntervalPrimes`:

| Workstream | Bridge Module(s) | Certified `v1.2.0` Deliverable |
| :--- | :--- | :--- |
| `#68`/`#73` | `ParametricQrhLadder` | `theta(k) -> 1/2`, Kim-Sarnak `7/64` |
| `#69`/`#74` | `UltraDeep72` -> `ZD` | `N=256,512` `0.50025` strip (`3/5200`) |
| `#70`/`#75` | `ArtinShortInterval` | `Z[i]` & `MiniVM` NTT AP primes `< 7/8` |
| `#71`/`#76` | `DyadicAbelBridge` | `[M, M*2^k)` shells & `1/sqrt(N)` Abel |

### 3.1 Parametric QRH Ladder & Kim-Sarnak Coupling (`#68` / PR `#73`)

- **Dual Sequences**: `qrhShortExponent k = (2^k + 1) / 2^(k + 1)` strictly
  decreases toward `1/2`, while `qrhDualFraction k = (2^(k + 1) - 1) /
  2^(k + 1)` strictly increases toward `1`.
- **Duality & Density Comparisons**: `qrhShortExponent_strict_anti` (`5/8 >
  9/16 > 17/32 > 33/64 > 1/2`, `< 7/8` for `k >= 2`),
  `qrhDualFraction_strict_mono`, exact dualities `theta(k) + vartheta(k) = 3/2`
  and `vartheta(k) - 1/2 = 1 - theta(k)`, and comparisons against Huxley
  (`7/12`), Guth-Maynard (`17/30`), and `zdGuthMaynard` saving (`11/26`).
- **Automorphic Feedback**: `kim_sarnak_amplified_qrh_step` and
  `parametric_qrh_kim_sarnak_certs` couple `thetaKimSarnakSym4 = 7/64` and
  `selbergLambda1 = 975/4096` to certify `vartheta = 25/32`, `theta = 39/64 <
  5/8`, and `[10^96, 10^96 + 10^57]` prime positivity at `theta = 17/32`
  (`shortIntervalQrh1732Spec_has_prime`).

### 3.2 Rational Box Contraction & Strip Export (`#69` / PR `#74`)

- **Generalized Contraction (`UltraDeep72.lean`, Part 19)**: Replaces fixed
  `1/2` halving with `0 < q_num < q_den` (`RationalBoxContractionSpec`,
  `rational_box_contraction_step`, `nat_pow_contraction_le`,
  `rational_telescoping_chain_cert`) and shrunk-ball `M / (r - delta)` margins.
- **`N = 256, 512` Zero-Free Rectangles**: Certifies
  `ultraDeep72_N256_rational_rect_cert` (`N = 256`, `sigma = 0.5005`,
  `t ~ 10^12`, `q = 1/3`, `dirichletGradBoundScaled6_512 500500 256 =
  117284435`) and `ultraDeep72_N512_rational_rect_cert` (`N = 512`, `sigma =
  0.50025 = 1/2 + 1/4000`, `t ~ 10^18`, `q = 2/5`, `195620879`).
- **Strip Export (`ZeroDensityBridge.lean`, Part 7)**:
  `CertifiedStripWidthSpec`, `ultradeep72_strip_to_zero_density_bridge`, and
  `ultradeep72_N512_strip_zd_certs` tighten zero-density exponents by `3/5200`
  (`zdGuthMaynard`) and `3/5000` (`zdHuxley`).

### 3.3 `GL(1)` Artin Short-Interval Primes (`#70` / PR `#75`)

- **Gaussian Orthogonality (`ArtinShortIntervalBridge.lean`)**: Proves
  `artin_gaussian_char_orthogonality` in `Z[i]` and links `MiniVM`
  `ntt4AsmFermat` / `intt4AsmFermat` execution modulo `F_k in
  {5, 17, 257, 65537}` back to residue-class prime sums via
  `artin_ntt4_residue_class_recovery`.
- **Twisted Positivity**: `ArtinTwistedShortIntervalSpec` proves
  `artin_twisted_ap_short_interval_pos`,
  `artin_twisted_coset_short_interval_pos`, and
  `fermat_tower_artin_short_interval_certs` for
  `theta in {17/32, 39/64, 5/8, 2/3, 3/4}`.

### 3.4 Dyadic-Shell Foliation & Discrete Abel Summation (`#71` / PR `#76`)

- **Constructive `[M, M * 2^k)` Shells (`DyadicAbelBridge.lean`)**: Extends
  `slab_sum_foliation` to `halfOpenRange`, `rangeSumInt`, `partialSumInt`, and
  `dyadicShellPartition` (`dyadic_shell_sum_partition`,
  `dyadic_shell_sum_foliation`).
- **Abel Summation & `1 / sqrt(N)` Tail Gates**: Proves
  `discrete_abel_summation_by_parts`, `abel_summation_by_parts_list`, and
  monotone-weight envelopes (`abel_monotone_weight_envelope_qrat`, bound
  `2 E |w(M + 1)|`) alongside quadratic `SqrtTailGateSpec` /
  `InvSqrtTailGateSpec` (`inv_sqrt_tail_gate_dyadic_step`), yielding
  `short_interval_dyadic_abel_envelope` and
  `dyadic_abel_short_interval_certs` across
  `theta in {17/32, 9/16, 5/8, 2/3, 3/4}`.

---

## 4. Unified Provenance Closure & Parts 1-46 Axiom Audit

[`src/LeanAsm/ProvenanceSummary.lean`](../src/LeanAsm/ProvenanceSummary.lean)
pairs eight `def ...Provenance : Prop` conjunctions with constructive witnesses
and binds them in `LeanAsm.leanasm_full_provenance_certified` (whose type is
the explicit 8-way conjunction of all eight domain predicates). Auditing
`LeanAsm.leanasm_full_provenance_certified` therefore traverses every theorem
across all **35 modules**.

Running `lake env lean tests/TestAxioms.lean` audits **513** `#print axioms`
declarations across **630 lines** (**Parts 1-46**): `165` zero-axiom (`none`),
`36` `[propext]`, `312` `[propext, Quot.sound]`, **`0` `Classical.choice`**,
**`0` `sorryAx`**, and **`0` warnings**:

- **Parts 1-38 (`v1.0.0`)**: Core `MiniVM`, `CrtNtt`, `PiChudnovsky`,
  `CollatzQrhBridge`, `EulerFactorNonVanishing`, `FiniteFieldRH`,
  `WeilZetaBridge`, `Genus2Jacobian`, `QuasiRiemann`, `ZeroDensityBridge`,
  `ShortIntervalPrimes`, `UltraDeep72`, and initial `ProvenanceSummary` bundles.
- **Parts 39-40 (`#59`, `#61` / PRs `#62`-`#63`)**: `ArtinFermatBridge`,
  `GSp4FunctorialityBridge`, `UltraDeep72.telescoping_box_contraction_cert`.
- **Part 41 (`#65` / PR `#66`)**: `ConstructiveOpenaiBridge` (`Cover4`,
  `slab_sum_foliation`, `q8_plaquette_holonomy_gauge_invariant`,
  `q8_send_price_trace_invariant`).
- **Part 42 (`#60` / PR `#67`)**: `EllipticModularityBridge` (`E_{11a1}` /
  `f_{11}`, `p <= 97`).
- **Part 43 (`#68` / PR `#73`)**: `ParametricQrhLadder`.
- **Part 44 (`#69` / PR `#74`)**: `UltraDeep72` Part 19 & `ZeroDensityBridge`
  Part 7.
- **Part 45 (`#70` / PR `#75`)**: `ArtinShortIntervalBridge`.
- **Part 46 (`#71` / PR `#76`)**: `DyadicAbelBridge`.

Running `make sync` verifies both full **72-job** Lake compilation across all
**35 modules** and live CLI execution (`Main.lean`, Parts 1-11).

<!-- end of file: leanasm/docs/ARCH_REVIEW_V1_2_0.md -->
