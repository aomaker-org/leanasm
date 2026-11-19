# Path: leanasm/docs/ARCHITECTURE_AND_PROVENANCE.md
# Architecture and Provenance Guide (`ARCHITECTURE_AND_PROVENANCE.md`)
# Max Column: 80 Columns

This document provides a comprehensive architectural audit of all 63 Lean 4
modules in `leanasm` post-PR-#95, detailing how each subsystem contributes to
the master provenance certificate `LeanAsm.leanasm_full_provenance_certified`
strictly within constructive foundations (`[propext, Quot.sound]`, with zero
`Classical.choice` and zero `sorryAx`).

---

## 1. Master Provenance Synthesis & Foundational Principles

### 1.1 The Constructive Invariant
`leanasm` is engineered without reliance on Mathlib or non-constructive choice
axioms. The formal kernel verifies every proposition using purely constructive
reduction:
- Permitted axioms: `propext` (propositional extensionality) and `Quot.sound`
  (quotient soundness).
- Prohibited axioms: `Classical.choice` (law of excluded middle / axiom of
  choice) and `sorryAx` (unproven assumptions / stubs).

The central theorem binding all subsystems is defined in
`src/LeanAsm/ProvenanceSummary.lean`:
```lean
theorem leanasm_full_provenance_certified : LeanAsmFullProvenance
```
where `LeanAsmFullProvenance` is the conjunction of ten domain certificates:
1. `MiniVmProvenance`
2. `CollatzProvenance`
3. `YangMillsProvenance`
4. `QuasiRiemannProvenance`
5. `EulerRnsProvenance`
6. `FiniteFieldWeilProvenance`
7. `CrtNttProvenance`
8. `ChudnovskyPiProvenance`
9. `ProthNttTowerProvenance`
10. `ValuationDynamicsProvenance`

### 1.2 Exact Algebraic/Computational vs. Rational Model/Envelope Bridges
To ensure complete mathematical transparency, `leanasm` explicitly separates
two classes of formal results:
- **Exact Constructive Algebraic & Computational Certificates**:
  Absolute equalities, group-theoretic identities, verified interpreter
  transitions, exact multi-precision integers, and Diophantine exclusions.
  Examples: `MiniVM` bytecode operational semantics, Garner CRT isomorphism,
  NTT invertible matrix butterflies, Chudnovsky 100-digit $\pi$ integer
  bounds, Cantor-Mumford genus-2 Jacobian group laws, and Eisenstein 2-adic
  valuation drops.
- **Rational Envelope & Cleared-Denominator Model Bridges**:
  Constructive approximations where continuous or complex analytic objects
  (such as $\zeta(s)$, $L(s, \chi)$, or path integrals) are represented via
  exact rational dyadic models $\mathbb{Q}$, cleared denominators over
  $\mathbb{N}/\mathbb{Z}$, discrete sums, and explicit interval arithmetic.
  Examples: 2D zero-free rectangle descent tiles ($\sigma \ge 0.5000625$),
  discrete Abel summation bounds, Chebyshev prime count envelopes
  $[10^{12}, 10^{336}]$, and variational mollifier minimization.

---

## 2. Seven-Layer Subsystem Architecture

The 63 modules of `leanasm` form a strictly stratified directed acyclic graph
spanning seven conceptual layers.

### Layer 1: Constructive Invariant & Toolchain Kernel
The execution harness, memory governors, and automated verification suite:
- `AI.md` & `AGENTS.md`: Mandatory operational kernel governing zero silent
  suppression, branch immutability, formatting rules, and execution integrity.
- `Makefile`: Unified build targets (`build-seq`, `build-incremental`,
  `axioms`, `sync`, `status`).
- `tools/incremental_build.py`: Time-boxed sequential Lake build runner with
  heap capping (`-M 4096`) and rolling telemetry tracking against
  `.lake/build-history.json` to prevent RAM thrashing.
- `scripts/inspect_build_history.py`: Telemetry inspector monitoring module
  compilation durations, memory baselines, and regressions.
- `scripts/clip_groups.py` & `scripts/files2clip`: Automated clipboard and
  context ingestion tooling splitting workspace modules into size-capped review
  batches.
- `tests/TestAxioms.lean`: Transitive axiom audit verifying 705+ exported
  theorems reduce strictly to `[propext, Quot.sound]`.
- `tests/TestPreperiodic.lean` & `tests/TestRNS.lean`: Execution test suites
  for $p$-adic dynamical systems and RNS arithmetic.

### Layer 2: Zero-Import Constant Leaves
Self-contained mathematical constants and certified precomputations:
- `LeanAsm/Constants/PiAndSqrt.lean`: Integer square root bounds, scaled
  rational bounds for $\pi$ and $\sqrt{10005}$, and Chudnovsky series constants.
- `LeanAsm/Constants/PrimeTowers.lean`: Certified Fermat primes
  $F_0 = 3, F_1 = 5, F_2 = 17, F_3 = 257, F_4 = 65537$, primitive roots, and
  Proth prime tower data.
- `LeanAsm/Constants/CurveTables.lean`: Points and multiplication tables for
  genus-2 curves and elliptic curves over finite fields $\mathbb{F}_5$ and
  $\mathbb{F}_7$.

### Layer 3: Modular, NTT & Multi-Prime CRT Engines
High-precision multi-prime arithmetic and convolution algorithms:
- `LeanAsm/NttArithmetic.lean`: Universal 4-point and 8-point Number Theoretic
  Transforms, butterfly arithmetic, cyclic convolution soundness, and primitive
  root certificates in $\mathbb{F}_5$ and $\mathbb{F}_{17}$.
- `LeanAsm/CrtNtt.lean`: Multi-prime Garner Chinese Remainder Theorem
  reconstruction over the Fermat moduli $\{5, 17, 257, 65537\}$, Karatsuba
  multiplication, and 192-digit CRT-NTT convolution.
- `LeanAsm/CrtNttUniversal.lean`: Generalized CRT engines with certified bounds
  preventing modular overflow across arbitrary channel widths.
- `LeanAsm/RnsArithmetic.lean`: Residue Number System arithmetic with verified
  channel operations, mixed-radix conversions, and parallel mod operations.
- `LeanAsm/ProthNttTowerBridge.lean`: Alignment of Fermat-Proth modulus chains
  for scalable hierarchical NTT butterflies.
- `LeanAsm/PiChudnovsky/`: Subsystem computing 100 verified decimal digits of
  $\pi$:
  - `Sqrt10005.lean`: Certified Newton-Raphson integer square root of $10005$.
  - `ChudnovskySeries.lean`: Binary splitting partial sums and tail bounds.
  - `CrtMulBridge.lean`: Multi-precision CRT acceleration for Ramanujan-
    Chudnovsky series coefficients.
  - `LeanAsm/PiChudnovsky.lean`: Master module establishing exact two-sided
     rational brackets for $\pi$.

### Layer 4: Register-VM Execution Soundness
Verified hardware/interpreter formalization:
- `LeanAsm/MiniVM.lean`: Formal operational semantics of a register machine
  with register files, memory, and arithmetic instructions; verified execution
  soundness and determinism.
- `LeanAsm/MiniVMNttBridge.lean`: Integration of MiniVM bytecode programs with
  in-register Garner CRT and NTT transforms, proving that assembly execution
  implements mathematical cyclic convolution without overflow.

### Layer 5: p-Adic Ultrametric Valuation, Hensel Lifting & Dynamics
Non-archimedean analysis and arithmetic dynamical systems:
- `LeanAsm/QuasiRiemann/Valuation/Ultrametric.lean`: $p$-adic valuations $v_p$,
  ultrametric triangle inequalities, and non-archimedean absolute values.
- `LeanAsm/QuasiRiemann/Valuation/Contraction.lean`: Strict contraction mappings
  on complete ultrametric spaces and fixed-point uniqueness.
- `LeanAsm/QuasiRiemann/Valuation/Hensel.lean`: Hensel's lemma formalization for
  polynomial root lifting over $\mathbb{Z}_p$.
- `LeanAsm/QuasiRiemann/Valuation/Eisenstein2Adic.lean`: 2-adic valuations of
  Eisenstein series coefficients and modular forms.
- `LeanAsm/QuasiRiemann/Valuation/EisensteinWeights.lean`: Weight-filtration
  bounds and rational valuation lattices for modular structures.
- `LeanAsm/QuasiRiemann/Valuation/PreperiodicDynamics.lean`: Algebraic dynamics,
  wandering point bounds, and preperiodic orbit classifications.
- `LeanAsm/QuasiRiemann/Valuation/RNS.lean`: Bridge linking non-archimedean
  valuation bounds to Residue Number System channels.

### Layer 6: Analytic & Rational Envelope Bridges
Rational interval approximations and zero-free regions for $L$-functions:
- `LeanAsm/QuasiRiemann/Rat.lean`: Exact rational utility lemmas and dyadic
  arithmetic primitives.
- `LeanAsm/QuasiRiemann/QR/QrhCore.lean` & `DirichletSweepLowN.lean` &
  `DirichletSweepN64.lean`: Core Dirichlet polynomial evaluation and certified
  sums over low orders.
- `LeanAsm/QuasiRiemann.lean`: Foundation for Quasi-Riemann Hypothesis (QRH)
  bounding Dirichlet polynomials away from zero.
- `LeanAsm/QuasiRiemann/UltraDeep*`: Deep computational verification of 2D
  zero-free rectangles:
  - `UltraDeep72Core.lean` & `UltraDeep72.lean`: Dimension-72 Dirichlet
    dominance down to $\sigma = 0.501$.
  - `UltraDeep90.lean`: Dimension-90 polynomial evaluations.
  - `UltraDeep108Tables.lean`, `UltraDeep108Eval.lean`,
    `UltraDeep108N1024.lean`, and split modules
    `UltraDeep108N2048Part1/2/3.lean` & `UltraDeep108N2048.lean` &
    `UltraDeep108.lean`: Ultra-deep certified evaluation proving non-vanishing
    down to $\sigma = 0.5000625$ at heights $t \sim 10^{30}$.
- `LeanAsm/QuasiRiemann/AsymptoticZfr.lean` & `AsymptoticZfrBridge.lean`:
  Asymptotic zero-free region envelopes verifying de la Vallée-Poussin bounds.
- `LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`: Zero-density estimates bounding
  the number of potential off-line zeros via rational moments.
- `LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`: Explicit prime existence
  within short intervals $[x, x + x^\theta]$ certified by Chebyshev envelopes.
- `LeanAsm/QuasiRiemann/ParametricQrhLadder.lean`: Rational threshold ladder
  $\theta(k) = (2^k + 1) / 2^{k+1}$ connecting deep sweeps to analytic density.
- `LeanAsm/QuasiRiemann/DyadicAbelBridge.lean`: Discrete Abel summation-by-parts
  on dyadic shells $[M, 2M)$ controlling oscillatory exponential sums.
- `LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean`: Variational
  optimization of two-piece rational mollifiers minimizing mean-square
  Dirichlet integrals.
- `LeanAsm/EulerFactorNonVanishing.lean`: Local Euler factors non-vanishing on
  the critical strip $\sigma \in \{1/2, 3/4, 1\}$.

### Layer 7: Arithmetic, Geometric, Dynamical & Lattice Bridges
Cross-domain applications connecting the kernel to broader mathematics:
- `LeanAsm/Conjectures.lean`: Collatz dynamical step definitions and verified
  base-case cycle exclusions.
- `LeanAsm/CollatzQrhBridge.lean`: Diophantine barriers, Steiner 1-cycle
  exclusions, Simons-de Weger bounds ($m \ge 666$), and logarithmic convergents
  bounding Collatz trajectories.
- `LeanAsm/YangMillsToy.lean`: $4\text{D}$ $\mathbb{Z}_2$ lattice gauge theory,
  Wilson plaquettes, and local gauge invariance.
- `LeanAsm/YangMillsQ8.lean`: Non-abelian $Q_8 \subset \mathrm{SU}(2)$
  quaternion lattice gauge action, plaquette trace cyclicity, and box/slab
  foliation.
- `LeanAsm/ConstructiveOpenaiBridge.lean`: $\mathrm{SignedSym4}$ face-holonomy
  trace identities and discrete geometric gauge bridges.
- `LeanAsm/FiniteFieldRH.lean`: Hasse-Weil bound and Riemann Hypothesis for
  elliptic curves over $\mathbb{F}_7$.
- `LeanAsm/Genus2/PolyF5.lean` & `Cantor.lean`: Explicit polynomial arithmetic
  over $\mathbb{F}_5[x]$ and Cantor algorithm for divisor addition.
- `LeanAsm/Genus2Jacobian.lean`: Group law verification on the Jacobian
  $\mathrm{Jac}(C)(\mathbb{F}_5) \cong \mathbb{Z}/71\mathbb{Z}$ for the genus-2
  curve $y^2 = x^5 - x + 1$.
- `LeanAsm/WeilZetaBridge.lean`: Rational zeta function factorization and
  functional equation $\Xi_C(1 - s) = \Xi_C(s)$.
- `LeanAsm/GSp4FunctorialityBridge.lean`: Degree-4 $L$-function and cyclotomic
  Euler lifts for $\mathrm{GSp}(4)$.
- `LeanAsm/EllipticModularityBridge.lean`: Modularity and Eichler-Shimura trace
  equality for curve $E_{11a1}$.
- `LeanAsm/LanglandsRankinSelbergBridge.lean`: Rankin-Selberg $L$-function
  convolutions and non-vanishing certificates.
- `LeanAsm/ArtinFermatBridge.lean`: GL(1) Artin $L$-function collapse and
  cyclotomic Dedekind splitting across Fermat-tower fields.
- `LeanAsm/ArtinShortIntervalBridge.lean`: Twisted character sums and prime
  distribution in arithmetic progressions.

---

## 3. Comprehensive 63-Module Inventory & Provenance Mapping

Below is the complete topological inventory of all 63 Lean 4 modules, detailing
their architectural layer and hook in `LeanAsmFullProvenance`:

1. `LeanAsm.MiniVM` [Layer 4: VM]
   Hook: `MiniVmProvenance` (`exec_garner_crt_sound`, `mul_mod_reg_correct`).
2. `LeanAsm.Constants.PiAndSqrt` [Layer 2: Constant Leaf]
   Hook: `ChudnovskyPiProvenance` (Certified square root and series constants).
3. `LeanAsm.Constants.PrimeTowers` [Layer 2: Constant Leaf]
   Hook: `ProthNttTowerProvenance` (Fermat primes $\{5, 17, 257, 65537\}$).
4. `LeanAsm.NttArithmetic` [Layer 3: NTT/CRT]
   Hook: `CrtNttProvenance` (NTT matrix invertible butterfly operations).
5. `LeanAsm.CrtNtt` [Layer 3: NTT/CRT]
   Hook: `CrtNttProvenance` (Garner CRT isomorphism & cyclic convolution).
6. `LeanAsm.RnsArithmetic` [Layer 3: NTT/CRT]
   Hook: `EulerRnsProvenance` (Residue Number System mixed-radix conversion).
7. `LeanAsm.EulerFactorNonVanishing` [Layer 6: Analytic]
   Hook: `EulerRnsProvenance` (Local Euler factors non-vanishing on strip).
8. `LeanAsm.CrtNttUniversal` [Layer 3: NTT/CRT]
   Hook: `CrtNttProvenance` (Universal CRT bounds avoiding word overflow).
9. `LeanAsm.MiniVMNttBridge` [Layer 4: VM]
   Hook: `MiniVmProvenance` (`crtNtt4ConvAsm_sound` assembly execution).
10. `LeanAsm.Conjectures` [Layer 7: Bridges]
    Hook: `CollatzProvenance` (Collatz small-value base-case cycle reach).
11. `LeanAsm.YangMillsToy` [Layer 7: Bridges]
    Hook: `YangMillsProvenance` ($\mathbb{Z}_2$ Wilson plaquette invariance).
12. `LeanAsm.YangMillsQ8` [Layer 7: Bridges]
    Hook: `YangMillsProvenance` ($Q_8$ non-abelian gauge action & foliation).
13. `LeanAsm.QuasiRiemann.Rat` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Exact dyadic rational arithmetic basis).
14. `LeanAsm.QuasiRiemann.QR.QrhCore` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Core Dirichlet polynomial evaluation).
15. `LeanAsm.QuasiRiemann.QR.DirichletSweepLowN` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Low-$N$ certified Dirichlet bounds).
16. `LeanAsm.PiChudnovsky.CrtMulBridge` [Layer 3: NTT/CRT]
    Hook: `ChudnovskyPiProvenance` (CRT acceleration for Ramanujan sums).
17. `LeanAsm.QuasiRiemann.QR.DirichletSweepN64` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=64$ certified Dirichlet sums).
18. `LeanAsm.QuasiRiemann` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Mollified 2D zero-free region core).
19. `LeanAsm.QuasiRiemann.UltraDeep72Core` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Dimension-72 lookup tables).
20. `LeanAsm.QuasiRiemann.UltraDeep90` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Dimension-90 phase reduction bounds).
21. `LeanAsm.QuasiRiemann.UltraDeep108Tables` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (108-digit certified rational tables).
22. `LeanAsm.QuasiRiemann.UltraDeep108Eval` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (108-digit Lipschitz evaluations).
23. `LeanAsm.QuasiRiemann.UltraDeep108N1024` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=1024$ tile at $\sigma = 0.500125$).
24. `LeanAsm.QuasiRiemann.UltraDeep108N2048Part1` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=2048$ split part 1 evaluation).
25. `LeanAsm.QuasiRiemann.UltraDeep108N2048Part2` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=2048$ split part 2 evaluation).
26. `LeanAsm.QuasiRiemann.UltraDeep108N2048Part3` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=2048$ split part 3 evaluation).
27. `LeanAsm.QuasiRiemann.UltraDeep108N2048` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` ($N=2048$ tile at $\sigma = 0.5000625$).
28. `LeanAsm.QuasiRiemann.UltraDeep108` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (108-digit master descent verification).
29. `LeanAsm.QuasiRiemann.UltraDeep72` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Dimension-72 master descent tile).
30. `LeanAsm.QuasiRiemann.AsymptoticZfr` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (de la Vallée-Poussin asymptotic ZFR).
31. `LeanAsm.QuasiRiemann.AsymptoticZfrBridge` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Bridge from discrete tiles to ZFR).
32. `LeanAsm.QuasiRiemann.ZeroDensityBridge` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Zero-density rational descent $3/5$).
33. `LeanAsm.QuasiRiemann.ShortIntervalPrimes` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Chebyshev short-interval primes).
34. `LeanAsm.Genus2.PolyF5` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` (Polynomial rings over $\mathbb{F}_5$).
35. `LeanAsm.Constants.CurveTables` [Layer 2: Constant Leaf]
    Hook: `FiniteFieldWeilProvenance` (Point tables for genus-2 curve).
36. `LeanAsm.Genus2.Cantor` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` (Cantor composition & reduction).
37. `LeanAsm.Genus2Jacobian` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` ($\mathrm{Jac}(C) \cong \mathbb{Z}/71$).
38. `LeanAsm.FiniteFieldRH` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` (Hasse-Weil bound on $E/\mathbb{F}_7$).
39. `LeanAsm.GSp4FunctorialityBridge` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` ($\mathrm{GSp}(4) \to \mathrm{SO}(5)$).
40. `LeanAsm.QuasiRiemann.ParametricQrhLadder` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Parametric ladder $\theta(k)$).
41. `LeanAsm.ConstructiveOpenaiBridge` [Layer 7: Bridges]
    Hook: `YangMillsProvenance` ($\mathrm{SignedSym4}$ trace invariance).
42. `LeanAsm.QuasiRiemann.DyadicAbelBridge` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Abel summation on dyadic shells).
43. `LeanAsm.QuasiRiemann.MollifierVariationalBridge` [Layer 6: Analytic]
    Hook: `QuasiRiemannProvenance` (Two-piece variational mollifiers).
44. `LeanAsm.QuasiRiemann.Valuation.Ultrametric` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` ($p$-adic valuation triangle laws).
45. `LeanAsm.QuasiRiemann.Valuation.Contraction` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (Ultrametric contraction mapping).
46. `LeanAsm.QuasiRiemann.Valuation.Hensel` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (Hensel polynomial root lifting).
47. `LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (2-adic Eisenstein coefficients).
48. `LeanAsm.QuasiRiemann.Valuation.EisensteinWeights` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (Weight filtrations on forms).
49. `LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (Preperiodic orbit classifications).
50. `LeanAsm.QuasiRiemann.Valuation.RNS` [Layer 5: Valuation]
    Hook: `ValuationDynamicsProvenance` (Non-archimedean RNS channels).
51. `LeanAsm.WeilZetaBridge` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` (Zeta functional equation $\Xi_C$).
52. `LeanAsm.CollatzQrhBridge` [Layer 7: Bridges]
    Hook: `CollatzProvenance` (Steiner 1-cycle & Simons-de Weger bounds).
53. `LeanAsm.PiChudnovsky.Sqrt10005` [Layer 3: NTT/CRT]
    Hook: `ChudnovskyPiProvenance` (Newton-Raphson $\sqrt{10005}$ bracket).
54. `LeanAsm.PiChudnovsky.ChudnovskySeries` [Layer 3: NTT/CRT]
    Hook: `ChudnovskyPiProvenance` (Chudnovsky series binary splitting).
55. `LeanAsm.PiChudnovsky` [Layer 3: NTT/CRT]
    Hook: `ChudnovskyPiProvenance` (100-digit $\pi$ two-sided bracket).
56. `LeanAsm.ArtinFermatBridge` [Layer 7: Bridges]
    Hook: `ArtinShortIntervalProvenanceProp` (Artin $L$-function collapse).
57. `LeanAsm.ArtinShortIntervalBridge` [Layer 7: Bridges]
    Hook: `ArtinShortIntervalProvenanceProp` (AP prime bounds in towers).
58. `LeanAsm.EllipticModularityBridge` [Layer 7: Bridges]
    Hook: `FiniteFieldWeilProvenance` ($E_{11a1}$ Eichler-Shimura trace).
59. `LeanAsm.LanglandsRankinSelbergBridge` [Layer 7: Bridges]
    Hook: `LanglandsRankinSelbergProvenance` (Rankin-Selberg convolution).
60. `LeanAsm.ProthNttTowerBridge` [Layer 3: NTT/CRT]
    Hook: `ProthNttTowerProvenance` (Proth-Fermat NTT butterfly towers).
61. `LeanAsm.ProvenanceSummary` [Orchestration]
    Hook: Master certificate conjunction `LeanAsmFullProvenance`.
62. `LeanAsm` [Root Library]
    Hook: Top-level aggregate export module importing all submodules.
63. `Main` [CLI Entrypoint]
    Hook: Runtime execution and validation across Parts 1-11.

---

## 4. Verification Workflow & Guardrails

The workspace enforces strict verification steps prior to any commit:
1. **Formatting Audit**: All text and markdown files must not exceed 80
   columns. Code files must not exceed 120 characters.
2. **Sequential Incremental Build**: Heavy files (`UltraDeep108N2048*`,
   `CrtNtt`) must compile within memory budgets via `make build-incremental`.
3. **Strict Axiom Check**: Execute `lake env lean tests/TestAxioms.lean`.
   Any appearance of `Classical.choice`, `sorryAx`, or unverified axioms is
   flagged as an immediate build failure.
4. **Clean Tree Synchronization**: Run `make sync` to ensure full pass on
   CLI parts and pristine git status.

<!-- end of file: leanasm/docs/ARCHITECTURE_AND_PROVENANCE.md -->
