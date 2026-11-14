<!-- Path: leanasm/docs/openai-20261028/LEAN_TOC.md -->
<!-- Max Column: 80 Columns -->

# OpenAI 2026-10-28 Lean 4 Proof Table of Contents & Hygiene Audit

## 1. Corpus & Declaration Totals

- **Total Lean Files**: 9,564
- **Total Declarations**: 100,680
- **Full AST/TOC JSON**: See `LEAN_TOC.json` for every file, import, scope, and
  decl.

### Declarations by Kind

| Kind      | Count  |
| --------- | ------ |
| abbrev    | 4,852  |
| axiom     | 1      |
| class     | 4      |
| def       | 24,462 |
| inductive | 45     |
| instance  | 363    |
| lemma     | 60,424 |
| structure | 4,150  |
| theorem   | 6,379  |

## 2. `leanasm` Compatibility Hygiene Audit

| Audit Check                 | Files |
| --------------------------- | ----- |
| Custom `axiom` decls        | 1     |
| Uses `sorry`                | 7     |
| Uses `admit`                | 0     |
| Classical / noncomputable   | 9527  |
| Explicit `Classical.choice` | 166   |
| Real/Complex/Filter/Asymp   | 9437  |
| Mathlib/Std-ext imports     | 707   |
| Pure constructive files     | 21    |

### Files with Custom Axioms

- `verification/controls/forbidden_axiom/Solution.lean`: unapproved@L1

### Files with `sorry` or `admit`

- `submission/Challenge.lean` sorry @ L6
- `verification/AcceptanceChallenge.lean` sorry @ L12
- `verification/OPEChallenge.lean` sorry @ L12
- `verification/controls/accept/Challenge.lean` sorry @ L1
- `verification/controls/definition_mismatch/Challenge.lean` sorry @ L2
- `verification/controls/forbidden_axiom/Challenge.lean` sorry @ L1
- `verification/controls/statement_mismatch/Challenge.lean` sorry @ L1

### Pure Constructive Files (Zero Mathlib/Real/Complex/Sorry)

- `checks/AxiomAudit.lean` (0 decls)
- `provenance/lgt/LGT/GaugeField/Connection.lean` (8 decls)
- `provenance/lgt/LGT/GaugeField/Holonomy.lean` (0 decls)
- `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean` (0 decls)
- `submission/Solution.lean` (1 decls)
- `submission/YM.lean` (0 decls)
- `submission/YM/Lattice/Faces.lean` (20 decls)
- `submission/YM/Lattice/Foliation.lean` (14 decls)
- `submission/YM/Lattice/Route.lean` (15 decls)
- `submission/YM/UVExtension/Orchard/Apple.lean` (0 decls)
- `submission/YM/UVExtension/Orchard/Barrel.lean` (4 decls)
- `submission/YM/UVExtension/Orchard/Muesli.lean` (0 decls)
- `submission/YM/UVExtension/Orchard/Pours.lean` (0 decls)
- `submission/YM/UVExtension/Orchard/Shears.lean` (0 decls)
- `submission/YM/UVExtension/Orchard/Tarts.lean` (0 decls)
- `submission/YM/UVExtension/Orchard/Vanilla.lean` (0 decls)
- `submission/verification/Inventory.lean` (0 decls)
- `submission/verification/Usage.lean` (1 decls)
- `verification/controls/accept/Solution.lean` (1 decls)
- `verification/controls/definition_mismatch/Solution.lean` (2 decls)
- `verification/controls/statement_mismatch/Solution.lean` (1 decls)

## 3. Root, Checks, Docs & Verification TOC

- `checks/AFSourceBridge.lean` (78L, 7 decls, [noncomp/Classical, Real/Complex])
imports: ImportedAFSpecification, YM.TraceExtension.Endpoint, SourceScalar
    - L15 `theorem YMAFBridge.same_center` -- The endpoint's centering is
  exactly the field used in the completed OS bridge.
    - L26 `def YMAFBridge.K` -- Same centered selected-phase kernel, with one
  insertion at the origin.
    - L29 `theorem YMAFBridge.K`
    - L40 `theorem YMAFBridge.canonical_award`
    - L48 `theorem YMAFBridge.leading_all_directions` -- Full punctured-space
  leading limit, not only a time-axis or sequence limit.
  - ... (2 more decls in `LEAN_TOC.json`)
- `checks/AcceptanceSpec.lean` (178L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: CompleteOS, AFSourceBridge, CommonScaleAudit,
TwoPointPhysicalObservable (+4)
    - L34 `structure YMReview.Acceptance.LatticeAndScale` -- The actual finite
  law and common calibration, with full UV then extracted IR. The coupling
  conversion is beta_lgt = beta_submission / representation dimension.
    - L63 `structure YMReview.Acceptance.PhaseAndOS` -- Exact group OS interface
  on the selected centered trace, plus the actual integral and the phase-average
  identification with the lattice-limit table.
    - L84 `structure YMReview.Acceptance.TranslationWard` -- The coefficient and
  sign are fixed here, not existentially fitted. Every central field and every
  phase is covered; shell integrability is explicit.
    - L112 `structure YMReview.Acceptance.OperatorContent` -- The accepted
  registered local content, no additional null fields and dense word domain.
  This is not an isomorphism to a separately specified canonical QFT.
    - L131 `structure YMReview.Acceptance.LeadingTrace` -- The fixed leading
  coefficient on the same selected field, in all directions. No two-loop rate,
  intrinsic Lambda or positive-order matching is asserted.
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/ArityGrowth.lean` (163L, 4 decls, [noncomp/Classical, Real/Complex])
imports: Invariance, YangMills.OSRecon.Growth, YM.Work.B11
    - L20 `theorem YMOSBridge.scalarKernel_all_arity_bound` -- One pair of
  constants works for all arities of the fixed observable.
    - L51 `theorem YMOSBridge.targetKernel_all_arity_bound` -- A linearly
  growing singular order, with the explicit n^(A*n) cost.
    - L74 `theorem YMOSBridge.arity_power_le_factorial` -- The elementary
  factorial estimate absorbs the explicit arity cost.
    - L91 `theorem YMOSBridge.E0_prime_growth` -- E0′ as an estimate,
  independent of the still-open E4 obligation. The prefactor alpha can be taken
  to be one; both the seminorm slope and factorial exponent a...
- `checks/AxiomAudit.lean` (12L, 0 decls, [PURE]) imports: CombinedAcceptance
- `checks/ClusterCones.lean` (104L, 4 decls, [noncomp/Classical, Real/Complex])
imports: ClusterCore, YM.Ground.Lean
    - L12 `theorem YMOSBridge.chamber_vacuum_transverse`
    - L18 `theorem YMOSBridge.chamber_transverse_cluster`
    - L39 `theorem YMOSBridge.chamber_word_placements` -- Arbitrary separated
  words have positive-half-space representatives whose vacuum matrix elements
  retain the original one-word expectations.
    - L84 `theorem YMOSBridge.chamber_word_cone_cluster`
- `checks/ClusterCore.lean` (73L, 5 decls, [noncomp/Classical, Real/Complex])
imports: YM.EveryPhase.Extension
    - L15 `theorem YMOSBridge.chamber_ground_projection` -- Uniqueness of the
  heat vacuum identifies the full ground projection.
    - L28 `theorem YMOSBridge.chamber_mixed_heat_limit` -- Mixed heat pairings
  factorize, with no compact-support or rate premise.
    - L38 `theorem YMOSBridge.chamber_word_cluster` -- A reflected word and a
  positive word factorize along the chamber axis. Both words may have arbitrary
  registered labels and any finite length.
    - L50 `theorem YMOSBridge.phase_word_cluster` -- Axis-separated word
  clustering is available in every constructed character.
    - L58 `theorem YMOSBridge.phase_mixed_heat_limit` -- The boundary
  Hilbert-space version, using its actual energy evolution.
- `checks/ClusterDomination.lean` (79L, 3 decls, [noncomp/Classical,
Real/Complex]) imports: Temperedness
    - L11 `theorem YMOSBridge.separation_translate`
    - L23 `theorem YMOSBridge.translated_flat`
    - L40 `theorem YMOSBridge.translated_kernel_majorant` -- The bound depends
  on f, but not on the displacement b or the flat witness h.
- `checks/ClusterKernel.lean` (92L, 6 decls, [noncomp/Classical, Real/Complex])
imports: ClusterCones, SourceScalar
    - L11 `def YMOSBridge.joinPoints`
    - L14 `theorem YMOSBridge.realize_join`
    - L24 `theorem YMOSBridge.move_join`
    - L33 `theorem YMOSBridge.exists_signed_large_coordinate`
    - L50 `theorem YMOSBridge.scalarKernel_cone_cluster`
  - ... (1 more decls in `LEAN_TOC.json`)
- `checks/ClusterSchwartz.lean` (134L, 6 decls, [noncomp/Classical,
Real/Complex]) imports: ClusterTarget, ClusterDomination,
ImportedSchwartzProduct
    - L12 `theorem YMOSBridge.zeroDiagonal_zero_of_noninjective`
    - L23 `theorem YMOSBridge.joint_test_shift`
    - L38 `theorem YMOSBridge.split_measurePreserving`
    - L49 `theorem YMOSBridge.cluster_integral_product`
    - L74 `theorem YMOSBridge.weighted_kernel_cluster`
  - ... (1 more decls in `LEAN_TOC.json`)
- `checks/ClusterTarget.lean` (93L, 8 decls, [noncomp/Classical, Real/Complex])
imports: ClusterKernel, TargetKernel
    - L11 `def YMOSBridge.blockShift`
    - L14 `def YMOSBridge.joinConfig`
    - L18 `theorem YMOSBridge.joinConfig_eq_add`
    - L24 `theorem YMOSBridge.configEquiv_join`
    - L32 `theorem YMOSBridge.pointEquiv_supnorm`
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/CombinedAcceptance.lean` (122L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: AcceptanceSpec
    - L13 `theorem YMReview.Acceptance.finite_law_on_family`
    - L22 `theorem YMReview.Acceptance.lattice_and_scale`
    - L40 `theorem YMReview.Acceptance.phase_and_os`
    - L52 `theorem YMReview.Acceptance.translation_ward`
    - L58 `theorem YMReview.Acceptance.operator_content`
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/CommonScaleAudit.lean` (94L, 12 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Spec.Closed
    - L14 `theorem YMReview.CommonScale.reference_spacing`
    - L16 `theorem YMReview.CommonScale.physical_side`
    - L23 `theorem YMReview.CommonScale.reference_coupling`
    - L27 `theorem YMReview.CommonScale.same_reference_coupling`
    - L31 `theorem YMReview.CommonScale.positive_common_reference`
  - ... (7 more decls in `LEAN_TOC.json`)
- `checks/CompleteOS.lean` (82L, 5 decls, [noncomp/Classical, Real/Complex])
imports: ClusterSchwartz, RemainingObligations
    - L14 `theorem YMOSBridge.E4_cluster_norm`
    - L37 `theorem YMOSBridge.E4_cluster` -- The exact spatial E4 field from the
  vendored OSreconstruction definition.
    - L60 `def YMOSBridge.verifiedOS` -- E0, E1, E2, E3 and E4 for the original
  selected hierarchy, without any additional analytic premise.
    - L62 `theorem YMOSBridge.verifiedOS_growth`
    - L67 `theorem YMOSBridge.constructed_OS_family` -- Actual outputs of the
  submitted construction satisfy all target OS axioms and the corrected E0-prime
  growth condition, retaining the original limit orders.
- `checks/CompletenessAudit.lean` (78L, 7 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Spec.Closed, YM.Next.MAXWELL.System,
YM.EveryPhase.Extension
    - L20 `theorem YMReview.OperatorCompleteness.raw_register_exhaustive` --
  Every gauge-invariant polynomial belongs to some finite register level.
    - L31 `theorem YMReview.OperatorCompleteness.free_no_extra_nulls` -- The
  free comparison space has no further separated-correlator nulls.
    - L35 `theorem YMReview.OperatorCompleteness.free_sector_exhaustive` -- Its
  on-shell image is exactly the full invariant polynomial space at this weight.
    - L45 `theorem YMReview.OperatorCompleteness.local_field_content` --
  Combining the submitted rank theorem with the exact free quotient.
    - L52 `theorem YMReview.OperatorCompleteness.phase_field_content` -- Phase
  selection preserves this full degreewise field content.
  - ... (2 more decls in `LEAN_TOC.json`)
- `checks/Coordinates.lean` (83L, 13 decls, [noncomp/Classical, Real/Complex])
imports: SourceScalar, YangMills.OSRecon.Vendored.Axioms
    - L10 `def YMOSBridge.axisSwap`
    - L12 `def YMOSBridge.pointLinear`
    - L20 `def YMOSBridge.pointEquiv`
    - L22 `def YMOSBridge.configEquiv`
    - L26 `theorem YMOSBridge.configEquiv_apply`
  - ... (8 more decls in `LEAN_TOC.json`)
- `checks/ImportedAFGauge.lean` (140L, 7 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib.Analysis.SpecialFunctions.Pow.Real
    - L52 `structure GaugeGroupData` -- The Lie-algebra invariants of a compact
  simple gauge group that appear in the statement of the Yang-Mills existence
  and mass gap problem: the dimension of th...
    - L85 `def GaugeGroupData.betaZero` -- The one-loop beta-function
  coefficient `b₀ = (11/3) C₂(adj)`, in the convention `μ dg/dμ = − b₀
  g³/(16π²)`. Its positivity — asymptotic freedom of perturbati...
    - L88 `theorem GaugeGroupData.betaZero_pos`
    - L96 `def GaugeGroupData.betaOne` -- The two-loop beta-function coefficient
  `b₁ = (34/3) C₂(adj)²`, in the convention `μ dg/dμ = − b₀ g³/(16π²) − b₁
  g⁵/(16π²)²`. For `SU(3)`: `b₁ = 102`.
    - L99 `theorem GaugeGroupData.betaOne_pos`
  - ... (2 more decls in `LEAN_TOC.json`)
- `checks/ImportedAFSpecification.lean` (71L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Spec.Closed, ImportedAFGauge
    - L8 `abbrev SpaceTime`
    - L10 `def uvLog`
    - L13 `def freeTraceTwoPoint`
    - L15 `theorem freeTraceTwoPoint_pos`
    - L20 `def KernelUVPowerLaw`
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/ImportedCenterWeights.lean` (34L, 4 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib.Analysis.SpecialFunctions.JapaneseBracket,
Mathlib.MeasureTheory.Integral.Pi, Mathlib.MeasureTheory.Group.Prod,
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
    - L11 `def EuclideanField.centerWeight` -- Integrable polynomial center
  weight.
    - L13 `lemma EuclideanField.centerWeight_nonneg`
    - L17 `lemma EuclideanField.centerWeight_pos`
    - L24 `lemma EuclideanField.integrable_centerWeight`
- `checks/ImportedDiagonalFlatBounds.lean` (370L, 15 decls, [noncomp/Classical,
Real/Complex]) imports: ImportedCenterWeights,
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Normed.Module.Convex
    - L19 `theorem YangMills.Analysis.norm_le_pow_mul_of_iteratedFDeriv_eq_zero`
  -- An arbitrary-order Taylor bound with a coarse constant independent of the
  order. The first `N` derivatives vanish at the base point. No compactness or
  scalar...
    - L56 `theorem YangMills.Analysis.one_add_norm_le_of_mem_segment` --
  Schwartz decay weights are comparable along every segment of length at most
  one.
    - L69 `theorem
  YangMills.Analysis.weighted_norm_le_pow_mul_sup_seminorm_of_flat` -- A
  directed Schwartz-seminorm Taylor estimate. The uniform constant is explicit
  and grows only exponentially in the weight and derivative rectangle orders.
    - L109 `theorem YangMills.Analysis.norm_sub_update_eq` -- Moving one
  coordinate to an affine coincidence locus costs exactly the corresponding
  affine separation in the joint maximum norm.
    - L125 `def YangMills.Analysis.affineCoincidenceSeparation` -- The minimum
  of one and a finite family's affine pair separations. Empty families have
  separation one. Arbitrary shifts include both ordinary and translated c...
  - ... (10 more decls in `LEAN_TOC.json`)
- `checks/ImportedLGTData.lean` (121L, 25 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib
    - L6 `abbrev GaussianField.FinLatticeSites`
    - L11 `structure LatticeLink`
    - L17 `def siteShift` -- Shift a site by +1 in direction μ.
    - L22 `theorem siteShift_comm` -- Shifts in different directions commute.
    - L29 `def LatticeLink.target` -- Target of a link.
  - ... (20 more decls in `LEAN_TOC.json`)
- `checks/ImportedReflectionApproximation.lean` (190L, 8 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.Axioms,
ImportedSchwartzCutoffs, ImportedSchwartzProduct
    - L12 `theorem SchwartzMap.exists_compactCutoff_sequence_tsupport_subset` --
  Compact approximation that retains the original topological support.
    - L39 `theorem YangMills.OSRecon.exists_compact_ordered_sequence`
    - L52 `theorem YangMills.OSRecon.continuous_source_tensorProduct`
    - L63 `theorem YangMills.OSRecon.continuous_source_osConj`
    - L89 `theorem YangMills.OSRecon.continuous_source_osConjTensorProduct`
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/ImportedSchwartzCutoffs.lean` (183L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension,
Mathlib.Topology.Sequences, ImportedSchwartzDomain
    - L25 `theorem SchwartzMap.norm_iteratedFDeriv_dilate_le`
    - L46 `theorem SchwartzMap.norm_iteratedFDeriv_dilate_sub_one_le`
    - L59 `theorem SchwartzMap.weighted_derivative_le_inv_mul_seminorm`
    - L68 `theorem SchwartzMap.dilate_hasTemperateGrowth`
    - L75 `theorem SchwartzMap.seminorm_dilateCutoff_sub_le` -- Every weighted
  derivative of a cutoff error is controlled by one additional Schwartz decay
  weight. The cutoff derivative constants do not depend on R.
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/ImportedSchwartzDomain.lean` (27L, 2 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
    - L8 `def SchwartzMap.complexDomCongr` -- A domain equivalence acts
  continuously and complex linearly by pullback.
    - L22 `theorem SchwartzMap.complexDomCongr_apply`
- `checks/ImportedSchwartzProduct.lean` (222L, 21 decls, [noncomp/Classical,
Real/Complex]) imports: ImportedSchwartzDomain, Mathlib.Tactic.GCongr
    - L15 `def SchwartzMap.productSeminorm` -- Finite Schwartz seminorm envelope
  used for the external-product estimate.
    - L19 `theorem SchwartzMap.continuous_productSeminorm`
    - L24 `theorem SchwartzMap.seminorm_le_productSeminorm`
    - L37 `theorem SchwartzMap.norm_iteratedFDeriv_comp_contract`
    - L51 `theorem SchwartzMap.weighted_derivative_externalProduct_le`
  - ... (16 more decls in `LEAN_TOC.json`)
- `checks/Invariance.lean` (140L, 12 decls, [noncomp/Classical, Real/Complex])
imports: Temperedness
    - L11 `theorem YMOSBridge.schwinger_comp`
    - L21 `theorem YMOSBridge.E1_translation_invariant`
    - L31 `theorem YMOSBridge.E3_symmetric`
    - L47 `theorem YMOSBridge.E0_reality`
    - L61 `def YMOSBridge.matrixOrtho`
  - ... (7 more decls in `LEAN_TOC.json`)
- `checks/LGTWilsonBridge.lean` (135L, 18 decls, [noncomp/Classical,
Real/Complex]) imports: ImportedLGTData, WilsonBridge
    - L12 `def YMLGTBridge.linkEquiv`
    - L18 `instance YMLGTBridge.<anonymous_instance>`
    - L20 `def YMLGTBridge.faceEquiv`
    - L26 `instance YMLGTBridge.<anonymous_instance>`
    - L28 `instance YMLGTBridge.<anonymous_instance>`
  - ... (13 more decls in `LEAN_TOC.json`)
- `checks/NonzeroPhysicalObservable.lean` (126L, 16 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Nonperturbative.Continuum,
Mathlib.Analysis.SpecialFunctions.Pow.Continuity
    - L19 `def YMReview.NonzeroScale.massMagnitude`
    - L21 `theorem YMReview.NonzeroScale.continuous_massMagnitude`
    - L24 `theorem YMReview.NonzeroScale.massMagnitude_pos`
    - L28 `theorem YMReview.NonzeroScale.map_limits`
    - L40 `theorem YMReview.NonzeroScale.nonzero_field_detected` -- A field is
  zero precisely when every tested correlation containing it is zero. This gives
  a nonzero unselected correlation without equating phases.
  - ... (11 more decls in `LEAN_TOC.json`)
- `checks/OPECheck.lean` (89L, 6 decls, [noncomp/Classical, Real/Complex])
imports: OPESpec, Solution
    - L11 `theorem YMReview.OPE.radius_of_eventually`
    - L17 `theorem YMReview.OPE.from_source` -- Translate the source OPE into
  the review's explicit radius statement.
    - L28 `theorem YMReview.OPE.phase_difference` -- Subtracting two phases
  preserves exactly the same OPE coefficients. The estimate is uniform in BOTH
  phases, with twice the original remainder.
    - L56 `theorem YMReview.OPE.constructed` -- One family is chosen before
  every requested volume sequence. The review check and original Properties hold
  for the SAME resulting hierarchy.
    - L72 `theorem YMReview.OPE.channel_assembly` -- Channels assemble into the
  actual degree-j coefficient field.
  - ... (1 more decls in `LEAN_TOC.json`)
- `checks/OPESpec.lean` (45L, 4 decls, [noncomp/Classical, Real/Complex])
imports: ChallengeSpec
    - L14 `def YMReview.OPE.Cluster`
    - L18 `def YMReview.OPE.Spectators`
    - L22 `def YMReview.OPE.truncated`
    - L31 `structure YMReview.OPE.CommonOPE` -- Coefficients are already fixed
  in T, before spectators, truncation, geometry bounds, radius, or phase are
  requested. In particular the radius for the remaind...
- `checks/ReflectionPositivity.lean` (58L, 3 decls, [noncomp/Classical,
Real/Complex]) imports: ReflectionTransport, ImportedReflectionApproximation
    - L17 `theorem YMOSBridge.compact_reflection_positive` -- Compact-test
  positivity on the target's exact reflection form, in arbitrary mixed arities
  with arbitrary complex coefficients (including arity zero).
    - L37 `theorem YMOSBridge.reflection_positive_family` -- Positivity extends
  to all ordered-support Schwartz test families by support-preserving compact
  cutoffs and continuity of E0 and reflected tensors.
    - L48 `theorem YMOSBridge.E2_reflection_positive` -- The literal
  OSreconstruction E2 field for every Borchers sequence allowed by that axiom,
  not merely finite tensor-product or compact-support tests.
- `checks/ReflectionTransport.lean` (151L, 11 decls, [noncomp/Classical,
Real/Complex]) imports: Invariance, YM.Euclid.Pairing
    - L14 `theorem YMOSBridge.pointEquiv_measurePreserving` -- Swapping the time
  coordinate and passing to Euclidean coordinates has unit Jacobian, including
  the zero-arity product below.
    - L20 `theorem YMOSBridge.configEquiv_measurePreserving`
    - L25 `theorem YMOSBridge.ordered_config_conf`
    - L33 `def YMOSBridge.compactTest` -- The same compact test, expressed in
  the submitted construction's coordinates.
    - L48 `def YMOSBridge.tracePastTest` -- Constant centered-trace labels on
  the transported compact test.
  - ... (6 more decls in `LEAN_TOC.json`)
- `checks/RemainingObligations.lean` (101L, 7 decls, [noncomp/Classical,
Real/Complex]) imports: ReflectionPositivity, ArityGrowth,
YM.Nonperturbative.Continuum
    - L17 `def YMOSBridge.ReflectionObligation` -- The exact E2 predicate, now
  discharged by E2_reflection_positive.
    - L22 `def YMOSBridge.ClusterObligation` -- Exactly the target E4 field,
  with the same state and observable.
    - L34 `def YMOSBridge.completeOS` -- The literal group-vendored
  OSreconstruction record with only E4 remaining as an explicit premise. E0, E1,
  E2 and E3 are all theorems of this family.
    - L48 `def YMOSBridge.GrowthObligation` -- The corrected OS-II growth
  predicate, now discharged by E0_prime below. No old fixed-order growth
  condition is substituted for it.
    - L53 `theorem YMOSBridge.E0_prime` -- The exact corrected target growth
  record. E4 occurs only because its OS record is an argument to the target
  structure; E0_prime_growth does not use E4.
  - ... (2 more decls in `LEAN_TOC.json`)
- `checks/SourceScalar.lean` (74L, 9 decls, [noncomp/Classical, Real/Complex])
imports: YM.Trace.Center
    - L14 `def YMOSBridge.scalarKernel`
    - L17 `theorem YMOSBridge.scalarKernel_smooth`
    - L21 `theorem YMOSBridge.scalarKernel_translation`
    - L26 `theorem YMOSBridge.scalarKernel_permutation`
    - L32 `theorem YMOSBridge.scalarKernel_rotation`
  - ... (4 more decls in `LEAN_TOC.json`)
- `checks/TargetKernel.lean` (113L, 12 decls, [noncomp/Classical, Real/Complex])
imports: Coordinates, ImportedDiagonalFlatBounds
    - L13 `def YMOSBridge.targetKernel` -- Zero on diagonals is an explicit
  harmless totalization, not a contact-term claim.
    - L17 `theorem YMOSBridge.targetKernel_eq`
    - L22 `theorem YMOSBridge.targetKernel_measurable`
    - L31 `def YMOSBridge.coincidencePairs`
    - L34 `def YMOSBridge.separation`
  - ... (7 more decls in `LEAN_TOC.json`)
- `checks/Temperedness.lean` (117L, 8 decls, [noncomp/Classical, Real/Complex])
imports: TargetKernel
    - L14 `def YMOSBridge.schwinger`
    - L17 `theorem YMOSBridge.schwinger_integrable_bound`
    - L47 `theorem YMOSBridge.schwinger_integrable`
    - L52 `theorem YMOSBridge.E0_linear`
    - L62 `def YMOSBridge.schwingerLinear`
  - ... (3 more decls in `LEAN_TOC.json`)
- `checks/TwoPointPhysicalObservable.lean` (172L, 11 decls, [noncomp/Classical,
Real/Complex]) imports: NonzeroPhysicalObservable
    - L15 `theorem YMReview.TwoPointScale.joined_eq_opposed`
    - L35 `def YMReview.TwoPointScale.phaseValue`
    - L38 `theorem YMReview.TwoPointScale.phaseValue_selected`
    - L44 `theorem YMReview.TwoPointScale.phaseValue_nonneg`
    - L58 `theorem YMReview.TwoPointScale.phaseValue_continuous_and_average`
  - ... (6 more decls in `LEAN_TOC.json`)
- `checks/WardFormulationAudit.lean` (67L, 4 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Spec.Closed, YM.Work.A01.Support
    - L19 `theorem YMReview.WardAudit.windows_exist` -- Every separated
  configuration admits an admissible shell.
    - L25 `theorem YMReview.WardAudit.phase_translation_derivative` -- The same
  stress field generates the actual coordinate derivative in every phase, for
  every central field and every finite list of exterior spectators.
    - L39 `theorem YMReview.WardAudit.phase_translation_integrable` -- Shell
  integrability is proved, rather than relying on the totalized value of a Lean
  integral for a nonintegrable function.
    - L53 `theorem YMReview.WardAudit.phase_window_independent` -- Two
  admissible windows give the same charge, with the state and fields held fixed.
- `checks/YangMills/OSRecon/Growth.lean` (152L, 5 decls, [noncomp/Classical,
Real/Complex]) imports: YangMills.OSRecon.Vendored.Axioms
    - L49 `structure OSLinearGrowthCondition'` -- (E0'), OS II eq. (4.1).** `S₀
  = 1` and `‖S_n(f)‖ ≤ α (n!)^β · ‖f‖_{n·s}`, with the Schwartz norm of order
  `n·s`.
    - L65 `structure OSProductGrowthCondition` -- (E0''), OS II eq. (4.2).** On
  product test functions `f₁ ⊗ ⋯ ⊗ f_n`, `‖S_n(f₁ ⊗ ⋯ ⊗ f_n)‖ ≤ α (n!)^β ∏
  ‖f_i‖_s` with a fixed order `s`.
    - L93 `structure OSArityLinearGrowthCondition` --
  `OSArityLinearGrowthCondition`**, the corrected upstream growth condition,
  verbatim in its field list: `S₀(f) = f(0)`, and `‖Sₙ(f)‖ ≤ α βⁿ (n!)^γ ·
  P_{n,s}(f...
    - L112 `def OSLinearGrowthCondition'.toArity` -- OS II (4.1) is the upstream
  form with `β = 1`.
    - L124 `def OSArityLinearGrowthCondition.toLinearGrowth'` -- The upstream
  form is OS II (4.1) with `α ↦ α e^β` and `γ ↦ γ + 1`, since `βⁿ ≤ e^β n!`.
- `checks/YangMills/OSRecon/Vendored/Axioms.lean` (224L, 6 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.OSConj
    - L46 `def OSInnerProduct`
    - L57 `def OSTensorAdmissible` -- The genuine zero-diagonal compatibility
  condition for the OS tensor terms appearing in `OSInnerProduct`. This is the
  precise hypothesis needed for additive m...
    - L63 `theorem
  OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion` -- Ordered
  positive-time topological support is enough to guarantee that every OS tensor
  term of two Borchers sequences already lies in `°S`.
    - L92 `structure OsterwalderSchraderAxioms` -- The Osterwalder-Schrader
  axioms E0-E4 for Euclidean field theory. From OS I (1973): - E0: Temperedness
  (Sₙ ∈ S'(ℝ^{dn})) - E1: Euclidean invariance - E2: Ref...
    - L179 `def OsterwalderSchraderAxioms.schwingerCLM` -- The Schwinger
  functional packaged as a continuous linear map on the honest zero-diagonal
  test space.
  - ... (1 more decls in `LEAN_TOC.json`)
- `checks/YangMills/OSRecon/Vendored/OSConj.lean` (302L, 10 decls,
[noncomp/Classical, Real/Complex]) imports:
YangMills.OSRecon.Vendored.TensorProduct,
YangMills.OSRecon.Vendored.ZeroDiagonal
    - L39 `structure BorchersSequence` -- A Borchers sequence: a finite sequence
  of test functions, one for each n. The `funcs` field is indexed by all n ∈ ℕ,
  with `bound_spec` ensuring all component...
    - L57 `def SchwartzNPoint.timeReflect` -- Time reflection on n-point
  Schwartz functions. (θf)(x₁,...,xₙ) = f(θx₁,...,θxₙ) where θ(τ,x⃗) = (-τ,x⃗).
  This is the correct involution for the Osterwalder-S...
    - L86 `theorem SchwartzNPoint.timeReflect_apply`
    - L91 `theorem SchwartzNPoint.timeReflect_timeReflect` -- Time reflection is
  an involution on Schwartz functions.
    - L97 `theorem SchwartzNPoint.seminorm_timeReflect_le` -- Time reflection
  does not increase Schwartz seminorms.
  - ... (5 more decls in `LEAN_TOC.json`)
- `checks/YangMills/OSRecon/Vendored/Spacetime.lean` (354L, 35 decls,
[noncomp/Classical, Real/Complex]) imports:
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.MeasureTheory.Constructions.Pi,
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
    - L57 `abbrev SpacetimeDim` -- The spacetime dimension type for Schwartz
  functions. For d spatial dimensions, spacetime is ℝ^{d+1}.
    - L60 `abbrev SchwartzSpacetime` -- Schwartz space on d+1 dimensional
  spacetime with complex values
    - L63 `abbrev NPointDomain` -- The space of n copies of spacetime for
  n-point functions
    - L66 `abbrev SchwartzNPoint` -- Schwartz space on n copies of spacetime
    - L76 `def splitFirst` -- The splitting map: given x : Fin (m+k) → E,
  extract the first m components. This sends x to (x₁, ..., xₘ).
  - ... (30 more decls in `LEAN_TOC.json`)
- `checks/YangMills/OSRecon/Vendored/TensorProduct.lean` (238L, 6 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.Spacetime
    - L41 `def SchwartzMap.conj` -- Complex conjugation of a ℂ-valued Schwartz
  function. If f ∈ S(E, ℂ), then f̄ ∈ S(E, ℂ) where f̄(x) = conj(f(x)). This is
  well-defined because: 1. conj : ℂ →...
    - L59 `theorem SchwartzMap.conj_apply` -- Conjugation preserves the
  pointwise values.
    - L63 `theorem SchwartzMap.conj_conj` -- Conjugation is an involution.
    - L69 `theorem SchwartzMap.seminorm_conj_le` -- Complex conjugation does not
  increase Schwartz seminorms.
    - L92 `def SchwartzMap.tensorProduct` -- The external tensor product of two
  Schwartz functions. Given f ∈ S(Fin m → E, ℂ) and g ∈ S(Fin k → E, ℂ), define:
  (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(...
  - ... (1 more decls in `LEAN_TOC.json`)
- `checks/YangMills/OSRecon/Vendored/ZeroDiagonal.lean` (281L, 28 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.Spacetime
    - L44 `def PositiveTimeRegion` -- The positive Euclidean time region:
  n-point configurations with all τᵢ > 0.
    - L51 `def OrderedPositiveTimeRegion` -- The OS-I ordered positive-time
  region: `0 < x₁⁰ < ... < xₙ⁰`. This is the support surface used in the
  positivity axiom `E2`, matching the test-function space...
    - L55 `def OrderedNegativeTimeRegion` -- The time-reflected ordered region:
  all times are negative and strictly decrease.
    - L58 `theorem OrderedPositiveTimeRegion_subset_positiveTimeRegion`
    - L64 `def CoincidenceLocus` -- The coincidence locus where at least two
  Euclidean arguments coincide.
  - ... (23 more decls in `LEAN_TOC.json`)
- `docs/examples/CommonOPE-20261028.lean` (174L, 7 decls, [noncomp/Classical,
Real/Complex]) imports: OPECheck
    - L37 `theorem YMReview.Examples.CommonOPE.explicit_radius_from_source`
    - L55 `theorem YMReview.Examples.CommonOPE.coefficient_bound`
    - L79 `theorem YMReview.Examples.CommonOPE.remainder_uniform_in_state`
    - L99 `theorem YMReview.Examples.CommonOPE.difference_of_states`
    - L128 `theorem YMReview.Examples.CommonOPE.channel_assembly`
  - ... (2 more decls in `LEAN_TOC.json`)
- `docs/examples/LatticeAndScale-20261028.lean` (180L, 11 decls,
[noncomp/Classical, Real/Complex]) imports: CombinedAcceptance
    - L35 `theorem YMReview.Examples.LatticeAndScale.same_plaquette`
    - L55 `theorem YMReview.Examples.LatticeAndScale.coupling_conversion`
    - L63 `theorem
  YMReview.Examples.LatticeAndScale.normalized_law_on_each_lattice`
    - L70 `theorem
  YMReview.Examples.LatticeAndScale.finite_moments_are_the_family_moments`
    - L90 `theorem YMReview.Examples.LatticeAndScale.reference_unit`
  - ... (6 more decls in `LEAN_TOC.json`)
- `docs/examples/LeadingTrace-20261028.lean` (357L, 12 decls,
[noncomp/Classical, Real/Complex]) imports: CombinedAcceptance, OctoberChain
    - L58 `theorem YMReview.Examples.LeadingTrace.selected_state_is_fixed`
    - L61 `theorem YMReview.Examples.LeadingTrace.centering_uses_the_phase_mean`
    - L66 `theorem YMReview.Examples.LeadingTrace.centered_one_point`
    - L88 `theorem YMReview.Examples.LeadingTrace.two_point_is_selected_kernel`
    - L93 `theorem YMReview.Examples.LeadingTrace.separated_kernel_is_real`
  - ... (7 more decls in `LEAN_TOC.json`)
- `docs/examples/OSAxioms-20261028.lean` (180L, 9 decls, [noncomp/Classical,
Real/Complex]) imports: CombinedAcceptance
    - L44 `theorem
  YMReview.Examples.OSAxioms.kernel_is_the_selected_correlation`
    - L64 `theorem YMReview.Examples.OSAxioms.separated_bound`
    - L71 `theorem YMReview.Examples.OSAxioms.pairing_is_integrable`
    - L76 `theorem YMReview.Examples.OSAxioms.pairing_is_the_selected_integral`
    - L81 `theorem YMReview.Examples.OSAxioms.E0_continuity`
  - ... (4 more decls in `LEAN_TOC.json`)
- `docs/examples/OctoberChain.lean` (298L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: AcceptanceSpec
    - L78 `def YMReview.Chain.bareCoefficients` -- Undo the terminal
  renormalization and the nonzero diagonal threshold scaling. This is an
  equivalence on raw coefficient space at each cutoff.
    - L92 `theorem YMReview.Chain.actual_insertion_formula`
    - L113 `theorem YMReview.Chain.every_primary_is_represented` -- Every placed
  primary section is represented by an actual renormalized insertion, up to the
  common engineering factor. No coefficient direction is discarded b...
    - L130 `theorem YMReview.Chain.nonconstant_primary_survives` -- Nonconstant
  primary observables cannot all become constants merely by the terminal
  renormalization. This is a finite-cutoff statement.
    - L172 `theorem YMReview.Chain.every_field_word_has_lattice_origin` --
  Quotient fields have fixed raw representatives, and their entire mean
  correlation functions are limits of those representatives' lattice moments.
  - ... (3 more decls in `LEAN_TOC.json`)
- `docs/examples/OperatorContent-20261028.lean` (153L, 7 decls,
[noncomp/Classical, Real/Complex]) imports: CompletenessAudit
    - L41 `theorem
  YMReview.Examples.OperatorContent.every_registered_polynomial_appears`
    - L56 `theorem YMReview.Examples.OperatorContent.free_sector_dictionary`
    - L62 `theorem YMReview.Examples.OperatorContent.free_residual_vanishes`
    - L89 `theorem
  YMReview.Examples.OperatorContent.interacting_field_dictionary`
    - L103 `theorem
  YMReview.Examples.OperatorContent.each_phase_retains_the_dictionary`
  - ... (2 more decls in `LEAN_TOC.json`)
- `docs/examples/TranslationWard-20261028.lean` (129L, 4 decls,
[noncomp/Classical, Real/Complex]) imports: WardFormulationAudit
    - L40 `theorem YMReview.Examples.TranslationWard.admissible_shell_exists`
    - L64 `theorem
  YMReview.Examples.TranslationWard.tensor_generates_translations`
    - L85 `theorem
  YMReview.Examples.TranslationWard.shell_integrand_is_integrable`
    - L102 `theorem
  YMReview.Examples.TranslationWard.shell_charge_is_window_independent`
- `provenance/af/YangMills/Core/GaugeGroup.lean` (140L, 7 decls,
[noncomp/Classical, Real/Complex]) imports:
Mathlib.Analysis.SpecialFunctions.Pow.Real
    - L52 `structure GaugeGroupData` -- The Lie-algebra invariants of a compact
  simple gauge group that appear in the statement of the Yang-Mills existence
  and mass gap problem: the dimension of th...
    - L85 `def GaugeGroupData.betaZero` -- The one-loop beta-function
  coefficient `b₀ = (11/3) C₂(adj)`, in the convention `μ dg/dμ = − b₀
  g³/(16π²)`. Its positivity — asymptotic freedom of perturbati...
    - L88 `theorem GaugeGroupData.betaZero_pos`
    - L96 `def GaugeGroupData.betaOne` -- The two-loop beta-function coefficient
  `b₁ = (34/3) C₂(adj)²`, in the convention `μ dg/dμ = − b₀ g³/(16π²) − b₁
  g⁵/(16π²)²`. For `SU(3)`: `b₁ = 102`.
    - L99 `theorem GaugeGroupData.betaOne_pos`
  - ... (2 more decls in `LEAN_TOC.json`)
- `provenance/af/YangMills/Core/ShortDistance.lean` (304L, 15 decls,
[noncomp/Classical, Real/Complex]) imports: OSforGFF.Schwinger.TwoPoint,
YangMills.Core.GaugeGroup
    - L68 `def uvLog` -- The asymptotic-freedom logarithm `ℓ(x) =
  log(1/(Λ‖x‖))`, positive for `‖x‖ < 1/Λ` and `→ ∞` as `x → 0`. `1/ℓ(x)` is (up
  to the constant `16π²/(2b₀)`) the run...
    - L81 `def freeTraceTwoPoint` -- Leading amplitude of the trace-channel
  two-point function per gluon: `⟨Θ(x)Θ(0)⟩ ~ dimG · freeTraceTwoPoint · ‖x‖⁻⁸
  ℓ⁻²`, where `Θ = T^μ_μ`. Derivation: the...
    - L83 `theorem freeTraceTwoPoint_pos`
    - L92 `def KernelUVPowerLaw` -- Kernel-parametric leading short-distance
  criterion: `K(x) · ‖x‖⁸ · ℓ(x)² → A` for some `A > 0`, `Λ > 0`. The v4 primary
  form — the argument is any two-point...
    - L102 `def UVPowerLaw` -- Leading short-distance behavior of an
  asymptotically free `tr F²` channel, measure form (delegates to the
  kernel-parametric criterion).
  - ... (10 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/Bridge/ScaleTransfer.lean` (534L, 18 decls,
[noncomp/Classical, Real/Complex]) imports:
Mathlib.Analysis.SpecialFunctions.Log.Basic,
Mathlib.Analysis.SpecialFunctions.Pow.Real, Mathlib.Algebra.Order.Field.Basic,
Mathlib.Order.Filter.Basic (+1)
    - L80 `lemma pow_le_pow_of_le_div` -- Monotonicity of exponential decay: if
  `d1 >= d2` and `0 < alpha < 1`, then `alpha^d1 <= alpha^d2`. Stated for
  natural number exponents with the division `d_f...
    - L96 `theorem correlation_decay_transfer_gen` -- Abstract correlation decay
  transfer (general overhead).** If fine-lattice covariance is bounded by
  blocked covariance, blocked covariance decays exponentiall...
    - L138 `theorem correlation_decay_transfer` -- Abstract correlation decay
  transfer.** Special case of `correlation_decay_transfer_gen` with `overhead =
  1`. If `d_fine <= scale * d_coarse + scale`, then `d...
    - L169 `theorem correlation_decay_transfer_exp` -- Correlation decay
  transfer with explicit rate.** Variant of `correlation_decay_transfer` that
  makes the decay rate explicit. If the coarse lattice has mass g...
    - L196 `theorem mass_gap_rate_rescaled` -- Rescaled mass gap rate.** If
  `alpha = exp(-m_eff)` and `|cov| <= C' * alpha^(d/scale)`, then the effective
  fine-lattice mass gap rate is `m_eff / scale`.
  - ... (13 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/GaugeField/Connection.lean` (74L, 8 decls, [PURE])
imports: LGT.Lattice.CellComplex
    - L31 `def GaugeConnection` -- A gauge connection on the symmetric torus:
  G-valued function on links.
    - L34 `def AsymGaugeConnection` -- A gauge connection on the asymmetric 2D
  lattice.
    - L40 `def plaquetteHolonomy` -- Holonomy around a plaquette on the
  symmetric torus: U_p = U(l₁) · U(l₂) · U(l₃)⁻¹ · U(l₄)⁻¹.
    - L45 `def asymPlaquetteHolonomy` -- Holonomy around a 2D plaquette on the
  asymmetric lattice.
    - L53 `def GaugeTransform` -- A gauge transformation on the symmetric torus:
  G-valued function on sites.
  - ... (3 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/GaugeField/GaugeGroup.lean` (31L, 4 decls, [Real/Complex])
imports: Mathlib.LinearAlgebra.Matrix.Trace, Mathlib.Data.Complex.Basic
    - L18 `class HasGaugeTrace` -- A matrix representation for the gauge group.
    - L22 `def gaugeTrace` -- Complex trace of a group element in the gauge
  representation.
    - L26 `def gaugeReTr` -- Real part of the trace.
    - L30 `def wilsonPlaquetteCost` -- Wilson action integrand: Re Tr(I - U_p) =
  n - Re Tr(U_p).
- `provenance/lgt/LGT/GaugeField/Holonomy.lean` (1L, 0 decls, [PURE]) imports:
(none)
- `provenance/lgt/LGT/GaugeField/UnitaryGroup.lean` (223L, 17 decls,
[noncomp/Classical, Real/Complex]) imports: LGT.GaugeField.GaugeGroup,
LGT.MassGap.YMMeasure, Mathlib.LinearAlgebra.UnitaryGroup,
Mathlib.Analysis.Complex.Basic (+7)
    - L42 `def unitaryGroupIncl` -- The inclusion `U(n) → M_n(ℂ)` as a monoid
  homomorphism.
    - L47 `instance instHasGaugeTraceUnitaryGroup`
    - L58 `lemma unitaryGroup_entry_normSq_le` -- Every entry of a unitary
  matrix has norm-squared at most 1.
    - L82 `lemma unitaryGroup_entry_norm_le` -- Every entry of a unitary matrix
  has norm at most 1.
    - L92 `theorem unitaryGroup_gaugeReTr_le` -- `gaugeReTr G n g ≤ n` for the
  unitary group.
  - ... (12 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/Gibbs/YMIsGibbs.lean` (961L, 11 decls, [noncomp/Classical,
Real/Complex]) imports: LGT.MassGap.YMMeasure, LGT.Gibbs.YMSpec,
MarkovSemigroups.Dobrushin.Specification
    - L71 `theorem gibbsConditionalZ_eq_of_agrees_outside` -- The conditional
  partition function depends only on the boundary `σ|_{Λᶜ}`. If `σ` and `τ`
  agree outside `Λ`, then `gibbsConditionalZ Λ σ = gibbsConditionalZ...
    - L109 `theorem glue_measurePreserving` -- The pushforward of `productHaar ×
  productHaar` under `(uΛ, σ) ↦ gluedConfig Λ uΛ σ` is `productHaar`. Proven
  directly via `Measure.pi_eq`: the preimage of a...
    - L198 `theorem integral_glue_split_eq` -- Reduces the double integral
  through `glue` to a single integral over `productHaar`, given
  `glue_measurePreserving`. Uses `integral_map` for change-of-variabl...
    - L266 `theorem partitionFn_eq_integral_gibbsConditionalZ` -- Key
  identity.** The integral of the Boltzmann weight equals `∫ σ Z(σ) dHaar(σ)`,
  the σ-average of the conditional partition function. ### Proof sketch
  (Fubin...
    - L289 `theorem integral_smul_condZ_eq_integral_smul_w` -- Identity A.** For
  any observable `h` that depends on `σ` only through `σ|_Λᶜ`: ``` ∫ σ h(σ) ·
  Z_Λ(σ) ∂productHaar = ∫ U h(U) · w(U) ∂productHaar ``` Direct c...
  - ... (6 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/Gibbs/YMSpec.lean` (458L, 13 decls, [noncomp/Classical,
Real/Complex]) imports: LGT.MassGap.YMMeasure, LGT.WilsonAction.GaugeInvariance,
MarkovSemigroups.Dobrushin.Specification
    - L61 `def gluedConfig` -- Glue a Λ-config and a boundary σ into a full
  config.
    - L67 `theorem gluedConfig_eq_outside` -- The glued config agrees with σ
  outside Λ.
    - L74 `theorem gluedConfig_eq_inside` -- The glued config equals uΛ on Λ.
    - L84 `theorem measurable_gluedConfig` -- The gluing map `uΛ ↦ gluedConfig Λ
  uΛ σ` is measurable. On the product measurable space, the map is the pointwise
  if-then-else between a (measurable) project...
    - L113 `def gibbsConditionalWeight` -- The conditional Boltzmann weight for
  a Λ-config given boundary σ. This is exp(-S(U)) where U = glue(uΛ, σ).
  - ... (8 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/Lattice/CellComplex.lean` (803L, 39 decls,
[noncomp/Classical]) imports: Lattice.Sites, Torus.AsymmetricTorus
    - L27 `structure LatticeLink` -- A link (oriented 1-cell): site + direction.
    - L33 `def siteShift` -- Shift a site by +1 in direction μ.
    - L38 `theorem siteShift_comm` -- Shifts in different directions commute.
    - L45 `def LatticeLink.target` -- Target of a link.
    - L50 `structure LatticePlaquette` -- A plaquette (oriented 2-cell): site +
  two ordered directions.
  - ... (34 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/MassGap/StrongCoupling.lean` (2232L, 58 decls,
[noncomp/Classical, Real/Complex]) imports: LGT.MassGap.MassGap3D,
LGT.Lattice.LatticeDistance, LGT.GaugeField.UnitaryGroup,
Mathlib.Topology.Algebra.Star.Unitary (+1)
    - L66 `instance instTopologicalSpaceGaugeConnection`
    - L69 `instance instBorelSpaceGaugeConnection`
    - L80 `instance instFirstCountableGaugeConnection`
    - L96 `theorem continuous_evalLink` -- Link evaluation is continuous in the
  product topology.
    - L102 `theorem continuous_gaugeReTr` -- gaugeReTr is continuous when the
  representation is continuous.
  - ... (53 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/MassGap/YMMeasure.lean` (349L, 25 decls,
[noncomp/Classical, Real/Complex]) imports: LGT.Lattice.LatticeDistance,
LGT.GaugeField.Connection, LGT.GaugeField.GaugeGroup, LGT.MassGap.Integrability
(+3)
    - L48 `instance instMeasurableSpaceGaugeConnection`
    - L57 `class HasHaarProbability` -- Normalized Haar probability measure on a
  compact group G. Every compact group admits a unique bi-invariant probability
  measure. Mathlib provides this via `ha...
    - L66 `def haarG` -- The Haar probability measure on G.
    - L68 `instance <anonymous_instance>`
    - L76 `def productHaar` -- The product Haar measure on gauge configurations
  G^{links}.
  - ... (20 more decls in `LEAN_TOC.json`)
- `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean` (1L, 0 decls, [PURE])
imports: (none)
- `provenance/osreconstruction/Specification.lean` (287L, 17 decls,
[noncomp/Classical, Real/Complex]) imports:
OSReconstruction.Wightman.Reconstruction.Core,
OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIOriginalSeminorm
    - L28 `def OSInnerProduct`
    - L52 `structure OsterwalderSchraderAxioms` -- The Osterwalder-Schrader
  axioms E0-E4 for Euclidean field theory. From OS I (1973): - E0: Temperedness
  (Sₙ ∈ S'(ℝ^{dn})) - E1: Euclidean invariance - E2: Ref...
    - L141 `def OSReconstruction.osArityLinearSchwartzSeminorm` -- The OS-II
  source seminorm retains every weight/derivative pair through the arity-linear
  bound, including `(0, 0)` at arity zero.
    - L149 `structure OSReconstruction.OSArityLinearGrowthCondition` -- The
  genuine OS-II growth hypothesis on the original zero-diagonal Euclidean test
  space. Its defining Schwartz orders grow linearly in arity; the coefficient...
    - L166 `abbrev OSLinearGrowthCondition` -- Public OS-II linear growth is the
  arity-linear condition. The former fixed exact-index condition is not an
  equivalent reconstruction input.
  - ... (12 more decls in `LEAN_TOC.json`)
- `provenance/osreconstruction/Specification/Wightman.lean` (259L, 13 decls,
[noncomp/Classical, Real/Complex]) imports:
OSReconstruction.Wightman.SpectralCondition,
OSReconstruction.Wightman.SchwartzTensorProduct
    - L26 `abbrev NPointDomain` -- The space of n copies of spacetime for
  n-point functions
    - L29 `abbrev SchwartzNPoint` -- Schwartz space on n copies of spacetime
    - L39 `def IsTranslationInvariantWeak` -- Translation invariance: W_n(x₁+a,
  ..., xₙ+a) = W_n(x₁, ..., xₙ) for all translations a. At the distribution
  level: W_n(τ_{-a} f) = W_n(f) where (τ_a f)(x) =...
    - L57 `def IsLorentzCovariantWeak` -- Lorentz covariance: W_n(Λx₁, ..., Λxₙ)
  = W_n(x₁, ..., xₙ) for all Λ in the connected Lorentz group SO⁺(1,d). For
  scalar fields, the Wightman functions are Lo...
    - L81 `def IsAdjacentLocallyCommutativeWeak` -- Adjacent local commutativity
  condition for Wightman functions. For a collection of n-point functions W_n,
  local commutativity means: When adjacent points x_i...
  - ... (8 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/Analysis/DiagonalFlatBounds.lean` (370L, 15
decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.Analysis.DifferentiatedKernels,
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Normed.Module.Convex
    - L19 `theorem YangMills.Analysis.norm_le_pow_mul_of_iteratedFDeriv_eq_zero`
  -- An arbitrary-order Taylor bound with a coarse constant independent of the
  order. The first `N` derivatives vanish at the base point. No compactness or
  scalar...
    - L56 `theorem YangMills.Analysis.one_add_norm_le_of_mem_segment` --
  Schwartz decay weights are comparable along every segment of length at most
  one.
    - L69 `theorem
  YangMills.Analysis.weighted_norm_le_pow_mul_sup_seminorm_of_flat` -- A
  directed Schwartz-seminorm Taylor estimate. The uniform constant is explicit
  and grows only exponentially in the weight and derivative rectangle orders.
    - L109 `theorem YangMills.Analysis.norm_sub_update_eq` -- Moving one
  coordinate to an affine coincidence locus costs exactly the corresponding
  affine separation in the joint maximum norm.
    - L125 `def YangMills.Analysis.affineCoincidenceSeparation` -- The minimum
  of one and a finite family's affine pair separations. Empty families have
  separation one. Arbitrary shifts include both ordinary and translated c...
  - ... (10 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/Analysis/DifferentiatedKernels.lean` (485L,
30 decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.Analysis.SchwartzSeminorms,
Mathlib.Analysis.SpecialFunctions.JapaneseBracket,
Mathlib.MeasureTheory.Integral.Pi, Mathlib.MeasureTheory.Group.Prod (+1)
    - L17 `def EuclideanField.pairCoordinates` -- Independent relative and
  center coordinates for a collection of pairs. The second endpoint of each pair
  is the center itself.
    - L20 `lemma EuclideanField.pairCoordinates_left`
    - L24 `lemma EuclideanField.pairCoordinates_right`
    - L28 `lemma EuclideanField.norm_center_le_pairCoordinates`
    - L32 `lemma EuclideanField.continuous_pairCoordinates`
  - ... (25 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/Analysis/SchwartzExternalProduct.lean` (275L,
27 decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.Analysis.SchwartzKernels, Mathlib.Tactic.GCongr
    - L15 `def SchwartzMap.productSeminorm` -- Finite Schwartz seminorm envelope
  used for the external-product estimate.
    - L19 `theorem SchwartzMap.continuous_productSeminorm`
    - L24 `theorem SchwartzMap.seminorm_le_productSeminorm`
    - L37 `theorem SchwartzMap.norm_iteratedFDeriv_comp_contract`
    - L51 `theorem SchwartzMap.weighted_derivative_externalProduct_le`
  - ... (22 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/Analysis/SchwartzKernels.lean` (354L, 25
decls, [noncomp/Classical, Real/Complex]) imports:
GeneralResults.NuclearExtensionComplex, Mathlib.Analysis.InnerProductSpace.PiL2
    - L13 `abbrev EuclideanField.RealTest` -- Finite scalar component tests with
  the product Schwartz topology.
    - L15 `abbrev EuclideanField.ComplexTest`
    - L18 `abbrev EuclideanField.JointTest` -- Degree `n` joint kernels, indexed
  by words of component labels.
    - L26 `def SchwartzMap.complexDomCongr` -- A domain equivalence acts
  continuously and complex linearly by pullback.
    - L40 `theorem SchwartzMap.complexDomCongr_apply`
  - ... (20 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/Analysis/SchwartzSupportedDensity.lean`
(862L, 36 decls, [noncomp/Classical, Real/Complex]) imports:
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension,
Mathlib.Topology.Sequences, YangMills.Analysis.SchwartzKernels
    - L25 `theorem SchwartzMap.norm_iteratedFDeriv_dilate_le`
    - L46 `theorem SchwartzMap.norm_iteratedFDeriv_dilate_sub_one_le`
    - L59 `theorem SchwartzMap.weighted_derivative_le_inv_mul_seminorm`
    - L68 `theorem SchwartzMap.dilate_hasTemperateGrowth`
    - L75 `theorem SchwartzMap.seminorm_dilateCutoff_sub_le` -- Every weighted
  derivative of a cutoff error is controlled by one additional Schwartz decay
  weight. The cutoff derivative constants do not depend on R.
  - ... (31 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Growth.lean` (152L, 5 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.Axioms
    - L49 `structure OSLinearGrowthCondition'` -- (E0'), OS II eq. (4.1).** `S₀
  = 1` and `‖S_n(f)‖ ≤ α (n!)^β · ‖f‖_{n·s}`, with the Schwartz norm of order
  `n·s`.
    - L65 `structure OSProductGrowthCondition` -- (E0''), OS II eq. (4.2).** On
  product test functions `f₁ ⊗ ⋯ ⊗ f_n`, `‖S_n(f₁ ⊗ ⋯ ⊗ f_n)‖ ≤ α (n!)^β ∏
  ‖f_i‖_s` with a fixed order `s`.
    - L93 `structure OSArityLinearGrowthCondition` --
  `OSArityLinearGrowthCondition`**, the corrected upstream growth condition,
  verbatim in its field list: `S₀(f) = f(0)`, and `‖Sₙ(f)‖ ≤ α βⁿ (n!)^γ ·
  P_{n,s}(f...
    - L112 `def OSLinearGrowthCondition'.toArity` -- OS II (4.1) is the upstream
  form with `β = 1`.
    - L124 `def OSArityLinearGrowthCondition.toLinearGrowth'` -- The upstream
  form is OS II (4.1) with `α ↦ α e^β` and `γ ↦ γ + 1`, since `βⁿ ≤ e^β n!`.
- `provenance/yang-mills/YangMills/OSRecon/ReflectionApproximation.lean` (190L,
8 decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.OSRecon.CoordinateTransport,
YangMills.Analysis.SchwartzSupportedDensity,
YangMills.Analysis.SchwartzExternalProduct
    - L12 `theorem SchwartzMap.exists_compactCutoff_sequence_tsupport_subset` --
  Compact approximation that retains the original topological support.
    - L39 `theorem YangMills.OSRecon.exists_compact_ordered_sequence`
    - L52 `theorem YangMills.OSRecon.continuous_source_tensorProduct`
    - L63 `theorem YangMills.OSRecon.continuous_source_osConj`
    - L89 `theorem YangMills.OSRecon.continuous_source_osConjTensorProduct`
  - ... (3 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/Axioms.lean` (224L, 6 decls,
[noncomp/Classical, Real/Complex]) imports: YangMills.OSRecon.Vendored.OSConj
    - L46 `def OSInnerProduct`
    - L57 `def OSTensorAdmissible` -- The genuine zero-diagonal compatibility
  condition for the OS tensor terms appearing in `OSInnerProduct`. This is the
  precise hypothesis needed for additive m...
    - L63 `theorem
  OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion` -- Ordered
  positive-time topological support is enough to guarantee that every OS tensor
  term of two Borchers sequences already lies in `°S`.
    - L92 `structure OsterwalderSchraderAxioms` -- The Osterwalder-Schrader
  axioms E0-E4 for Euclidean field theory. From OS I (1973): - E0: Temperedness
  (Sₙ ∈ S'(ℝ^{dn})) - E1: Euclidean invariance - E2: Ref...
    - L179 `def OsterwalderSchraderAxioms.schwingerCLM` -- The Schwinger
  functional packaged as a continuous linear map on the honest zero-diagonal
  test space.
  - ... (1 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/OSConj.lean` (302L, 10
decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.OSRecon.Vendored.TensorProduct,
YangMills.OSRecon.Vendored.ZeroDiagonal
    - L39 `structure BorchersSequence` -- A Borchers sequence: a finite sequence
  of test functions, one for each n. The `funcs` field is indexed by all n ∈ ℕ,
  with `bound_spec` ensuring all component...
    - L57 `def SchwartzNPoint.timeReflect` -- Time reflection on n-point
  Schwartz functions. (θf)(x₁,...,xₙ) = f(θx₁,...,θxₙ) where θ(τ,x⃗) = (-τ,x⃗).
  This is the correct involution for the Osterwalder-S...
    - L86 `theorem SchwartzNPoint.timeReflect_apply`
    - L91 `theorem SchwartzNPoint.timeReflect_timeReflect` -- Time reflection is
  an involution on Schwartz functions.
    - L97 `theorem SchwartzNPoint.seminorm_timeReflect_le` -- Time reflection
  does not increase Schwartz seminorms.
  - ... (5 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/Spacetime.lean` (354L, 35
decls, [noncomp/Classical, Real/Complex]) imports:
Mathlib.Analysis.Distribution.SchwartzSpace.Deriv,
Mathlib.MeasureTheory.Constructions.Pi,
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
    - L57 `abbrev SpacetimeDim` -- The spacetime dimension type for Schwartz
  functions. For d spatial dimensions, spacetime is ℝ^{d+1}.
    - L60 `abbrev SchwartzSpacetime` -- Schwartz space on d+1 dimensional
  spacetime with complex values
    - L63 `abbrev NPointDomain` -- The space of n copies of spacetime for
  n-point functions
    - L66 `abbrev SchwartzNPoint` -- Schwartz space on n copies of spacetime
    - L76 `def splitFirst` -- The splitting map: given x : Fin (m+k) → E,
  extract the first m components. This sends x to (x₁, ..., xₘ).
  - ... (30 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/TensorProduct.lean` (238L, 6
decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.OSRecon.Vendored.Spacetime
    - L41 `def SchwartzMap.conj` -- Complex conjugation of a ℂ-valued Schwartz
  function. If f ∈ S(E, ℂ), then f̄ ∈ S(E, ℂ) where f̄(x) = conj(f(x)). This is
  well-defined because: 1. conj : ℂ →...
    - L59 `theorem SchwartzMap.conj_apply` -- Conjugation preserves the
  pointwise values.
    - L63 `theorem SchwartzMap.conj_conj` -- Conjugation is an involution.
    - L69 `theorem SchwartzMap.seminorm_conj_le` -- Complex conjugation does not
  increase Schwartz seminorms.
    - L92 `def SchwartzMap.tensorProduct` -- The external tensor product of two
  Schwartz functions. Given f ∈ S(Fin m → E, ℂ) and g ∈ S(Fin k → E, ℂ), define:
  (f ⊗ g)(x₁,...,x_{m+k}) = f(x₁,...,xₘ) · g(...
  - ... (1 more decls in `LEAN_TOC.json`)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/ZeroDiagonal.lean` (279L, 28
decls, [noncomp/Classical, Real/Complex]) imports:
YangMills.OSRecon.Vendored.Spacetime
    - L42 `def PositiveTimeRegion` -- The positive Euclidean time region:
  n-point configurations with all τᵢ > 0.
    - L49 `def OrderedPositiveTimeRegion` -- The OS-I ordered positive-time
  region: `0 < x₁⁰ < ... < xₙ⁰`. This is the support surface used in the
  positivity axiom `E2`, matching the test-function space...
    - L53 `def OrderedNegativeTimeRegion` -- The time-reflected ordered region:
  all times are negative and strictly decrease.
    - L56 `theorem OrderedPositiveTimeRegion_subset_positiveTimeRegion`
    - L62 `def CoincidenceLocus` -- The coincidence locus where at least two
  Euclidean arguments coincide.
  - ... (23 more decls in `LEAN_TOC.json`)
- `submission/Challenge.lean` (6L, 1 decls, [SORRY]) imports: ChallengeSpec
    - L5 `theorem YangMills.jointExistence`
- `submission/ChallengeSpec.lean` (190L, 27 decls, [noncomp/Classical,
Real/Complex]) imports: PublicWilson
    - L12 `structure YangMills.WilsonRegularity` -- A fixed finite lattice
  stencil for each insertion works at every spacing and volume.
    - L24 `structure YangMills.Hierarchy`
    - L55 `abbrev YangMills.Hierarchy.Tag`
    - L58 `def YangMills.Hierarchy.grouped` -- Enumerate the union of the
  insertion and spectator slots once, then read the hierarchy.
    - L63 `def YangMills.Hierarchy.weight`
  - ... (22 more decls in `LEAN_TOC.json`)
- `submission/ConcreteSU2.lean` (19L, 3 decls, [noncomp/Classical]) imports:
Solution, YM.Examples.SU2
    - L8 `def YangMills.su2` -- The defining complex two-dimensional
  representation of SU(2).
    - L12 `theorem YangMills.su2Simple`
    - L15 `theorem YangMills.su2Theory` -- Concrete specialization of the public
  challenge.
- `submission/Construction.lean` (42L, 1 decls, [noncomp/Classical,
Real/Complex]) imports: TraceBridge, ContactSpec, ContactBridge,
YM.Nonperturbative.Headlines
    - L15 `theorem YangMills.constructed` -- The penalty is fixed before
  choosing the family. The table, phases, fields, OPE reader and contact devices
  are then chosen once for each refinement.
- `submission/ContactBridge.lean` (50L, 1 decls, [noncomp/Classical,
Real/Complex]) imports: YM.Contacts.Solstice.Result,
YM.Contacts.Transport.Blend, PublicWilson
    - L14 `theorem YangMills.contactDistribution`
- `submission/ContactSpec.lean` (18L, 1 decls, [noncomp/Classical,
Real/Complex]) imports: ChallengeSpec
    - L12 `def YangMills.Hierarchy.Contacts` -- A distribution on the full
  configuration space, including every collision diagonal, whose restriction to
  pairwise separated insertions is the same correlatio...
- `submission/HierarchyBridge.lean` (134L, 6 decls, [noncomp/Classical,
Real/Complex]) imports: ChallengeSpec, PublicView, WilsonBridge,
YM.Nonperturbative.HeadlineSpec (+1)
    - L16 `theorem YangMills.regular`
    - L27 `def YangMills.hierarchy`
    - L44 `theorem YangMills.wilsonLimit`
    - L58 `theorem YangMills.grouped_eq`
    - L68 `theorem YangMills.publicOPE`
  - ... (1 more decls in `LEAN_TOC.json`)
- `submission/PublicTheory.lean` (325L, 37 decls, [noncomp/Classical,
Real/Complex]) imports: Mathlib
    - L20 `abbrev YangMills.UnitaryRepresentation` -- The fixed faithful unitary
  representation used to describe a gauge group.
    - L25 `structure YangMills.GaugeGroup` -- A compact matrix gauge group
  together with its one-parameter Lie algebra. The last field prevents the Lie
  algebra from being arbitrary: it consists exactly o...
    - L39 `def YangMills.GaugeGroup.IsSimple` -- Real simplicity of the Lie
  algebra, including the nonabelian condition.
    - L51 `abbrev YangMills.Axis`
    - L52 `abbrev YangMills.SpaceAxis`
  - ... (32 more decls in `LEAN_TOC.json`)
- `submission/PublicView.lean` (174L, 7 decls, [noncomp/Classical,
Real/Complex]) imports: PublicTheory, YM.Fields.System
    - L14 `def YangMills.stateSpace`
    - L20 `def YangMills.labelsOf`
    - L25 `def YangMills.fieldsOf`
    - L30 `def YangMills.view`
    - L92 `theorem YangMills.vector_eq`
  - ... (2 more decls in `LEAN_TOC.json`)
- `submission/PublicWilson.lean` (92L, 18 decls, [noncomp/Classical,
Real/Complex]) imports: PublicTheory
    - L10 `abbrev YangMills.Points`
    - L11 `abbrev YangMills.Site`
    - L12 `abbrev YangMills.Configuration`
    - L13 `abbrev YangMills.Directions`
    - L16 `instance YangMills.GaugeGroup.<anonymous_instance>`
  - ... (13 more decls in `LEAN_TOC.json`)
- `submission/Solution.lean` (10L, 1 decls, [PURE]) imports: Construction
    - L4 `theorem YangMills.jointExistence` -- The core comparator asks only for
  existence, reconstruction, the OPE and the trace test.
- `submission/TraceBridge.lean` (45L, 6 decls, [noncomp/Classical,
Real/Complex]) imports: HierarchyBridge, YM.TraceExtension.Wick.Refute
    - L14 `def YangMills.nativeMode`
    - L16 `def YangMills.nativeTrack`
    - L17 `def YangMills.nativeTerms`
    - L19 `theorem YangMills.profile_eq`
    - L24 `theorem YangMills.award_eq`
  - ... (1 more decls in `LEAN_TOC.json`)
- `submission/Verify.lean` (89L, 3 decls, [noncomp/Classical]) imports: YM,
Lean, Lean.Replay
    - L12 `def IndependentAudit.projectModule`
    - L15 `def IndependentAudit.standardAxioms`
    - L17 `def IndependentAudit.replayProofs`
- `submission/VerifyJoint.lean` (107L, 3 decls, [noncomp/Classical]) imports:
ConcreteSU2, Lean, Lean.Replay
    - L12 `def IndependentAudit.projectModule`
    - L17 `def IndependentAudit.standardAxioms`
    - L19 `def IndependentAudit.replayProofs`
- `submission/WilsonBridge.lean` (69L, 8 decls, [noncomp/Classical,
Real/Complex]) imports: PublicWilson, YM.Extraction.Limits
    - L10 `def YangMills.GaugeGroup.core`
    - L12 `theorem YangMills.GaugeGroup.coreSimple`
    - L20 `def YangMills.wilsonFamily`
    - L32 `theorem YangMills.energy_eq`
    - L43 `theorem YangMills.law_eq`
  - ... (3 more decls in `LEAN_TOC.json`)
- `submission/YM.lean` (1L, 0 decls, [PURE]) imports:
YM.Nonperturbative.Headlines
- `submission/verification/CompactCheck.lean` (102L, 5 decls,
[noncomp/Classical, Real/Complex]) imports: ChallengeSpec
    - L12 `theorem YangMills.CompactCheck.smallLower`
    - L21 `theorem YangMills.CompactCheck.bounds`
    - L46 `theorem YangMills.CompactCheck.outside`
    - L64 `theorem YangMills.CompactCheck.compactCoefficient`
    - L80 `theorem YangMills.CompactCheck.compactRemainder`
- `submission/verification/Comparator.lean` (35L, 0 decls, [noncomp/Classical,
Real/Complex]) imports: YM, YM.Examples.SU2, Lean
- `submission/verification/Inventory.lean` (28L, 0 decls, [PURE]) imports: YM,
Lean
- `submission/verification/Usage.lean` (66L, 1 decls, [PURE]) imports:
ConcreteSU2, Lean, Lean.DeclarationRange
    - L11 `def auditModule`
- `verification/AcceptanceChallenge.lean` (14L, 1 decls, [SORRY, Real/Complex])
imports: AcceptanceSpec
    - L10 `theorem YMReview.Acceptance.combined_acceptance`
- `verification/OPEChallenge.lean` (14L, 1 decls, [SORRY]) imports: OPESpec
    - L8 `theorem YMReview.OPE.constructed`
- `verification/controls/accept/Challenge.lean` (1L, 1 decls, [SORRY]) imports:
(none)
    - L1 `theorem comparatorSmoke`
- `verification/controls/accept/Solution.lean` (1L, 1 decls, [PURE]) imports:
(none)
    - L1 `theorem comparatorSmoke`
- `verification/controls/definition_mismatch/Challenge.lean` (2L, 2 decls,
[SORRY]) imports: (none)
    - L1 `def reference`
    - L2 `theorem comparatorSmoke`
- `verification/controls/definition_mismatch/Solution.lean` (2L, 2 decls,
[PURE]) imports: (none)
    - L1 `def reference`
    - L2 `theorem comparatorSmoke`
- `verification/controls/forbidden_axiom/Challenge.lean` (1L, 1 decls, [SORRY])
imports: (none)
    - L1 `theorem comparatorSmoke`
- `verification/controls/forbidden_axiom/Solution.lean` (2L, 2 decls, [AXIOM])
imports: (none)
    - L1 `axiom unapproved`
    - L2 `theorem comparatorSmoke`
- `verification/controls/statement_mismatch/Challenge.lean` (1L, 1 decls,
[SORRY]) imports: (none)
    - L1 `theorem comparatorSmoke`
- `verification/controls/statement_mismatch/Solution.lean` (1L, 1 decls, [PURE])
imports: (none)
    - L1 `theorem comparatorSmoke`

## 4. `submission/YM` Subpackage TOC Summary

| Subpkg              | Files | Thm/Lem | Other | Sorry | Pure |
| ------------------- | ----- | ------- | ----- | ----- | ---- |
| (YM-root)           | 3     | 6       | 0     | 0     | 0    |
| Ac                  | 3     | 26      | 21    | 0     | 0    |
| Analysis            | 11    | 79      | 37    | 0     | 0    |
| Analytic            | 3     | 7       | 5     | 0     | 0    |
| AnalyticBridge      | 421   | 3223    | 1788  | 0     | 0    |
| AnalyticNext        | 554   | 3637    | 1908  | 0     | 0    |
| Axis                | 2     | 13      | 15    | 0     | 0    |
| Bid                 | 18    | 29      | 264   | 0     | 0    |
| Boundary            | 1     | 6       | 18    | 0     | 0    |
| Branch              | 9     | 91      | 26    | 0     | 0    |
| CellFourier         | 4     | 49      | 23    | 0     | 0    |
| Cells               | 17    | 126     | 72    | 0     | 0    |
| Climb               | 4     | 11      | 37    | 0     | 0    |
| Compact             | 3     | 26      | 16    | 0     | 0    |
| Complex             | 3     | 43      | 16    | 0     | 0    |
| Contact             | 3     | 30      | 16    | 0     | 0    |
| Contacts            | 75    | 991     | 378   | 0     | 0    |
| Corona              | 4     | 28      | 3     | 0     | 0    |
| Dash                | 7     | 48      | 34    | 0     | 0    |
| Distribution        | 2     | 50      | 25    | 0     | 0    |
| Euclid              | 14    | 129     | 132   | 0     | 0    |
| EveryPhase          | 34    | 315     | 118   | 0     | 0    |
| Examples            | 1     | 14      | 6     | 0     | 0    |
| Extension           | 57    | 388     | 151   | 0     | 0    |
| Exterior            | 3     | 26      | 24    | 0     | 0    |
| Extra               | 232   | 2025    | 1172  | 0     | 0    |
| Extraction          | 22    | 155     | 77    | 0     | 0    |
| Fields              | 7     | 60      | 73    | 0     | 0    |
| Frontier6           | 3     | 65      | 16    | 0     | 0    |
| FullVolume          | 653   | 3104    | 1307  | 0     | 0    |
| Further             | 284   | 1935    | 1288  | 0     | 0    |
| Gauge               | 8     | 118     | 49    | 0     | 0    |
| Ground              | 5     | 57      | 20    | 0     | 0    |
| Heat                | 5     | 47      | 13    | 0     | 0    |
| Hilbert             | 1     | 5       | 7     | 0     | 0    |
| Independent         | 2     | 3       | 2     | 0     | 0    |
| Integration         | 32    | 74      | 50    | 0     | 0    |
| Labels              | 6     | 56      | 47    | 0     | 0    |
| Lane                | 1     | 5       | 4     | 0     | 0    |
| Lattice             | 10    | 141     | 79    | 0     | 3    |
| Laurent             | 4     | 36      | 25    | 0     | 0    |
| LocalH              | 2     | 11      | 7     | 0     | 0    |
| Marker              | 3     | 53      | 28    | 0     | 0    |
| Maxwell             | 9     | 95      | 65    | 0     | 0    |
| MergeProof          | 428   | 1465    | 636   | 0     | 0    |
| Mink                | 4     | 116     | 43    | 0     | 0    |
| MultiNext           | 89    | 475     | 387   | 0     | 0    |
| MultipleContact     | 150   | 780     | 400   | 0     | 0    |
| Next                | 693   | 8509    | 3735  | 0     | 0    |
| Nonperturbative     | 3     | 5       | 6     | 0     | 0    |
| OPE                 | 211   | 1291    | 518   | 0     | 0    |
| OS                  | 8     | 65      | 33    | 0     | 0    |
| Org                 | 4     | 12      | 31    | 0     | 0    |
| Ovens               | 1     | 3       | 22    | 0     | 0    |
| Overlay             | 9     | 38      | 33    | 0     | 0    |
| PCalc               | 4     | 15      | 37    | 0     | 0    |
| PREC                | 6     | 45      | 41    | 0     | 0    |
| Paley               | 4     | 21      | 9     | 0     | 0    |
| Pert                | 115   | 1022    | 526   | 0     | 0    |
| PertExtension       | 33    | 399     | 216   | 0     | 0    |
| Phase               | 6     | 40      | 43    | 0     | 0    |
| PhysicalNext        | 874   | 4532    | 2781  | 0     | 0    |
| Planned             | 197   | 1238    | 834   | 0     | 0    |
| Pressure            | 7     | 43      | 95    | 0     | 0    |
| Price               | 3     | 14      | 15    | 0     | 0    |
| Primitives          | 56    | 469     | 263   | 0     | 0    |
| Progress            | 63    | 368     | 281   | 0     | 0    |
| ProjectorNext       | 66    | 426     | 252   | 0     | 0    |
| ProofPorts          | 18    | 118     | 111   | 0     | 0    |
| Push                | 553   | 4821    | 2506  | 0     | 0    |
| R2I                 | 20    | 168     | 87    | 0     | 0    |
| RG                  | 10    | 98      | 141   | 0     | 0    |
| RG05Readout         | 70    | 357     | 168   | 0     | 0    |
| RG08                | 857   | 6669    | 2846  | 0     | 0    |
| RG12                | 75    | 311     | 140   | 0     | 0    |
| RG17                | 11    | 41      | 6     | 0     | 0    |
| RemainderComparison | 322   | 1630    | 976   | 0     | 0    |
| SNAG                | 5     | 32      | 22    | 0     | 0    |
| SectorNext          | 133   | 965     | 646   | 0     | 0    |
| SectorTools         | 34    | 307     | 109   | 0     | 0    |
| SharpGram           | 27    | 147     | 50    | 0     | 0    |
| Shift               | 8     | 86      | 64    | 0     | 0    |
| Shoot               | 3     | 10      | 17    | 0     | 0    |
| Slice               | 15    | 178     | 169   | 0     | 0    |
| Source              | 6     | 49      | 58    | 0     | 0    |
| Space               | 3     | 51      | 43    | 0     | 0    |
| Spark               | 2     | 6       | 3     | 0     | 0    |
| Spec                | 1     | 0       | 9     | 0     | 0    |
| Spectral            | 2     | 7       | 4     | 0     | 0    |
| Spin                | 6     | 24      | 29    | 0     | 0    |
| TimeKernel          | 2     | 16      | 11    | 0     | 0    |
| Trace               | 16    | 204     | 75    | 0     | 0    |
| Trace2              | 1     | 22      | 7     | 0     | 0    |
| TraceExtension      | 718   | 4107    | 1755  | 0     | 0    |
| Tree                | 2     | 15      | 13    | 0     | 0    |
| UVExt               | 6     | 58      | 13    | 0     | 0    |
| UVExtension         | 509   | 2479    | 1166  | 0     | 7    |
| UVNext              | 96    | 709     | 418   | 0     | 0    |
| Vac                 | 3     | 25      | 10    | 0     | 0    |
| Ward                | 12    | 120     | 48    | 0     | 0    |
| Wilson              | 2     | 25      | 12    | 0     | 0    |
| WilsonBulk          | 161   | 1848    | 678   | 0     | 0    |
| Work                | 169   | 1610    | 350   | 0     | 0    |

<!-- end of file: leanasm/docs/openai-20261028/LEAN_TOC.md -->
