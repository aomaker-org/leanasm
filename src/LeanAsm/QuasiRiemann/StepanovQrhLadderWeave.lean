-- Path: leanasm/src/LeanAsm/QuasiRiemann/StepanovQrhLadderWeave.lean
-- Stepanov Gain-vs.-Cost x Parametric QRH Ladder & Mollifier Variational Weave.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.MollifierVariationalBridge
import LeanAsm.QuasiRiemann.ContractionReflectionBridge

namespace QuasiRiemann

/-!
# Stepanov Gain-vs.-Cost x Parametric QRH Ladder & Mollifier Variational Weave

This module weaves:
1. The constructive Stepanov-style multi-step gain-vs.-cost lift chain
   (`StepanovLiftChainSpec`, `stepanov_lift_chain_accumulated_strict_dominance`,
   `stepanov_lift_chain_net_margin_pos`, `stepanov_lift_chain_composition_bound`)
   from `ContractionReflectionBridge.lean`.
2. The parametric dyadic QRH binary ladder descent (`qrhShortExponent k ↓ 1/2`) and
   Chebyshev gap widening (`chebyshevGap (qrhShortExponent k) ↑ 1/2`) from
   `ParametricQrhLadder.lean`.
3. The two-piece variational mollifier off-diagonal energy contraction
   (`mollifierVariationalEnergy variationalMollifier3414Spec = 13/16 < 1`) from
   `MollifierVariationalBridge.lean`, providing an explicit rational defect witness
   `1 - E_var = 3/16 > 0`.
4. High-order parametric dyadic rungs `k ≥ 5`, including rung `k = 29` (`eGap = 24`,
   `stages = 24`), yielding constructive net positive gain-minus-cost advances,
   non-vanishing effective error envelopes, and guaranteed short-interval primes
   under `[propext, Quot.sound]` with zero `sorryAx`, zero `Classical.choice`,
   and zero Mathlib.
-/

-- =============================================================================
-- 1. Variational Energy Rational Defect Witness
-- =============================================================================

/-- Explicit rational defect witness from the sub-unit variational mollifier energy:
    `energyVariationalDefectWitness = 1 - E_var(3/4, 1/4) = 1 - 13/16 = 3/16`.
    Serves as the non-zero initial budget envelope for the Stepanov lift chain. -/
def energyVariationalDefectWitness : QRat :=
  QRat.ofInt 1 -
    mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2

/-- Exact rational computation of `energyVariationalDefectWitness = 3/16`. -/
theorem energyVariationalDefectWitness_eq :
    QRat.eqv energyVariationalDefectWitness (QRat.mk' 3 16 (by decide)) := by
  decide

/-- Positivity of the rational defect witness numerator: `0 < 3`. -/
theorem energyVariationalDefectWitness_num_pos :
    0 < energyVariationalDefectWitness.num := by
  decide

/-- Constructive non-vanishing of `energyVariationalDefectWitness`. -/
theorem energyVariationalDefectWitness_ne_zero :
    ¬ QRat.eqv energyVariationalDefectWitness (QRat.ofInt 0) := by
  decide

-- =============================================================================
-- 2. Stepanov Rung Weave Specifications across Dyadic Rungs k ≥ 5
-- =============================================================================

/-- Stepanov lift chain specification weaving rung `k = 5` to rung `k = 6` (`stages = 1`).
    Per-step gain is `chebyshevGap(θ(6)) = 63/128`; per-step cost is `chebyshevGap(θ(5)) = 31/64`. -/
def stepanovRungWeaveSpec5_6 : StepanovLiftChainSpec where
  stages := 1
  h_stages_pos := by decide
  initBudget := energyVariationalDefectWitness
  h_init_pos := energyVariationalDefectWitness_num_pos
  gainPerStep := chebyshevGap (qrhShortExponent 6)
  costPerStep := chebyshevGap (qrhShortExponent 5)
  h_gain_pos := by decide
  h_cost_pos := by decide
  h_step_dom := by decide

/-- Stepanov lift chain specification weaving rung `k = 5` to rung `k = 14` (`stages = 9`).
    Per-step gain is `chebyshevGap(θ(14)) = 16383/32768`. -/
def stepanovRungWeaveSpec14 : StepanovLiftChainSpec where
  stages := 9
  h_stages_pos := by decide
  initBudget := energyVariationalDefectWitness
  h_init_pos := energyVariationalDefectWitness_num_pos
  gainPerStep := chebyshevGap (qrhShortExponent 14)
  costPerStep := chebyshevGap (qrhShortExponent 5)
  h_gain_pos := by decide
  h_cost_pos := by decide
  h_step_dom := by decide

/-- Stepanov lift chain specification weaving rung `k = 5` to rung `k = 29` (`stages = 24`, `eGap = 24`).
    Per-step gain is `chebyshevGap(θ(29)) = 536870911/1073741824`. -/
def stepanovRungWeaveSpec29 : StepanovLiftChainSpec where
  stages := 24
  h_stages_pos := by decide
  initBudget := energyVariationalDefectWitness
  h_init_pos := energyVariationalDefectWitness_num_pos
  gainPerStep := chebyshevGap (qrhShortExponent 29)
  costPerStep := chebyshevGap (qrhShortExponent 5)
  h_gain_pos := by decide
  h_cost_pos := by decide
  h_step_dom := by decide

-- =============================================================================
-- 3. Stepanov Ladder Weave Bundle
-- =============================================================================

/-- Bundle pairing a constructive Stepanov lift chain with its dyadic ladder rung
    and guaranteed short-interval prime existence certificate. -/
structure StepanovLadderWeaveBundle (k : Nat) (m : Nat) where
  chain : StepanovLiftChainSpec
  h_stages : chain.stages = m
  rungK : Nat
  h_rung : rungK = k
  shortSpec : ShortIntervalChebyshevSpec
  h_prime : shortSpec.HasGuaranteedPrime

/-- Canonical high-rung Stepanov ladder weave bundle at `k = 29` (`stages = 24`). -/
def stepanovLadderWeaveBundle29 : StepanovLadderWeaveBundle 29 24 where
  chain := stepanovRungWeaveSpec29
  h_stages := rfl
  rungK := 29
  h_rung := rfl
  shortSpec := shortIntervalDyadicRung29Spec
  h_prime := shortIntervalDyadicRung29Spec_has_prime

/-- Certificate for the `k = 29` Stepanov ladder weave bundle establishing strict
    cost-gain dominance, non-vanishing effective cost, and guaranteed prime existence. -/
theorem stepanovLadderWeaveBundle29_certs :
    stepanovLadderWeaveBundle29.chain.accumulatedCost 24 <
      stepanovLadderWeaveBundle29.chain.accumulatedGain 24 ∧
    stepanovLadderWeaveBundle29.chain.effectiveCost 24 <
      stepanovLadderWeaveBundle29.chain.initBudget +
        stepanovLadderWeaveBundle29.chain.accumulatedGain 24 ∧
    0 < (stepanovLadderWeaveBundle29.chain.netMargin 24).num ∧
    (¬ QRat.eqv (stepanovLadderWeaveBundle29.chain.netMargin 24) (QRat.ofInt 0)) ∧
    0 < (stepanovLadderWeaveBundle29.chain.effectiveCost 24).num ∧
    (¬ QRat.eqv (stepanovLadderWeaveBundle29.chain.effectiveCost 24) (QRat.ofInt 0)) ∧
    stepanovLadderWeaveBundle29.shortSpec.HasGuaranteedPrime := by
  have hm : 0 < 24 := by decide
  have h_dom := stepanov_lift_chain_accumulated_strict_dominance
    stepanovLadderWeaveBundle29.chain 24 hm
  have h_comp := stepanov_lift_chain_composition_bound
    stepanovLadderWeaveBundle29.chain 24 hm
  have h_net := stepanov_lift_chain_net_margin_pos
    stepanovLadderWeaveBundle29.chain 24 hm
  exact ⟨h_dom, h_comp.1, h_net.1, h_net.2, h_comp.2.1, h_comp.2.2,
         stepanovLadderWeaveBundle29.h_prime⟩

-- =============================================================================
-- 4. Master Stepanov x Parametric QRH Ladder Weave Theorems
-- =============================================================================

/-- Comprehensive master weave certificate linking the Stepanov gain-vs.-cost lift chain
    with the parametric QRH ladder and variational mollifier bridge across rungs `k = 6, 14, 29`:
    1. Multi-stage strict cost-gain dominance (`accumulatedCost < accumulatedGain`).
    2. Strictly positive and non-vanishing net gain margins.
    3. Variational energy bound `13/16 < 1` and rational defect witness `3/16 > 0`.
    4. Guaranteed short-interval primes at rungs `k = 5, 6, 14, 29`.
    5. Monotone exponent descent and Chebyshev gap widening along the dyadic ladder. -/
theorem stepanov_qrh_ladder_weave_certs :
    -- Rung 6 (stage 1)
    stepanovRungWeaveSpec5_6.accumulatedCost 1 < stepanovRungWeaveSpec5_6.accumulatedGain 1 ∧
    0 < (stepanovRungWeaveSpec5_6.netMargin 1).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec5_6.netMargin 1) (QRat.ofInt 0)) ∧
    -- Rung 14 (stage 9)
    stepanovRungWeaveSpec14.accumulatedCost 9 < stepanovRungWeaveSpec14.accumulatedGain 9 ∧
    0 < (stepanovRungWeaveSpec14.netMargin 9).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec14.netMargin 9) (QRat.ofInt 0)) ∧
    -- Rung 29 (stage 24)
    stepanovRungWeaveSpec29.accumulatedCost 24 < stepanovRungWeaveSpec29.accumulatedGain 24 ∧
    stepanovRungWeaveSpec29.effectiveCost 24 <
      stepanovRungWeaveSpec29.initBudget + stepanovRungWeaveSpec29.accumulatedGain 24 ∧
    0 < (stepanovRungWeaveSpec29.netMargin 24).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec29.netMargin 24) (QRat.ofInt 0)) ∧
    0 < (stepanovRungWeaveSpec29.effectiveCost 24).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec29.effectiveCost 24) (QRat.ofInt 0)) ∧
    -- Energy defect witness
    QRat.eqv (mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 13 16 (by decide)) ∧
    mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2 < QRat.ofInt 1 ∧
    QRat.eqv energyVariationalDefectWitness (QRat.mk' 3 16 (by decide)) ∧
    0 < energyVariationalDefectWitness.num ∧
    (¬ QRat.eqv energyVariationalDefectWitness (QRat.ofInt 0)) ∧
    -- Short interval prime guarantees
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung29Spec.HasGuaranteedPrime ∧
    -- Monotone exponents & gaps
    qrhShortExponent 29 < qrhShortExponent 14 ∧
    qrhShortExponent 14 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    chebyshevGap (qrhShortExponent 5) < chebyshevGap (qrhShortExponent 6) ∧
    chebyshevGap (qrhShortExponent 6) < chebyshevGap (qrhShortExponent 14) ∧
    chebyshevGap (qrhShortExponent 14) < chebyshevGap (qrhShortExponent 29) := by
  have hm1 : 0 < 1 := by decide
  have hm9 : 0 < 9 := by decide
  have hm24 : 0 < 24 := by decide
  have h_dom1 := stepanov_lift_chain_accumulated_strict_dominance stepanovRungWeaveSpec5_6 1 hm1
  have h_net1 := stepanov_lift_chain_net_margin_pos stepanovRungWeaveSpec5_6 1 hm1
  have h_dom9 := stepanov_lift_chain_accumulated_strict_dominance stepanovRungWeaveSpec14 9 hm9
  have h_net9 := stepanov_lift_chain_net_margin_pos stepanovRungWeaveSpec14 9 hm9
  have h_dom24 := stepanov_lift_chain_accumulated_strict_dominance stepanovRungWeaveSpec29 24 hm24
  have h_comp24 := stepanov_lift_chain_composition_bound stepanovRungWeaveSpec29 24 hm24
  have h_net24 := stepanov_lift_chain_net_margin_pos stepanovRungWeaveSpec29 24 hm24
  refine ⟨h_dom1, h_net1.1, h_net1.2,
          h_dom9, h_net9.1, h_net9.2,
          h_dom24, h_comp24.1, h_net24.1, h_net24.2, h_comp24.2.1, h_comp24.2.2,
          by decide, by decide, by decide, by decide, by decide,
          shortIntervalQrh3364Spec_has_prime,
          shortIntervalQrh65128Spec_has_prime,
          shortIntervalDyadicRung14Spec_has_prime,
          shortIntervalDyadicRung29Spec_has_prime,
          by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Standalone master certificate for rung `k = 29` (`eGap = 24`, `stages = 24`)
    combining exact arithmetic identities, strict gap dominance, and guaranteed prime existence. -/
theorem stepanov_ladder_rung29_weave_cert :
    stepanovRungWeaveSpec29.accumulatedCost 24 < stepanovRungWeaveSpec29.accumulatedGain 24 ∧
    stepanovRungWeaveSpec29.effectiveCost 24 <
      stepanovRungWeaveSpec29.initBudget + stepanovRungWeaveSpec29.accumulatedGain 24 ∧
    0 < (stepanovRungWeaveSpec29.netMargin 24).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec29.netMargin 24) (QRat.ofInt 0)) ∧
    0 < (stepanovRungWeaveSpec29.effectiveCost 24).num ∧
    (¬ QRat.eqv (stepanovRungWeaveSpec29.effectiveCost 24) (QRat.ofInt 0)) ∧
    QRat.eqv (mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 13 16 (by decide)) ∧
    mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2 < QRat.ofInt 1 ∧
    QRat.eqv energyVariationalDefectWitness (QRat.mk' 3 16 (by decide)) ∧
    0 < energyVariationalDefectWitness.num ∧
    (¬ QRat.eqv energyVariationalDefectWitness (QRat.ofInt 0)) ∧
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64 (by decide)) ∧
    QRat.eqv (chebyshevGap (qrhShortExponent 5)) (QRat.mk' 31 64 (by decide)) ∧
    QRat.eqv (qrhShortExponent 29) (QRat.mk' 536870913 1073741824 (by decide)) ∧
    QRat.eqv (qrhDualFraction 29) (QRat.mk' 1073741823 1073741824 (by decide)) ∧
    QRat.eqv (chebyshevGap (qrhShortExponent 29)) (QRat.mk' 536870911 1073741824 (by decide)) ∧
    qrhShortExponent 29 < qrhShortExponent 5 ∧
    chebyshevGap (qrhShortExponent 5) < chebyshevGap (qrhShortExponent 29) ∧
    shortIntervalDyadicRung29Spec.HasGuaranteedPrime := by
  have hm : 0 < 24 := by decide
  have h_dom := stepanov_lift_chain_accumulated_strict_dominance stepanovRungWeaveSpec29 24 hm
  have h_comp := stepanov_lift_chain_composition_bound stepanovRungWeaveSpec29 24 hm
  have h_net := stepanov_lift_chain_net_margin_pos stepanovRungWeaveSpec29 24 hm
  have h_prime := shortIntervalDyadicRung29Spec_has_prime
  refine ⟨h_dom, h_comp.1, h_net.1, h_net.2, h_comp.2.1, h_comp.2.2,
          by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, h_prime⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/StepanovQrhLadderWeave.lean
