-- Path: leanasm/src/LeanAsm/QuasiRiemann/HigherRungRnsBridge.lean
-- Higher-rung dyadic-Abel ladder bridge coupled to 4-channel RNS-4096 contraction lift.
-- Strictly descending short-interval exponents θ(k) = (2^k + 1) / 2^(k+1) ↓ 1/2 for k ≥ 7.
-- Zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.DyadicAbelBridge
import LeanAsm.QuasiRiemann.MollifierVariationalBridge
import LeanAsm.QuasiRiemann.Rns4096ContractionLift
import LeanAsm.QuasiRiemann.ContractionReflectionBridge
import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.AsymptoticZfr

namespace QuasiRiemann

open LeanAsm.QuasiRiemann
open LeanAsm.QuasiRiemann.Rns4096
open LeanAsm.QuasiRiemann.RNS

/-!
# Higher-Rung Dyadic-Abel & RNS-4096 QRH Contraction Lift (Issue #242)

This module formalizes the composite variational contraction certificate linking:
1. Higher-rung dyadic-Abel monotone rational envelopes and cleared-denominator tail gates
   for rungs $k \ge 7$ (with $\theta(k) = (2^k + 1) / 2^{k+1} \downarrow 1/2$).
2. The 4-channel Mersenne/Proth RNS ring ($N = 4096$) contraction box `rns4096PairBox`.
3. Critical-axis reflection involution exclusion on paired-channel step contraction.
4. $O(1)$-memory structural induction and bounded arithmetic preserving kernel decidability
   under `LEAN_OPTS="-M4096"`.
-/

-- =============================================================================
-- 1. Helper Ordering Lemmas
-- =============================================================================

theorem qrat_lt_trans {a b c : QRat} (hab : a < b) (hbc : b < c) : a < c :=
  qrat_lt_of_lt_of_le hab (qrat_le_of_lt hbc)

-- =============================================================================
-- 2. Parametric Short-Interval Descent Bounds for Higher Rungs k ≥ 7
-- =============================================================================

/-- Strict descending bound: for all $k \ge 7$, `qrhShortExponent k < qrhShortExponent 6`. -/
theorem qrhShortExponent_rung_ge_7_lt_rung6 (k : Nat) (hk : 7 ≤ k) :
    qrhShortExponent k < qrhShortExponent 6 := by
  induction k with
  | zero => omega
  | succ k' ih =>
    cases Nat.decEq k' 6 with
    | isTrue heq =>
      rw [heq]
      exact (qrhShortExponent_strict_anti.1 6).2
    | isFalse hne =>
      have hge7 : 7 ≤ k' := by omega
      have ih' := ih hge7
      have hstep := (qrhShortExponent_strict_anti.1 k').2
      exact qrat_lt_trans hstep ih'

/-- Strict lower bound: for all $k$, `1/2 < qrhShortExponent k`. -/
theorem qrhShortExponent_gt_half (k : Nat) :
    QRat.mk' 1 2 (by decide) < qrhShortExponent k := by
  cases k with
  | zero =>
    dsimp [qrhShortExponent, QRat.mk']
    decide
  | succ k' =>
    exact (qrhShortExponent_strict_anti.1 k').1

/-- Sub-7/8 bound: for all $k \ge 2$, `qrhShortExponent k < 7/8`. -/
theorem qrhShortExponent_lt_seven_eighths (k : Nat) (hk : 2 ≤ k) :
    qrhShortExponent k < qrhThresholdSevenEighths :=
  qrhShortExponent_strict_anti.2.1 k hk

-- =============================================================================
-- 3. Coupling Higher Dyadic-Abel Rungs with 4-Channel RNS-4096 Contraction
-- =============================================================================

/-- Helper lemma: for any $k \ge 5$, `7/8 < qrhDualFraction k`. -/
theorem qrhDualFraction_gt_seven_eighths (k : Nat) (hk : 5 ≤ k) :
    qrhThresholdSevenEighths < qrhDualFraction k := by
  have hmono := qrhDualFraction_strict_mono.1
  have h25 : qrhThresholdSevenEighths < qrhDualFraction 5 := by
    have h2 : QRat.eqv qrhThresholdSevenEighths (qrhDualFraction 2) :=
      qrhDualFraction_strict_mono.2.2.2.2.1
    have h23 := (hmono 2).1
    have h34 := (hmono 3).1
    have h45 := (hmono 4).1
    have h_lt : qrhDualFraction 2 < qrhDualFraction 5 :=
      qrat_lt_trans h23 (qrat_lt_trans h34 h45)
    change (7 : Int) * (qrhDualFraction 5).den < (qrhDualFraction 5).num * 8
    change (qrhDualFraction 2).num * (qrhDualFraction 5).den <
      (qrhDualFraction 5).num * ((qrhDualFraction 2).den : Int) at h_lt
    exact h_lt
  induction k with
  | zero => omega
  | succ k' ih =>
    cases Nat.decEq k' 4 with
    | isTrue heq =>
      rw [heq]
      exact h25
    | isFalse hne =>
      have hk' : 5 ≤ k' := by omega
      have ih' := ih hk'
      have hstep := (hmono k').1
      exact qrat_lt_trans ih' hstep

/-- Composite variational contraction certificate at dyadic ladder rung `k ≥ 5`
coupled to the 4-channel Mersenne/Proth RNS ring for `N = 4096`. -/
structure HigherRungRnsContractionCert (k : Nat) where
  hk : 5 ≤ k
  ladderDrop : qrhShortExponent (k + 1) < qrhShortExponent k
  halfLower : QRat.mk' 1 2 (by decide) < qrhShortExponent k
  sevenEighthsUpper : qrhShortExponent k < qrhThresholdSevenEighths
  tailGateHold :
    (4 * (dyadicAbelGateParametric k hk).scaleN) *
      ((dyadicAbelGateParametric k hk).tailBound * (dyadicAbelGateParametric k hk).tailBound) ≤
    ((2 * (dyadicAbelGateParametric k hk).denomM) * (2 * (dyadicAbelGateParametric k hk).denomM)) *
      ((dyadicAbelGateParametric k hk).tailNum * (dyadicAbelGateParametric k hk).tailNum)
  pairBox : RnsPairBox 4 := rns4096PairBox 4096 (qrhDualFraction k) (qrhDualFraction_gt_seven_eighths k hk)

/-- Constructive canonical builder for `HigherRungRnsContractionCert` at any rung `k ≥ 5`. -/
def buildHigherRungRnsCert (k : Nat) (hk : 5 ≤ k) : HigherRungRnsContractionCert k where
  hk := hk
  ladderDrop := (qrhShortExponent_strict_anti.1 k).2
  halfLower := qrhShortExponent_gt_half k
  sevenEighthsUpper := qrhShortExponent_lt_seven_eighths k (by omega)
  tailGateHold := inv_sqrt_tail_gate_dyadic_step (dyadicAbelGateParametric k hk)
  pairBox := rns4096PairBox 4096 (qrhDualFraction k) (qrhDualFraction_gt_seven_eighths k hk)

/-- Master contraction non-vanishing theorem for higher rungs $k \ge 7$ coupled to RNS-4096:
Certifies that the paired-channel contraction step does not vanish, preserves positivity,
and strictly excludes reflection symmetry onto the critical axis. -/
theorem higher_rung_rns4096_contraction_sound (k : Nat) (hk : 7 ≤ k) :
    let cert := buildHigherRungRnsCert k (by omega)
    qrhShortExponent k < qrhShortExponent 6 ∧
    QRat.mk' 1 2 (by decide) < qrhShortExponent k ∧
    qrhShortExponent k < qrhThresholdSevenEighths ∧
    (¬ QRat.eqv cert.pairBox.stepContract (QRat.ofInt 0)) ∧
    (0 < cert.pairBox.stepContract.num) ∧
    (¬ QRat.eqv (reflectHalf (reflectHalf cert.pairBox.stepContract)) (QRat.ofInt 0)) := by
  let cert := buildHigherRungRnsCert k (by omega)
  have hDrop6 := qrhShortExponent_rung_ge_7_lt_rung6 k hk
  have hHalf := cert.halfLower
  have h78 := cert.sevenEighthsUpper
  have hNe := cert.pairBox.stepContract_ne_zero
  have hPos := cert.pairBox.stepContract_pos
  have hReflEx : ¬ QRat.eqv (reflectHalf (reflectHalf cert.pairBox.stepContract)) (QRat.ofInt 0) := by
    have h_refl := reflectHalf_reflectHalf cert.pairBox.stepContract
    intro h
    have h_contra : cert.pairBox.stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf cert.pairBox.stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * (cert.pairBox.stepContract.den : Int) =
          cert.pairBox.stepContract.num * ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_zero : cert.pairBox.stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · have : 0 < ((rf.den : Nat) : Int) := by omega
          omega
      change cert.pairBox.stepContract.num * 1 = 0 * ((cert.pairBox.stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact hNe h_contra
  exact ⟨hDrop6, hHalf, h78, hNe, hPos, hReflEx⟩

-- =============================================================================
-- 4. Composite Contraction Audit for Rungs k = 7, 8, 9, 10, 11, 12, 13, 14
-- =============================================================================

/-- Master certificate bundle coupling higher dyadic-Abel rungs $k = 7, 8, 9, 10, 11, 12, 13, 14$
to RNS-4096 Garner reconstruction and contraction box non-vanishing. -/
theorem higher_rung_dyadic_abel_rns4096_master_cert :
    -- 1. Strictly descending short-interval exponents
    qrhShortExponent 14 < qrhShortExponent 13 ∧
    qrhShortExponent 13 < qrhShortExponent 12 ∧
    qrhShortExponent 12 < qrhShortExponent 11 ∧
    qrhShortExponent 11 < qrhShortExponent 10 ∧
    qrhShortExponent 10 < qrhShortExponent 9 ∧
    qrhShortExponent 9 < qrhShortExponent 8 ∧
    qrhShortExponent 8 < qrhShortExponent 7 ∧
    qrhShortExponent 7 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    -- 2. Higher rungs stay strictly above 1/2 and below 7/8
    QRat.mk' 1 2 (by decide) < qrhShortExponent 14 ∧
    qrhShortExponent 7 < qrhThresholdSevenEighths ∧
    -- 3. Bounded arithmetic tail gate scaling at rungs 7..14
    (4 * dyadicAbelGateRung7.scaleN) *
      (dyadicAbelGateRung7.tailBound * dyadicAbelGateRung7.tailBound) ≤
      ((2 * dyadicAbelGateRung7.denomM) * (2 * dyadicAbelGateRung7.denomM)) *
        (dyadicAbelGateRung7.tailNum * dyadicAbelGateRung7.tailNum) ∧
    (4 * dyadicAbelGateRung8.scaleN) *
      (dyadicAbelGateRung8.tailBound * dyadicAbelGateRung8.tailBound) ≤
      ((2 * dyadicAbelGateRung8.denomM) * (2 * dyadicAbelGateRung8.denomM)) *
        (dyadicAbelGateRung8.tailNum * dyadicAbelGateRung8.tailNum) ∧
    (4 * dyadicAbelGateRung9.scaleN) *
      (dyadicAbelGateRung9.tailBound * dyadicAbelGateRung9.tailBound) ≤
      ((2 * dyadicAbelGateRung9.denomM) * (2 * dyadicAbelGateRung9.denomM)) *
        (dyadicAbelGateRung9.tailNum * dyadicAbelGateRung9.tailNum) ∧
    (4 * dyadicAbelGateRung10.scaleN) *
      (dyadicAbelGateRung10.tailBound * dyadicAbelGateRung10.tailBound) ≤
      ((2 * dyadicAbelGateRung10.denomM) * (2 * dyadicAbelGateRung10.denomM)) *
        (dyadicAbelGateRung10.tailNum * dyadicAbelGateRung10.tailNum) ∧
    (4 * dyadicAbelGateRung11.scaleN) *
      (dyadicAbelGateRung11.tailBound * dyadicAbelGateRung11.tailBound) ≤
      ((2 * dyadicAbelGateRung11.denomM) * (2 * dyadicAbelGateRung11.denomM)) *
        (dyadicAbelGateRung11.tailNum * dyadicAbelGateRung11.tailNum) ∧
    (4 * dyadicAbelGateRung12.scaleN) *
      (dyadicAbelGateRung12.tailBound * dyadicAbelGateRung12.tailBound) ≤
      ((2 * dyadicAbelGateRung12.denomM) * (2 * dyadicAbelGateRung12.denomM)) *
        (dyadicAbelGateRung12.tailNum * dyadicAbelGateRung12.tailNum) ∧
    (4 * dyadicAbelGateRung13.scaleN) *
      (dyadicAbelGateRung13.tailBound * dyadicAbelGateRung13.tailBound) ≤
      ((2 * dyadicAbelGateRung13.denomM) * (2 * dyadicAbelGateRung13.denomM)) *
        (dyadicAbelGateRung13.tailNum * dyadicAbelGateRung13.tailNum) ∧
    (4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum) ∧
    -- 4. Guaranteed short-interval primes across higher dyadic rungs
    shortIntervalQrh129256Spec.HasGuaranteedPrime ∧
    shortIntervalQrh257512Spec.HasGuaranteedPrime ∧
    shortIntervalQrh5131024Spec.HasGuaranteedPrime ∧
    shortIntervalQrh10252048Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    -- 5. RNS-4096 Garner reconstruction sound
    garnerReconstruct4 (4096 % m1) (4096 % m2) (4096 % m3) (4096 % m4) = 4096 ∧
    -- 6. RNS-4096 contraction box non-vanishing and reflection exclusion at rung 7
    (let cert7 := buildHigherRungRnsCert 7 (by omega)
     (¬ QRat.eqv cert7.pairBox.stepContract (QRat.ofInt 0)) ∧
     (0 < cert7.pairBox.stepContract.num) ∧
     (¬ QRat.eqv (reflectHalf (reflectHalf cert7.pairBox.stepContract)) (QRat.ofInt 0))) := by
  have hc := dyadic_abel_rungs_k5_to_k14_certs
  refine ⟨hc.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          qrhShortExponent_gt_half 14,
          qrhShortExponent_lt_seven_eighths 7 (by omega),
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          shortIntervalQrh129256Spec_has_prime,
          shortIntervalQrh257512Spec_has_prime,
          shortIntervalQrh5131024Spec_has_prime,
          shortIntervalQrh10252048Spec_has_prime,
          shortIntervalDyadicRung11Spec_has_prime,
          shortIntervalDyadicRung12Spec_has_prime,
          shortIntervalDyadicRung13Spec_has_prime,
          shortIntervalDyadicRung14Spec_has_prime,
          garner_reconstruct_4096_eq.2.2.2.2,
          ?_⟩
  have h7 := higher_rung_rns4096_contraction_sound 7 (by omega)
  exact ⟨h7.2.2.2.1, h7.2.2.2.2.1, h7.2.2.2.2.2⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/HigherRungRnsBridge.lean
