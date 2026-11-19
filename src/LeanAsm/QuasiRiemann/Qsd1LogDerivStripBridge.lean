-- Path: leanasm/src/LeanAsm/QuasiRiemann/Qsd1LogDerivStripBridge.lean
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.QsdAlgebraBridge
import LeanAsm.QuasiRiemann.QR.QrhCore
import LeanAsm.QuasiRiemann.ZeroDensityBridge
import LeanAsm.QuasiRiemann.HighTruncDyadicAbelWeave
import LeanAsm.QuasiRiemann.AsymptoticZfr

namespace QuasiRiemann

private theorem nat_lt_of_mul_lt_mul_right_local {a b c : Nat} (h : a * c < b * c) : a < b := by
  cases Nat.decLt a b with
  | isTrue hlt => exact hlt
  | isFalse hge =>
    have hle : b ≤ a := Nat.ge_of_not_lt hge
    have hle' : b * c ≤ a * c := Nat.mul_le_mul_right c hle
    exact False.elim (Nat.lt_irrefl (a * c) (Nat.lt_of_lt_of_le h hle'))

private theorem half_lt_of_half_add_pos_local (s w : QRat) (hw : (0 : Int) < w.num)
    (heq : QRat.eqv s (QRat.mk' 1 2 + w)) : QRat.mk' 1 2 < s := by
  have hAdd : QRat.mk' 1 2 < QRat.mk' 1 2 + w := by
    change (1 : Int) * ((2 * w.den : Nat) : Int) < ((1 : Int) * (w.den : Int) + w.num * 2) * 2
    rw [Int.natCast_mul]
    rw [show ((2 : Nat) : Int) = 2 from rfl]
    omega
  change (1 : Int) * (s.den : Int) < s.num * 2
  change (1 : Int) * (((QRat.mk' 1 2 + w).den : Nat) : Int) <
    (QRat.mk' 1 2 + w).num * 2 at hAdd
  change s.num * (((QRat.mk' 1 2 + w).den : Nat) : Int) =
    (QRat.mk' 1 2 + w).num * (s.den : Int) at heq
  have hSDenPos : (0 : Int) < (s.den : Int) := Int.natCast_pos.mpr s.den_pos
  have hADenPos : (0 : Int) < ((QRat.mk' 1 2 + w).den : Int) :=
    Int.natCast_pos.mpr (QRat.mk' 1 2 + w).den_pos
  have h1 : ((1 : Int) * (s.den : Int)) * ((QRat.mk' 1 2 + w).den : Int) <
      ((QRat.mk' 1 2 + w).num * (s.den : Int)) * 2 := by
    have hmul := Int.mul_lt_mul_of_pos_right hAdd hSDenPos
    have hL : (1 * ((QRat.mk' 1 2 + w).den : Int)) * (s.den : Int) =
        ((1 : Int) * (s.den : Int)) * ((QRat.mk' 1 2 + w).den : Int) := by ac_rfl
    have hR : ((QRat.mk' 1 2 + w).num * 2) * (s.den : Int) =
        ((QRat.mk' 1 2 + w).num * (s.den : Int)) * 2 := by ac_rfl
    rw [← hL, ← hR]
    exact hmul
  rw [← heq] at h1
  have hR2 : (s.num * ((QRat.mk' 1 2 + w).den : Int)) * 2 =
      (s.num * 2) * ((QRat.mk' 1 2 + w).den : Int) := by ac_rfl
  rw [hR2] at h1
  exact Int.lt_of_mul_lt_mul_right h1 (Int.le_of_lt hADenPos)

/-- Structure bundling a DualJetBoxBoundSpec envelope with a dyadic Abel strip certificate
    and sub-7/8 mollifier step improvement parameters. -/
structure Qsd1LogDerivStripBridgeSpec where
  jetSpec : DualJetBoxBoundSpec
  weaveSpec : HighTruncDyadicAbelSpec
  vNum1 : Nat
  vDen1 : Nat
  vNum2 : Nat
  vDen2 : Nat
  hDen1_pos : 0 < vDen1
  hDen2_pos : 0 < vDen2
  h_ge_one_fourth : 1 * vDen1 ≤ 4 * vNum1
  h_lt : vNum1 * vDen2 < vNum2 * vDen1
  h_le_one : vNum2 ≤ vDen2
  sigmaLo_lt_theta1 :
    have h_den_pos : 0 < mollifierThetaDen vDen1 := by
      dsimp [mollifierThetaDen]; omega
    weaveSpec.strip.sigmaLo <
      QRat.mk' (mollifierThetaNum vNum1 vDen1) (mollifierThetaDen vDen1) h_den_pos

/-- Constructive bridge theorem connecting QSD[1] dual-jet logarithmic-derivative box bounds
    with sub-7/8 mollifier step improvements and certified dyadic Abel strip bounds. -/
theorem qsd1_logderiv_sub78_strip_bridge (spec : Qsd1LogDerivStripBridgeSpec) :
    (2 * spec.jetSpec.qSpec.lipNumerator * spec.jetSpec.qSpec.radius ≤
      spec.jetSpec.qSpec.centerLower *
        (spec.jetSpec.qSpec.radius - spec.jetSpec.qSpec.deltaShrink) ∧
     spec.jetSpec.qSpec.lipNumerator * spec.jetSpec.qSpec.radius <
      spec.jetSpec.qSpec.centerLower *
        (spec.jetSpec.qSpec.radius - spec.jetSpec.qSpec.deltaShrink)) ∧
    (mollifierThetaDen spec.vDen2 ≤ 2 * mollifierThetaNum spec.vNum2 spec.vDen2 ∧
     mollifierThetaNum spec.vNum2 spec.vDen2 * mollifierThetaDen spec.vDen1 <
       mollifierThetaNum spec.vNum1 spec.vDen1 * mollifierThetaDen spec.vDen2 ∧
     8 * mollifierThetaNum spec.vNum1 spec.vDen1 ≤ 7 * mollifierThetaDen spec.vDen1) ∧
    (0 < spec.weaveSpec.margin ∧
     spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
    (QRat.mk' 1 2 < spec.weaveSpec.strip.sigmaLo ∧
     spec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths) := by
  have hJet := qsd1_log_deriv_to_rational_box_contraction spec.jetSpec
  have hMoll := mollifier_step_improvement_below_seven_eighths
    spec.vNum1 spec.vDen1 spec.vNum2 spec.vDen2
    spec.hDen1_pos spec.hDen2_pos spec.h_ge_one_fourth spec.h_lt spec.h_le_one
  have hMargin : 0 < spec.weaveSpec.margin := by
    dsimp [HighTruncDyadicAbelSpec.margin]
    have h := spec.weaveSpec.margin_pos
    omega
  have hRect := spec.weaveSpec.strip.rect_certified
  have hHalf : QRat.mk' 1 2 < spec.weaveSpec.strip.sigmaLo :=
    half_lt_of_half_add_pos_local spec.weaveSpec.strip.sigmaLo spec.weaveSpec.strip.halfWidth
      spec.weaveSpec.strip.halfWidth_pos spec.weaveSpec.strip.sigma_eq_half_add
  have h_n1_le_2d1 : spec.vNum1 ≤ 2 * spec.vDen1 := by
    have h1 : spec.vNum1 * spec.vDen2 < spec.vDen2 * spec.vDen1 := by
      calc spec.vNum1 * spec.vDen2 < spec.vNum2 * spec.vDen1 := spec.h_lt
        _ ≤ spec.vDen2 * spec.vDen1 := Nat.mul_le_mul_right spec.vDen1 spec.h_le_one
    rw [Nat.mul_comm spec.vDen2 spec.vDen1] at h1
    have h2 : spec.vNum1 < spec.vDen1 := nat_lt_of_mul_lt_mul_right_local h1
    omega
  have h78 : spec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths := by
    have hTheta1 := spec.sigmaLo_lt_theta1
    dsimp [qrhThresholdSevenEighths]
    have h_den1_pos := spec.hDen1_pos
    have h_den_pos : 0 < mollifierThetaDen spec.vDen1 := by
      dsimp [mollifierThetaDen]; omega
    have hLe78 : QRat.mk' (mollifierThetaNum spec.vNum1 spec.vDen1)
        (mollifierThetaDen spec.vDen1) h_den_pos ≤ QRat.mk' 7 8 (by decide) := by
      dsimp [QRat.le, QRat.mk', mollifierThetaNum, mollifierThetaDen]
      have h_cast : ((2 * spec.vDen1 - spec.vNum1 : Nat) : Int) =
          2 * (spec.vDen1 : Int) - (spec.vNum1 : Int) := by
        exact Int.ofNat_sub h_n1_le_2d1
      change ((2 * spec.vDen1 - spec.vNum1 : Nat) : Int) * 8 ≤
        7 * ((2 * spec.vDen1 : Nat) : Int)
      rw [h_cast]
      push_cast
      have h_ge' : spec.vDen1 ≤ 4 * spec.vNum1 := by
        have h_ge := spec.h_ge_one_fourth
        omega
      have h_int_ge : (spec.vDen1 : Int) ≤ 4 * (spec.vNum1 : Int) :=
        Int.ofNat_le.mpr h_ge'
      omega
    exact qrat_lt_of_lt_of_le hTheta1 hLe78
  exact ⟨hJet, hMoll, ⟨hMargin, hRect⟩, ⟨hHalf, h78⟩⟩

/-- Concrete bridge certificate combining `qsd1_log_deriv_N2048_cert`,
    `highTruncDyadicAbel32000Spec`, and Weil-to-RH mollifier step `1/4 -> 1/2`. -/
def qsd1LogDerivRung32000Spec : Qsd1LogDerivStripBridgeSpec where
  jetSpec := qsd1_log_deriv_N2048_cert
  weaveSpec := highTruncDyadicAbel32000Spec
  vNum1 := 1
  vDen1 := 4
  vNum2 := 1
  vDen2 := 2
  hDen1_pos := by decide
  hDen2_pos := by decide
  h_ge_one_fourth := by decide
  h_lt := by decide
  h_le_one := by decide
  sigmaLo_lt_theta1 := by decide

/-- Concrete end-to-end certificate theorem for `qsd1LogDerivRung32000Spec`. -/
theorem qsd1_logderiv_rung32000_cert :
    (2 * qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
        qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius ≤
      qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
        (qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
          qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink) ∧
     qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
        qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius <
      qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
        (qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
          qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink)) ∧
    (mollifierThetaDen qsd1LogDerivRung32000Spec.vDen2 ≤
        2 * mollifierThetaNum qsd1LogDerivRung32000Spec.vNum2 qsd1LogDerivRung32000Spec.vDen2 ∧
     mollifierThetaNum qsd1LogDerivRung32000Spec.vNum2 qsd1LogDerivRung32000Spec.vDen2 *
         mollifierThetaDen qsd1LogDerivRung32000Spec.vDen1 <
       mollifierThetaNum qsd1LogDerivRung32000Spec.vNum1 qsd1LogDerivRung32000Spec.vDen1 *
         mollifierThetaDen qsd1LogDerivRung32000Spec.vDen2 ∧
     8 * mollifierThetaNum qsd1LogDerivRung32000Spec.vNum1 qsd1LogDerivRung32000Spec.vDen1 ≤
       7 * mollifierThetaDen qsd1LogDerivRung32000Spec.vDen1) ∧
    (qsd1LogDerivRung32000Spec.weaveSpec.margin = 2682997 ∧
     (4 * qsd1LogDerivRung32000Spec.weaveSpec.gate.scaleN) *
         (qsd1LogDerivRung32000Spec.weaveSpec.gate.tailBound *
           qsd1LogDerivRung32000Spec.weaveSpec.gate.tailBound) ≤
       ((2 * qsd1LogDerivRung32000Spec.weaveSpec.gate.denomM) *
         (2 * qsd1LogDerivRung32000Spec.weaveSpec.gate.denomM)) *
         (qsd1LogDerivRung32000Spec.weaveSpec.gate.tailNum *
           qsd1LogDerivRung32000Spec.weaveSpec.gate.tailNum) ∧
     QRat.mk' 1 2 < qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
     qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
       highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
     qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo < QRat.mk' 3 4 ∧
     qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths ∧
     zdGuthMaynard.exponent qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
       zdGuthMaynard.exponent (QRat.mk' 1 2) ∧
     zdHuxley.exponent qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
       zdHuxley.exponent (QRat.mk' 1 2) ∧
     qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing ∧
     (highTruncTiles_1e30_N2048.length = 4 ∧
       (∀ t ∈ highTruncTiles_1e30_N2048, IsValidLipTile2D t))) := by
  have hBridge := qsd1_logderiv_sub78_strip_bridge qsd1LogDerivRung32000Spec
  have hWeave := hightrunc_dyadic_abel_weave_rung32000_cert
  exact ⟨hBridge.1, hBridge.2.1, hWeave⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Qsd1LogDerivStripBridge.lean
