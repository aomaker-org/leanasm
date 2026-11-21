-- Path: leanasm/src/LeanAsm/QuasiRiemann/Qsd1IdempotentDyadicAbelWeave.lean
-- Weaves QSD[1] split-idempotents and logDeriv strip bounds with HighTruncDyadicAbelWeave.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.QsdAlgebraBridge
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge
import LeanAsm.QuasiRiemann.HighTruncDyadicAbelWeave

namespace QuasiRiemann

/-!
# QSD[1] Split Idempotents & High-Truncation Dyadic-Abel Weave

This module weaves:
1. `QSD[1]` orthogonal split idempotents `e_+ = (1 + L)/2` and `e_- = (1 - L)/2` (`L^2 = 1`)
   satisfying `e_+ + e_- = 1`, `e_+^2 = e_+`, `e_-^2 = e_-`, `e_+ * e_- = 0`
   (`QsdAlgebraBridge.lean`).
2. Dual-jet logarithmic-derivative rational box-contraction and sub-7/8 strip bounds
   (`Qsd1LogDerivStripBridge.lean`).
3. High-truncation (`N = 1024, 2048`) dyadic-Abel rung contraction certificates
   (`HighTruncDyadicAbelWeave.lean`).

All proofs are constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

/-- Specification structure bundling a split-idempotent generator with a QSD[1] log-derivative
    strip bridge specification. -/
structure Qsd1IdempotentDyadicAbelSpec where
  splitGen : SplitIdempotentQRat
  hSplit : splitGen = canL ∨ splitGen = canL_neg
  stripBridgeSpec : Qsd1LogDerivStripBridgeSpec

/-- Constructive bridge theorem connecting QSD[1] split-idempotent projections and dual-jet
    logarithmic-derivative box contraction with high-truncation dyadic-Abel strip bounds. -/
theorem qsd1_idempotent_dyadic_abel_weave (spec : Qsd1IdempotentDyadicAbelSpec) :
    -- 1. Orthogonal split-idempotent properties
    (QRat.eqv (e_plus spec.splitGen + e_minus spec.splitGen) (QRat.ofInt 1) ∧
     QRat.eqv (e_plus spec.splitGen * e_plus spec.splitGen) (e_plus spec.splitGen) ∧
     QRat.eqv (e_minus spec.splitGen * e_minus spec.splitGen) (e_minus spec.splitGen) ∧
     QRat.eqv (e_plus spec.splitGen * e_minus spec.splitGen) (QRat.ofInt 0)) ∧
    -- 2. Dual-jet log-derivative box contraction & mollifier step improvement
    ((2 * spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.stripBridgeSpec.jetSpec.qSpec.radius <
      spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (mollifierThetaDen spec.stripBridgeSpec.vDen2 ≤
        2 * mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 ∧
      mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 *
          mollifierThetaDen spec.stripBridgeSpec.vDen1 <
        mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 *
          mollifierThetaDen spec.stripBridgeSpec.vDen2 ∧
      8 * mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 ≤
        7 * mollifierThetaDen spec.stripBridgeSpec.vDen1) ∧
     (0 < spec.stripBridgeSpec.weaveSpec.margin ∧
      spec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QRat.mk' 1 2 < spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      spec.stripBridgeSpec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths)) := by
  have hSplit := split_idempotent_properties spec.splitGen spec.hSplit
  have hStripBridge := qsd1_logderiv_sub78_strip_bridge spec.stripBridgeSpec
  exact ⟨hSplit, hStripBridge⟩

/-- Canonical concrete specification combining `canL` with `qsd1LogDerivRung32000Spec`. -/
def qsd1IdempotentDyadicAbelCertSpec : Qsd1IdempotentDyadicAbelSpec where
  splitGen := canL
  hSplit := Or.inl rfl
  stripBridgeSpec := qsd1LogDerivRung32000Spec

/-- Concrete certificate theorem for `qsd1_idempotent_dyadic_abel_weave` on rung 32000
    with canonical split-idempotent generator `canL`. -/
theorem qsd1_idempotent_dyadic_abel_cert :
    (QRat.eqv (e_plus qsd1IdempotentDyadicAbelCertSpec.splitGen +
        e_minus qsd1IdempotentDyadicAbelCertSpec.splitGen) (QRat.ofInt 1) ∧
     QRat.eqv (e_plus qsd1IdempotentDyadicAbelCertSpec.splitGen *
        e_plus qsd1IdempotentDyadicAbelCertSpec.splitGen)
       (e_plus qsd1IdempotentDyadicAbelCertSpec.splitGen) ∧
     QRat.eqv (e_minus qsd1IdempotentDyadicAbelCertSpec.splitGen *
        e_minus qsd1IdempotentDyadicAbelCertSpec.splitGen)
       (e_minus qsd1IdempotentDyadicAbelCertSpec.splitGen) ∧
     QRat.eqv (e_plus qsd1IdempotentDyadicAbelCertSpec.splitGen *
        e_minus qsd1IdempotentDyadicAbelCertSpec.splitGen) (QRat.ofInt 0)) ∧
    ((2 * qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.radius <
      qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (mollifierThetaDen qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen2 ≤
        2 * mollifierThetaNum qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vNum2
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen2 ∧
      mollifierThetaNum qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vNum2
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen2 *
        mollifierThetaDen qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen1 <
      mollifierThetaNum qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vNum1
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen1 *
        mollifierThetaDen qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen2 ∧
      8 * mollifierThetaNum qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vNum1
          qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen1 ≤
        7 * mollifierThetaDen qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.vDen1) ∧
     (let weave := qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.weaveSpec
      0 < weave.margin ∧ weave.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QRat.mk' 1 2 < qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      qsd1IdempotentDyadicAbelCertSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
        qrhThresholdSevenEighths)) :=
  qsd1_idempotent_dyadic_abel_weave qsd1IdempotentDyadicAbelCertSpec

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Qsd1IdempotentDyadicAbelWeave.lean
