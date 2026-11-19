-- Path: leanasm/src/LeanAsm/QuasiRiemann/LuckyQrh78Strip.lean
-- Constructive Lucky Beurling sub-7/8 strip and rational box certificates.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.LuckySieve.BeurlingCerts
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge
import LeanAsm.QuasiRiemann.UltraDeep90

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann.LuckySieve

namespace LeanAsm.QuasiRiemann

/-!
### Scope Note
An unconditional global proof of non-vanishing for all x or all s with Re(s) > 7/8
is out of scope without unproved Beurling generalized prime density / sieve conjectures.
Instead, this module establishes constructive finite-prefix Beurling partial-product
envelopes, positivity/non-vanishing lower bounds, and rational box-contraction certificates
at and above the critical threshold σ = 7/8, bridged with Qsd1LogDerivStripBridge under
strict [propext, Quot.sound] provenance.
-/

/-- Partial Beurling Euler product evaluated on generator list `gens` with truncation `M`. -/
def beurlingEulerPartialProductRat (gens : List Nat) (M : Nat) : QRat :=
  gens.foldl (fun acc l => acc * beurlingEulerPartialFactor (invRat l) M) (QRat.ofInt 1)

/-- Finite-cutoff Beurling / Lucky sub-7/8 strip certificate structure at `sigma ≥ 7/8`. -/
structure LuckySub78StripCert (N : Nat) where
  sigmaTest : QRat
  h_sigma_ge : qrhThresholdSevenEighths ≤ sigmaTest
  truncOrder : Nat
  eulerLower : QRat
  eulerUpper : QRat
  h_euler_lo : eulerLower ≤ beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) truncOrder
  h_euler_hi : beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) truncOrder ≤ eulerUpper
  h_euler_pos : QRat.ofInt 0 < eulerLower
  boxSpec : RationalBoxContractionSpec

/-- Concrete constructive certificate at N = 50 and σ = 7/8. -/
def luckySub78StripCert_50 : LuckySub78StripCert 50 where
  sigmaTest := qrhThresholdSevenEighths
  h_sigma_ge := by decide
  truncOrder := 1
  eulerLower := QRat.mk' 241 100
  eulerUpper := QRat.mk' 242 100
  h_euler_lo := by decide
  h_euler_hi := by decide
  h_euler_pos := by decide
  boxSpec := rationalBoxSpec_N256

/-- Concrete constructive certificate at N = 200 and σ = 7/8. -/
def luckySub78StripCert_200 : LuckySub78StripCert 200 where
  sigmaTest := qrhThresholdSevenEighths
  h_sigma_ge := by decide
  truncOrder := 1
  eulerLower := QRat.mk' 308 100
  eulerUpper := QRat.mk' 311 100
  h_euler_lo := by decide
  h_euler_hi := by decide
  h_euler_pos := by decide
  boxSpec := rationalBoxSpec_N512

/-- Exact non-vanishing / positivity of Beurling partial product at N = 50. -/
theorem lucky_beurling_product_50_pos :
    QRat.ofInt 0 < beurlingEulerPartialProductRat (luckyGeneratorsUpTo 50) 1 := by
  decide

/-- Exact non-vanishing / positivity of Beurling partial product at N = 200. -/
theorem lucky_beurling_product_200_pos :
    QRat.ofInt 0 < beurlingEulerPartialProductRat (luckyGeneratorsUpTo 200) 1 := by
  decide

/-- Constructive bridge theorem connecting finite Beurling partial-product envelopes
and rational box-contraction certificates to Qsd1LogDerivStripBridge under [propext, Quot.sound]. -/
theorem lucky_sub78_strip_certificate_bridge {N : Nat}
    (cert : LuckySub78StripCert N) (bridgeSpec : Qsd1LogDerivStripBridgeSpec) :
    (QRat.ofInt 0 < beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) cert.truncOrder ∧
     cert.eulerLower ≤ beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) cert.truncOrder ∧
     beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) cert.truncOrder ≤ cert.eulerUpper ∧
     qrhThresholdSevenEighths ≤ cert.sigmaTest ∧
     cert.boxSpec.lipNumerator * cert.boxSpec.radius <
       cert.boxSpec.centerLower * (cert.boxSpec.radius - cert.boxSpec.deltaShrink)) ∧
    ((2 * bridgeSpec.jetSpec.qSpec.lipNumerator * bridgeSpec.jetSpec.qSpec.radius ≤
        bridgeSpec.jetSpec.qSpec.centerLower *
          (bridgeSpec.jetSpec.qSpec.radius - bridgeSpec.jetSpec.qSpec.deltaShrink) ∧
       bridgeSpec.jetSpec.qSpec.lipNumerator * bridgeSpec.jetSpec.qSpec.radius <
        bridgeSpec.jetSpec.qSpec.centerLower *
          (bridgeSpec.jetSpec.qSpec.radius - bridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
      (mollifierThetaDen bridgeSpec.vDen2 ≤ 2 * mollifierThetaNum bridgeSpec.vNum2 bridgeSpec.vDen2 ∧
       mollifierThetaNum bridgeSpec.vNum2 bridgeSpec.vDen2 * mollifierThetaDen bridgeSpec.vDen1 <
         mollifierThetaNum bridgeSpec.vNum1 bridgeSpec.vDen1 * mollifierThetaDen bridgeSpec.vDen2 ∧
       8 * mollifierThetaNum bridgeSpec.vNum1 bridgeSpec.vDen1 ≤ 7 * mollifierThetaDen bridgeSpec.vDen1) ∧
      (0 < bridgeSpec.weaveSpec.margin ∧
       bridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
      (QRat.mk' 1 2 < bridgeSpec.weaveSpec.strip.sigmaLo ∧
       bridgeSpec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths)) := by
  have hBridge := qsd1_logderiv_sub78_strip_bridge bridgeSpec
  have hBoxLip := cert.boxSpec.lip_mul_radius_lt
  have hPos : QRat.ofInt 0 < beurlingEulerPartialProductRat (luckyGeneratorsUpTo N) cert.truncOrder :=
    qrat_lt_of_lt_of_le cert.h_euler_pos cert.h_euler_lo
  exact ⟨⟨hPos, cert.h_euler_lo, cert.h_euler_hi, cert.h_sigma_ge, hBoxLip⟩, hBridge⟩

/-- Concrete end-to-end sub-7/8 strip certificate linking N = 50 Lucky Beurling
to Qsd1LogDeriv rung 32000. -/
theorem lucky_sub78_strip_cert_50_bridge :
    (QRat.ofInt 0 < beurlingEulerPartialProductRat (luckyGeneratorsUpTo 50) 1 ∧
     QRat.mk' 241 100 ≤ beurlingEulerPartialProductRat (luckyGeneratorsUpTo 50) 1 ∧
     beurlingEulerPartialProductRat (luckyGeneratorsUpTo 50) 1 ≤ QRat.mk' 242 100 ∧
     qrhThresholdSevenEighths ≤ qrhThresholdSevenEighths ∧
     rationalBoxSpec_N256.lipNumerator * rationalBoxSpec_N256.radius <
       rationalBoxSpec_N256.centerLower *
         (rationalBoxSpec_N256.radius - rationalBoxSpec_N256.deltaShrink)) ∧
    ((2 * qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
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
      (0 < qsd1LogDerivRung32000Spec.weaveSpec.margin ∧
       qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
      (QRat.mk' 1 2 < qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
       qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths)) :=
  lucky_sub78_strip_certificate_bridge luckySub78StripCert_50 qsd1LogDerivRung32000Spec

end LeanAsm.QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/LuckyQrh78Strip.lean
