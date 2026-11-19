-- Path: leanasm/src/LeanAsm/QuasiRiemann/LuckyBeurlingStripWeave.lean
-- Weaving Lucky Beurling certificates with QSD1LogDerivStripBridge.
-- Max Column: 120 Columns

import LeanAsm.QuasiRiemann.LuckySieve.BeurlingCerts
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann.LuckySieve

namespace LeanAsm.QuasiRiemann

/-- Combined Lucky Beurling certificate with QSD1 log-derivative strip bridge. -/
structure LuckyBeurlingQsd1StripCert (N : Nat) where
  luckyCert : LuckyBeurlingCertificate N
  bridgeSpec : Qsd1LogDerivStripBridgeSpec
  lucky_surv_pos : QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo N)
  lucky_harm_pos : QRat.ofInt 0 < luckyHarmonicRat (luckyGeneratorsUpTo N)

/-- Master weave connecting finite Lucky Beurling certificates to the QSD[1] sub-7/8 strip bridge. -/
theorem lucky_beurling_qsd1_strip_weave {N : Nat} (cert : LuckyBeurlingQsd1StripCert N) :
    (QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo N) ∧
     QRat.ofInt 0 < luckyHarmonicRat (luckyGeneratorsUpTo N) ∧
     (luckyPrefixUpTo N).length = cert.luckyCert.countUpToN ∧
     cert.luckyCert.harmonicLower ≤ luckyHarmonicRat (luckyGeneratorsUpTo N) ∧
     luckyHarmonicRat (luckyGeneratorsUpTo N) ≤ cert.luckyCert.harmonicUpper ∧
     survivalProductRat (luckyGeneratorsUpTo N) ≤ cert.luckyCert.survivalUpper) ∧
    ((2 * cert.bridgeSpec.jetSpec.qSpec.lipNumerator * cert.bridgeSpec.jetSpec.qSpec.radius ≤
        cert.bridgeSpec.jetSpec.qSpec.centerLower *
          (cert.bridgeSpec.jetSpec.qSpec.radius - cert.bridgeSpec.jetSpec.qSpec.deltaShrink) ∧
       cert.bridgeSpec.jetSpec.qSpec.lipNumerator * cert.bridgeSpec.jetSpec.qSpec.radius <
        cert.bridgeSpec.jetSpec.qSpec.centerLower *
          (cert.bridgeSpec.jetSpec.qSpec.radius - cert.bridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
      (mollifierThetaDen cert.bridgeSpec.vDen2 ≤ 2 * mollifierThetaNum cert.bridgeSpec.vNum2 cert.bridgeSpec.vDen2 ∧
       mollifierThetaNum cert.bridgeSpec.vNum2 cert.bridgeSpec.vDen2 * mollifierThetaDen cert.bridgeSpec.vDen1 <
         mollifierThetaNum cert.bridgeSpec.vNum1 cert.bridgeSpec.vDen1 * mollifierThetaDen cert.bridgeSpec.vDen2 ∧
       8 * mollifierThetaNum cert.bridgeSpec.vNum1 cert.bridgeSpec.vDen1 ≤
         7 * mollifierThetaDen cert.bridgeSpec.vDen1) ∧
      (0 < cert.bridgeSpec.weaveSpec.margin ∧
       cert.bridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
      (QRat.mk' 1 2 < cert.bridgeSpec.weaveSpec.strip.sigmaLo ∧
       cert.bridgeSpec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths)) := by
  have hBridge := qsd1_logderiv_sub78_strip_bridge cert.bridgeSpec
  exact ⟨⟨cert.lucky_surv_pos, cert.lucky_harm_pos, cert.luckyCert.h_count,
          cert.luckyCert.h_harm_lo, cert.luckyCert.h_harm_hi, cert.luckyCert.h_surv_hi⟩,
         hBridge⟩

/-- Concrete woven certificate at N = 50. -/
def lucky_beurling_qsd1_strip_cert_50 : LuckyBeurlingQsd1StripCert 50 where
  luckyCert := luckyBeurlingCert_50
  bridgeSpec := qsd1LogDerivRung32000Spec
  lucky_surv_pos := lucky_survival_product_50_pos
  lucky_harm_pos := lucky_harmonic_50_pos

/-- Concrete woven certificate at N = 200. -/
def lucky_beurling_qsd1_strip_cert_200 : LuckyBeurlingQsd1StripCert 200 where
  luckyCert := luckyBeurlingCert_200
  bridgeSpec := qsd1LogDerivRung32000Spec
  lucky_surv_pos := lucky_survival_product_200_pos
  lucky_harm_pos := lucky_harmonic_200_pos

/-- Concrete end-to-end woven certificate theorem for Lucky Beurling N = 50 and QSD1 strip bridge. -/
theorem lucky_beurling_qsd1_strip_cert :
    (QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo 50) ∧
     QRat.ofInt 0 < luckyHarmonicRat (luckyGeneratorsUpTo 50) ∧
     (luckyPrefixUpTo 50).length = 13 ∧
     QRat.mk' 95 100 ≤ luckyHarmonicRat (luckyGeneratorsUpTo 50) ∧
     luckyHarmonicRat (luckyGeneratorsUpTo 50) ≤ QRat.mk' 96 100 ∧
     survivalProductRat (luckyGeneratorsUpTo 50) ≤ QRat.mk' 35 100) ∧
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
  lucky_beurling_qsd1_strip_weave lucky_beurling_qsd1_strip_cert_50

end LeanAsm.QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/LuckyBeurlingStripWeave.lean
