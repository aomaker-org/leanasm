-- Path: leanasm/src/LeanAsm/QuasiRiemann/SieveSequenceStripWeave.lean
-- Weaving SieveSequence Beurling certificates with QSD1LogDerivStripBridge.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.SieveSequence.Core
import LeanAsm.QuasiRiemann.SieveSequence.BeurlingCerts
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann.SieveSequence

namespace LeanAsm.QuasiRiemann.SieveSequence

/-- Combined generalized SieveSequence Beurling certificate
    with QSD1 log-derivative strip bridge. -/
structure SieveSequenceQsd1StripCert (N : Nat) where
  ludicCert : SieveSequenceCertificate N
  josephusCert : JosephusBeurlingCertificate N
  bridgeSpec : Qsd1LogDerivStripBridgeSpec
  ludic_surv_pos : QRat.ofInt 0 < survivalProductRat (ludicGeneratorsUpTo N)
  ludic_harm_pos : QRat.ofInt 0 < sequenceHarmonicRat (ludicGeneratorsUpTo N)
  josephus_surv_pos : QRat.ofInt 0 < survivalProductRat (josephusGeneratorsUpTo N)
  josephus_harm_pos : QRat.ofInt 0 < sequenceHarmonicRat (josephusGeneratorsUpTo N)

/-- Master weave connecting SieveSequence Beurling certificates (Ludic and Josephus)
    to the QSD[1] sub-7/8 strip bridge. -/
theorem sieve_sequence_qsd1_strip_weave {N : Nat} (cert : SieveSequenceQsd1StripCert N) :
    ((QRat.ofInt 0 < survivalProductRat (ludicGeneratorsUpTo N) ∧
      QRat.ofInt 0 < sequenceHarmonicRat (ludicGeneratorsUpTo N) ∧
      (ludicGeneratorsUpTo N).length = cert.ludicCert.countUpToN ∧
      cert.ludicCert.harmonicLower ≤ sequenceHarmonicRat (ludicGeneratorsUpTo N) ∧
      sequenceHarmonicRat (ludicGeneratorsUpTo N) ≤ cert.ludicCert.harmonicUpper ∧
      survivalProductRat (ludicGeneratorsUpTo N) ≤ cert.ludicCert.survivalUpper) ∧
     (QRat.ofInt 0 < survivalProductRat (josephusGeneratorsUpTo N) ∧
      QRat.ofInt 0 < sequenceHarmonicRat (josephusGeneratorsUpTo N) ∧
      (josephusGeneratorsUpTo N).length = cert.josephusCert.countUpToN ∧
      cert.josephusCert.harmonicLower ≤ sequenceHarmonicRat (josephusGeneratorsUpTo N) ∧
      sequenceHarmonicRat (josephusGeneratorsUpTo N) ≤ cert.josephusCert.harmonicUpper ∧
      survivalProductRat (josephusGeneratorsUpTo N) ≤ cert.josephusCert.survivalUpper)) ∧
    ((2 * cert.bridgeSpec.jetSpec.qSpec.lipNumerator * cert.bridgeSpec.jetSpec.qSpec.radius ≤
        cert.bridgeSpec.jetSpec.qSpec.centerLower *
          (cert.bridgeSpec.jetSpec.qSpec.radius - cert.bridgeSpec.jetSpec.qSpec.deltaShrink) ∧
       cert.bridgeSpec.jetSpec.qSpec.lipNumerator * cert.bridgeSpec.jetSpec.qSpec.radius <
        cert.bridgeSpec.jetSpec.qSpec.centerLower *
          (cert.bridgeSpec.jetSpec.qSpec.radius - cert.bridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
      (mollifierThetaDen cert.bridgeSpec.vDen2 ≤
          2 * mollifierThetaNum cert.bridgeSpec.vNum2 cert.bridgeSpec.vDen2 ∧
       mollifierThetaNum cert.bridgeSpec.vNum2 cert.bridgeSpec.vDen2 *
           mollifierThetaDen cert.bridgeSpec.vDen1 <
         mollifierThetaNum cert.bridgeSpec.vNum1 cert.bridgeSpec.vDen1 *
           mollifierThetaDen cert.bridgeSpec.vDen2 ∧
       8 * mollifierThetaNum cert.bridgeSpec.vNum1 cert.bridgeSpec.vDen1 ≤
         7 * mollifierThetaDen cert.bridgeSpec.vDen1) ∧
      (0 < cert.bridgeSpec.weaveSpec.margin ∧
       cert.bridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
      (QRat.mk' 1 2 < cert.bridgeSpec.weaveSpec.strip.sigmaLo ∧
       cert.bridgeSpec.weaveSpec.strip.sigmaLo < qrhThresholdSevenEighths)) := by
  have hBridge := qsd1_logderiv_sub78_strip_bridge cert.bridgeSpec
  exact ⟨⟨⟨cert.ludic_surv_pos, cert.ludic_harm_pos, cert.ludicCert.h_count,
            cert.ludicCert.h_harm_lo, cert.ludicCert.h_harm_hi, cert.ludicCert.h_surv_hi⟩,
           ⟨cert.josephus_surv_pos, cert.josephus_harm_pos, cert.josephusCert.h_count,
            cert.josephusCert.h_harm_lo, cert.josephusCert.h_harm_hi,
            cert.josephusCert.h_surv_hi⟩⟩,
         hBridge⟩

/-- Concrete woven SieveSequence certificate at N = 50. -/
def sieve_sequence_qsd1_strip_cert_50 : SieveSequenceQsd1StripCert 50 where
  ludicCert := ludicBeurlingCert_50
  josephusCert := josephusBeurlingCert_50
  bridgeSpec := qsd1LogDerivRung32000Spec
  ludic_surv_pos := ludic_survival_product_50_pos
  ludic_harm_pos := ludic_harmonic_50_pos
  josephus_surv_pos := josephus_survival_product_50_pos
  josephus_harm_pos := josephus_harmonic_50_pos

/-- Concrete end-to-end woven certificate theorem for SieveSequence Beurling at N = 50
    and QSD1 strip bridge. -/
theorem sieve_sequence_qsd1_strip_cert :
    ((QRat.ofInt 0 < survivalProductRat (ludicGeneratorsUpTo 50) ∧
      QRat.ofInt 0 < sequenceHarmonicRat (ludicGeneratorsUpTo 50) ∧
      (ludicGeneratorsUpTo 50).length = 14 ∧
      QRat.mk' 16 10 ≤ sequenceHarmonicRat (ludicGeneratorsUpTo 50) ∧
      sequenceHarmonicRat (ludicGeneratorsUpTo 50) ≤ QRat.mk' 17 10 ∧
      survivalProductRat (ludicGeneratorsUpTo 50) ≤ QRat.mk' 15 100) ∧
     (QRat.ofInt 0 < survivalProductRat (josephusGeneratorsUpTo 50) ∧
      QRat.ofInt 0 < sequenceHarmonicRat (josephusGeneratorsUpTo 50) ∧
      (josephusGeneratorsUpTo 50).length = 7 ∧
      QRat.mk' 68 100 ≤ sequenceHarmonicRat (josephusGeneratorsUpTo 50) ∧
      sequenceHarmonicRat (josephusGeneratorsUpTo 50) ≤ QRat.mk' 70 100 ∧
      survivalProductRat (josephusGeneratorsUpTo 50) ≤ QRat.mk' 46 100)) ∧
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
  sieve_sequence_qsd1_strip_weave sieve_sequence_qsd1_strip_cert_50

end LeanAsm.QuasiRiemann.SieveSequence

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/SieveSequenceStripWeave.lean
