-- Path: leanasm/src/LeanAsm/QuasiRiemann/PreperiodicQsd1StripWeave.lean
-- Weaves Andersen & Garton preperiodic partition rational bounds with
-- QSD[1] log-derivative box-contraction and sub-7/8 strip certificates.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge

open _root_.QuasiRiemann
open _root_.QuasiRiemann.Valuation
open _root_.LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

namespace LeanAsm.QuasiRiemann.PreperiodicQsd1StripWeave

/-!
# Preperiodic Dynamics & QSD[1] Sub-7/8 Log-Derivative Strip Weave

This module weaves:
1. Rational preperiodic partition, uniform divisibility, and asymptotic / average proportion
   bounds from Andersen & Garton (`PreperiodicDynamics.lean`).
2. `QSD[1]` dual-jet logarithmic-derivative rational box-contraction and sub-$7/8$ mollifier
   strip certificates (`Qsd1LogDerivStripBridge.lean`).

All proofs are strictly constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

/-- Specification structure bundling QSD[1] log-derivative strip bridge parameters with
    rational preperiodic bounds. -/
structure PreperiodicQsd1StripWeaveSpec where
  stripBridgeSpec : Qsd1LogDerivStripBridgeSpec

/-- Bridge theorem connecting Andersen & Garton preperiodic dynamics invariants with QSD[1]
    dual-jet logarithmic-derivative box contraction and sub-7/8 strip certificates. -/
theorem preperiodic_qsd1_strip_weave (spec : PreperiodicQsd1StripWeaveSpec) :
    -- 1. Preperiodic partition & dynamical bounds
    (((w0_formula 5 2 (by decide) (by decide)).reduce = QRat.mk' 2 5) ∧
     (let base := QRat.mk' 2 5 (by decide)
      theorem51AsymptoticBound 2 2 base ≥ base) ∧
     (theorem13AverageBound 134).num > 0 ∧
     (proposition53AverageBound 2 2 134).num > 0 ∧
     (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0 ∧
     (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0) ∧
    -- 2. QSD[1] log-derivative box bounds & sub-7/8 strip certificates
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
  have hPreperiodic :
      ((w0_formula 5 2 (by decide) (by decide)).reduce = QRat.mk' 2 5) ∧
      (let base := QRat.mk' 2 5 (by decide)
       theorem51AsymptoticBound 2 2 base ≥ base) ∧
      (theorem13AverageBound 134).num > 0 ∧
      (proposition53AverageBound 2 2 134).num > 0 ∧
      (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0 ∧
      (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0 :=
    ⟨andersen_garton_prop22_q5_d2_reduced,
     theorem51_asymptotic_bound_sound,
     theorem13_average_bound_sound,
     proposition53_average_bound_sound,
     wreath_product_bound_sound,
     lemma43_divisibility_bound_sound⟩
  have hStripBridge := qsd1_logderiv_sub78_strip_bridge spec.stripBridgeSpec
  exact ⟨hPreperiodic, hStripBridge⟩

/-- Concrete canonical specification tying `qsd1LogDerivRung32000Spec` with preperiodic bounds. -/
def preperiodicQsd1Rung32000Spec : PreperiodicQsd1StripWeaveSpec where
  stripBridgeSpec := qsd1LogDerivRung32000Spec

/-- Concrete certificate theorem for `preperiodic_qsd1_strip_weave` on rung 32000. -/
theorem preperiodic_qsd1_strip_cert :
    (((w0_formula 5 2 (by decide) (by decide)).reduce = QRat.mk' 2 5) ∧
     (let base := QRat.mk' 2 5 (by decide)
      theorem51AsymptoticBound 2 2 base ≥ base) ∧
     (theorem13AverageBound 134).num > 0 ∧
     (proposition53AverageBound 2 2 134).num > 0 ∧
     (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0 ∧
     (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0) ∧
    ((2 * preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius -
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius <
      preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius -
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (mollifierThetaDen preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen2 ≤
        2 * mollifierThetaNum preperiodicQsd1Rung32000Spec.stripBridgeSpec.vNum2
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen2 ∧
      mollifierThetaNum preperiodicQsd1Rung32000Spec.stripBridgeSpec.vNum2
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen2 *
        mollifierThetaDen preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen1 <
      mollifierThetaNum preperiodicQsd1Rung32000Spec.stripBridgeSpec.vNum1
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen1 *
        mollifierThetaDen preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen2 ∧
      8 * mollifierThetaNum preperiodicQsd1Rung32000Spec.stripBridgeSpec.vNum1
          preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen1 ≤
        7 * mollifierThetaDen preperiodicQsd1Rung32000Spec.stripBridgeSpec.vDen1) ∧
     (0 < preperiodicQsd1Rung32000Spec.stripBridgeSpec.weaveSpec.margin ∧
      preperiodicQsd1Rung32000Spec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QRat.mk' 1 2 < preperiodicQsd1Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      preperiodicQsd1Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
        qrhThresholdSevenEighths)) :=
  preperiodic_qsd1_strip_weave preperiodicQsd1Rung32000Spec

end LeanAsm.QuasiRiemann.PreperiodicQsd1StripWeave

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/PreperiodicQsd1StripWeave.lean
