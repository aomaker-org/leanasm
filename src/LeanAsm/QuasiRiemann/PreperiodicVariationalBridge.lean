-- Path: leanasm/src/LeanAsm/QuasiRiemann/PreperiodicVariationalBridge.lean
-- Bridges Andersen-Garton preperiodic dynamics with contraction reflection
-- and variational mollifier bounds.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
import LeanAsm.QuasiRiemann.PreperiodicQsd1StripWeave
import LeanAsm.QuasiRiemann.ContractionReflectionBridge
import LeanAsm.QuasiRiemann.MollifierVariationalBridge

open QuasiRiemann
open QuasiRiemann.Valuation
open LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
open LeanAsm.QuasiRiemann.PreperiodicQsd1StripWeave

namespace QuasiRiemann

/-!
# Preperiodic Dynamics x Variational & Contraction Bridge

This module extends `PreperiodicQsd1StripWeave` into `ContractionReflectionBridge`
and `MollifierVariationalBridge`:
1. Supplies explicit non-degenerate rational window box witnesses (`NonDegenerateWindowBox`)
   and positive variational energy witnesses (`NonDegenerateMollifierSpec`) for preperiodic
   orbit certificates.
2. Weaves preperiodic orbit invariants (Andersen-Garton Proposition 2.2, Theorem 5.1,
   Theorem 1.3, Proposition 5.3, Lemma 4.2 wreath product bound, Lemma 4.3 divisibility bound)
   with cleared-denominator contraction nonvanishing, reflection duality, and sub-7/8
   variational mollifier energy bounds.
3. Provides computable nonvanishing witnesses for window containment and character conductor
   lower bounds.

All proofs are strictly constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

private theorem qrat_mul_num_pos {x y : QRat} (hx : 0 < x.num) (hy : 0 < y.num) :
    0 < (x * y).num :=
  Int.mul_pos hx hy

private theorem qrat_add_num_pos {x y : QRat} (hx : 0 < x.num) (hy : 0 < y.num) :
    0 < (x + y).num := by
  have h_yden : 0 < ((y.den : Nat) : Int) := by have := y.den_pos; omega
  have h_xden : 0 < ((x.den : Nat) : Int) := by have := x.den_pos; omega
  have p1 := Int.mul_pos hx h_yden
  have p2 := Int.mul_pos hy h_xden
  exact Int.add_pos p1 p2

-- =============================================================================
-- 1. Explicit Non-Degenerate Preperiodic Window Box Witness
-- =============================================================================

/-- Explicit non-degenerate rational window box `[2/5, 4/5] × [1/10, 9/10]`
constructed from Andersen-Garton reduced preperiodic base `w0(5, 2) = 2/5`. -/
def preperiodicWindowBox : NonDegenerateWindowBox where
  sLo := QRat.mk' 2 5 (by decide)
  sHi := QRat.mk' 4 5 (by decide)
  tLo := QRat.mk' 1 10 (by decide)
  tHi := QRat.mk' 9 10 (by decide)
  hs  := by decide
  ht  := by decide
  sLo_pos := by decide
  tLo_pos := by decide

/-- Exact verification that the lower coordinate `sLo` of `preperiodicWindowBox`
matches the reduced Andersen-Garton preperiodic base `w0(5, 2) = 2/5`. -/
theorem preperiodicWindowBox_sLo_eq :
    QRat.eqv preperiodicWindowBox.sLo (QRat.mk' 2 5 (by decide)) := by
  decide

/-- Constructive non-degenerate character conductor bound witness supplied from
`preperiodicWindowBox` at conductor `cond = 1`. -/
def preperiodicCharWitness : NonDegenerateCharBound :=
  supplyNonDegenerateCharWitness 1 (by decide) preperiodicWindowBox

/-- Constructive non-vanishing of the character conductor lower bound from
`preperiodicWindowBox`. -/
theorem preperiodicCharWitness_boundLo_ne_zero :
    ¬ QRat.eqv preperiodicCharWitness.boundLo (QRat.ofInt 0) :=
  preperiodicCharWitness.boundLo_ne_zero

/-- Canonical point `(1/2, 1/2)` lies within `preperiodicWindowBox`. -/
theorem preperiodicWindowBox_contains_half :
    preperiodicWindowBox.toQRatWindowBox.contains (QRat.mk' 1 2) (QRat.mk' 1 2) := by
  dsimp [QRatWindowBox.contains]
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Constructive coordinate positivity for any point in `preperiodicWindowBox`. -/
theorem preperiodicWindowBox_pos {s t : QRat}
    (h : preperiodicWindowBox.toQRatWindowBox.contains s t) :
    QRat.ofInt 0 < s ∧ QRat.ofInt 0 < t :=
  preperiodicWindowBox.contains_pos h

/-- Constructive coordinate non-vanishing for any point in `preperiodicWindowBox`. -/
theorem preperiodicWindowBox_ne_zero {s t : QRat}
    (h : preperiodicWindowBox.toQRatWindowBox.contains s t) :
    ¬ QRat.eqv s (QRat.ofInt 0) ∧ ¬ QRat.eqv t (QRat.ofInt 0) :=
  preperiodicWindowBox.contains_ne_zero h

-- =============================================================================
-- 2. Positive Variational Energy Witness for Preperiodic Dynamics
-- =============================================================================

/-- Strict numerator positivity of `mollifierVariationalEnergy` for any
`NonDegenerateMollifierSpec`. -/
theorem nonDegenerateMollifier_energy_num_pos (m : NonDegenerateMollifierSpec) :
    0 < (mollifierVariationalEnergy m.c1 m.c2).num := by
  have hp1 := m.c1_pos
  have hp2 := m.c2_pos
  change (0 : Int) * (m.c1.den : Int) < m.c1.num * 1 at hp1
  rw [Int.zero_mul, Int.mul_one] at hp1
  change (0 : Int) * (m.c2.den : Int) < m.c2.num * 1 at hp2
  rw [Int.zero_mul, Int.mul_one] at hp2
  have h1 : 0 < (m.c1 * m.c1).num := qrat_mul_num_pos hp1 hp1
  have h2 : 0 < (m.c1 * m.c2).num := qrat_mul_num_pos hp1 hp2
  have h3 : 0 < (m.c2 * m.c2).num := qrat_mul_num_pos hp2 hp2
  have h12 : 0 < (m.c1 * m.c1 + m.c1 * m.c2).num := qrat_add_num_pos h1 h2
  exact qrat_add_num_pos h12 h3

/-- Constructive non-vanishing of `mollifierVariationalEnergy` for any
`NonDegenerateMollifierSpec`. -/
theorem nonDegenerateMollifier_energy_ne_zero (m : NonDegenerateMollifierSpec) :
    ¬ QRat.eqv (mollifierVariationalEnergy m.c1 m.c2) (QRat.ofInt 0) := by
  intro h
  have hp := nonDegenerateMollifier_energy_num_pos m
  change (mollifierVariationalEnergy m.c1 m.c2).num * 1 = 0 * _ at h
  rw [Int.mul_one, Int.zero_mul] at h
  omega

/-- Explicit rational defect witness from the sub-unit variational mollifier energy:
    `preperiodicVariationalEnergyWitness = E_var(3/4, 1/4) = 13/16`. -/
def preperiodicVariationalEnergyWitness : QRat :=
  mollifierVariationalEnergy variationalMollifier3414Spec.c1
    variationalMollifier3414Spec.c2

/-- Exact rational computation: `preperiodicVariationalEnergyWitness = 13/16`. -/
theorem preperiodicVariationalEnergyWitness_eq :
    QRat.eqv preperiodicVariationalEnergyWitness (QRat.mk' 13 16 (by decide)) := by
  decide

/-- Strict numerator positivity of `preperiodicVariationalEnergyWitness`: `0 < 13`. -/
theorem preperiodicVariationalEnergyWitness_num_pos :
    0 < preperiodicVariationalEnergyWitness.num := by
  decide

/-- Constructive non-vanishing of `preperiodicVariationalEnergyWitness`. -/
theorem preperiodicVariationalEnergyWitness_ne_zero :
    ¬ QRat.eqv preperiodicVariationalEnergyWitness (QRat.ofInt 0) := by
  decide

/-- Strict sub-unit bound on `preperiodicVariationalEnergyWitness`: `13/16 < 1`. -/
theorem preperiodicVariationalEnergyWitness_lt_one :
    preperiodicVariationalEnergyWitness < QRat.ofInt 1 := by
  decide

-- =============================================================================
-- 3. Specification Structure & Master Weave Theorem
-- =============================================================================

/-- Unified specification structure bundling preperiodic strip weave,
non-degenerate window box, and non-degenerate variational mollifier parameters. -/
structure PreperiodicVariationalBridgeSpec where
  weaveSpec : PreperiodicQsd1StripWeaveSpec
  windowBox : NonDegenerateWindowBox
  mollifierSpec : NonDegenerateMollifierSpec

/-- Canonical concrete specification on rung 32000 with `preperiodicWindowBox`
and `nonDegenerateMollifier3414Spec`. -/
def preperiodicVariationalRung32000Spec : PreperiodicVariationalBridgeSpec where
  weaveSpec := preperiodicQsd1Rung32000Spec
  windowBox := preperiodicWindowBox
  mollifierSpec := nonDegenerateMollifier3414Spec

/-- Unified preperiodic dynamics x variational & contraction bridge theorem:
Weaves preperiodic partition invariants with:
1. Non-degenerate rational window box coordinate positivity and non-vanishing.
2. Contraction reflection involution and Euler contraction non-vanishing.
3. Sub-unit positive variational mollifier energy bounds.
4. QSD[1] dual-jet box contraction and sub-7/8 strip certificates. -/
theorem preperiodic_variational_contraction_bridge
    (spec : PreperiodicVariationalBridgeSpec) :
    -- (1) Andersen-Garton preperiodic dynamical invariants
    (((w0_formula 5 2 (by decide) (by decide)).reduce = QRat.mk' 2 5) ∧
     (let base := QRat.mk' 2 5 (by decide)
      theorem51AsymptoticBound 2 2 base ≥ base) ∧
     (theorem13AverageBound 134).num > 0 ∧
     (proposition53AverageBound 2 2 134).num > 0 ∧
     (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0 ∧
     (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0) ∧
    -- (2) Non-degenerate window box non-vanishing witnesses
    (QRat.ofInt 0 < spec.windowBox.sLo ∧
     QRat.ofInt 0 < spec.windowBox.tLo ∧
     ¬ QRat.eqv spec.windowBox.sLo (QRat.ofInt 0) ∧
     ¬ QRat.eqv (supplyNonDegenerateCharWitness 1 (by decide) spec.windowBox).boundLo
         (QRat.ofInt 0)) ∧
    -- (3) Contraction reflection involution & non-vanishing
    (QRat.eqv (reflectQRat (reflectQRat spec.windowBox.sLo)) spec.windowBox.sLo ∧
     (halfQRat < spec.windowBox.sLo ↔ reflectQRat spec.windowBox.sLo < halfQRat) ∧
     (∀ (p k : Nat) (hp : 0 < p) (c : Int) (_hc : c.natAbs < p ^ k),
       ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0))) ∧
    -- (4) Positive variational energy witnesses
    (0 < (mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2).num ∧
     ¬ QRat.eqv (mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2)
         (QRat.ofInt 0) ∧
     mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2 < QRat.ofInt 1) ∧
    -- (5) QSD[1] sub-7/8 strip bridge certificates
    ((2 * spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius <
      spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen2 ≤
        2 * mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum2
          spec.weaveSpec.stripBridgeSpec.vDen2 ∧
      mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum2
          spec.weaveSpec.stripBridgeSpec.vDen2 *
        mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen1 <
      mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum1
          spec.weaveSpec.stripBridgeSpec.vDen1 *
        mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen2 ∧
      8 * mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum1
          spec.weaveSpec.stripBridgeSpec.vDen1 ≤
        7 * mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen1) ∧
     (0 < spec.weaveSpec.stripBridgeSpec.weaveSpec.margin ∧
      spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QRat.mk' 1 2 < spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
        qrhThresholdSevenEighths)) := by
  have hWeave := preperiodic_qsd1_strip_weave spec.weaveSpec
  have hPre := hWeave.1
  have hStrip := hWeave.2
  have hsLo_pos := spec.windowBox.sLo_pos
  have htLo_pos := spec.windowBox.tLo_pos
  have hsLo_ne : ¬ QRat.eqv spec.windowBox.sLo (QRat.ofInt 0) := by
    intro h
    change (0 : Int) * (spec.windowBox.sLo.den : Int) < spec.windowBox.sLo.num * 1 at hsLo_pos
    rw [Int.zero_mul, Int.mul_one] at hsLo_pos
    change spec.windowBox.sLo.num * 1 = 0 * ((spec.windowBox.sLo.den : Nat) : Int) at h
    rw [Int.mul_one, Int.zero_mul] at h
    omega
  have hChar_ne := (supplyNonDegenerateCharWitness 1 (by decide) spec.windowBox).boundLo_ne_zero
  have hBox :
      QRat.ofInt 0 < spec.windowBox.sLo ∧
      QRat.ofInt 0 < spec.windowBox.tLo ∧
      ¬ QRat.eqv spec.windowBox.sLo (QRat.ofInt 0) ∧
      ¬ QRat.eqv (supplyNonDegenerateCharWitness 1 (by decide) spec.windowBox).boundLo
          (QRat.ofInt 0) :=
    ⟨hsLo_pos, htLo_pos, hsLo_ne, hChar_ne⟩
  have hReflInv := half_plane_reflection_qrat_involution spec.windowBox.sLo
  have hReflLt := half_plane_reflection_qrat_lt spec.windowBox.sLo
  have hEuler := fun p k hp c (hc : c.natAbs < p ^ k) =>
    qrh_contraction_qrat_ne_zero p k hp c hc
  have hContr :
      QRat.eqv (reflectQRat (reflectQRat spec.windowBox.sLo)) spec.windowBox.sLo ∧
      (halfQRat < spec.windowBox.sLo ↔ reflectQRat spec.windowBox.sLo < halfQRat) ∧
      (∀ (p k : Nat) (hp : 0 < p) (c : Int) (_hc : c.natAbs < p ^ k),
        ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0)) :=
    ⟨hReflInv, hReflLt, hEuler⟩
  have hVarPos := nonDegenerateMollifier_energy_num_pos spec.mollifierSpec
  have hVarNe := nonDegenerateMollifier_energy_ne_zero spec.mollifierSpec
  have hVarLtOne := spec.mollifierSpec.variational_energy_lt_one
  have hVar :
      0 < (mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2).num ∧
      ¬ QRat.eqv (mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2)
          (QRat.ofInt 0) ∧
      mollifierVariationalEnergy spec.mollifierSpec.c1 spec.mollifierSpec.c2 < QRat.ofInt 1 :=
    ⟨hVarPos, hVarNe, hVarLtOne⟩
  exact ⟨hPre, hBox, hContr, hVar, hStrip⟩

/-- Concrete certificate theorem for `preperiodic_variational_contraction_bridge`
under `preperiodicVariationalRung32000Spec`. -/
theorem preperiodic_variational_bridge_cert :
    (((w0_formula 5 2 (by decide) (by decide)).reduce = QRat.mk' 2 5) ∧
     (let base := QRat.mk' 2 5 (by decide)
      theorem51AsymptoticBound 2 2 base ≥ base) ∧
     (theorem13AverageBound 134).num > 0 ∧
     (proposition53AverageBound 2 2 134).num > 0 ∧
     (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0 ∧
     (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0) ∧
    (QRat.ofInt 0 < preperiodicVariationalRung32000Spec.windowBox.sLo ∧
     QRat.ofInt 0 < preperiodicVariationalRung32000Spec.windowBox.tLo ∧
     ¬ QRat.eqv preperiodicVariationalRung32000Spec.windowBox.sLo (QRat.ofInt 0) ∧
     ¬ QRat.eqv (supplyNonDegenerateCharWitness 1 (by decide)
         preperiodicVariationalRung32000Spec.windowBox).boundLo (QRat.ofInt 0)) ∧
    (QRat.eqv (reflectQRat (reflectQRat preperiodicVariationalRung32000Spec.windowBox.sLo))
         preperiodicVariationalRung32000Spec.windowBox.sLo ∧
     (halfQRat < preperiodicVariationalRung32000Spec.windowBox.sLo ↔
       reflectQRat preperiodicVariationalRung32000Spec.windowBox.sLo < halfQRat) ∧
     (∀ (p k : Nat) (hp : 0 < p) (c : Int) (_hc : c.natAbs < p ^ k),
       ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0))) ∧
    (0 < (mollifierVariationalEnergy preperiodicVariationalRung32000Spec.mollifierSpec.c1
         preperiodicVariationalRung32000Spec.mollifierSpec.c2).num ∧
     ¬ QRat.eqv (mollifierVariationalEnergy preperiodicVariationalRung32000Spec.mollifierSpec.c1
         preperiodicVariationalRung32000Spec.mollifierSpec.c2) (QRat.ofInt 0) ∧
     mollifierVariationalEnergy preperiodicVariationalRung32000Spec.mollifierSpec.c1
         preperiodicVariationalRung32000Spec.mollifierSpec.c2 < QRat.ofInt 1) ∧
    ((2 * preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius <
      preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (mollifierThetaDen preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen2 ≤
        2 * mollifierThetaNum preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vNum2
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen2 ∧
      mollifierThetaNum preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vNum2
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen2 *
        mollifierThetaDen preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen1 <
      mollifierThetaNum preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vNum1
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen1 *
        mollifierThetaDen preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen2 ∧
      8 * mollifierThetaNum preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vNum1
          preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen1 ≤
        7 * mollifierThetaDen preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.vDen1) ∧
     (0 < preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.weaveSpec.margin ∧
      preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QRat.mk' 1 2 < preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      preperiodicVariationalRung32000Spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
        qrhThresholdSevenEighths)) :=
  preperiodic_variational_contraction_bridge preperiodicVariationalRung32000Spec

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/PreperiodicVariationalBridge.lean
