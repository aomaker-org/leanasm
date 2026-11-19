-- Path: leanasm/tests/TestPreperiodic.lean
-- Kernel verification test auditing unicritical polynomial preperiodic dynamics axioms.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
import LeanAsm.QuasiRiemann.Valuation.RNS

open QuasiRiemann
open QuasiRiemann.Valuation

open LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

/-!
# Preperiodic Dynamics Axiom Provenance Audit

Verifies that unicritical polynomial preperiodic partition certificates,
Proposition 2.2 evaluations, and valuation stabilization theorems depend
strictly on authorized constructive axioms (`propext`, `Quot.sound`) with
ZERO `sorryAx` and ZERO `Classical.choice`.
-/

#print axioms preperiodic_partition_sound
#print axioms preperiodic_partition_n1_sound
#print axioms generalized_partition_m1_n2_sound
#print axioms proposition41_lower_bound_m2_n3_sound
#print axioms preperiodic_partition_zero_sound
#print axioms andersen_garton_prop22_q5_d2
#print axioms andersen_garton_prop22_q5_d2_reduced
#print axioms iter0_val
#print axioms iter1_val
#print axioms iter2_val
#print axioms unicritical_iterate_valuation_growth
#print axioms theorem51_asymptotic_bound_sound
#print axioms theorem13_average_bound_sound
#print axioms proposition53_average_bound_sound
#print axioms wreath_product_bound_sound
#print axioms lemma43_divisibility_bound_sound
#print axioms unicriticalPoly_eval_cross_eq
#print axioms pAdicVal_qPow
#print axioms pAdicVal_add_eq_of_lt
#print axioms unicritical_integral_orbit_invariant
#print axioms unicritical_escape_val_exact
#print axioms unicritical_escape_no_preperiodic
#print axioms unicritical_escape_concrete_iter0
#print axioms unicritical_escape_concrete_iter1
#print axioms unicritical_escape_concrete_iter0_ne_iter1


-- =============================================================================
-- RNS/CRT and Valuation/Orbit Soundness Weave Verification
-- =============================================================================

theorem test_preperiodic_rns_weave_sound :
    let poly := unicriticalPoly (QRat.ofInt 1) 2
    let x0 := QRat.mk' 1 2 (by decide)
    have sampleRnsA : LeanAsm.QuasiRiemann.RNS.RnsInt 3 :=
      ⟨#[1, 2, 3], #[2, 3, 5], rfl, rfl⟩
    have sampleRnsRat : LeanAsm.QuasiRiemann.RNS.RnsQRat 3 :=
      ⟨sampleRnsA, sampleRnsA⟩
    ((LeanAsm.QuasiRiemann.RNS.rnsContractionStep sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0) ∧
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct = 5512 ∧
      (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
        (fun q => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower q 1 0
          (QuasiRiemann.Valuation.mersenneCofactorInv q))
        QuasiRiemann.Valuation.mersenneFiveInv).num % 27559 = 5512 ∧
      QuasiRiemann.Valuation.PrimeTowerHenselCert QuasiRiemann.Valuation.mersenneTower 1
        (QuasiRiemann.Valuation.qOfInt 5)
        (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
          (fun q => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower q 1 0
            (QuasiRiemann.Valuation.mersenneCofactorInv q))
          QuasiRiemann.Valuation.mersenneFiveInv)) ∧
    (∀ n : Nat, QuasiRiemann.Valuation.pAdicVal 2 (iterateEval poly n x0) =
      some (Int.ofNat (2 ^ n) * (-1))) ∧
    (∀ m n : Nat, m ≠ n → iterateEval poly m x0 ≠ iterateEval poly n x0) := by
  have hp : IsPrime 2 := by decide
  have hd : 2 ≤ 2 := by decide
  have hv0 : (-1 : Int) < 0 := by decide
  have hx0 : pAdicVal 2 (QRat.mk' 1 2 (by decide)) = some (-1) := by decide
  have ha : valLe (some (Int.ofNat 2 * (-1) + 1)) (pAdicVal 2 (QRat.ofInt 1)) := by decide
  exact LeanAsm.QuasiRiemann.RNS.rns_valuation_orbit_step_sound 2 hp hd (QRat.ofInt 1)
    (QRat.mk' 1 2 (by decide)) hv0 hx0 ha _ _

#print axioms test_preperiodic_rns_weave_sound

-- end of file: leanasm/tests/TestPreperiodic.lean
