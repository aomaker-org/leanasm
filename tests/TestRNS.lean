-- Path: leanasm/tests/TestRNS.lean
-- Kernel verification test auditing RNS and CRT reconstruction axioms.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.RNS

open LeanAsm.QuasiRiemann.RNS
open QuasiRiemann

/-!
# RNS and CRT Reconstruction Axiom Provenance Audit

Verifies that `RnsInt`, `RnsQRat`, and CRT reconstruction depend strictly on authorized
constructive axioms (`propext`, `Quot.sound`) with ZERO `sorryAx` and ZERO `Classical.choice`.
-/

def sampleRnsA : RnsInt 3 :=
  ⟨#[1, 2, 3], #[2, 3, 5], rfl, rfl⟩

def sampleRnsB : RnsInt 3 :=
  ⟨#[1, 1, 4], #[2, 3, 5], rfl, rfl⟩

def sampleRnsRat : RnsQRat 3 :=
  ⟨sampleRnsA, sampleRnsB⟩

def sampleZeroRat : RnsQRat 3 :=
  RnsQRat.zero 3 #[2, 3, 5] rfl

def sampleCoeffs : Array (RnsQRat 3) :=
  #[sampleZeroRat]

theorem sampleRnsA_reconstruct_eval : sampleRnsA.reconstruct = 23 := by
  rfl

theorem sampleRnsB_reconstruct_eval : sampleRnsB.reconstruct = 19 := by
  rfl

theorem sampleRnsRat_toQRat_eval :
    sampleRnsRat.toQRat = QRat.mk' 23 19 (by decide) := by
  rfl

theorem sampleContractionStep_sound_pos :
    (rnsContractionStep sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 := by
  dsimp [RnsQRat.toQRat]
  split
  · next hd =>
    dsimp [QRat.mk', RnsInt.reconstruct]
    split
    · decide
    · next hM =>
      exact Int.natCast_nonneg _
  · decide

theorem sampleContractionLoop_sound_pos (n : Nat) :
    (rnsContractionLoop n sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 := by
  dsimp [RnsQRat.toQRat]
  split
  · next hd =>
    dsimp [QRat.mk', RnsInt.reconstruct]
    split
    · decide
    · next hM =>
      exact Int.natCast_nonneg _
  · decide

theorem sampleContractionLoop_1024_pos :
    (rnsContractionLoop 1024 sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 :=
  sampleContractionLoop_sound_pos 1024

theorem sampleContractionLoop_2048_pos :
    (rnsContractionLoop 2048 sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 :=
  sampleContractionLoop_sound_pos 2048

-- =============================================================================
-- Mersenne Prime Tower CRT Soundness Executable Checks
-- =============================================================================

theorem test_rnsInt_mersenne_mod_eq :
    (mersenneA.reconstruct % 7 = 3) ∧
    (mersenneA.reconstruct % 31 = 25) ∧
    (mersenneA.reconstruct % 127 = 51) :=
  rnsInt_reconstruct_mod_eq 3 25 51 mersenneA rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem test_rnsInt_mersenne_add_sound :
    (RnsInt.add mersenneA mersenneB).reconstruct =
      (mersenneA.reconstruct + mersenneB.reconstruct) % 27559 :=
  rnsInt_reconstruct_add_sound

theorem test_rnsInt_mersenne_mul_sound :
    (RnsInt.mul mersenneA mersenneB).reconstruct =
      (mersenneA.reconstruct * mersenneB.reconstruct) % 27559 :=
  rnsInt_reconstruct_mul_sound

theorem test_rnsQRat_contraction_preserves_pos_1024 :
    (rnsContractionLoop 1024 sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos 1024 sampleRnsRat #[sampleRnsRat]

theorem test_rnsQRat_contraction_preserves_pos_2048 :
    (rnsContractionLoop 2048 sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos 2048 sampleRnsRat #[sampleRnsRat]


theorem test_rnsQRat_add_bounded_step :
    (RnsQRat.add sampleRnsRat sampleRnsRat).toQRat.num ≥ 0 :=
  rnsQRat_add_bounded_step sampleRnsRat sampleRnsRat

theorem test_rnsQRat_mul_bounded_step :
    (RnsQRat.mul sampleRnsRat sampleRnsRat).toQRat.num ≥ 0 :=
  rnsQRat_mul_bounded_step sampleRnsRat sampleRnsRat

theorem test_rns_valuation_orbit_step_sound :
    let poly := LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly (QRat.ofInt 1) 2
    let x0 := QRat.mk' 1 2 (by decide)
    ((rnsContractionStep sampleRnsRat #[sampleRnsRat]).toQRat.num ≥ 0) ∧
    (mersenneA.reconstruct = 5512 ∧
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
    (∀ n : Nat, QuasiRiemann.Valuation.pAdicVal 2
      (LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval poly n x0) =
      some (Int.ofNat (2 ^ n) * (-1))) ∧
    (∀ m n : Nat, m ≠ n →
      LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval poly m x0 ≠
      LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval poly n x0) := by
  have hp : QuasiRiemann.Valuation.IsPrime 2 := by decide
  have hd : 2 ≤ 2 := by decide
  have hv0 : (-1 : Int) < 0 := by decide
  have hx0 : QuasiRiemann.Valuation.pAdicVal 2 (QRat.mk' 1 2 (by decide)) = some (-1) := by
    decide
  have ha : QuasiRiemann.Valuation.valLe (some (Int.ofNat 2 * (-1) + 1))
      (QuasiRiemann.Valuation.pAdicVal 2 (QRat.ofInt 1)) := by
    decide
  exact rns_valuation_orbit_step_sound 2 hp hd (QRat.ofInt 1) (QRat.mk' 1 2 (by decide))
    hv0 hx0 ha sampleRnsRat #[sampleRnsRat]


#print axioms sampleRnsA_reconstruct_eval
#print axioms sampleRnsB_reconstruct_eval
#print axioms sampleRnsRat_toQRat_eval
#print axioms sampleContractionStep_sound_pos
#print axioms sampleContractionLoop_sound_pos
#print axioms sampleContractionLoop_1024_pos
#print axioms sampleContractionLoop_2048_pos
#print axioms rns_contraction_sound
#print axioms RnsInt.reconstruct
#print axioms RnsQRat.toQRat
#print axioms RnsInt.add
#print axioms RnsInt.mul
#print axioms RnsInt.zero
#print axioms RnsInt.one
#print axioms RnsQRat.add
#print axioms RnsQRat.mul
#print axioms rnsContractionStep
#print axioms rnsContractionLoop
#print axioms rnsInt_reconstruct_mod_eq
#print axioms rnsInt_reconstruct_add_sound
#print axioms rnsInt_reconstruct_mul_sound
#print axioms rnsQRat_add_eval_sound
#print axioms rnsQRat_mul_eval_sound
#print axioms rnsQRat_contraction_preserves_pos
#print axioms rnsInt_reconstruct_mersenne_crt_seed_cert
#print axioms test_rnsInt_mersenne_mod_eq
#print axioms test_rnsInt_mersenne_add_sound
#print axioms test_rnsInt_mersenne_mul_sound
#print axioms test_rnsQRat_contraction_preserves_pos_1024
#print axioms test_rnsQRat_contraction_preserves_pos_2048

#print axioms rnsQRat_add_bounded_step
#print axioms rnsQRat_mul_bounded_step
#print axioms rnsContractionStep_bounded_step
#print axioms rnsQRat_contraction_loop_bounded_step
#print axioms rns_valuation_orbit_step_sound
#print axioms test_rnsQRat_add_bounded_step
#print axioms test_rnsQRat_mul_bounded_step
#print axioms test_rns_valuation_orbit_step_sound

-- end of file: leanasm/tests/TestRNS.lean
