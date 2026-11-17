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

-- end of file: leanasm/tests/TestRNS.lean
