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

theorem sampleRnsA_reconstruct_eval : sampleRnsA.reconstruct = 23 := by
  rfl

theorem sampleRnsB_reconstruct_eval : sampleRnsB.reconstruct = 19 := by
  rfl

theorem sampleRnsRat_toQRat_eval :
    sampleRnsRat.toQRat = QRat.mk' 23 19 (by decide) := by
  rfl

#print axioms sampleRnsA_reconstruct_eval
#print axioms sampleRnsB_reconstruct_eval
#print axioms sampleRnsRat_toQRat_eval
#print axioms RnsInt.reconstruct
#print axioms RnsQRat.toQRat
#print axioms RnsInt.add
#print axioms RnsInt.zero

-- end of file: leanasm/tests/TestRNS.lean
