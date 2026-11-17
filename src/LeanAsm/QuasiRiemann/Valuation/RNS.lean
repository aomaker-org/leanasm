-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/RNS.lean
-- Prime Tower Residue Number System (RNS) and Rational Representation (RnsQRat).
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat

namespace LeanAsm.QuasiRiemann.RNS

open _root_.QuasiRiemann

/-- Prime Tower Residue Number System (RNS) integer representation.
    Decomposes an integer across a vector of pairwise coprime moduli. -/
structure RnsInt (k : Nat) where
  residues : Array Nat
  moduli : Array Nat
  h_len : residues.size = k
  h_mod_len : moduli.size = k

/-- RNS Rational representation (`RnsQRat`), pairing an RnsInt numerator
    with an RnsInt denominator to eliminate intermediate height blowups. -/
structure RnsQRat (k : Nat) where
  num : RnsInt k
  den : RnsInt k

/-- Constructive zero RnsInt initialization. -/
def RnsInt.zero (k : Nat) (moduli : Array Nat) (h : moduli.size = k) : RnsInt k :=
  { residues := Array.replicate k 0
    moduli := moduli
    h_len := by simp
    h_mod_len := h }

/-- Element-wise RnsInt addition across independent residue channels. -/
def RnsInt.add {k : Nat} (a b : RnsInt k) : RnsInt k :=
  let res := Array.zipWith (fun r_a r_b => fun m => (r_a + r_b) % m) a.residues b.residues
  let res' := Array.zipWith (fun f m => f m) res a.moduli
  { residues := res'
    moduli := a.moduli
    h_len := by
      dsimp [res', res]
      rw [Array.size_zipWith, Array.size_zipWith]
      simp [a.h_len, b.h_len, a.h_mod_len]
    h_mod_len := a.h_mod_len }

/-- Constructive search for modular multiplicative inverse: finds `x < m` such that `(a * x) % m == 1`. -/
def modInv (a m : Nat) : Nat :=
  if m = 0 then 0
  else (List.range m).find? (fun x => (a * x) % m == 1) |>.getD 0

/-- Constructive Chinese Remainder Theorem (CRT) reconstruction helper for RnsInt:
    Reconstructs the full integer modulo the modulus product M from parallel residue channels. -/
def RnsInt.reconstruct {k : Nat} (x : RnsInt k) : Int :=
  let rList := x.residues.toList
  let mList := x.moduli.toList
  let M : Nat := mList.foldl (· * ·) 1
  if M = 0 then (0 : Int)
  else
    let sum : Nat := (rList.zip mList).foldl (init := 0) fun acc (r, m) =>
      if m = 0 then acc
      else
        let mi := M / m
        let inv := modInv mi m
        acc + (r * mi * inv)
    (sum % M : Nat)

/-- Helper lemma showing `0 < d.toNat` when `0 < d`. -/
theorem toNat_pos_of_pos {d : Int} (hd : 0 < d) : 0 < d.toNat := by
  match d with
  | Int.ofNat (n + 1) => exact Nat.succ_pos n
  | Int.ofNat 0 => contradiction
  | Int.negSucc _ => contradiction

/-- Conversion helper from RnsQRat back to constructive QRat via deferred CRT reconstruction. -/
def RnsQRat.toQRat {k : Nat} (x : RnsQRat k) : QRat :=
  let n := x.num.reconstruct
  let d := x.den.reconstruct
  if hd : 0 < d then
    QRat.mk' n d.toNat (toNat_pos_of_pos hd)
  else
    QRat.ofInt 0

end LeanAsm.QuasiRiemann.RNS

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/RNS.lean
