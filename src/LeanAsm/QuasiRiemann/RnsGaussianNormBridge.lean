-- Path: leanasm/src/LeanAsm/QuasiRiemann/RnsGaussianNormBridge.lean
-- Extension of RnsInt CRT reconstruction and GaussianQsdInt norm bounds.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.GaussianQsdBridge
import LeanAsm.QuasiRiemann.QsdAlgebraBridge

namespace LeanAsm.QuasiRiemann.RnsGaussianNormBridge

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann.RNS

/-!
# RnsInt CRT and GaussianQsdBridge Norm Bounds Bridge

This module extends `RnsInt` Chinese Remainder Theorem (CRT) reconstruction and parallel
residue-channel bounds (`RNS.lean`) with:
1. Constructive `Int` norm (`a^2 + b^2`) and multiplicative norm compatibility for `GaussianQsdInt`.
2. Constructive CRT remainder certificates for `GaussianQsdInt` norm values embedded into
   `RnsInt 3` channels over the Mersenne prime tower `[7, 31, 127]`.
3. Constructive bridge theorems:
   - `rns_crt_gaussian_norm_bound`: General bound stating norm non-negativity, multiplicativity,
     and CRT residue recovery for any valid Gaussian embedding.
   - `rns_crt_gaussian_norm_cert`: Concrete certificate for canonical Gaussian integer elements
     certifying exact norm values, multiplicativity, and Mersenne tower residue channels.

All results are constructive and proved under `[propext, Quot.sound]` with zero Mathlib,
zero `Classical.choice`, and zero `sorryAx`.
-/

/-- Square non-negativity helper for `Int`. -/
private theorem mul_self_nonneg' (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at this
    exact this

/-- Constructive non-negativity of the Gaussian norm on `GaussianQsdInt`. -/
theorem gaussian_norm_nonneg (z : GaussianQsdInt) : 0 ≤ z.norm := by
  dsimp [GaussianQsdInt.norm]
  have ha : 0 ≤ z.a * z.a := mul_self_nonneg' z.a
  have hb : 0 ≤ z.b * z.b := mul_self_nonneg' z.b
  exact Int.add_nonneg ha hb

/-- Canonical Mersenne prime tower moduli array `#[7, 31, 127]`. -/
def mersenneTowerModuli : Array Nat := #[7, 31, 127]

/-- Mersenne tower moduli array length lemma. -/
theorem mersenneTowerModuli_size : mersenneTowerModuli.size = 3 := rfl

/-- Embedding any Gaussian integer slice with a non-negative norm into an `RnsInt 3`
    element across the Mersenne prime tower `[7, 31, 127]`. -/
def gaussianToRnsMersenne (z : GaussianQsdInt) : RnsInt 3 :=
  let n := z.norm.toNat
  { residues := #[n % 7, n % 31, n % 127],
    moduli := mersenneTowerModuli,
    h_len := rfl,
    h_mod_len := rfl }

/-- Residues of `gaussianToRnsMersenne` expand definitionally. -/
theorem gaussianToRnsMersenne_residues (z : GaussianQsdInt) :
    (gaussianToRnsMersenne z).residues =
      #[z.norm.toNat % 7, z.norm.toNat % 31, z.norm.toNat % 127] := rfl

/-- Moduli of `gaussianToRnsMersenne` match `#[7, 31, 127]`. -/
theorem gaussianToRnsMersenne_moduli (z : GaussianQsdInt) :
    (gaussianToRnsMersenne z).moduli = #[7, 31, 127] := rfl

/-- Prime property of Mersenne tower moduli list. -/
theorem mersenneTower_allPrimes :
    QuasiRiemann.Valuation.AllPrimes [7, 31, 127] := by decide

/-- Pairwise distinct property of Mersenne tower moduli list. -/
theorem mersenneTower_pairwiseDistinct :
    QuasiRiemann.Valuation.PairwiseDistinct [7, 31, 127] := by decide

/-- Constructive CRT residue recovery for `gaussianToRnsMersenne`:
    The reconstructed integer modulo 27559 preserves each residue modulo 7, 31, and 127. -/
theorem gaussian_rns_reconstruct_mod_eq (z : GaussianQsdInt) :
    let rns := gaussianToRnsMersenne z
    let r1 := z.norm.toNat % 7
    let r2 := z.norm.toNat % 31
    let r3 := z.norm.toNat % 127
    (rns.reconstruct % 7 = (r1 : Int)) ∧
    (rns.reconstruct % 31 = (r2 : Int)) ∧
    (rns.reconstruct % 127 = (r3 : Int)) := by
  intro rns r1 r2 r3
  have hr1 : r1 < 7 := Nat.mod_lt _ (by decide)
  have hr2 : r2 < 31 := Nat.mod_lt _ (by decide)
  have hr3 : r3 < 127 := Nat.mod_lt _ (by decide)
  have hp : QuasiRiemann.Valuation.AllPrimes [7, 31, 127] := mersenneTower_allPrimes
  have hd : QuasiRiemann.Valuation.PairwiseDistinct [7, 31, 127] := mersenneTower_pairwiseDistinct
  have h_res : rns.residues = #[r1, r2, r3] := rfl
  have h_mod : rns.moduli = #[7, 31, 127] := rfl
  have hp' : QuasiRiemann.Valuation.AllPrimes rns.moduli.toList := by
    rw [h_mod]; exact hp
  have hd' : QuasiRiemann.Valuation.PairwiseDistinct rns.moduli.toList := by
    rw [h_mod]; exact hd
  exact rnsInt_reconstruct_mod_eq r1 r2 r3 rns h_res h_mod hr1 hr2 hr3 hp' hd'

/-- General constructive bridge theorem `rns_crt_gaussian_norm_bound`:
    Binds Gaussian norm non-negativity, multiplicativity under Gaussian multiplication,
    and exact CRT residue preservation on the Mersenne prime tower. -/
theorem rns_crt_gaussian_norm_bound (x y : GaussianQsdInt) :
    0 ≤ x.norm ∧
    0 ≤ y.norm ∧
    GaussianQsdInt.norm (GaussianQsdInt.mulGaussian x y) =
      GaussianQsdInt.norm x * GaussianQsdInt.norm y ∧
    (let rnsX := gaussianToRnsMersenne x
     (rnsX.reconstruct % 7 = ((x.norm.toNat % 7 : Nat) : Int)) ∧
     (rnsX.reconstruct % 31 = ((x.norm.toNat % 31 : Nat) : Int)) ∧
     (rnsX.reconstruct % 127 = ((x.norm.toNat % 127 : Nat) : Int))) ∧
    (let rnsY := gaussianToRnsMersenne y
     (rnsY.reconstruct % 7 = ((y.norm.toNat % 7 : Nat) : Int)) ∧
     (rnsY.reconstruct % 31 = ((y.norm.toNat % 31 : Nat) : Int)) ∧
     (rnsY.reconstruct % 127 = ((y.norm.toNat % 127 : Nat) : Int))) := by
  refine ⟨gaussian_norm_nonneg x, gaussian_norm_nonneg y,
          gaussian_qsd_norm_multiplicative x y,
          gaussian_rns_reconstruct_mod_eq x,
          gaussian_rns_reconstruct_mod_eq y⟩

/-- Concrete test element `z1 = 2 + 1*i`. -/
def z1_test : GaussianQsdInt := GaussianQsdInt.ofGaussian 2 1

/-- Concrete test element `z2 = 1 + 3*i`. -/
def z2_test : GaussianQsdInt := GaussianQsdInt.ofGaussian 1 3

/-- Product test element `z1 * z2 = -1 + 7*i`. -/
def z12_test : GaussianQsdInt := GaussianQsdInt.mulGaussian z1_test z2_test

/-- Concrete CRT certificate theorem for `RnsInt` and `GaussianQsdInt` norm bounds:
    Certifies exact norms `N(z1) = 5`, `N(z2) = 10`, `N(z1 * z2) = 50`,
    exact Mersenne residue channels `#[5, 5, 5]`, `#[3, 10, 10]`, and `#[1, 19, 50]`,
    and CRT reconstruction modulo 27559. -/
theorem rns_crt_gaussian_norm_cert :
    -- (1) Concrete norm values and multiplicativity
    z1_test.norm = 5 ∧
    z2_test.norm = 10 ∧
    z12_test.norm = 50 ∧
    GaussianQsdInt.norm (GaussianQsdInt.mulGaussian z1_test z2_test) =
      z1_test.norm * z2_test.norm ∧
    -- (2) RNS channel residues for z1
    (gaussianToRnsMersenne z1_test).residues = #[5, 5, 5] ∧
    (gaussianToRnsMersenne z1_test).reconstruct = 5 ∧
    -- (3) RNS channel residues for z2
    (gaussianToRnsMersenne z2_test).residues = #[3, 10, 10] ∧
    (gaussianToRnsMersenne z2_test).reconstruct = 10 ∧
    -- (4) RNS channel residues for z1 * z2
    (gaussianToRnsMersenne z12_test).residues = #[1, 19, 50] ∧
    (gaussianToRnsMersenne z12_test).reconstruct = 50 ∧
    -- (5) CRT remainder verification modulo channel moduli
    (gaussianToRnsMersenne z12_test).reconstruct % 7 = 1 ∧
    (gaussianToRnsMersenne z12_test).reconstruct % 31 = 19 ∧
    (gaussianToRnsMersenne z12_test).reconstruct % 127 = 50 := by
  have hz1_norm : z1_test.norm = 5 := by decide
  have hz2_norm : z2_test.norm = 10 := by decide
  have hz12_norm : z12_test.norm = 50 := by decide
  have hmul : GaussianQsdInt.norm (GaussianQsdInt.mulGaussian z1_test z2_test) =
      z1_test.norm * z2_test.norm := by
    rw [gaussian_qsd_norm_multiplicative]
  have hz1_res : (gaussianToRnsMersenne z1_test).residues = #[5, 5, 5] := by decide
  have hz1_rec : (gaussianToRnsMersenne z1_test).reconstruct = 5 := by
    have h := rnsInt_reconstruct_mersenne_eq 5 5 5 (gaussianToRnsMersenne z1_test) hz1_res rfl
    rw [h]; decide
  have hz2_res : (gaussianToRnsMersenne z2_test).residues = #[3, 10, 10] := by decide
  have hz2_rec : (gaussianToRnsMersenne z2_test).reconstruct = 10 := by
    have h := rnsInt_reconstruct_mersenne_eq 3 10 10 (gaussianToRnsMersenne z2_test) hz2_res rfl
    rw [h]; decide
  have hz12_res : (gaussianToRnsMersenne z12_test).residues = #[1, 19, 50] := by decide
  have hz12_rec : (gaussianToRnsMersenne z12_test).reconstruct = 50 := by
    have h := rnsInt_reconstruct_mersenne_eq 1 19 50 (gaussianToRnsMersenne z12_test) hz12_res rfl
    rw [h]; decide
  refine ⟨hz1_norm, hz2_norm, hz12_norm, hmul,
          hz1_res, hz1_rec,
          hz2_res, hz2_rec,
          hz12_res, hz12_rec,
          by decide, by decide, by decide⟩

end LeanAsm.QuasiRiemann.RnsGaussianNormBridge

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/RnsGaussianNormBridge.lean
