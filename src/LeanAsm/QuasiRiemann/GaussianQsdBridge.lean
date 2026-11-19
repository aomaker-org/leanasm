-- Path: leanasm/src/LeanAsm/QuasiRiemann/GaussianQsdBridge.lean
-- Integral (Int) Gaussian QSD[1-4] Slices, Norm Multiplicativity & Hensel Prime-Tower Links.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.Valuation.QsdHenselTower
import LeanAsm.QuasiRiemann.QsdAlgebraBridge

namespace QuasiRiemann

open LeanAsm.QuasiRiemann.RNS
open QuasiRiemann.Valuation

/-!
# Integral Gaussian QSD[1-4] Slices, Norm Multiplicativity & Hensel Bridge

Formalization of the integral (`Int`) 6-basis slice `GaussianQsdInt` over `(a, b, c, d, e, f) : Int`
corresponding to the integer ring analog of `QsdTrunc6` (`a + b i + c j + d k + e L + f m`).

Key properties established constructively:
1. `GaussianQsdInt`: Integer 6-basis coordinate record with projection, addition, and multiplication.
2. Canonical Gaussian embedding `ofGaussian`: `(a, b) ↦ (a, b, 0, 0, 0, 0)`.
3. Gaussian norm on the `(a, b, 0, 0, 0, 0)` slice: `norm z = a^2 + b^2`.
4. Constructive algebraic norm multiplicativity: `norm (z1 * z2) = norm z1 * norm z2`.
5. Bridge connecting integral Gaussian QSD slices to `QSD[1-4]` algebra, `RnsInt` residue channels,
   and `QsdHenselTower` prime-power tangent lifts / nilpotent remainder bounds.
-/

/-- Integral 6-basis element representing `a + b i + c j + d k + e L + f m` with `Int` coordinates. -/
structure GaussianQsdInt where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  deriving Repr, DecidableEq

/-- Coordinate projection for `GaussianQsdInt`. -/
def GaussianQsdInt.project (x : GaussianQsdInt) : Int × Int × Int × Int × Int × Int :=
  (x.a, x.b, x.c, x.d, x.e, x.f)

/-- Coordinate-wise addition on `GaussianQsdInt`. -/
def GaussianQsdInt.add (x y : GaussianQsdInt) : GaussianQsdInt :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e, x.f + y.f⟩

instance : Add GaussianQsdInt := ⟨GaussianQsdInt.add⟩

/-- Truncated integer multiplication on `GaussianQsdInt` consistent with `QsdTrunc6.mulTrunc6`. -/
def GaussianQsdInt.mulTrunc (x y : GaussianQsdInt) : GaussianQsdInt :=
  ⟨x.a * y.a,
   x.a * y.b + x.b * y.a,
   x.a * y.c + x.c * y.a,
   x.a * y.d + x.d * y.a,
   x.a * y.e + x.e * y.a + x.b * y.b,
   x.a * y.f + x.f * y.a + x.e * y.b⟩

/-- Standard Gaussian multiplication on the `(a, b, 0, 0, 0, 0)` integral slice
    ` (a1 + b1 i) * (a2 + b2 i) = (a1 a2 - b1 b2) + (a1 b2 + b1 a2) i `. -/
def GaussianQsdInt.mulGaussian (x y : GaussianQsdInt) : GaussianQsdInt :=
  ⟨x.a * y.a - x.b * y.b,
   x.a * y.b + x.b * y.a,
   0, 0, 0, 0⟩

/-- Canonical embedding of Gaussian integers `(a, b)` into `GaussianQsdInt`. -/
def GaussianQsdInt.ofGaussian (a b : Int) : GaussianQsdInt :=
  ⟨a, b, 0, 0, 0, 0⟩

/-- Predicate characterizing elements residing entirely in the Gaussian `(a, b, 0, 0, 0, 0)` slice. -/
def GaussianQsdInt.isGaussianSlice (x : GaussianQsdInt) : Prop :=
  x.c = 0 ∧ x.d = 0 ∧ x.e = 0 ∧ x.f = 0

/-- Gaussian norm `N(a + b i) = a^2 + b^2` on `GaussianQsdInt`. -/
def GaussianQsdInt.norm (x : GaussianQsdInt) : Int :=
  x.a * x.a + x.b * x.b

/-- Constructive multiplicativity of the Gaussian norm on integral Gaussian slices:
    `(a1^2 + b1^2) * (a2^2 + b2^2) = (a1 a2 - b1 b2)^2 + (a1 b2 + b1 a2)^2`. -/
theorem gaussian_qsd_norm_multiplicative (x y : GaussianQsdInt) :
    GaussianQsdInt.norm (GaussianQsdInt.mulGaussian x y) =
      GaussianQsdInt.norm x * GaussianQsdInt.norm y := by
  dsimp [GaussianQsdInt.norm, GaussianQsdInt.mulGaussian]
  simp only [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add]
  have h1 : (x.a * y.a) * (x.b * y.b) = (x.a * x.b) * (y.a * y.b) := by ac_rfl
  have h1a : (x.b * y.b) * (x.a * y.a) = (x.a * x.b) * (y.a * y.b) := by ac_rfl
  have h2 : (x.a * y.b) * (x.b * y.a) = (x.a * x.b) * (y.a * y.b) := by ac_rfl
  have h2a : (x.b * y.a) * (x.a * y.b) = (x.a * x.b) * (y.a * y.b) := by ac_rfl
  have h3 : (x.a * y.a) * (x.a * y.a) = (x.a * x.a) * (y.a * y.a) := by ac_rfl
  have h4 : (x.b * y.b) * (x.b * y.b) = (x.b * x.b) * (y.b * y.b) := by ac_rfl
  have h5 : (x.a * y.b) * (x.a * y.b) = (x.a * x.a) * (y.b * y.b) := by ac_rfl
  have h6 : (x.b * y.a) * (x.b * y.a) = (x.b * x.b) * (y.a * y.a) := by ac_rfl
  rw [h1, h1a, h2, h2a, h3, h4, h5, h6]
  omega

/-- Conversion from `GaussianQsdInt` to rational `QsdTrunc6`. -/
def GaussianQsdInt.toQsdTrunc6 (x : GaussianQsdInt) : QsdTrunc6 :=
  ⟨QRat.ofInt x.a, QRat.ofInt x.b, QRat.ofInt x.c,
   QRat.ofInt x.d, QRat.ofInt x.e, QRat.ofInt x.f⟩

/-- Integer basis element `b` (coordinate corresponding to `i`). -/
def gaussian_b_basis : GaussianQsdInt :=
  ⟨0, 1, 0, 0, 0, 0⟩

/-- Constructive associativity defect on `GaussianQsdInt` matching
    `qsd2_truncation_associativity_defect`. -/
theorem gaussian_qsd_truncation_defect :
    (gaussian_b_basis.mulTrunc gaussian_b_basis).mulTrunc gaussian_b_basis ≠
      gaussian_b_basis.mulTrunc (gaussian_b_basis.mulTrunc gaussian_b_basis) ∧
    ((gaussian_b_basis.mulTrunc gaussian_b_basis).mulTrunc gaussian_b_basis).f = 1 ∧
    (gaussian_b_basis.mulTrunc (gaussian_b_basis.mulTrunc gaussian_b_basis)).f = 0 := by
  decide

/-- Embedding a Gaussian norm value into an `RnsInt 3` channel across moduli `[7, 31, 127]`. -/
def gaussianNormToRns3 (z : GaussianQsdInt) (_h_nonneg : 0 ≤ z.norm) : RnsInt 3 :=
  let n := z.norm.toNat
  { residues := #[n % 7, n % 31, n % 127],
    moduli := #[7, 31, 127],
    h_len := rfl,
    h_mod_len := rfl }

/-- Constructive bridge theorem connecting integral Gaussian QSD slices, Gaussian norm
    multiplicativity, `QSD[1-4]` algebra, `RnsInt` residue channels, and Hensel tower lifts. -/
theorem gaussian_qsd_hensel_tower_bridge :
    (∀ (x y : GaussianQsdInt),
      GaussianQsdInt.norm (GaussianQsdInt.mulGaussian x y) =
        GaussianQsdInt.norm x * GaussianQsdInt.norm y) ∧
    (let z1 := GaussianQsdInt.ofGaussian 2 1
     let z2 := GaussianQsdInt.ofGaussian 1 3
     GaussianQsdInt.norm z1 = 5 ∧
     GaussianQsdInt.norm z2 = 10 ∧
     GaussianQsdInt.norm (GaussianQsdInt.mulGaussian z1 z2) = 50) ∧
    ((gaussian_b_basis.mulTrunc gaussian_b_basis).mulTrunc gaussian_b_basis ≠
        gaussian_b_basis.mulTrunc (gaussian_b_basis.mulTrunc gaussian_b_basis) ∧
     ((gaussian_b_basis.mulTrunc gaussian_b_basis).mulTrunc gaussian_b_basis).f = 1) ∧
    (∀ (p k x t : Nat) (_hp : 2 ≤ p) (_hk : 1 ≤ k),
      let pk := p ^ k
      let x_lift := x + t * pk
      (x_lift % pk = x % pk) ∧
      ((t * pk) * (t * pk)) % (pk * pk) = 0) ∧
    (∀ (p : Nat) (hp : 2 ≤ p) (k : Nat) (_hk : 1 ≤ k),
      let m := p ^ k
      let m2 := m * m
      have hm_pos : 0 < m := pow_pos_of_ge_two hp k
      have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
      let tan_elem := QsdModRing.ofNat m2 hm2_pos m
      (QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
      (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val)) ∧
    ((mersenneA.reconstruct % 7 = 3) ∧
     (mersenneA.reconstruct % 31 = 25) ∧
     (mersenneA.reconstruct % 127 = 51)) := by
  refine ⟨gaussian_qsd_norm_multiplicative, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨gaussian_qsd_truncation_defect.1, gaussian_qsd_truncation_defect.2.1⟩
  · intro p k x t hp hk
    have hstep := qsd4_hensel_tangent_lift_step p k x t hp hk
    exact ⟨hstep.1, hstep.2.1⟩
  · intro p hp k hk
    exact qsd4_prime_tower_nilpotent_remainder_bound p hp k hk
  · exact qsd4_rns_channel_crt_decomposition mersenneA rfl rfl

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/GaussianQsdBridge.lean
