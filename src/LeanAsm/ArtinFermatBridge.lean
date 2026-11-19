-- Path: leanasm/src/LeanAsm/ArtinFermatBridge.lean
-- GL(1) Artin factorization of Fermat-tower Euler factors and MiniVM 4-point NTT orthogonality.
-- Max Column: 120 Columns

import LeanAsm.EulerFactorNonVanishing
import LeanAsm.MiniVMNttBridge

namespace ArtinFermatBridge

open EulerFactorNonVanishing
open NttArithmetic
open MiniVM
open MiniVMNttBridge

-- =============================================================================
-- Part 1: Fermat-Tower GL(1) Artin Character Specifications
-- =============================================================================

/-- Specification for Fermat-tower primes `F_k = 2^(2^k) + 1 ∈ {5, 17, 257, 65537}`
with Galois degree `φ(F_k) = F_k - 1 = 2 * splittingDeg` and order-4 character
generator `ω₄ ∈ {2, 4, 16, 256}` (`ω₄^2 ≡ -1 mod F_k`). -/
structure ArtinFermatCharacterSpec where
  fermatIndex : Nat
  primeMod : Nat
  galoisOrder : Nat
  splittingDeg : Nat
  omega4 : Nat
  invOmega4 : Nat
  invFour : Nat
  deriving DecidableEq, Repr

/-- Constructive validity predicate aligning `ArtinFermatCharacterSpec` with both
Fermat cyclotomic arithmetic in `EulerFactorNonVanishing` and order-4 modular NTT
parameters in `MiniVMNttBridge.FermatNtt4Spec`. -/
def ArtinFermatCharacterSpec.Valid (spec : ArtinFermatCharacterSpec) : Prop :=
  1 ≤ spec.fermatIndex ∧
  spec.primeMod = fermatNumber spec.fermatIndex ∧
  1 < spec.primeMod ∧
  spec.galoisOrder = spec.primeMod - 1 ∧
  spec.splittingDeg = fermatCyclotomicSplittingDeg spec.fermatIndex ∧
  spec.galoisOrder = 2 * spec.splittingDeg ∧
  (spec.omega4 * spec.omega4 + 1) % spec.primeMod = 0 ∧
  (spec.omega4 * spec.invOmega4) % spec.primeMod = 1 ∧
  (4 * spec.invFour) % spec.primeMod = 1

/-- Project an `ArtinFermatCharacterSpec` to a `MiniVMNttBridge.FermatNtt4Spec`. -/
def ArtinFermatCharacterSpec.toNttSpec (spec : ArtinFermatCharacterSpec) :
    FermatNtt4Spec :=
  { p := spec.primeMod
    omega4 := spec.omega4
    invOmega4 := spec.invOmega4
    invFour := spec.invFour }

/-- Valid Artin-Fermat specs induce valid `MiniVMNttBridge.FermatNtt4Spec` instances. -/
theorem ArtinFermatCharacterSpec.toNttSpec_valid (spec : ArtinFermatCharacterSpec)
    (hspec : spec.Valid) :
    spec.toNttSpec.Valid := by
  rcases hspec with ⟨_, _, hp1, _, _, _, hsq, hwi, h4i⟩
  exact ⟨hp1, hsq, hwi, h4i⟩

/-- Concrete GL(1) Artin-Fermat spec for `F_1 = 5` (`φ = 4`, `g = 2`, `ω₄ = 2`). -/
def artinFermatSpec5 : ArtinFermatCharacterSpec :=
  { fermatIndex := 1
    primeMod := 5
    galoisOrder := 4
    splittingDeg := 2
    omega4 := 2
    invOmega4 := 3
    invFour := 4 }

/-- Concrete GL(1) Artin-Fermat spec for `F_2 = 17` (`φ = 16`, `g = 8`, `ω₄ = 4`). -/
def artinFermatSpec17 : ArtinFermatCharacterSpec :=
  { fermatIndex := 2
    primeMod := 17
    galoisOrder := 16
    splittingDeg := 8
    omega4 := 4
    invOmega4 := 13
    invFour := 13 }

/-- Concrete GL(1) Artin-Fermat spec for `F_3 = 257` (`φ = 256`, `g = 128`, `ω₄ = 16`). -/
def artinFermatSpec257 : ArtinFermatCharacterSpec :=
  { fermatIndex := 3
    primeMod := 257
    galoisOrder := 256
    splittingDeg := 128
    omega4 := 16
    invOmega4 := 241
    invFour := 193 }

/-- Concrete GL(1) Artin-Fermat spec for `F_4 = 65537` (`φ = 65536`, `g = 32768`, `ω₄ = 256`). -/
def artinFermatSpec65537 : ArtinFermatCharacterSpec :=
  { fermatIndex := 4
    primeMod := 65537
    galoisOrder := 65536
    splittingDeg := 32768
    omega4 := 256
    invOmega4 := 65281
    invFour := 49153 }

/-- All four Fermat-tower GL(1) Artin character specifications (`F_1..F_4`). -/
def artinFermatTowerSpecs : List ArtinFermatCharacterSpec :=
  [artinFermatSpec5, artinFermatSpec17, artinFermatSpec257, artinFermatSpec65537]

theorem artinFermatSpec5_valid : artinFermatSpec5.Valid := by
  dsimp [ArtinFermatCharacterSpec.Valid, artinFermatSpec5,
         fermatNumber, fermatCyclotomicSplittingDeg]
  decide

theorem artinFermatSpec17_valid : artinFermatSpec17.Valid := by
  dsimp [ArtinFermatCharacterSpec.Valid, artinFermatSpec17,
         fermatNumber, fermatCyclotomicSplittingDeg]
  decide

theorem artinFermatSpec257_valid : artinFermatSpec257.Valid := by
  dsimp [ArtinFermatCharacterSpec.Valid, artinFermatSpec257,
         fermatNumber, fermatCyclotomicSplittingDeg]
  decide

theorem artinFermatSpec65537_valid : artinFermatSpec65537.Valid := by
  dsimp [ArtinFermatCharacterSpec.Valid, artinFermatSpec65537,
         fermatNumber, fermatCyclotomicSplittingDeg]
  decide

/-- Every Fermat-tower spec in `[5, 17, 257, 65537]` satisfies `ArtinFermatCharacterSpec.Valid`. -/
theorem artinFermatTowerSpecs_valid :
    ∀ spec ∈ artinFermatTowerSpecs, spec.Valid := by
  intro spec hmem
  dsimp [artinFermatTowerSpecs] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact artinFermatSpec5_valid
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · exact artinFermatSpec17_valid
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact artinFermatSpec257_valid
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact artinFermatSpec65537_valid
        · contradiction

-- =============================================================================
-- Part 2: Modular Order-4 Helpers
-- =============================================================================

private theorem emod_eq_of_dvd_sub {p a b : Int} (h : p ∣ (a - b)) :
    a % p = b % p := by
  rcases h with ⟨k, hk⟩
  have heq : a = b + p * k := by omega
  rw [heq, Int.add_mul_emod_self_left]

private theorem w_sq_dvd_add_one {p w : Nat} (hsq : (w * w + 1) % p = 0) :
    (p : Int) ∣ ((w : Int) * (w : Int) + 1) := by
  have hmod : (((w * w + 1 : Nat) : Int)) % (p : Int) = 0 := by
    rw [← Int.natCast_emod, hsq]
    rfl
  exact Int.dvd_of_emod_eq_zero hmod

private theorem w_sq_mod_neg_one {p w : Nat} (hsq : (w * w + 1) % p = 0) :
    ((w : Int) * (w : Int)) % (p : Int) = (-1 : Int) % (p : Int) := by
  apply emod_eq_of_dvd_sub
  have heq : (w : Int) * (w : Int) - (-1) = (w : Int) * (w : Int) + 1 := by omega
  rw [heq]
  exact w_sq_dvd_add_one hsq

private theorem w_cube_mod_neg_w {p w : Nat} (hsq : (w * w + 1) % p = 0) :
    ((w : Int) ^ 3) % (p : Int) = (-(w : Int)) % (p : Int) := by
  apply emod_eq_of_dvd_sub
  have hw3 : (w : Int) ^ 3 - (-(w : Int)) = ((w : Int) * (w : Int) + 1) * (w : Int) := by
    have hp3 : (w : Int) ^ 3 = ((w : Int) * (w : Int)) * (w : Int) := by
      simp [Int.pow_succ, Int.pow_zero]
    rw [hp3, Int.add_mul, Int.one_mul]
    omega
  rw [hw3]
  exact Int.dvd_mul_of_dvd_left (w_sq_dvd_add_one hsq)

private theorem invW_mod_neg_w {p w invW : Nat} (hp : 1 < p)
    (hsq : (w * w + 1) % p = 0) (hwi : (w * invW) % p = 1) :
    (invW : Int) % (p : Int) = (-(w : Int)) % (p : Int) := by
  have hdvd1 : (p : Int) ∣ ((w : Int) * (invW : Int) - 1) := by
    apply Int.dvd_of_emod_eq_zero
    have hmul : (((w * invW : Nat) : Int)) % (p : Int) = (1 : Int) % (p : Int) := by
      have h1 : (((w * invW : Nat) : Int)) % (p : Int) = ((1 : Nat) : Int) := by
        rw [← Int.natCast_emod, hwi]
      have h2 : ((1 : Nat) : Int) = (1 : Int) % (p : Int) := by
        symm
        exact Int.emod_eq_of_lt (by omega) (by omega)
      exact h1.trans h2
    have hcast : ((w : Int) * (invW : Int)) % (p : Int) = (1 : Int) % (p : Int) := hmul
    rw [Int.sub_emod, hcast, Int.sub_self, Int.zero_emod]
  have hdiff : (invW : Int) - (-(w : Int)) =
      ((w : Int) * (w : Int) + 1) * (invW : Int) -
        ((w : Int) * (invW : Int) - 1) * (w : Int) := by
    rw [Int.add_mul, Int.sub_mul, Int.one_mul, Int.one_mul]
    have hc : (w : Int) * (w : Int) * (invW : Int) =
        (w : Int) * (invW : Int) * (w : Int) := by
      ac_rfl
    rw [hc]
    omega
  apply emod_eq_of_dvd_sub
  rw [hdiff]
  exact Int.dvd_sub
    (Int.dvd_mul_of_dvd_left (w_sq_dvd_add_one hsq))
    (Int.dvd_mul_of_dvd_left hdvd1)

private theorem invW_sq_add_one_mod {p w invW : Nat} (hp : 1 < p)
    (hsq : (w * w + 1) % p = 0) (hwi : (w * invW) % p = 1) :
    (invW * invW + 1) % p = 0 := by
  have hinv := invW_mod_neg_w hp hsq hwi
  have hw2 := w_sq_mod_neg_one hsq
  have hint : (((invW * invW + 1 : Nat) : Int)) % (p : Int) = 0 := by
    have hcast : ((invW * invW + 1 : Nat) : Int) = (invW : Int) * (invW : Int) + 1 := rfl
    rw [hcast, Int.add_emod, Int.mul_emod, hinv, ← Int.mul_emod, Int.neg_mul_neg, hw2,
        ← Int.add_emod]
    simp
  rw [← Int.natCast_emod] at hint
  exact Int.ofNat.inj hint

private theorem w_pow_mod_int (p w : Nat) (hsq : (w * w + 1) % p = 0) :
    (((w ^ 0 : Nat) : Int) % (p : Int) = 1 % (p : Int)) ∧
    (((w ^ 1 : Nat) : Int) % (p : Int) = (w : Int) % (p : Int)) ∧
    (((w ^ 2 : Nat) : Int) % (p : Int) = (-1 : Int) % (p : Int)) ∧
    (((w ^ 3 : Nat) : Int) % (p : Int) = (-(w : Int)) % (p : Int)) ∧
    (((w ^ 4 : Nat) : Int) % (p : Int) = 1 % (p : Int)) ∧
    (((w ^ 6 : Nat) : Int) % (p : Int) = (-1 : Int) % (p : Int)) ∧
    (((w ^ 9 : Nat) : Int) % (p : Int) = (w : Int) % (p : Int)) := by
  have hw2 : (((w ^ 2 : Nat) : Int)) % (p : Int) = (-1 : Int) % (p : Int) := by
    have h : (w ^ 2 : Nat) = w * w := by simp [Nat.pow_succ, Nat.pow_zero]
    rw [h]
    exact w_sq_mod_neg_one hsq
  have hw3 : (((w ^ 3 : Nat) : Int)) % (p : Int) = (-(w : Int)) % (p : Int) := by
    have h : ((w ^ 3 : Nat) : Int) = (w : Int) ^ 3 := by
      simp [Nat.pow_succ, Nat.pow_zero, Int.pow_succ, Int.pow_zero]
    rw [h]
    exact w_cube_mod_neg_w hsq
  have hw4 : (((w ^ 4 : Nat) : Int)) % (p : Int) = (1 : Int) % (p : Int) := by
    have h4 : w ^ 4 = w ^ 2 * w ^ 2 := by
      rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add]
    have hc4 : ((w ^ 4 : Nat) : Int) = ((w ^ 2 : Nat) : Int) * ((w ^ 2 : Nat) : Int) := by
      rw [h4]; rfl
    rw [hc4, Int.mul_emod, hw2, ← Int.mul_emod]
    simp
  have hw6 : (((w ^ 6 : Nat) : Int)) % (p : Int) = (-1 : Int) % (p : Int) := by
    have h6 : w ^ 6 = w ^ 4 * w ^ 2 := by
      rw [show (6 : Nat) = 4 + 2 from rfl, Nat.pow_add]
    have hc6 : ((w ^ 6 : Nat) : Int) = ((w ^ 4 : Nat) : Int) * ((w ^ 2 : Nat) : Int) := by
      rw [h6]; rfl
    rw [hc6, Int.mul_emod, hw4, hw2, ← Int.mul_emod]
    simp
  have hw9 : (((w ^ 9 : Nat) : Int)) % (p : Int) = (w : Int) % (p : Int) := by
    have h9 : w ^ 9 = w ^ 4 * w ^ 4 * w := by
      rw [show (9 : Nat) = 4 + 4 + 1 from rfl, Nat.pow_add, Nat.pow_add, Nat.pow_one]
    have hc9 : ((w ^ 9 : Nat) : Int) =
        ((w ^ 4 : Nat) : Int) * ((w ^ 4 : Nat) : Int) * (w : Int) := by
      rw [h9]; rfl
    rw [hc9, Int.mul_emod (((w ^ 4 : Nat) : Int) * ((w ^ 4 : Nat) : Int)),
        Int.mul_emod ((w ^ 4 : Nat) : Int), hw4, ← Int.mul_emod 1 1, Int.one_mul,
        ← Int.mul_emod, Int.one_mul]
  refine ⟨by simp, by simp, hw2, hw3, hw4, hw6, hw9⟩

private theorem eq_of_lt_of_int_emod_eq {p a b : Nat} (ha : a < p) (hb : b < p)
    (h : (a : Int) % (p : Int) = (b : Int) % (p : Int)) : a = b := by
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg a) (Int.ofNat_lt.mpr ha),
      Int.emod_eq_of_lt (Int.natCast_nonneg b) (Int.ofNat_lt.mpr hb)] at h
  exact Int.ofNat.inj h

private theorem emod_add_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x + y) % p = (z + u) % p := by
  rw [Int.add_emod, hx, hy, ← Int.add_emod]

private theorem emod_sub_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x - y) % p = (z - u) % p := by
  rw [Int.sub_emod, hx, hy, ← Int.sub_emod]

private theorem emod_mul_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x * y) % p = (z * u) % p := by
  rw [Int.mul_emod, hx, hy, ← Int.mul_emod]

private theorem nat_mod_cast_emod (p a : Nat) :
    (((a % p : Nat) : Int)) % (p : Int) = (a : Int) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod]

-- =============================================================================
-- Part 3: GL(1) Artin Euler-Factor Factorization & Cyclotomic Collapse
-- =============================================================================

/-- Cleared-denominator Artin character Euler product `∏_{χ ∈ chis} (d - χ * n)`. -/
def artinCharProductEval (chis : List Int) (d n : Int) : Int :=
  match chis with
  | [] => 1
  | chi :: rest => (d - chi * n) * artinCharProductEval rest d n

/-- When a prime `p ≡ 1 (mod F_k)` splits completely, every Galois character
evaluates to `1`, collapsing the cleared Artin Euler product to `(d - n)^g`. -/
theorem artinCharProductEval_replicate_one (g : Nat) (d n : Int) :
    artinCharProductEval (List.replicate g 1) d n = (d - n) ^ g := by
  induction g with
  | zero =>
    dsimp [List.replicate, artinCharProductEval]
    simp
  | succ k ih =>
    dsimp [List.replicate, artinCharProductEval]
    rw [Int.one_mul, ih, Int.mul_comm (d - n), ← Int.pow_succ]

/-- Degree-4 Artin product over the order-4 character subgroup `{1, ω, ω^2, ω^3}`
evaluated at `T : Int`: `∏_{j=0}^{3} (1 - ω^j * T)`. -/
def artinOrder4EulerPoly (w T : Int) : Int :=
  (1 - T) * (1 - w * T) * (1 - w ^ 2 * T) * (1 - w ^ 3 * T)

/-- Cleared-denominator GL(1) Artin split Euler-factor collapse:
for any valid `ArtinFermatCharacterSpec` (`F_k ∈ {5, 17, 257, 65537}`,
`φ(F_k) = 2 * g_k`) and any admissible `EulerLocalFactorSpec`:
1. The `φ(F_k)`-character Artin product at trivial character `1` collapses to
   `(d - r)^φ(F_k) = (d - r)^(2 * g_k)`.
2. Positivity and lower-bound dominance hold constructively in terms of the
   Dedekind norm `(d - zx)^2 + zy^2`.
3. Across `{5, 17, 257, 65537}`, both `EulerFactorNonVanishing.FermatTowerStripCert`
   and `fermat_tower_dedekind_euler_strip_certs` certify strictly positive
   strip lower bounds at `σ ∈ {1/2, 3/4, 1}`. -/
theorem artin_split_euler_factor_collapse
    (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (f : EulerLocalFactorSpec) (hf : ValidEulerLocalFactorSpec f) :
    artinCharProductEval (List.replicate spec.galoisOrder 1) f.d f.rNum =
      (f.d - f.rNum) ^ spec.galoisOrder ∧
    (f.d - f.rNum) ^ spec.galoisOrder =
      (f.d - f.rNum) ^ (2 * spec.splittingDeg) ∧
    0 < (f.d - f.rNum) ^ spec.galoisOrder ∧
    (f.d - f.rNum) ^ spec.galoisOrder ≤
      ((f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy) ^ spec.splittingDeg ∧
    0 < (f.d * f.d) ^ spec.splittingDeg ∧
    FermatTowerStripCert ∧
    (artinFermatTowerSpecs.map (·.primeMod) = fermatTowerPrimes ∧
     artinFermatTowerSpecs.map (·.splittingDeg) = fermatTowerSplittingDegs ∧
     artinFermatTowerSpecs.map (·.galoisOrder) = [4, 16, 256, 65536] ∧
     (artinFermatTowerSpecs.map (·.galoisOrder)).prod = 2 ^ 30) ∧
    (∀ zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int,
      (zx5 * zx5 + zy5 * zy5 ≤ 1 →
       zx17 * zx17 + zy17 * zy17 ≤ 1 →
       zx257 * zx257 + zy257 * zy257 ≤ 1 →
       zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
       let fsOne : List CyclotomicSplitFactorSpec :=
         [ ⟨⟨5, 5, 1, zx5, zy5⟩, 2⟩,
           ⟨⟨17, 17, 1, zx17, zy17⟩, 8⟩,
           ⟨⟨257, 257, 1, zx257, zy257⟩, 128⟩,
           ⟨⟨65537, 65537, 1, zx65537, zy65537⟩, 32768⟩ ]
       0 < cyclotomicProdMarginPow fsOne ∧
       cyclotomicProdMarginPow fsOne ≤ cyclotomicProdNormPow fsOne ∧
       cyclotomicProdDenPow fsOne < 256 * cyclotomicProdNormPow fsOne)) := by
  have hcol := artinCharProductEval_replicate_one spec.galoisOrder f.d f.rNum
  rcases hspec with ⟨_, _, _, _, hsd, hgd, _, _, _⟩
  have hgk1 : 1 ≤ spec.splittingDeg := by
    rw [hsd]
    exact Nat.one_le_two_pow
  have hded := cyclotomic_split_euler_factor_nonvanishing f hf spec.splittingDeg hgk1
  rw [← hgd] at hded
  refine ⟨hcol, ?_, hded.1, hded.2.1, hded.2.2,
          fermat_tower_euler_product_strip_certs, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hgd]
  · intro zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 h1 h2 h3 h4
    exact (fermat_tower_dedekind_euler_strip_certs
      zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537).2.2 h1 h2 h3 h4

/-- Generic modular identity: whenever `(w^2 + 1) % p = 0`, the 4-character Artin
Euler product satisfies `∏_{j=0}^{3} (1 - w^j * T) ≡ 1 - T^4 (mod p)` for every `T : Int`. -/
theorem artinOrder4EulerPoly_mod_eq {p w : Nat} (hsq : (w * w + 1) % p = 0) (T : Int) :
    artinOrder4EulerPoly w T % (p : Int) = (1 - T ^ 4) % (p : Int) := by
  have hdvd : (p : Int) ∣ ((w : Int) * (w : Int) + 1) := w_sq_dvd_add_one hsq
  have hw2 : (w : Int) ^ 2 = (w : Int) * (w : Int) := by
    simp [Int.pow_succ, Int.pow_zero]
  have hw3 : (w : Int) ^ 3 = (w : Int) * ((w : Int) * (w : Int)) := by
    simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc]
  have hf2 : (1 - (w : Int) ^ 2 * T) % (p : Int) = (1 + T) % (p : Int) := by
    apply emod_eq_of_dvd_sub
    have hdiff : (1 - (w : Int) ^ 2 * T) - (1 + T) =
        ((w : Int) * (w : Int) + 1) * (-T) := by
      rw [hw2, Int.add_mul, Int.one_mul, Int.mul_neg]
      omega
    rw [hdiff]
    exact Int.dvd_mul_of_dvd_left hdvd
  have hf3 : (1 - (w : Int) ^ 3 * T) % (p : Int) = (1 + (w : Int) * T) % (p : Int) := by
    apply emod_eq_of_dvd_sub
    have ha : (w : Int) * ((w : Int) * (w : Int)) * T =
        ((w : Int) * (w : Int)) * ((w : Int) * T) := by ac_rfl
    have hdiff : (1 - (w : Int) ^ 3 * T) - (1 + (w : Int) * T) =
        ((w : Int) * (w : Int) + 1) * (-((w : Int) * T)) := by
      rw [hw3, ha, Int.add_mul, Int.one_mul, Int.mul_neg]
      omega
    rw [hdiff]
    exact Int.dvd_mul_of_dvd_left hdvd
  have hw2t2 : (1 - ((w : Int) * T) * ((w : Int) * T)) % (p : Int) =
      (1 + T * T) % (p : Int) := by
    apply emod_eq_of_dvd_sub
    have ha : ((w : Int) * T) * ((w : Int) * T) =
        ((w : Int) * (w : Int)) * (T * T) := by ac_rfl
    have hdiff : (1 - ((w : Int) * T) * ((w : Int) * T)) - (1 + T * T) =
        ((w : Int) * (w : Int) + 1) * (-(T * T)) := by
      rw [ha, Int.add_mul, Int.one_mul, Int.mul_neg]
      omega
    rw [hdiff]
    exact Int.dvd_mul_of_dvd_left hdvd
  have h12 : (1 - T) * (1 + T) = 1 - T * T := by
    rw [Int.mul_add, Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_one]
    omega
  have h34 : (1 - (w : Int) * T) * (1 + (w : Int) * T) =
      1 - ((w : Int) * T) * ((w : Int) * T) := by
    rw [Int.mul_add, Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_one]
    omega
  have hpow4 : (1 - T * T) * (1 + T * T) = 1 - T ^ 4 := by
    rw [Int.mul_add, Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_one]
    have ht4 : T ^ 4 = (T * T) * (T * T) := by
      simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc]
    rw [ht4]
    omega
  have hperm : ((1 - T) * (1 - (w : Int) * T)) * ((1 + T) * (1 + (w : Int) * T)) =
      ((1 - T) * (1 + T)) * ((1 - (w : Int) * T) * (1 + (w : Int) * T)) := by
    ac_rfl
  dsimp [artinOrder4EulerPoly]
  calc ((1 - T) * (1 - (w : Int) * T) * (1 - (w : Int) ^ 2 * T) *
        (1 - (w : Int) ^ 3 * T)) % (p : Int)
      = ((((1 - T) * (1 - (w : Int) * T)) * (1 - (w : Int) ^ 2 * T)) *
          (1 - (w : Int) ^ 3 * T)) % (p : Int) := rfl
    _ = (((((1 - T) * (1 - (w : Int) * T)) % (p : Int) *
            ((1 - (w : Int) ^ 2 * T) % (p : Int))) % (p : Int)) *
          ((1 - (w : Int) ^ 3 * T) % (p : Int))) % (p : Int) := by
            rw [Int.mul_emod _ (1 - (w : Int) ^ 3 * T),
                Int.mul_emod ((1 - T) * (1 - (w : Int) * T))]
    _ = (((((1 - T) * (1 - (w : Int) * T)) % (p : Int) *
            ((1 + T) % (p : Int))) % (p : Int)) *
          ((1 + (w : Int) * T) % (p : Int))) % (p : Int) := by
            rw [hf2, hf3]
    _ = (((1 - T) * (1 - (w : Int) * T)) * ((1 + T) * (1 + (w : Int) * T))) % (p : Int) := by
            rw [← Int.mul_emod ((1 - T) * (1 - (w : Int) * T)) (1 + T),
                ← Int.mul_emod, Int.mul_assoc]
    _ = (((1 - T) * (1 + T)) * ((1 - (w : Int) * T) * (1 + (w : Int) * T))) % (p : Int) := by
            rw [hperm]
    _ = ((1 - T * T) * (1 - ((w : Int) * T) * ((w : Int) * T))) % (p : Int) := by
            rw [h12, h34]
    _ = (((1 - T * T) % (p : Int)) *
          ((1 - ((w : Int) * T) * ((w : Int) * T)) % (p : Int))) % (p : Int) :=
            Int.mul_emod _ _ _
    _ = ((1 - T * T) * (1 + T * T)) % (p : Int) := by
            rw [hw2t2, ← Int.mul_emod]
    _ = (1 - T ^ 4) % (p : Int) := by rw [hpow4]

/-- Theorem (Order-4 Artin Cyclotomic Factorization across `{5, 17, 257, 65537}`):
Certifies that `∏_{j=0}^{3} (1 - ω₄^j T) ≡ 1 - T^4 (mod F_k)` for every valid
`ArtinFermatCharacterSpec`, and concretely across all four Fermat-tower pairs
`(F_k, ω₄) ∈ {(5, 2), (17, 4), (257, 16), (65537, 256)}` for all `T : Int`. -/
theorem artin_order4_cyclotomic_factorization :
    (∀ spec ∈ artinFermatTowerSpecs, ∀ T : Int,
      artinOrder4EulerPoly spec.omega4 T % (spec.primeMod : Int) =
        (1 - T ^ 4) % (spec.primeMod : Int)) ∧
    (∀ spec : ArtinFermatCharacterSpec, spec.Valid → ∀ T : Int,
      artinOrder4EulerPoly spec.omega4 T % (spec.primeMod : Int) =
        (1 - T ^ 4) % (spec.primeMod : Int)) := by
  refine ⟨?_, ?_⟩
  · intro spec hmem T
    have hval := artinFermatTowerSpecs_valid spec hmem
    rcases hval with ⟨_, _, _, _, _, _, hsq, _, _⟩
    exact artinOrder4EulerPoly_mod_eq hsq T
  · intro spec hval T
    rcases hval with ⟨_, _, _, _, _, _, hsq, _, _⟩
    exact artinOrder4EulerPoly_mod_eq hsq T

-- =============================================================================
-- Part 4: GL(1) Artin Character Transform = NttArithmetic.ntt4
-- =============================================================================

/-- Evaluation of the `j`-th order-4 GL(1) Artin character on the generator power
`g^i`: `χ_j(g^i) = ω₄^(i * j) mod p`. -/
def artinCharPow (p w i j : Nat) : Nat :=
  w ^ (i * j) % p

/-- Lane `j` of the 4-element GL(1) Artin Fourier transform:
`v̂_j = ∑_{i=0}^{3} χ_j(g^i) * v_i (mod p)`. -/
def artinCharTransformLane (p w : Nat) (v : Vec4) (j : Nat) : Nat :=
  (v.x0 * artinCharPow p w 0 j +
   v.x1 * artinCharPow p w 1 j +
   v.x2 * artinCharPow p w 2 j +
   v.x3 * artinCharPow p w 3 j) % p

/-- Full 4-element GL(1) Artin character Fourier transform over `ℤ/pℤ`. -/
def artinCharTransform4 (p w : Nat) (v : Vec4) : Vec4 :=
  ⟨artinCharTransformLane p w v 0,
   artinCharTransformLane p w v 1,
   artinCharTransformLane p w v 2,
   artinCharTransformLane p w v 3⟩

private theorem ntt4_lane_bounds (p w : Nat) (hp : 0 < p) (v : Vec4) :
    (ntt4 p w v).x0 < p ∧ (ntt4 p w v).x1 < p ∧
    (ntt4 p w v).x2 < p ∧ (ntt4 p w v).x3 < p := by
  dsimp [ntt4, nttButterfly2]
  exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

private theorem artinCharTransform4_lane_bounds (p w : Nat) (hp : 0 < p) (v : Vec4) :
    (artinCharTransform4 p w v).x0 < p ∧ (artinCharTransform4 p w v).x1 < p ∧
    (artinCharTransform4 p w v).x2 < p ∧ (artinCharTransform4 p w v).x3 < p := by
  dsimp [artinCharTransform4, artinCharTransformLane]
  exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

private theorem mod_add_congr_int_local (p a b : Nat) :
    (((a + b) % p : Nat) : Int) % (p : Int) = ((a : Int) + (b : Int)) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod]
  rfl

private theorem mod_sub_congr_int_local (p a b : Nat) (hp : 0 < p) :
    (((a + p - b % p) % p : Nat) : Int) % (p : Int) = ((a : Int) - (b : Int)) % (p : Int) := by
  have hle : b % p ≤ a + p := by
    have := Nat.mod_lt b hp
    omega
  rw [Int.natCast_emod, Int.emod_emod, Int.ofNat_sub hle]
  have ha : ((a + p : Nat) : Int) = (a : Int) + p := rfl
  rw [ha, Int.natCast_emod, Int.sub_emod, Int.add_emod, Int.emod_self, Int.add_zero,
      Int.emod_emod, Int.emod_emod, ← Int.sub_emod]

private theorem mod_mul_congr_int_local (p a b : Nat) :
    (((a * b) % p : Nat) : Int) % (p : Int) = ((a : Int) * (b : Int)) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod]
  rfl

private theorem lin4_emod (p a b c d ca cb cc cd ra rb rc rd : Int)
    (ha : ca % p = ra % p) (hb : cb % p = rb % p)
    (hc : cc % p = rc % p) (hd : cd % p = rd % p) :
    (a * ca + b * cb + c * cc + d * cd) % p =
      (a * ra + b * rb + c * rc + d * rd) % p := by
  rw [Int.add_emod (a * ca + b * cb + c * cc),
      Int.add_emod (a * ca + b * cb),
      Int.add_emod (a * ca),
      Int.mul_emod a ca, Int.mul_emod b cb, Int.mul_emod c cc, Int.mul_emod d cd,
      ha, hb, hc, hd,
      ← Int.mul_emod a ra, ← Int.mul_emod b rb, ← Int.mul_emod c rc, ← Int.mul_emod d rd,
      ← Int.add_emod (a * ra),
      ← Int.add_emod (a * ra + b * rb),
      ← Int.add_emod (a * ra + b * rb + c * rc)]

private theorem ntt4_mod_int_local (p w : Nat) (hp : 0 < p) (v : Vec4) :
    (((ntt4 p w v).x0 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 + ((v.x1 : Int) + v.x3)) % p) ∧
    (((ntt4 p w v).x1 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 + ((v.x1 : Int) - v.x3) * w) % p) ∧
    (((ntt4 p w v).x2 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 - ((v.x1 : Int) + v.x3)) % p) ∧
    (((ntt4 p w v).x3 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 - ((v.x1 : Int) - v.x3) * w) % p) := by
  rcases v with ⟨a, b, c, d⟩
  dsimp [ntt4, nttButterfly2]
  have he0 := mod_add_congr_int_local p a c
  have he1 := mod_sub_congr_int_local p a c hp
  have ht0 : ((↑((b + d) % p % p) : Int)) % p = ((b : Int) + d) % p :=
    (nat_mod_cast_emod p ((b + d) % p)).trans (mod_add_congr_int_local p b d)
  have ht1 : ((↑((b + p - d % p) % p * w % p) : Int)) % p = (((b : Int) - d) * w) % p :=
    (mod_mul_congr_int_local p _ w).trans (emod_mul_cancel (mod_sub_congr_int_local p b d hp) rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mod_add_congr_int_local p _ _).trans (emod_add_cancel he0 ht0)
  · exact (mod_add_congr_int_local p _ _).trans (emod_add_cancel he1 ht1)
  · exact (mod_sub_congr_int_local p _ _ hp).trans (emod_sub_cancel he0 ht0)
  · exact (mod_sub_congr_int_local p _ _ hp).trans (emod_sub_cancel he1 ht1)

private theorem artinCharTransform4_mod_int (p w : Nat) (hsq : (w * w + 1) % p = 0)
    (v : Vec4) :
    (((artinCharTransform4 p w v).x0 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 + ((v.x1 : Int) + v.x3)) % p) ∧
    (((artinCharTransform4 p w v).x1 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 + ((v.x1 : Int) - v.x3) * w) % p) ∧
    (((artinCharTransform4 p w v).x2 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 - ((v.x1 : Int) + v.x3)) % p) ∧
    (((artinCharTransform4 p w v).x3 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 - ((v.x1 : Int) - v.x3) * w) % p) := by
  rcases w_pow_mod_int p w hsq with ⟨hp0, hp1, hp2, hp3, hp4, hp6, hp9⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  have h1mod : ((1 : Int) % (p : Int)) % (p : Int) = (1 : Int) % (p : Int) :=
    Int.emod_emod 1 (p : Int)
  have hpowMod (k : Nat) (rhs : Int)
      (hk : ((w ^ k : Nat) : Int) % (p : Int) = rhs % (p : Int)) :
      (((w : Int) ^ k % (p : Int)) % (p : Int)) = rhs % (p : Int) := by
    rw [Int.emod_emod]
    exact hk
  dsimp [artinCharTransform4, artinCharTransformLane, artinCharPow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.emod_emod]
    rw [lin4_emod (p : Int) (v0 : Int) (v1 : Int) (v2 : Int) (v3 : Int)
          _ _ _ _ 1 1 1 1 h1mod h1mod h1mod h1mod]
    congr 1
    omega
  · rw [Int.emod_emod]
    rw [lin4_emod (p : Int) (v0 : Int) (v1 : Int) (v2 : Int) (v3 : Int)
          _ _ _ _ 1 (w : Int) (-1) (-(w : Int))
          h1mod (hpowMod 1 _ hp1) (hpowMod 2 _ hp2) (hpowMod 3 _ hp3)]
    congr 1
    simp only [Int.sub_mul, Int.mul_neg, Int.mul_one]
    omega
  · rw [Int.emod_emod]
    rw [lin4_emod (p : Int) (v0 : Int) (v1 : Int) (v2 : Int) (v3 : Int)
          _ _ _ _ 1 (-1) 1 (-1)
          h1mod (hpowMod 2 _ hp2) (hpowMod 4 _ hp4) (hpowMod 6 _ hp6)]
    congr 1
    simp only [Int.mul_neg, Int.mul_one]
    omega
  · rw [Int.emod_emod]
    rw [lin4_emod (p : Int) (v0 : Int) (v1 : Int) (v2 : Int) (v3 : Int)
          _ _ _ _ 1 (-(w : Int)) (-1) (w : Int)
          h1mod (hpowMod 3 _ hp3) (hpowMod 6 _ hp6) (hpowMod 9 _ hp9)]
    congr 1
    simp only [Int.sub_mul, Int.mul_neg, Int.mul_one]
    omega

/-- Generic equality of the 4-element GL(1) Artin Fourier transform and `NttArithmetic.ntt4`
whenever `0 < p` and `(w * w + 1) % p = 0`. -/
theorem artinCharTransform4_eq_ntt4_generic (p w : Nat) (hp : 0 < p)
    (hsq : (w * w + 1) % p = 0) (v : Vec4) :
    artinCharTransform4 p w v = ntt4 p w v := by
  rcases artinCharTransform4_lane_bounds p w hp v with ⟨ha0, ha1, ha2, ha3⟩
  rcases ntt4_lane_bounds p w hp v with ⟨hn0, hn1, hn2, hn3⟩
  rcases artinCharTransform4_mod_int p w hsq v with ⟨ma0, ma1, ma2, ma3⟩
  rcases ntt4_mod_int_local p w hp v with ⟨mn0, mn1, mn2, mn3⟩
  have e0 := eq_of_lt_of_int_emod_eq ha0 hn0 (ma0.trans mn0.symm)
  have e1 := eq_of_lt_of_int_emod_eq ha1 hn1 (ma1.trans mn1.symm)
  have e2 := eq_of_lt_of_int_emod_eq ha2 hn2 (ma2.trans mn2.symm)
  have e3 := eq_of_lt_of_int_emod_eq ha3 hn3 (ma3.trans mn3.symm)
  cases ha : artinCharTransform4 p w v
  cases hn : ntt4 p w v
  rw [ha] at e0 e1 e2 e3
  rw [hn] at e0 e1 e2 e3
  dsimp at e0 e1 e2 e3
  subst e0 e1 e2 e3
  rfl

/-- Theorem (`GL(1)` Artin Transform = `NttArithmetic.ntt4`):
Certifies `artinCharTransform4 spec.primeMod spec.omega4 v = ntt4 spec.primeMod spec.omega4 v`
across every `(F_k, ω₄) ∈ {(5, 2), (17, 4), (257, 16), (65537, 256)}` and every valid
`ArtinFermatCharacterSpec` / `FermatNtt4Spec`. -/
theorem artin_char_transform_eq_ntt4 :
    (∀ spec ∈ artinFermatTowerSpecs, ∀ v : Vec4,
      artinCharTransform4 spec.primeMod spec.omega4 v =
        ntt4 spec.primeMod spec.omega4 v) ∧
    (∀ spec : ArtinFermatCharacterSpec, spec.Valid → ∀ v : Vec4,
      artinCharTransform4 spec.primeMod spec.omega4 v =
        ntt4 spec.primeMod spec.omega4 v) ∧
    (∀ cfg : FermatNtt4Spec, cfg.Valid → ∀ v : Vec4,
      artinCharTransform4 cfg.p cfg.omega4 v = ntt4 cfg.p cfg.omega4 v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro spec hmem v
    rcases artinFermatTowerSpecs_valid spec hmem with ⟨_, _, hp1, _, _, _, hsq, _, _⟩
    exact artinCharTransform4_eq_ntt4_generic spec.primeMod spec.omega4
      (Nat.lt_trans Nat.zero_lt_one hp1) hsq v
  · intro spec hval v
    rcases hval with ⟨_, _, hp1, _, _, _, hsq, _, _⟩
    exact artinCharTransform4_eq_ntt4_generic spec.primeMod spec.omega4
      (Nat.lt_trans Nat.zero_lt_one hp1) hsq v
  · intro cfg hval v
    rcases hval with ⟨hp1, hsq, _, _⟩
    exact artinCharTransform4_eq_ntt4_generic cfg.p cfg.omega4
      (Nat.lt_trans Nat.zero_lt_one hp1) hsq v

-- =============================================================================
-- Part 6: MiniVM GL(1) Artin Character Orthogonality
-- =============================================================================

/-- Standard 4-vector basis element `e_i` (`1` at lane `i`, `0` elsewhere). -/
def basisVec4 (i : Nat) : Vec4 :=
  ⟨if i = 0 then 1 else 0,
   if i = 1 then 1 else 0,
   if i = 2 then 1 else 0,
   if i = 3 then 1 else 0⟩

/-- Inverse-scaled GL(1) Artin character inner product sum modulo `p`:
`inv4 * ∑_{j=0}^{3} χ_j(g^i) χ_j(g^{-m}) (mod p)`. -/
def artinCharOrthoSum (p w invW inv4 i m : Nat) : Nat :=
  (inv4 *
    (artinCharPow p w i 0 * artinCharPow p invW m 0 +
     artinCharPow p w i 1 * artinCharPow p invW m 1 +
     artinCharPow p w i 2 * artinCharPow p invW m 2 +
     artinCharPow p w i 3 * artinCharPow p invW m 3)) % p

private theorem basisVec4_lt {p : Nat} (hp : 1 < p) (i : Fin 4) :
    (basisVec4 i.val).x0 < p ∧ (basisVec4 i.val).x1 < p ∧
    (basisVec4 i.val).x2 < p ∧ (basisVec4 i.val).x3 < p := by
  have hp0 : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => refine ⟨hp, hp0, hp0, hp0⟩
  | 1 => refine ⟨hp0, hp, hp0, hp0⟩
  | 2 => refine ⟨hp0, hp0, hp, hp0⟩
  | 3 => refine ⟨hp0, hp0, hp0, hp⟩
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

private theorem intt4_eq_scaled_artinCharTransform4 (p inv4 invW : Nat)
    (hp : 1 < p) (hinvSq : (invW * invW + 1) % p = 0) (X : Vec4) :
    intt4 p inv4 invW X =
      let Y := artinCharTransform4 p invW X
      ⟨(Y.x0 * inv4) % p, (Y.x1 * inv4) % p,
       (Y.x2 * inv4) % p, (Y.x3 * inv4) % p⟩ := by
  have h0 : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hinv_ntt : artinCharTransform4 p invW X = ntt4 p invW X :=
    artinCharTransform4_eq_ntt4_generic p invW h0 hinvSq X
  rw [hinv_ntt]
  dsimp [intt4, ntt4, nttButterfly2]
  simp only [Nat.mod_mul_mod]

private theorem artinCharTransform4_basis_lane_mod (p w : Nat) (hp : 1 < p)
    (i : Fin 4) :
    artinCharTransform4 p w (basisVec4 i.val) =
      ⟨artinCharPow p w i.val 0,
       artinCharPow p w i.val 1,
       artinCharPow p w i.val 2,
       artinCharPow p w i.val 3⟩ := by
  have hlt (j : Nat) : artinCharPow p w i.val j < p :=
    Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hp)
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 =>
    simp [artinCharTransform4, artinCharTransformLane, basisVec4,
          Nat.mod_eq_of_lt (hlt 0), Nat.mod_eq_of_lt (hlt 1),
          Nat.mod_eq_of_lt (hlt 2), Nat.mod_eq_of_lt (hlt 3)]
  | _ + 4 => omega

private theorem artinCharOrthoSum_eq_intt4_lane (p w invW inv4 : Nat) (hp : 1 < p)
    (hinvSq : (invW * invW + 1) % p = 0) (i m : Fin 4) :
    let Y := intt4 p inv4 invW (artinCharTransform4 p w (basisVec4 i.val))
    artinCharOrthoSum p w invW inv4 i.val m.val =
      match m.val with
      | 0 => Y.x0
      | 1 => Y.x1
      | 2 => Y.x2
      | _ => Y.x3 := by
  rw [intt4_eq_scaled_artinCharTransform4 p inv4 invW hp hinvSq]
  rw [artinCharTransform4_basis_lane_mod p w hp i]
  rcases m with ⟨m, hm⟩
  match m with
  | 0 | 1 | 2 | 3 =>
    dsimp [artinCharOrthoSum, artinCharTransform4, artinCharTransformLane, artinCharPow]
    rw [Nat.mul_comm inv4]
    simp only [Nat.mod_mul_mod]
    try rfl
  | _ + 4 => omega

private theorem basisVec4_lane_eq (v : Vec4) (i m : Fin 4) (hv : v = basisVec4 i.val) :
    (match m.val with
     | 0 => v.x0
     | 1 => v.x1
     | 2 => v.x2
     | _ => v.x3) = (if i.val = m.val then 1 else 0) := by
  subst hv
  rcases i with ⟨i, hi⟩
  rcases m with ⟨m, hm⟩
  match i, m with
  | 0, 0 | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 1 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 2 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 | 3, 3 => simp [basisVec4]
  | _ + 4, _ => omega
  | _, _ + 4 => omega

/-- Theorem (`MiniVM` GL(1) Artin Character Orthogonality):
Composes `MiniVMNttBridge.ntt4AsmFermat_sound` and `MiniVMNttBridge.intt4_ntt4_asm_fermat_roundtrip`
to certify end-to-end inside `MiniVM` assembly execution across all four Fermat-tower
specs `{5, 17, 257, 65537}` (and every valid `ArtinFermatCharacterSpec`):
1. For any bounded `v : Vec4`, `ntt4AsmFermat` computes the exact GL(1) Artin Fourier
   transform `artinCharTransform4`, and `intt4AsmFermat` inverts it back to `v`.
2. For every pair `(i, m) : Fin 4 × Fin 4`, executing `ntt4AsmFermat` on basis vector
   `basisVec4 i` computes `(χ_0(g^i), χ_1(g^i), χ_2(g^i), χ_3(g^i))` in registers `r0..r3`,
   and executing `intt4AsmFermat` evaluates `artinCharOrthoSum` in register `m`, recovering
   the Kronecker delta `δ_{i,m}` (`if i.val = m.val then 1 else 0`). -/
theorem artin_char_orthogonality_minivm :
    (∀ spec ∈ artinFermatTowerSpecs,
      ∀ (s : State) (v : Vec4),
        v.x0 < spec.primeMod → v.x1 < spec.primeMod →
        v.x2 < spec.primeMod → v.x3 < spec.primeMod →
        s.r0 = v.x0 → s.r1 = v.x1 → s.r2 = v.x2 → s.r3 = v.x3 →
        let s1 := runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)
        let s2 := runProgram s1 (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
        (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : Vec4) =
          artinCharTransform4 spec.primeMod spec.omega4 v ∧
        (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : Vec4) = v) ∧
    (∀ spec : ArtinFermatCharacterSpec, spec.Valid →
      ∀ (s : State) (i m : Fin 4),
        s.r0 = (basisVec4 i.val).x0 → s.r1 = (basisVec4 i.val).x1 →
        s.r2 = (basisVec4 i.val).x2 → s.r3 = (basisVec4 i.val).x3 →
        let s1 := runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)
        let s2 := runProgram s1 (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
        (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : Vec4) =
          ⟨artinCharPow spec.primeMod spec.omega4 i.val 0,
           artinCharPow spec.primeMod spec.omega4 i.val 1,
           artinCharPow spec.primeMod spec.omega4 i.val 2,
           artinCharPow spec.primeMod spec.omega4 i.val 3⟩ ∧
        artinCharOrthoSum spec.primeMod spec.omega4 spec.invOmega4 spec.invFour i.val m.val =
          (if i.val = m.val then 1 else 0) ∧
        (match m.val with
         | 0 => s2.r0
         | 1 => s2.r1
         | 2 => s2.r2
         | _ => s2.r3) = (if i.val = m.val then 1 else 0)) := by
  refine ⟨?_, ?_⟩
  · intro spec hmem s v h0 h1 h2 h3 hr0 hr1 hr2 hr3
    have hval := artinFermatTowerSpecs_valid spec hmem
    have hntt := artinCharTransform4_eq_ntt4_generic spec.primeMod spec.omega4
      (Nat.lt_trans Nat.zero_lt_one hval.2.2.1) hval.2.2.2.2.2.2.1 v
    have hs1 := ntt4AsmFermat_sound spec.primeMod spec.omega4 s v.x0 v.x1 v.x2 v.x3
      hr0 hr1 hr2 hr3
    have hs2 := intt4_ntt4_asm_fermat_roundtrip spec.toNttSpec
      (ArtinFermatCharacterSpec.toNttSpec_valid spec hval)
      s v.x0 v.x1 v.x2 v.x3 h0 h1 h2 h3 hr0 hr1 hr2 hr3
    exact ⟨hs1.trans hntt.symm, hs2⟩
  · intro spec hval s i m hr0 hr1 hr2 hr3
    rcases hval with ⟨_, _, hp1, _, _, _, hsq, hwi, h4i⟩
    have hntt := ntt4AsmFermat_sound spec.primeMod spec.omega4 s
      (basisVec4 i.val).x0 (basisVec4 i.val).x1 (basisVec4 i.val).x2 (basisVec4 i.val).x3
      hr0 hr1 hr2 hr3
    have htr := artinCharTransform4_eq_ntt4_generic spec.primeMod spec.omega4
      (Nat.lt_trans Nat.zero_lt_one hp1) hsq (basisVec4 i.val)
    have hbas := artinCharTransform4_basis_lane_mod spec.primeMod spec.omega4 hp1 i
    have hs1 : (⟨(runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r0,
                 (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r1,
                 (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r2,
                 (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r3⟩ : Vec4) =
        ⟨artinCharPow spec.primeMod spec.omega4 i.val 0,
         artinCharPow spec.primeMod spec.omega4 i.val 1,
         artinCharPow spec.primeMod spec.omega4 i.val 2,
         artinCharPow spec.primeMod spec.omega4 i.val 3⟩ :=
      hntt.trans (htr.symm.trans hbas)
    rcases basisVec4_lt hp1 i with ⟨hb0, hb1, hb2, hb3⟩
    have hcfgValid : spec.toNttSpec.Valid := ⟨hp1, hsq, hwi, h4i⟩
    have hs2 := intt4_ntt4_asm_fermat_roundtrip spec.toNttSpec hcfgValid s
      (basisVec4 i.val).x0 (basisVec4 i.val).x1 (basisVec4 i.val).x2 (basisVec4 i.val).x3
      hb0 hb1 hb2 hb3 hr0 hr1 hr2 hr3
    have hinvSq := invW_sq_add_one_mod hp1 hsq hwi
    have hortho := artinCharOrthoSum_eq_intt4_lane spec.primeMod spec.omega4
      spec.invOmega4 spec.invFour hp1 hinvSq i m
    have hintt := intt4AsmFermat_sound spec.primeMod spec.invFour spec.invOmega4
      (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
      (artinCharPow spec.primeMod spec.omega4 i.val 0)
      (artinCharPow spec.primeMod spec.omega4 i.val 1)
      (artinCharPow spec.primeMod spec.omega4 i.val 2)
      (artinCharPow spec.primeMod spec.omega4 i.val 3)
      (congrArg Vec4.x0 hs1) (congrArg Vec4.x1 hs1)
      (congrArg Vec4.x2 hs1) (congrArg Vec4.x3 hs1)
    have hY :
        intt4 spec.primeMod spec.invFour spec.invOmega4
          (artinCharTransform4 spec.primeMod spec.omega4 (basisVec4 i.val)) =
        basisVec4 i.val := by
      rw [hbas]
      exact hintt.symm.trans hs2
    rw [hY] at hortho
    have hs2_lane := basisVec4_lane_eq
      ⟨(runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
        (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r0,
       (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
        (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r1,
       (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
        (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r2,
       (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
        (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r3⟩
      i m hs2
    have hortho_delta := hortho.trans (basisVec4_lane_eq (basisVec4 i.val) i m rfl)
    exact ⟨hs1, hortho_delta, hs2_lane⟩

end ArtinFermatBridge

-- end of file: leanasm/src/LeanAsm/ArtinFermatBridge.lean
