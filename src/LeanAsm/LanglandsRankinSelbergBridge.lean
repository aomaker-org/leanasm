-- Path: leanasm/src/LeanAsm/LanglandsRankinSelbergBridge.lean
-- Rankin-Selberg / Sym^2 / GL2xGL2 -> GSp4 bridge (Issue #80), zero-Mathlib.
-- Max Column: 120 Columns

import LeanAsm.EllipticModularityBridge
import LeanAsm.GSp4FunctorialityBridge

namespace LanglandsRankinSelbergBridge

/-- Primitive Dirichlet character mod 4. -/
def chi4 (n : Nat) : Int :=
  if n % 2 == 0 then 0 else if n % 4 == 1 then 1 else -1

/-- Cleared-denominator Rankin-Selberg twist factor `f_11 x chi_4` at `X = u / v`.
At `p = 2` the factor is trivial; at `p = 11` it is the degree-1 factor `1 - chi4 a X`. -/
def rsClearedEuler (p : Nat) (ap u v : Int) : Int :=
  if p == 2 then v * v
  else if p == 11 then v * v - chi4 p * ap * u * v
  else v * v - chi4 p * ap * u * v + (p : Int) * u * u

theorem rs_at_11 (u v : Int) :
    rsClearedEuler 11 (EllipticModularityBridge.heckeCoeff11 11) u v = v * v + u * v := by
  rw [EllipticModularityBridge.heckeCoeff11_bad_11]
  have h : chi4 11 = -1 := by decide
  unfold rsClearedEuler
  simp only [show (11 == 2) = false from rfl, show (11 == 11) = true from rfl, h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : (-1 : Int) * 1 * u * v = -(u * v) := by
    rw [Int.mul_one, Int.neg_mul, Int.one_mul, Int.neg_mul]
  rw [h1, Int.sub_neg]

/-- Good-prime RS factor is the `GL(2)` homogeneous Euler form with twisted trace `chi4(p) a_p`. -/
theorem rs_good_eq_gl2 (p : Nat) (ap u v : Int) (h2 : p ≠ 2) (h11 : p ≠ 11) :
    rsClearedEuler p ap u v =
      EllipticModularityBridge.gl2EulerHomog (p : Int) (chi4 p * ap) u v := by
  simp [rsClearedEuler, EllipticModularityBridge.gl2EulerHomog, h2, h11, Int.pow_succ, Int.pow_zero, Int.mul_assoc]

/-- `chi4(p)^2 = 1` for odd `p`, so twisting preserves Hasse: `(chi4 a)^2 = a^2`. -/
theorem chi4_sq_odd (p : Nat) (h : p % 2 = 1) : chi4 p * chi4 p = 1 := by
  unfold chi4
  have hn : (p % 2 == 0) = false := by
    cases hc : (p % 2 == 0)
    · rfl
    · have := Nat.eq_of_beq_eq_true hc; omega
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : p % 4 = 1
  · have h4' : (p % 4 == 1) = true := by simpa using h4
    simp only [h4', ↓reduceIte]; decide
  · have h4' : (p % 4 == 1) = false := by simpa using h4
    simp only [h4', Bool.false_eq_true, ↓reduceIte]; decide

/-- RS positivity at good primes from Ramanujan `a_p^2 < 4p`. -/
theorem rs_pos_of_ramanujan (p : Nat) (ap u v : Int) (h2 : p ≠ 2) (h11 : p ≠ 11) (hodd : p % 2 = 1)
    (hram : ap ^ 2 < 4 * (p : Int)) (hv : 0 < v) : 0 < rsClearedEuler p ap u v := by
  rw [rs_good_eq_gl2 p ap u v h2 h11]
  apply EllipticModularityBridge.gl2_euler_homog_pos_of_ramanujan _ _ u v _ hv
  have hs := chi4_sq_odd p hodd
  have : (chi4 p * ap) ^ 2 = ap ^ 2 := by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.pow_succ, Int.pow_succ, Int.pow_zero]
    calc 1 * (chi4 p * ap) * (chi4 p * ap) = (chi4 p * chi4 p) * (ap * ap) := by
          simp only [Int.one_mul]; ac_rfl
      _ = 1 * (ap * ap) := by rw [hs]
      _ = _ := by simp only [Int.one_mul]
  omega

/-- Cleared-denominator `Sym^2` factor `(v - p u)(v^2 - (a^2 - 2p) u v + p^2 u^2)`. -/
def sym2ClearedEuler (p : Nat) (ap u v : Int) : Int :=
  if p == 11 then v - u
  else (v - (p : Int) * u) * (v * v - (ap * ap - 2 * (p : Int)) * u * v + (p : Int) * p * u * u)

/-! ## GL(2) x GL(2) -> GSp(4) -/

structure SpinorReciprocalPoly where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  c4 : Int
  deriving DecidableEq, Repr

def gl2ProdToGSp4Spinor (a1 a2 lam : Int) : SpinorReciprocalPoly :=
  { c0 := 1, c1 := -(a1 + a2), c2 := a1 * a2 + 2 * lam, c3 := -lam * (a1 + a2), c4 := lam * lam }

theorem gl2ProdToGSp4Spinor_reciprocal (a1 a2 lam : Int) :
    (gl2ProdToGSp4Spinor a1 a2 lam).c3 = lam * (gl2ProdToGSp4Spinor a1 a2 lam).c1 ∧
    (gl2ProdToGSp4Spinor a1 a2 lam).c4 = lam * lam * (gl2ProdToGSp4Spinor a1 a2 lam).c0 := by
  simp [gl2ProdToGSp4Spinor, Int.mul_neg, Int.neg_mul]

/-- The product `H1 * H2` of two GL(2) Hecke quadratics with common similitude `lam` is the
GSp(4) spin Euler polynomial with `a1 := al1 + al2`, `a2 := al1 al2 + 2 lam`. -/
theorem spin_eq_product (al1 al2 lam T : Int) :
    GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
      (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2) := by
  have h2 : (2 : Int) * lam = lam + lam := Int.two_mul lam
  rw [h2]
  simp only [GSp4FunctorialityBridge.gsp4SpinEulerPoly, Int.pow_succ, Int.pow_zero,
    Int.mul_add, Int.mul_sub, Int.mul_comm,
    Int.mul_left_comm, Int.mul_one]
  omega

/-- Identity: `4 Q = (2v - t u)^2 + s (4p - s) u^2` with `t = s - 2p`, `s = a_p^2`. -/
theorem sym2_quad_sos (p s u v : Int) :
    4 * (v * v - (s - 2 * p) * u * v + p * p * u * u) =
      (2 * v - (s - 2 * p) * u) * (2 * v - (s - 2 * p) * u) + s * (4 * p - s) * (u * u) := by
  have h2 : (2 : Int) * p = p + p := Int.two_mul p
  have h4 : (4 : Int) * p = p + p + p + p := by omega
  have h4' : (4 : Int) = 1 + 1 + 1 + 1 := rfl
  rw [h2, h4]
  have h2v : (2 : Int) * v = v + v := Int.two_mul v
  rw [h2v]
  rw [h4']
  simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Alternative identity: `Q = (v - p u)^2 + (4p - s) u v`. -/
theorem sym2_quad_alt (p s u v : Int) :
    v * v - (s - 2 * p) * u * v + p * p * u * u =
      (v - p * u) * (v - p * u) + (4 * p - s) * (u * v) := by
  have h2 : (2 : Int) * p = p + p := Int.two_mul p
  have h4 : (4 : Int) * p = p + p + p + p := by omega
  rw [h2, h4]
  simp only [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

private theorem mul_self_nonneg' (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at this
    exact this

private theorem mul_self_pos' (x : Int) (h : 0 < x) : 0 < x * x := Int.mul_pos h h

/-- `Sym^2` quadratic factor is nonnegative under Ramanujan `a_p^2 <= 4p`. -/
theorem sym2_quad_nonneg (p ap u v : Int) (hram : ap * ap ≤ 4 * p) :
    0 ≤ v * v - (ap * ap - 2 * p) * u * v + p * p * u * u := by
  have hid := sym2_quad_sos p (ap * ap) u v
  have hs : 0 ≤ ap * ap := mul_self_nonneg' ap
  have h1 : 0 ≤ (2 * v - (ap * ap - 2 * p) * u) * (2 * v - (ap * ap - 2 * p) * u) :=
    mul_self_nonneg' _
  have h2 : 0 ≤ ap * ap * (4 * p - ap * ap) * (u * u) :=
    Int.mul_nonneg (Int.mul_nonneg hs (by omega)) (mul_self_nonneg' u)
  omega

/-- Nonnegativity of the cleared `Sym^2` factor at `p ≠ 11`. -/
theorem sym2_nonneg_of_ramanujan (p : Nat) (ap u v : Int) (h11 : p ≠ 11)
    (hram : ap ^ 2 ≤ 4 * (p : Int)) (hv : 0 < v - (p : Int) * u) :
    0 ≤ sym2ClearedEuler p ap u v := by
  have hne : (p == 11) = false := by
    cases hc : (p == 11)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) h11
  unfold sym2ClearedEuler
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  have hr : ap * ap ≤ 4 * (p : Int) := by
    have : ap ^ 2 = ap * ap := by simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
    omega
  exact Int.mul_nonneg (Int.le_of_lt hv) (sym2_quad_nonneg (p : Int) ap u v hr)

/-- Strict positivity for `u ≥ 0`, `v > p u`, including supersingular `a_p = 0`. -/
theorem sym2_pos_of_ramanujan_pos_u (p : Nat) (ap u v : Int) (h11 : p ≠ 11)
    (hram : ap ^ 2 ≤ 4 * (p : Int)) (hu : 0 ≤ u) (hv : 0 < v - (p : Int) * u) :
    0 < sym2ClearedEuler p ap u v := by
  have hne : (p == 11) = false := by
    cases hc : (p == 11)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) h11
  unfold sym2ClearedEuler
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  have hr : ap * ap ≤ 4 * (p : Int) := by
    have : ap ^ 2 = ap * ap := by simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
    omega
  have hp : (0 : Int) ≤ (p : Int) := Int.natCast_nonneg p
  have hpu : 0 ≤ (p : Int) * u := Int.mul_nonneg hp hu
  have hv0 : 0 < v := by omega
  have halt := sym2_quad_alt (p : Int) (ap * ap) u v
  have h1 : 0 < (v - (p : Int) * u) * (v - (p : Int) * u) := mul_self_pos' _ hv
  have h2 : 0 ≤ (4 * (p : Int) - ap * ap) * (u * v) :=
    Int.mul_nonneg (by omega) (Int.mul_nonneg hu (Int.le_of_lt hv0))
  have hQ : 0 < v * v - (ap * ap - 2 * (p : Int)) * u * v + (p : Int) * p * u * u := by
    rw [halt]; omega
  exact Int.mul_pos hv hQ

theorem sym2_at_11 (ap u v : Int) (h : u < v) : 0 < sym2ClearedEuler 11 ap u v := by
  unfold sym2ClearedEuler
  simp only [show (11 == 11) = true from rfl, ↓reduceIte]
  omega

/-! ## `p <= 97` certificates -/

open EllipticModularityBridge in
theorem chi4_sq_goodPrimes_odd :
    ∀ p ∈ goodPrimes97, p ≠ 2 → chi4 p ^ 2 = 1 := by
  decide

open EllipticModularityBridge in
theorem heckeCoeff11_hasse_goodPrimes :
    ∀ p ∈ goodPrimes97, heckeCoeff11 p ^ 2 < 4 * (p : Int) := by
  have h : ∀ p ∈ goodPrimes97, f11TableLit.getD p 0 ^ 2 < 4 * (p : Int) := by decide
  intro p hp
  rw [heckeCoeff11_eq_table]
  exact h p hp

open EllipticModularityBridge in
theorem rs_pos_goodPrimes :
    ∀ p ∈ goodPrimes97, ∀ u v : Int, 0 < v → 0 < rsClearedEuler p (heckeCoeff11 p) u v := by
  intro p hp u v hv
  have hhasse := heckeCoeff11_hasse_goodPrimes p hp
  have h11 : p ≠ 11 := by
    have : ∀ q ∈ goodPrimes97, q ≠ 11 := by decide
    exact this p hp
  by_cases h2 : p = 2
  · subst h2
    unfold rsClearedEuler
    simp only [show (2 == 2) = true from rfl, ↓reduceIte]
    exact Int.mul_pos hv hv
  · have hodd : p % 2 = 1 := by
      have : ∀ q ∈ goodPrimes97, q ≠ 2 → q % 2 = 1 := by decide
      exact this p hp h2
    exact rs_pos_of_ramanujan p _ u v h2 h11 hodd hhasse hv

open EllipticModularityBridge in
theorem sym2_pos_goodPrimes :
    ∀ p ∈ goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
      0 < sym2ClearedEuler p (heckeCoeff11 p) u v := by
  intro p hp u v hu hv
  have h11 : p ≠ 11 := by
    have : ∀ q ∈ goodPrimes97, q ≠ 11 := by decide
    exact this p hp
  exact sym2_pos_of_ramanujan_pos_u p _ u v h11
    (Int.le_of_lt (heckeCoeff11_hasse_goodPrimes p hp)) hu hv

/-! ## Hecke-weighted Abel summation -/

/-- Hecke-`chi4` twisted coefficient `c(n) = chi4 n * a_n(f_11)`. -/
def heckeChi4Coeff (n : Nat) : Int := chi4 n * EllipticModularityBridge.heckeCoeff11 n

/-- Generic cumulative sum `sum_{k < n} c k`. -/
def partialSum (c : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => partialSum c n + c n

/-- Generic block sum `sum_{i < N} f (M + i)`. -/
def blockSum (f : Nat → Int) (M : Nat) : Nat → Int
  | 0 => 0
  | N + 1 => blockSum f M N + f (M + N)

/-- Cumulative Hecke-twisted partial sum. -/
def heckeChi4PartialSum (n : Nat) : Int := partialSum heckeChi4Coeff n

/-- Abel tail `sum_{i<N} S(M+i+1) (phi(M+i) - phi(M+i+1))`. -/
def abelTail (c : Nat → Int) (phi : Nat → Int) (M : Nat) : Nat → Int
  | 0 => 0
  | N + 1 => abelTail c phi M N +
      partialSum c (M + N + 1) * (phi (M + N) - phi (M + N + 1))

/-- Discrete Abel summation by parts on `[M, M + N)`. -/
theorem abel_summation (c phi : Nat → Int) (M N : Nat) :
    blockSum (fun k => c k * phi k) M N =
      partialSum c (M + N) * phi (M + N) - partialSum c M * phi M + abelTail c phi M N := by
  induction N with
  | zero => simp only [blockSum, abelTail, Nat.add_zero]; omega
  | succ N ih =>
    simp only [blockSum, abelTail]
    have hS : partialSum c (M + (N + 1)) = partialSum c (M + N) + c (M + N) := rfl
    have e : M + (N + 1) = M + N + 1 := rfl
    rw [e] at hS ⊢
    rw [ih, hS]
    simp only [Int.add_mul, Int.mul_sub]
    omega

/-- Abel specialization to Hecke-twisted coefficients. -/
theorem hecke_chi4_abel (phi : Nat → Int) (M N : Nat) :
    blockSum (fun k => heckeChi4Coeff k * phi k) M N =
      heckeChi4PartialSum (M + N) * phi (M + N) - heckeChi4PartialSum M * phi M +
        abelTail heckeChi4Coeff phi M N :=
  abel_summation heckeChi4Coeff phi M N

private theorem two_sided_mul (S B D : Int) (hS1 : -B ≤ S) (hS2 : S ≤ B) (hD : 0 ≤ D) :
    -(B * D) ≤ S * D ∧ S * D ≤ B * D := by
  have h1 := Int.mul_le_mul_of_nonneg_right hS1 hD
  have h2 := Int.mul_le_mul_of_nonneg_right hS2 hD
  rw [Int.neg_mul] at h1
  exact ⟨h1, h2⟩

/-- Tail bound under uniform partial-sum bound and non-increasing weights. -/
theorem abelTail_bound (c phi : Nat → Int) (B : Int)
    (hS : ∀ m, -B ≤ partialSum c m ∧ partialSum c m ≤ B)
    (hmono : ∀ k, phi (k + 1) ≤ phi k) (M N : Nat) :
    -(B * (phi M - phi (M + N))) ≤ abelTail c phi M N ∧
      abelTail c phi M N ≤ B * (phi M - phi (M + N)) := by
  induction N with
  | zero =>
    have h0 : phi M - phi (M + 0) = 0 := by rw [Nat.add_zero]; omega
    have hz : abelTail c phi M 0 = 0 := rfl
    rw [h0, hz, Int.mul_zero]
    refine ⟨?_, ?_⟩ <;> omega
  | succ N ih =>
    have hT : abelTail c phi M (N + 1) = abelTail c phi M N +
        partialSum c (M + N + 1) * (phi (M + N) - phi (M + N + 1)) := rfl
    rw [hT]
    have hD : 0 ≤ phi (M + N) - phi (M + N + 1) := by have := hmono (M + N); omega
    have h := two_sided_mul _ B _ (hS (M + N + 1)).1 (hS (M + N + 1)).2 hD
    have e : M + (N + 1) = M + N + 1 := rfl
    rw [e]
    have hsplit : B * (phi M - phi (M + N + 1)) =
        B * (phi M - phi (M + N)) + B * (phi (M + N) - phi (M + N + 1)) := by
      have hh : phi M - phi (M + N + 1) =
          (phi M - phi (M + N)) + (phi (M + N) - phi (M + N + 1)) := by omega
      rw [← Int.mul_add, ← hh]
    refine ⟨?_, ?_⟩ <;> omega

/-- Short-interval Hecke-weighted bound: `|sum c_n phi(n)| <= 2 B phi(M)`. -/
theorem hecke_chi4_short_interval_bound (phi : Nat → Int) (B : Int)
    (hS : ∀ m, -B ≤ heckeChi4PartialSum m ∧ heckeChi4PartialSum m ≤ B)
    (hmono : ∀ k, phi (k + 1) ≤ phi k) (hnn : ∀ k, 0 ≤ phi k) (M N : Nat) :
    -(2 * B * phi M) ≤ blockSum (fun k => heckeChi4Coeff k * phi k) M N ∧
      blockSum (fun k => heckeChi4Coeff k * phi k) M N ≤ 2 * B * phi M := by
  rw [hecke_chi4_abel]
  have ht := abelTail_bound heckeChi4Coeff phi B hS hmono M N
  have a1 := two_sided_mul _ B _ (hS (M + N)).1 (hS (M + N)).2 (hnn (M + N))
  have a2 := two_sided_mul _ B _ (hS M).1 (hS M).2 (hnn M)
  have h2 : 2 * B * phi M = B * phi M + B * phi M := by
    rw [Int.two_mul, Int.add_mul]
  rw [h2]
  have hsub : B * (phi M - phi (M + N)) = B * phi M - B * phi (M + N) := Int.mul_sub B _ _
  refine ⟨?_, ?_⟩ <;> omega


end LanglandsRankinSelbergBridge
-- end of file: leanasm/src/LeanAsm/LanglandsRankinSelbergBridge.lean
