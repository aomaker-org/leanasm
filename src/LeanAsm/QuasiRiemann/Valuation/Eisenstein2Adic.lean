-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Eisenstein2Adic.lean
import LeanAsm.QuasiRiemann.Valuation.Ultrametric

/-!
# Constructive 2-Adic Valuations and Binary Hamming Weights for Eisenstein Series

Self-contained, zero-Mathlib Lean 4 formalization of results from:
Liubomir Chiriac & Andrei Jorza, "Lacunary recurrences and 2-adic properties
of Eisenstein series" (arXiv:2605.09738v2, May 2026):

1. Binary Hamming weight `s(n)` and 2-adic valuation `v₂(n)` on `Nat`.
2. Step identity: `s(m) + v₂(m) = s(m - 1) + 1` for `m ≥ 1` (§3.1).
3. Legendre's formula: `v₂(m!) + s(m) = m` (§3.1).
4. Romik recurrence coefficient 2-adic balance for `k = 6n + 2`, `1 ≤ j ≤ n` (§3.1).
5. Proposition 4 (§2): For `k = 2^(m+2)`, the unique coefficient of
   `G_k = ∑_{4a + 6b = k} w(a, k) G_4^a G_6^b` with `v₂(w(a, k)) = 0` is `a = 2^m`,
   and `v₂(w(a, k)) > 0` for all `a ≠ 2^m`.

Axiom footprint: strictly constructive (`propext`, `Quot.sound` only;
zero `sorry`, zero `Classical.choice`).
-/


open _root_.QuasiRiemann.Valuation

namespace LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic

/-! ## 1. Binary Hamming Weight `s(n)` and 2-Adic Valuation `v₂(n)` -/

/-- Binary Hamming weight `s(n)`: count of `1`-bits in base-2 expansion of `n`. -/
def hammingWeight : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + hammingWeight ((n + 1) / 2)
termination_by n => n

/-- 2-adic valuation `v₂(n)` on `Nat` (returning `0` at `n = 0` by convention). -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      1 + v2 ((n + 1) / 2)
    else
      0
termination_by n => n

@[simp] theorem hammingWeight_zero : hammingWeight 0 = 0 := by simp [hammingWeight]
@[simp] theorem v2_zero : v2 0 = 0 := by simp [v2]

theorem hammingWeight_eq (n : Nat) :
    hammingWeight n = n % 2 + hammingWeight (n / 2) := by
  cases n with
  | zero => simp
  | succ k => simp [hammingWeight]

theorem v2_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  cases n with
  | zero => simp at h
  | succ k => simp [v2, h]

theorem v2_even {n : Nat} (hpos : 0 < n) (heven : n % 2 = 0) :
    v2 n = 1 + v2 (n / 2) := by
  cases n with
  | zero => omega
  | succ k => simp [v2, heven]

theorem hammingWeight_two_mul (n : Nat) :
    hammingWeight (2 * n) = hammingWeight n := by
  rw [hammingWeight_eq]
  have h1 : (2 * n) % 2 = 0 := Nat.mul_mod_right 2 n
  have h2 : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by decide)
  rw [h1, h2, Nat.zero_add]

theorem hammingWeight_two_mul_add_one (n : Nat) :
    hammingWeight (2 * n + 1) = 1 + hammingWeight n := by
  rw [hammingWeight_eq]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

theorem v2_two_mul {n : Nat} (hpos : 0 < n) :
    v2 (2 * n) = 1 + v2 n := by
  have h := v2_even (n := 2 * n) (by omega) (Nat.mul_mod_right 2 n)
  rw [h, Nat.mul_div_cancel_left n (by decide)]

private theorem hammingWeight_step_aux :
    ∀ bound m, m ≤ bound → 0 < m →
      hammingWeight m + v2 m = hammingWeight (m - 1) + 1
  | 0, m, hle, hpos => by omega
  | bound + 1, m, hle, hpos => by
    by_cases hmod : m % 2 = 1
    · have hv : v2 m = 0 := v2_odd hmod
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hv, hsub, hammingWeight_two_mul_add_one, hammingWeight_two_mul]
      omega
    · have heven : m % 2 = 0 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
      have hkpos : 0 < k := by omega
      have hsub : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
      rw [hsub, hammingWeight_two_mul, v2_two_mul hkpos, hammingWeight_two_mul_add_one]
      have hrec := hammingWeight_step_aux bound k (by omega) hkpos
      omega

/-- Paper §3.1 identity: `s(m) - s(m - 1) = 1 - v₂(m)` for all `m ≥ 1`,
    written additively on `Nat` as `s(m) + v₂(m) = s(m - 1) + 1`. -/
theorem hammingWeight_step {m : Nat} (hpos : 0 < m) :
    hammingWeight m + v2 m = hammingWeight (m - 1) + 1 :=
  hammingWeight_step_aux m m (Nat.le_refl m) hpos

/-! ## 2. Legendre's Formula `v₂(m!) + s(m) = m` (Paper §3.1) -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

private theorem v2_odd_mul_aux :
    ∀ bound a b, b ≤ bound → a % 2 = 1 → 0 < b → v2 (a * b) = v2 b
  | 0, a, b, hle, ha, hb => by omega
  | bound + 1, a, b, hle, ha, hb => by
    by_cases hb_even : b % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
      have hk : 0 < k := by omega
      have hak : 0 < a * k := Nat.mul_pos (by omega) hk
      have hcomm : a * (2 * k) = 2 * (a * k) := by
        calc a * (2 * k) = (a * 2) * k := (Nat.mul_assoc a 2 k).symm
          _ = (2 * a) * k := by rw [Nat.mul_comm a 2]
          _ = 2 * (a * k) := Nat.mul_assoc 2 a k
      rw [hcomm, v2_two_mul hak, v2_two_mul hk,
          v2_odd_mul_aux bound a k (by omega) ha hk]
    · have hb_odd : b % 2 = 1 := by omega
      have hab_odd : (a * b) % 2 = 1 := by rw [Nat.mul_mod, ha, hb_odd]
      rw [v2_odd hab_odd, v2_odd hb_odd]

theorem v2_odd_mul {a b : Nat} (ha : a % 2 = 1) (hb : 0 < b) :
    v2 (a * b) = v2 b :=
  v2_odd_mul_aux b a b (Nat.le_refl b) ha hb

private theorem v2_mul_pos_aux :
    ∀ bound a b, a ≤ bound → 0 < a → 0 < b → v2 (a * b) = v2 a + v2 b
  | 0, a, b, hle, ha, hb => by omega
  | bound + 1, a, b, hle, ha, hb => by
    by_cases ha_even : a % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      have hk : 0 < k := by omega
      have hkb : 0 < k * b := Nat.mul_pos hk hb
      rw [Nat.mul_assoc, v2_two_mul hkb, v2_two_mul hk,
          v2_mul_pos_aux bound k b (by omega) hk hb]
      omega
    · have ha_odd : a % 2 = 1 := by omega
      rw [v2_odd_mul ha_odd hb, v2_odd ha_odd, Nat.zero_add]

theorem v2_mul_pos {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    v2 (a * b) = v2 a + v2 b :=
  v2_mul_pos_aux a a b (Nat.le_refl a) ha hb

/-- Legendre's Theorem (Paper §3.1): `v₂(m!) + s(m) = m`. -/
theorem legendre_v2_factorial (m : Nat) :
    v2 (fact m) + hammingWeight m = m := by
  induction m with
  | zero => simp [fact, v2]
  | succ k ih =>
    have hpos : 0 < k + 1 := Nat.succ_pos k
    have hfpos : 0 < fact k := fact_pos k
    rw [fact, v2_mul_pos hpos hfpos]
    have hstep := hammingWeight_step hpos
    simp only [Nat.add_sub_cancel] at hstep
    omega

/-! ## 3. Romik Recurrence Coefficient `c_j` Valuation Balance (Paper §3.1) -/

theorem romik_cj_valuation_balance (n j : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    let num := fact (4 * n + 1) * fact (2 * n + 2 * j - 1) * fact (4 * n - 2 * j + 1)
    let den := fact (6 * n + 1) * fact (2 * n) * fact (2 * j - 1) * fact (2 * n - 2 * j + 1)
    v2 num + hammingWeight (4 * n + 1) + hammingWeight (2 * n + 2 * j - 1) +
        hammingWeight (4 * n - 2 * j + 1) =
      v2 den + hammingWeight (6 * n + 1) + hammingWeight (2 * n) +
        hammingWeight (2 * j - 1) + hammingWeight (2 * n - 2 * j + 1) := by
  intro num den
  have hnum :
      v2 num = v2 (fact (4 * n + 1)) + v2 (fact (2 * n + 2 * j - 1)) +
        v2 (fact (4 * n - 2 * j + 1)) := by
    dsimp [num]
    rw [v2_mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _),
        v2_mul_pos (fact_pos _) (fact_pos _)]
  have hden :
      v2 den = v2 (fact (6 * n + 1)) + v2 (fact (2 * n)) +
        v2 (fact (2 * j - 1)) + v2 (fact (2 * n - 2 * j + 1)) := by
    dsimp [den]
    have hp12 := Nat.mul_pos (fact_pos (6 * n + 1)) (fact_pos (2 * n))
    have hp123 := Nat.mul_pos hp12 (fact_pos (2 * j - 1))
    rw [v2_mul_pos hp123 (fact_pos _), v2_mul_pos hp12 (fact_pos _),
        v2_mul_pos (fact_pos _) (fact_pos _)]
  have L1 := legendre_v2_factorial (4 * n + 1)
  have L2 := legendre_v2_factorial (2 * n + 2 * j - 1)
  have L3 := legendre_v2_factorial (4 * n - 2 * j + 1)
  have L4 := legendre_v2_factorial (6 * n + 1)
  have L5 := legendre_v2_factorial (2 * n)
  have L6 := legendre_v2_factorial (2 * j - 1)
  have L7 := legendre_v2_factorial (2 * n - 2 * j + 1)
  rw [hnum, hden]
  omega

/-! ## 4. Proposition 4 (Paper §2): Powers of Two `k = 2^(m+2)` -/

/-- Indicator predicate modeling `v₂(w(a, 2^(m+2))) = 0`
    (`true` iff `w(a, 2^(m+2)) ≡ 1 (mod 2)`). -/
def isUnitMod2 : Nat → Nat → Bool
  | 0, a => decide (a = 1)
  | m + 1, a => (a % 2 == 0) && isUnitMod2 m (a / 2)

/-- Proposition 4 (Chiriac & Jorza, arXiv:2605.09738v2, §2):
    For every `m ≥ 0` (`k = 2^(m+2)`), `v₂(w(a, 2^(m+2))) = 0` iff `a = 2^m`. -/
theorem proposition_4 (m a : Nat) :
    isUnitMod2 m a = true ↔ a = 2 ^ m := by
  induction m generalizing a with
  | zero =>
    simp [isUnitMod2]
  | succ m ih =>
    simp only [isUnitMod2, Bool.and_eq_true, beq_iff_eq]
    rw [ih (a / 2)]
    constructor
    · rintro ⟨heven, hdiv⟩
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
        rw [Nat.pow_succ, Nat.mul_comm]
      omega
    · rintro rfl
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by
        rw [Nat.pow_succ, Nat.mul_comm]
      refine ⟨?_, ?_⟩
      · rw [hpow, Nat.mul_mod_right]
      · rw [hpow, Nat.mul_div_cancel_left _ (by decide)]

/-- Corollary (Proposition 4, uniqueness): `v₂(w(2^m, 2^(m+2))) = 0`, and
    `v₂(w(a, 2^(m+2))) > 0` whenever `a ≠ 2^m`. -/
theorem proposition_4_unique (m : Nat) :
    isUnitMod2 m (2 ^ m) = true ∧ ∀ a, a ≠ 2 ^ m → isUnitMod2 m a = false := by
  refine ⟨(proposition_4 m (2 ^ m)).mpr rfl, ?_⟩
  intro a hne
  cases h : isUnitMod2 m a with
  | false => rfl
  | true => exact False.elim (hne ((proposition_4 m a).mp h))

/-! ## 5. Equivalence with `QuasiRiemann.Valuation.padicValNat 2` -/

private theorem padicValNat_two_zero : padicValNat 2 0 = 0 := rfl

private theorem padicValNat_two_odd {n : Nat} (hodd : n % 2 = 1) :
    padicValNat 2 n = 0 := by
  cases n with
  | zero => simp at hodd
  | succ m =>
    unfold padicValNat padicValNatAux
    have hmod : ((m + 1) % 2 == 0) = false := by
      cases h : (m + 1) % 2 with
      | zero => omega
      | succ _ => rfl
    simp [hmod]

private theorem padicValNat_two_mul {n : Nat} (hpos : 0 < n) :
    padicValNat 2 (2 * n) = 1 + padicValNat 2 n := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  have h1 : padicValNat 2 (2 * n) = padicValNatAux 2 (k + 1) (2 * n) := by
    unfold padicValNat
    rw [hk]
  rw [h1]
  dsimp only [padicValNatAux]
  have hcond : (2 ≤ 1 || (2 * n == 0)) = false := by
    cases h : 2 * n with
    | zero => omega
    | succ _ => rfl
  have hmod : ((2 * n) % 2 == 0) = true := by
    have hm : (2 * n) % 2 = 0 := Nat.mul_mod_right 2 n
    rw [hm]
    rfl
  rw [hcond, hmod]
  have hdiv : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by decide)
  rw [hdiv]
  change 1 + padicValNatAux 2 k n = 1 + padicValNat 2 n
  congr 1
  have hp2 : (2 : Nat) ≤ 2 := Nat.le_refl 2
  have hle : n ≤ k := by
    have hlt : n < k + 1 := by
      rw [← hk, Nat.two_mul]
      exact Nat.lt_add_of_pos_left hpos
    exact Nat.le_of_lt_succ hlt
  exact padicValNatAux_eq_of_le (p := 2) (fuel := k) (n := n) hp2 hpos hle

private theorem eq_v2_of_spec_aux (g : Nat → Nat)
    (hg0 : g 0 = 0)
    (hg_odd : ∀ n, n % 2 = 1 → g n = 0)
    (hg_two_mul : ∀ n, 0 < n → g (2 * n) = 1 + g n) :
    ∀ bound n, n ≤ bound → v2 n = g n
  | 0, n, hle => by
    have hn : n = 0 := by omega
    subst hn
    rw [v2_zero, hg0]
  | bound + 1, n, hle => by
    cases n with
    | zero => rw [v2_zero, hg0]
    | succ m =>
      by_cases hmod : (m + 1) % 2 = 1
      · rw [v2_odd hmod, hg_odd (m + 1) hmod]
      · have heven : (m + 1) % 2 = 0 := by omega
        obtain ⟨k, hk⟩ : ∃ k, m + 1 = 2 * k := ⟨(m + 1) / 2, by omega⟩
        have hkpos : 0 < k := by omega
        rw [hk, v2_two_mul hkpos, hg_two_mul k hkpos,
            eq_v2_of_spec_aux g hg0 hg_odd hg_two_mul bound k (by omega)]

/-- Exact API equivalence: `Eisenstein2Adic.v2` agrees identically with
    `QuasiRiemann.Valuation.padicValNat 2` for all `n : Nat`. -/
theorem v2_eq_padicValNat_two (n : Nat) :
    v2 n = padicValNat 2 n :=
  eq_v2_of_spec_aux (padicValNat 2) padicValNat_two_zero
    (@padicValNat_two_odd) (@padicValNat_two_mul) n n (Nat.le_refl n)

/-- Legendre's formula expressed directly in `QuasiRiemann.Valuation.padicValNat 2`. -/
theorem legendre_padicValNat_two_factorial (m : Nat) :
    padicValNat 2 (fact m) + hammingWeight m = m := by
  rw [← v2_eq_padicValNat_two]
  exact legendre_v2_factorial m

end LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic
-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Eisenstein2Adic.lean
