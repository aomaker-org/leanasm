-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Ultrametric.lean
-- Constructive p-adic ultrametric valuation over QRat (v1.3.0).
-- ZERO Classical.choice, ZERO sorryAx, ZERO Mathlib dependencies.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat

open _root_.QuasiRiemann

namespace QuasiRiemann.Valuation

/-!
# Constructive p-Adic Ultrametric Valuation over `QRat`

Zero-Mathlib, zero-`Classical.choice` formalization of prime valuations `ν_p`,
the strong ultrametric triangle inequality `ν_p(x + y) ≥ min(ν_p(x), ν_p(y))`,
and log-valuation contraction certificates for cleared-denominator rationals `QRat`.
-/

/-- Trial-division helper: returns `true` iff `p` has a divisor in `2 .. d`. -/
def hasProperDivisorAux (p : Nat) : Nat → Bool
  | 0 | 1 => false
  | d + 2 =>
    if p % (d + 2) == 0 then true
    else hasProperDivisorAux p (d + 1)

/-- Constructive, decidable primality predicate (`Decidable` via `Bool` equality). -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ hasProperDivisorAux p (p - 1) = false

instance (p : Nat) : Decidable (IsPrime p) :=
  inferInstanceAs (Decidable (2 ≤ p ∧ hasProperDivisorAux p (p - 1) = false))

private theorem not_dvd_of_hasProperDivisorAux_false {p k : Nat}
    (h : hasProperDivisorAux p k = false) :
    ∀ d : Nat, 2 ≤ d → d ≤ k → ¬ (d ∣ p) := by
  induction k with
  | zero =>
    intro d hd2 hdk
    omega
  | succ m ih =>
    cases m with
    | zero =>
      intro d hd2 hdk
      omega
    | succ m' =>
      simp only [hasProperDivisorAux] at h
      by_cases hmod : (p % (m' + 2) == 0) = true
      · simp [hmod] at h
      · have hmod_f : (p % (m' + 2) == 0) = false := by
          cases h0 : p % (m' + 2) == 0 <;> simp_all
        rw [hmod_f] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        intro d hd2 hdk hdvd
        by_cases heq : d = m' + 2
        · rw [← heq] at hmod_f
          have hzero : (p % d == 0) = true :=
            beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hdvd)
          rw [hzero] at hmod_f
          cases hmod_f
        · exact ih h d hd2 (by omega) hdvd

theorem IsPrime.not_dvd_of_lt {p d : Nat} (hp : IsPrime p) (hd2 : 2 ≤ d) (hdp : d < p) :
    ¬ (d ∣ p) :=
  not_dvd_of_hasProperDivisorAux_false hp.2 d hd2 (by omega)

/-- Constructive Euclid's Lemma via strong induction and Euclidean remainder descent. -/
theorem IsPrime.dvd_mul {p : Nat} (hp : IsPrime p) {a b : Nat} (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      exact Or.inl (Nat.dvd_zero p)
    · by_cases hpa : p ∣ a
      · exact Or.inl hpa
      · right
        have hp2 : 2 ≤ p := hp.1
        let r := a % p
        have hr_lt : r < p := Nat.mod_lt a (by omega)
        have ha_decomp : p * (a / p) + r = a := Nat.div_add_mod a p
        have hr_pos : 0 < r := by
          by_cases hr0 : r = 0
          · exfalso
            apply hpa
            refine ⟨a / p, ?_⟩
            omega
          · omega
        have hprb : p ∣ r * b := by
          rcases h with ⟨k, hk⟩
          refine ⟨k - (a / p) * b, ?_⟩
          have h1 : a * b = (p * (a / p) + r) * b := by rw [ha_decomp]
          rw [Nat.add_mul, Nat.mul_assoc] at h1
          rw [Nat.mul_sub_left_distrib]
          omega
        by_cases hr1 : r = 1
        · rw [hr1, Nat.one_mul] at hprb
          exact hprb
        · have hr2 : 2 ≤ r := by omega
          have hnrp : ¬ (r ∣ p) := hp.not_dvd_of_lt hr2 hr_lt
          let q := p / r
          let r' := p % r
          have hr'_lt : r' < r := Nat.mod_lt p hr_pos
          have hp_decomp : r * q + r' = p := Nat.div_add_mod p r
          have hr'_pos : 0 < r' := by
            by_cases hr'0 : r' = 0
            · exfalso
              apply hnrp
              refine ⟨q, ?_⟩
              omega
            · omega
          have hpr'b : p ∣ r' * b := by
            rcases hprb with ⟨m, hm⟩
            refine ⟨b - q * m, ?_⟩
            have h2 : p * b = (r * q + r') * b := by rw [hp_decomp]
            rw [Nat.add_mul, Nat.mul_comm r q, Nat.mul_assoc] at h2
            rw [Nat.mul_sub_left_distrib]
            have hqm : p * (q * m) = q * (r * b) := by
              calc p * (q * m) = q * (p * m) := by ac_rfl
                _ = q * (r * b) := by rw [hm]
            omega
          have hr_le_a : r ≤ a := Nat.mod_le a p
          rcases ih r' (by omega) hpr'b with hpr' | hpb
          · exfalso
            have hle : p ≤ r' := Nat.le_of_dvd hr'_pos hpr'
            omega
          · exact hpb

/-! ### Fuel-Bounded Structural `p`-Adic Valuation on `Nat` -/

/-- Structural fuel-bounded p-adic valuation on `Nat` (lowers to `Nat.rec`). -/
def padicValNatAux (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if p ≤ 1 || n == 0 then 0
    else if n % p == 0 then 1 + padicValNatAux p fuel (n / p)
    else 0

def padicValNat (p n : Nat) : Nat :=
  padicValNatAux p n n

theorem padicValNatAux_eq_of_le {p fuel n : Nat} (hp : 2 ≤ p) (hn : 0 < n) (hle : n ≤ fuel) :
    padicValNatAux p fuel n = padicValNat p n := by
  unfold padicValNat
  suffices h : ∀ f₁ f₂ m, 0 < m → m ≤ f₁ → m ≤ f₂ →
      padicValNatAux p f₁ m = padicValNatAux p f₂ m from
    h fuel n n hn hle (Nat.le_refl n)
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ m hm h1 _
    omega
  | succ f₁ ih =>
    intro f₂ m hm h1 h2
    cases f₂ with
    | zero => omega
    | succ f₂ =>
      simp only [padicValNatAux]
      have hcond : (p ≤ 1 || m == 0) = false := by
        have h_p : ¬ (p ≤ 1) := by omega
        have h_m : (m == 0) = false := by
          cases m with
          | zero => omega
          | succ _ => rfl
        simp [h_p, h_m]
      rw [hcond]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hmod : (m % p == 0) = true
      · rw [hmod]
        simp only [↓reduceIte]
        have hm_div_pos : 0 < m / p := by
          have hdvd : p ∣ m := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
          rcases hdvd with ⟨q, rfl⟩
          rw [Nat.mul_div_cancel_left q (by omega)]
          cases q with
          | zero => simp at hm
          | succ _ => omega
        have hm_div_lt : m / p < m := Nat.div_lt_self hm (by omega)
        rw [ih f₂ (m / p) hm_div_pos (by omega) (by omega)]
      · have hmod_f : (m % p == 0) = false := by
          cases h : m % p == 0 <;> simp_all
        rw [hmod_f]
        simp

theorem padicValNat_of_dvd {p n : Nat} (hp : 2 ≤ p) (hn : 0 < n) (hdvd : p ∣ n) :
    padicValNat p n = 1 + padicValNat p (n / p) := by
  cases hn_eq : n with
  | zero => omega
  | succ m =>
    have h1 : padicValNat p (m + 1) = padicValNatAux p (m + 1) (m + 1) := rfl
    rw [h1]
    simp only [padicValNatAux]
    have hcond : (p ≤ 1 || (m + 1 == 0)) = false := by
      have : ¬ (p ≤ 1) := by omega
      simp [this]
    have hmod : ((m + 1) % p == 0) = true := by
      apply beq_iff_eq.mpr
      apply Nat.mod_eq_zero_of_dvd
      simpa [hn_eq] using hdvd
    rw [hcond, hmod]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hdiv_pos : 0 < (m + 1) / p := by
      have hdvd' : p ∣ m + 1 := by simpa [hn_eq] using hdvd
      rcases hdvd' with ⟨q, hq⟩
      rw [hq, Nat.mul_div_cancel_left q (by omega)]
      cases q with
      | zero => omega
      | succ _ => omega
    have hdiv_le : (m + 1) / p ≤ m := by
      have := Nat.div_lt_self (by omega : 0 < m + 1) (by omega : 1 < p)
      omega
    rw [padicValNatAux_eq_of_le hp hdiv_pos hdiv_le]

theorem padicValNat_of_not_dvd {p n : Nat} (hp : 2 ≤ p) (hn : 0 < n) (hndvd : ¬ (p ∣ n)) :
    padicValNat p n = 0 := by
  cases hn_eq : n with
  | zero => omega
  | succ m =>
    have h1 : padicValNat p (m + 1) = padicValNatAux p (m + 1) (m + 1) := rfl
    rw [h1]
    simp only [padicValNatAux]
    have hcond : (p ≤ 1 || (m + 1 == 0)) = false := by
      have : ¬ (p ≤ 1) := by omega
      simp [this]
    have hmod : ((m + 1) % p == 0) = false := by
      cases h : (m + 1) % p == 0
      · rfl
      · exfalso
        apply hndvd
        rw [hn_eq]
        exact Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h)
    rw [hcond, hmod]
    simp

private theorem dvd_of_mul_dvd_mul_left {a b c : Nat} (ha : 0 < a) (h : a * b ∣ a * c) :
    b ∣ c := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have h1 : a * c = a * (b * k) := by rw [hk, Nat.mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left ha h1

private theorem dvd_sub_of_dvd {k a b : Nat} (ha : k ∣ a) (hb : k ∣ b) : k ∣ a - b := by
  rcases ha with ⟨q₁, rfl⟩
  rcases hb with ⟨q₂, rfl⟩
  exact ⟨q₁ - q₂, (Nat.mul_sub_left_distrib k q₁ q₂).symm⟩

theorem pow_padicValNat_dvd {p n : Nat} (hp : 2 ≤ p) (hn : 0 < n) :
    p ^ padicValNat p n ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hdvd : p ∣ n
    · rw [padicValNat_of_dvd hp hn hdvd]
      rcases hdvd with ⟨q, rfl⟩
      have hq_pos : 0 < q := by
        cases q with
        | zero => simp at hn
        | succ _ => omega
      have hdiv : (p * q) / p = q := Nat.mul_div_cancel_left q (by omega)
      rw [hdiv]
      have hq_lt : q < p * q := by
        have : 1 * q < p * q := Nat.mul_lt_mul_of_pos_right (by omega) hq_pos
        simpa using this
      have h_ih : p ^ padicValNat p q ∣ q := ih q hq_lt hq_pos
      rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
      exact Nat.mul_dvd_mul_left p h_ih
    · rw [padicValNat_of_not_dvd hp hn hdvd, Nat.pow_zero]
      exact Nat.one_dvd n

theorem le_padicValNat_of_pow_dvd {p k n : Nat} (hp : 2 ≤ p) (hn : 0 < n) (h : p ^ k ∣ n) :
    k ≤ padicValNat p n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    have hp_dvd : p ∣ n := by
      have h1 : p * p ^ k ∣ n := by
        simpa [Nat.pow_succ, Nat.mul_comm] using h
      exact Nat.dvd_trans (Nat.dvd_mul_right p (p ^ k)) h1
    rw [padicValNat_of_dvd hp hn hp_dvd]
    rcases hp_dvd with ⟨q, rfl⟩
    have hq_pos : 0 < q := by
      cases q with
      | zero => simp at hn
      | succ _ => omega
    have hdiv : (p * q) / p = q := Nat.mul_div_cancel_left q (by omega)
    rw [hdiv]
    have hk_dvd : p ^ k ∣ q := by
      have h1 : p * p ^ k ∣ p * q := by
        simpa [Nat.pow_succ, Nat.mul_comm] using h
      exact dvd_of_mul_dvd_mul_left (by omega) h1
    have := ih hq_pos hk_dvd
    omega

theorem pow_dvd_iff_le_padicValNat {p k n : Nat} (hp : 2 ≤ p) (hn : 0 < n) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n := by
  constructor
  · exact le_padicValNat_of_pow_dvd hp hn
  · intro hle
    obtain ⟨d, hd⟩ : ∃ d, padicValNat p n = k + d := ⟨padicValNat p n - k, by omega⟩
    have hpow : p ^ k ∣ p ^ padicValNat p n := by
      rw [hd, Nat.pow_add]
      exact Nat.dvd_mul_right (p ^ k) (p ^ d)
    exact Nat.dvd_trans hpow (pow_padicValNat_dvd hp hn)

/-! ### Multiplicativity and Additive Ultrametric Bounds -/

private theorem le_padicValNat_add_of_pow_dvd_mul {p : Nat} (hp : IsPrime p) :
    ∀ k a b : Nat, 0 < a → 0 < b → p ^ k ∣ a * b →
      k ≤ padicValNat p a + padicValNat p b := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _
    omega
  | succ k ih =>
    intro a b ha hb h
    have hp2 : 2 ≤ p := hp.1
    have hp_dvd : p ∣ a * b := by
      have h1 : p * p ^ k ∣ a * b := by
        simpa [Nat.pow_succ, Nat.mul_comm] using h
      exact Nat.dvd_trans (Nat.dvd_mul_right p (p ^ k)) h1
    rcases hp.dvd_mul hp_dvd with hpa | hpb
    · rw [padicValNat_of_dvd hp2 ha hpa]
      rcases hpa with ⟨q, rfl⟩
      have hq_pos : 0 < q := by
        cases q with
        | zero => simp at ha
        | succ _ => omega
      rw [Nat.mul_div_cancel_left q (by omega)]
      have hk : p ^ k ∣ q * b := by
        have h1 : p * p ^ k ∣ p * (q * b) := by
          have hpow : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
          have hassoc : p * q * b = p * (q * b) := by ac_rfl
          rw [← hpow, ← hassoc]
          exact h
        exact dvd_of_mul_dvd_mul_left (by omega) h1
      have := ih q b hq_pos hb hk
      omega
    · rw [padicValNat_of_dvd hp2 hb hpb]
      rcases hpb with ⟨q, rfl⟩
      have hq_pos : 0 < q := by
        cases q with
        | zero => simp at hb
        | succ _ => omega
      rw [Nat.mul_div_cancel_left q (by omega)]
      have hk : p ^ k ∣ a * q := by
        have h1 : p * p ^ k ∣ p * (a * q) := by
          have hpow : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
          have hassoc : a * (p * q) = p * (a * q) := by ac_rfl
          rw [← hpow, ← hassoc]
          exact h
        exact dvd_of_mul_dvd_mul_left (by omega) h1
      have := ih a q ha hq_pos hk
      omega

theorem padicValNat_mul {p a b : Nat} (hp : IsPrime p) (ha : 0 < a) (hb : 0 < b) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  have hp2 : 2 ≤ p := hp.1
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have h_le : padicValNat p (a * b) ≤ padicValNat p a + padicValNat p b :=
    le_padicValNat_add_of_pow_dvd_mul hp (padicValNat p (a * b)) a b ha hb
      (pow_padicValNat_dvd hp2 hab)
  have h_ge : padicValNat p a + padicValNat p b ≤ padicValNat p (a * b) := by
    apply le_padicValNat_of_pow_dvd hp2 hab
    rw [Nat.pow_add]
    exact Nat.mul_dvd_mul (pow_padicValNat_dvd hp2 ha) (pow_padicValNat_dvd hp2 hb)
  omega

/-- Constructive p-adic valuation on nonzero `Int` via `natAbs`. -/
def padicValInt (p : Nat) (z : Int) : Nat :=
  padicValNat p z.natAbs

theorem padicValInt_neg (p : Nat) (z : Int) :
    padicValInt p (-z) = padicValInt p z := by
  unfold padicValInt
  rw [Int.natAbs_neg]

theorem padicValInt_mul {p : Nat} (hp : IsPrime p) {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  unfold padicValInt
  rw [Int.natAbs_mul]
  exact padicValNat_mul hp (Int.natAbs_pos.mpr ha) (Int.natAbs_pos.mpr hb)

theorem padicValInt_add_ge_min {p : Nat} (hp : 2 ≤ p) {A B : Int}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A + B ≠ 0) :
    min (padicValInt p A) (padicValInt p B) ≤ padicValInt p (A + B) := by
  unfold padicValInt
  have hA_pos : 0 < A.natAbs := Int.natAbs_pos.mpr hA
  have hB_pos : 0 < B.natAbs := Int.natAbs_pos.mpr hB
  have hAB_pos : 0 < (A + B).natAbs := Int.natAbs_pos.mpr hAB
  let m := min (padicValNat p A.natAbs) (padicValNat p B.natAbs)
  have hmA : p ^ m ∣ A.natAbs :=
    (pow_dvd_iff_le_padicValNat hp hA_pos).mpr (by omega)
  have hmB : p ^ m ∣ B.natAbs :=
    (pow_dvd_iff_le_padicValNat hp hB_pos).mpr (by omega)
  have hmAB : p ^ m ∣ (A + B).natAbs := by
    have h_cases :
        (A + B).natAbs = A.natAbs + B.natAbs ∨
        (A + B).natAbs = A.natAbs - B.natAbs ∨
        (A + B).natAbs = B.natAbs - A.natAbs := by
      omega
    rcases h_cases with h1 | h2 | h3
    · rw [h1]; exact Nat.dvd_add hmA hmB
    · rw [h2]; exact dvd_sub_of_dvd hmA hmB
    · rw [h3]; exact dvd_sub_of_dvd hmB hmA
  exact (pow_dvd_iff_le_padicValNat hp hAB_pos).mp hmAB

/-! ### Extended Valuation on `QRat` and the Ultrametric Inequality -/

/-- Extended integer valuation: `none` denotes +∞ (`pAdicVal p 0`). -/
abbrev ExtVal := Option Int

def valLe : ExtVal → ExtVal → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

instance : DecidableRel valLe
  | _, none => isTrue trivial
  | none, some _ => isFalse (fun h => h)
  | some a, some b => inferInstanceAs (Decidable (a ≤ b))

def valMin : ExtVal → ExtVal → ExtVal
  | none, y => y
  | x, none => x
  | some a, some b => some (min a b)

/-- Addition on extended integer valuations (`none` denotes `+∞`, i.e., `ν_p(0)`). -/
def valAdd : ExtVal → ExtVal → ExtVal
  | none, _ => none
  | _, none => none
  | some a, some b => some (a + b)

/-- Constructive p-adic valuation `ν_p` on cleared-denominator `QRat`. -/
def pAdicVal (p : Nat) (q : QRat) : ExtVal :=
  if q.num = 0 then none
  else
    let vn : Int := (padicValInt p q.num : Int)
    let vd : Int := (padicValNat p q.den : Int)
    some (vn - vd)

theorem pAdicVal_eq_none_iff (p : Nat) (x : QRat) :
    pAdicVal p x = none ↔ x.num = 0 := by
  by_cases hx0 : x.num = 0 <;> simp [pAdicVal, hx0]

theorem pAdicVal_eq_of_num_den_eq {p : Nat} {u v : QRat}
    (hnum : u.num = v.num) (hden : u.den = v.den) :
    pAdicVal p u = pAdicVal p v := by
  simp only [pAdicVal, hnum, hden]

private theorem qrat_neg_num (x : QRat) : (-x).num = -x.num := rfl
private theorem qrat_neg_den (x : QRat) : (-x).den = x.den := rfl
private theorem qrat_mul_num (x y : QRat) : (x * y).num = x.num * y.num := rfl
private theorem qrat_mul_den (x y : QRat) : (x * y).den = x.den * y.den := rfl

/-- **Negation Invariance** of `p`-adic valuation on `QRat`: `ν_p(-x) = ν_p(x)`. -/
theorem pAdicVal_neg (p : Nat) (x : QRat) :
    pAdicVal p (-x) = pAdicVal p x := by
  by_cases hx0 : x.num = 0
  · have hneg0 : (-x).num = 0 := by
      rw [qrat_neg_num, hx0]
      rfl
    simp [pAdicVal, hx0, hneg0]
  · have hneg0 : (-x).num ≠ 0 := by
      intro h
      rw [qrat_neg_num] at h
      omega
    simp only [pAdicVal, hx0, hneg0, ↓reduceIte]
    rw [qrat_neg_num, qrat_neg_den, padicValInt_neg]

/-- **Difference Symmetry** of `p`-adic valuation on `QRat`: `ν_p(x - y) = ν_p(y - x)`. -/
theorem pAdicVal_sub_comm (p : Nat) (x y : QRat) :
    pAdicVal p (x - y) = pAdicVal p (y - x) := by
  rw [← pAdicVal_neg p (y - x)]
  apply pAdicVal_eq_of_num_den_eq
  · rw [qrat_neg_num]
    have h1 : (x - y).num = x.num * (y.den : Int) - y.num * (x.den : Int) := rfl
    have h2 : (y - x).num = y.num * (x.den : Int) - x.num * (y.den : Int) := rfl
    omega
  · rw [qrat_neg_den]
    exact Nat.mul_comm x.den y.den

/-- **Multiplicativity** (Strong Homomorphism Property) of `p`-adic valuation on `QRat`:
    `ν_p(x * y) = ν_p(x) + ν_p(y)` for every prime `p`. -/
theorem pAdicVal_mul (p : Nat) (hp : IsPrime p) (x y : QRat) :
    pAdicVal p (x * y) = valAdd (pAdicVal p x) (pAdicVal p y) := by
  by_cases hx0 : x.num = 0
  · have hxy0 : (x * y).num = 0 := by
      rw [qrat_mul_num, hx0, Int.zero_mul]
    simp [pAdicVal, hx0, hxy0, valAdd]
  · by_cases hy0 : y.num = 0
    · have hxy0 : (x * y).num = 0 := by
        rw [qrat_mul_num, hy0, Int.mul_zero]
      simp [pAdicVal, hx0, hy0, hxy0, valAdd]
    · have hxy0 : (x * y).num ≠ 0 := by
        rw [qrat_mul_num]
        exact Int.mul_ne_zero hx0 hy0
      simp only [pAdicVal, hx0, hy0, hxy0, ↓reduceIte, valAdd]
      rw [qrat_mul_num, qrat_mul_den,
          padicValInt_mul hp hx0 hy0,
          padicValNat_mul hp x.den_pos y.den_pos]
      congr 1
      omega

/-- **Strong Ultrametric Triangle Inequality** on `QRat`:
    `ν_p(x + y) ≥ min(ν_p(x), ν_p(y))` for every prime `p`. -/
theorem ultrametric_ineq (p : Nat) (hp : IsPrime p) (x y : QRat) :
    valLe (valMin (pAdicVal p x) (pAdicVal p y)) (pAdicVal p (x + y)) := by
  have hp2 : 2 ≤ p := hp.1
  have hxd_pos : 0 < x.den := x.den_pos
  have hyd_pos : 0 < y.den := y.den_pos
  have hsum_num : (x + y).num = x.num * (y.den : Int) + y.num * (x.den : Int) := rfl
  have hsum_den : (x + y).den = x.den * y.den := rfl
  by_cases hxy0 : (x + y).num = 0
  · simp [pAdicVal, hxy0, valLe]
  · by_cases hx0 : x.num = 0
    · have hy0 : y.num ≠ 0 := by
        intro hy
        rw [hsum_num, hx0, hy] at hxy0
        simp at hxy0
      simp only [pAdicVal, hx0, hy0, hxy0, ↓reduceIte, valMin, valLe]
      have hnum_abs : (x + y).num.natAbs = y.num.natAbs * x.den := by
        rw [hsum_num, hx0]
        simp [Int.natAbs_mul, Int.natAbs_natCast]
      have hy_abs_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr hy0
      unfold padicValInt
      rw [hnum_abs, hsum_den, padicValNat_mul hp hy_abs_pos hxd_pos,
        padicValNat_mul hp hxd_pos hyd_pos]
      omega
    · by_cases hy0 : y.num = 0
      · simp only [pAdicVal, hx0, hy0, hxy0, ↓reduceIte, valMin, valLe]
        have hnum_abs : (x + y).num.natAbs = x.num.natAbs * y.den := by
          rw [hsum_num, hy0]
          simp [Int.natAbs_mul, Int.natAbs_natCast]
        have hx_abs_pos : 0 < x.num.natAbs := Int.natAbs_pos.mpr hx0
        unfold padicValInt
        rw [hnum_abs, hsum_den, padicValNat_mul hp hx_abs_pos hyd_pos,
          padicValNat_mul hp hxd_pos hyd_pos]
        omega
      · simp only [pAdicVal, hx0, hy0, hxy0, ↓reduceIte, valMin, valLe]
        let A : Int := x.num * (y.den : Int)
        let B : Int := y.num * (x.den : Int)
        have hA_ne : A ≠ 0 := Int.mul_ne_zero hx0 (Int.ofNat_ne_zero.mpr (by omega))
        have hB_ne : B ≠ 0 := Int.mul_ne_zero hy0 (Int.ofNat_ne_zero.mpr (by omega))
        have hAB_ne : A + B ≠ 0 := by simpa [A, B, hsum_num] using hxy0
        have h_ultra := padicValInt_add_ge_min hp2 hA_ne hB_ne hAB_ne
        have hA_val : padicValInt p A = padicValInt p x.num + padicValNat p y.den := by
          unfold padicValInt
          have : A.natAbs = x.num.natAbs * y.den := by
            simp [A, Int.natAbs_mul, Int.natAbs_natCast]
          rw [this, padicValNat_mul hp (Int.natAbs_pos.mpr hx0) hyd_pos]
        have hB_val : padicValInt p B = padicValInt p y.num + padicValNat p x.den := by
          unfold padicValInt
          have : B.natAbs = y.num.natAbs * x.den := by
            simp [B, Int.natAbs_mul, Int.natAbs_natCast]
          rw [this, padicValNat_mul hp (Int.natAbs_pos.mpr hy0) hxd_pos]
        have hAB_eq : padicValInt p (x + y).num = padicValInt p (A + B) := by
          simp [A, B, hsum_num]
        rw [hAB_eq, hsum_den, padicValNat_mul hp hxd_pos hyd_pos]
        rw [hA_val, hB_val] at h_ultra
        omega

/-! ### Cleared-Denominator Prime-Power Height Bounds across `QRat` Operations -/

/-- Prime-power valuation `ν_p(x.den)` of the cleared denominator of `x : QRat`. -/
def denVal (p : Nat) (x : QRat) : Nat :=
  padicValNat p x.den

/-- Exact prime-power divisibility characterization for `QRat` denominators:
    `p ^ k ∣ x.den ↔ k ≤ denVal p x`. -/
theorem pow_dvd_den_iff_le_denVal {p k : Nat} (hp : 2 ≤ p) (x : QRat) :
    p ^ k ∣ x.den ↔ k ≤ denVal p x :=
  pow_dvd_iff_le_padicValNat hp x.den_pos

/-- `p ^ denVal p x` always divides `x.den`. -/
theorem pow_denVal_dvd_den {p : Nat} (hp : 2 ≤ p) (x : QRat) :
    p ^ denVal p x ∣ x.den :=
  pow_padicValNat_dvd hp x.den_pos

/-- Sharp prime-power ceiling: `p ^ (denVal p x + 1)` never divides `x.den`. -/
theorem not_pow_succ_denVal_dvd_den {p : Nat} (hp : 2 ≤ p) (x : QRat) :
    ¬ (p ^ (denVal p x + 1) ∣ x.den) := by
  intro hdvd
  have hle : denVal p x + 1 ≤ denVal p x :=
    (pow_dvd_den_iff_le_denVal hp x).mp hdvd
  omega

/-- Negation invariance of cleared-denominator prime-power valuation. -/
theorem denVal_neg (p : Nat) (x : QRat) :
    denVal p (-x) = denVal p x := rfl

/-- Exact prime-power valuation of cleared-denominator `QRat` addition:
    `ν_p((x + y).den) = ν_p(x.den) + ν_p(y.den)`. -/
theorem denVal_add {p : Nat} (hp : IsPrime p) (x y : QRat) :
    denVal p (x + y) = denVal p x + denVal p y := by
  unfold denVal
  have hden : (x + y).den = x.den * y.den := rfl
  rw [hden]
  exact padicValNat_mul hp x.den_pos y.den_pos

/-- Exact prime-power valuation of cleared-denominator `QRat` subtraction:
    `ν_p((x - y).den) = ν_p(x.den) + ν_p(y.den)`. -/
theorem denVal_sub {p : Nat} (hp : IsPrime p) (x y : QRat) :
    denVal p (x - y) = denVal p x + denVal p y := by
  unfold denVal
  have hden : (x - y).den = x.den * y.den := rfl
  rw [hden]
  exact padicValNat_mul hp x.den_pos y.den_pos

/-- Exact prime-power valuation of cleared-denominator `QRat` multiplication:
    `ν_p((x * y).den) = ν_p(x.den) + ν_p(y.den)`. -/
theorem denVal_mul {p : Nat} (hp : IsPrime p) (x y : QRat) :
    denVal p (x * y) = denVal p x + denVal p y := by
  unfold denVal
  have hden : (x * y).den = x.den * y.den := rfl
  rw [hden]
  exact padicValNat_mul hp x.den_pos y.den_pos

/-- Denominator prime-power height bound for cleared-denominator `QRat` addition. -/
theorem denVal_add_le {p : Nat} (hp : IsPrime p) {x y : QRat} {bx by_ : Nat}
    (hx : denVal p x ≤ bx) (hy : denVal p y ≤ by_) :
    denVal p (x + y) ≤ bx + by_ := by
  rw [denVal_add hp]
  omega

/-- Denominator prime-power height bound for cleared-denominator `QRat` subtraction. -/
theorem denVal_sub_le {p : Nat} (hp : IsPrime p) {x y : QRat} {bx by_ : Nat}
    (hx : denVal p x ≤ bx) (hy : denVal p y ≤ by_) :
    denVal p (x - y) ≤ bx + by_ := by
  rw [denVal_sub hp]
  omega

/-- Denominator prime-power height bound for cleared-denominator `QRat` multiplication. -/
theorem denVal_mul_le {p : Nat} (hp : IsPrime p) {x y : QRat} {bx by_ : Nat}
    (hx : denVal p x ≤ bx) (hy : denVal p y ≤ by_) :
    denVal p (x * y) ≤ bx + by_ := by
  rw [denVal_mul hp]
  omega

/-- Equivalence between `denVal p x = 0` and `p` not dividing `x.den`. -/
theorem denVal_eq_zero_iff_not_dvd {p : Nat} (hp : 2 ≤ p) (x : QRat) :
    denVal p x = 0 ↔ ¬ (p ∣ x.den) := by
  constructor
  · intro hz hdvd
    have hpow : p ^ 1 ∣ x.den := by simpa using hdvd
    have hle : 1 ≤ denVal p x := (pow_dvd_den_iff_le_denVal hp x).mp hpow
    omega
  · intro hndvd
    exact padicValNat_of_not_dvd hp x.den_pos hndvd

/-- Preservation of `p`-coprime denominators under `QRat` addition. -/
theorem denVal_add_eq_zero {p : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : denVal p x = 0) (hy : denVal p y = 0) :
    denVal p (x + y) = 0 := by
  rw [denVal_add hp, hx, hy]

/-- Preservation of `p`-coprime denominators under `QRat` subtraction. -/
theorem denVal_sub_eq_zero {p : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : denVal p x = 0) (hy : denVal p y = 0) :
    denVal p (x - y) = 0 := by
  rw [denVal_sub hp, hx, hy]

/-- Preservation of `p`-coprime denominators under `QRat` multiplication. -/
theorem denVal_mul_eq_zero {p : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : denVal p x = 0) (hy : denVal p y = 0) :
    denVal p (x * y) = 0 := by
  rw [denVal_mul hp, hx, hy]

/-- Every `x : QRat` satisfies `ν_p(x) ≥ -ν_p(x.den)`. -/
theorem pAdicVal_ge_neg_denVal (p : Nat) (x : QRat) :
    valLe (some (-(Int.ofNat (denVal p x)))) (pAdicVal p x) := by
  by_cases hx0 : x.num = 0
  · simp [pAdicVal, hx0, valLe]
  · simp only [pAdicVal, hx0, ↓reduceIte, valLe, denVal]
    have hcast : Int.ofNat (padicValNat p x.den) = (padicValNat p x.den : Int) := rfl
    rw [hcast]
    omega

/-- Any denominator prime-power ceiling `ν_p(x.den) ≤ B` yields a uniform
    lower valuation floor `ν_p(x) ≥ -B`. -/
theorem pAdicVal_ge_neg_of_denVal_le {p B : Nat} {x : QRat} (hB : denVal p x ≤ B) :
    valLe (some (-(Int.ofNat B))) (pAdicVal p x) := by
  by_cases hx0 : x.num = 0
  · simp [pAdicVal, hx0, valLe]
  · simp only [pAdicVal, hx0, ↓reduceIte, valLe]
    unfold denVal at hB
    have hcast : Int.ofNat B = (B : Int) := rfl
    rw [hcast]
    omega

/-- Combined denominator-height ceiling and valuation floor for cleared-denominator
    `QRat` sums: `ν_p(x.den) ≤ B₁` and `ν_p(y.den) ≤ B₂` imply
    `ν_p((x + y).den) ≤ B₁ + B₂` and `ν_p(x + y) ≥ -(B₁ + B₂)`. -/
theorem denVal_and_pAdicVal_add_bound {p B₁ B₂ : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : denVal p x ≤ B₁) (hy : denVal p y ≤ B₂) :
    denVal p (x + y) ≤ B₁ + B₂ ∧
    valLe (some (-(Int.ofNat (B₁ + B₂)))) (pAdicVal p (x + y)) := by
  have hden := denVal_add_le hp hx hy
  exact ⟨hden, pAdicVal_ge_neg_of_denVal_le hden⟩

/-- Combined denominator-height ceiling and valuation floor for cleared-denominator
    `QRat` products: `ν_p(x.den) ≤ B₁` and `ν_p(y.den) ≤ B₂` imply
    `ν_p((x * y).den) ≤ B₁ + B₂` and `ν_p(x * y) ≥ -(B₁ + B₂)`. -/
theorem denVal_and_pAdicVal_mul_bound {p B₁ B₂ : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : denVal p x ≤ B₁) (hy : denVal p y ≤ B₂) :
    denVal p (x * y) ≤ B₁ + B₂ ∧
    valLe (some (-(Int.ofNat (B₁ + B₂)))) (pAdicVal p (x * y)) := by
  have hden := denVal_mul_le hp hx hy
  exact ⟨hden, pAdicVal_ge_neg_of_denVal_le hden⟩

/-- Linear denominator-height bound across an `N`-term cleared-denominator `QRat` sum:
    if every term `x ∈ xs` has `ν_p(x.den) ≤ B`, then
    `ν_p((xs.foldl (· + ·) init).den) ≤ ν_p(init.den) + xs.length * B`. -/
theorem denVal_foldl_add_le {p B : Nat} (hp : IsPrime p) :
    ∀ (xs : List QRat) (init : QRat),
      (∀ x ∈ xs, denVal p x ≤ B) →
      denVal p (xs.foldl (· + ·) init) ≤ denVal p init + xs.length * B
  | [], _, _ => by
    simp
  | x :: xs, init, hall => by
    simp only [List.foldl_cons, List.length_cons]
    have hx : denVal p x ≤ B := hall x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, denVal p y ≤ B := fun y hy =>
      hall y (List.mem_cons.mpr (Or.inr hy))
    have ih := denVal_foldl_add_le hp xs (init + x) hxs
    have hstep : denVal p (init + x) ≤ denVal p init + B := by
      rw [denVal_add hp]
      omega
    have hmul : (xs.length + 1) * B = xs.length * B + B := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Linear denominator-height bound across an `N`-term cleared-denominator `QRat` product:
    if every factor `x ∈ xs` has `ν_p(x.den) ≤ B`, then
    `ν_p((xs.foldl (· * ·) init).den) ≤ ν_p(init.den) + xs.length * B`. -/
theorem denVal_foldl_mul_le {p B : Nat} (hp : IsPrime p) :
    ∀ (xs : List QRat) (init : QRat),
      (∀ x ∈ xs, denVal p x ≤ B) →
      denVal p (xs.foldl (· * ·) init) ≤ denVal p init + xs.length * B
  | [], _, _ => by
    simp
  | x :: xs, init, hall => by
    simp only [List.foldl_cons, List.length_cons]
    have hx : denVal p x ≤ B := hall x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, denVal p y ≤ B := fun y hy =>
      hall y (List.mem_cons.mpr (Or.inr hy))
    have ih := denVal_foldl_mul_le hp xs (init * x) hxs
    have hstep : denVal p (init * x) ≤ denVal p init + B := by
      rw [denVal_mul hp]
      omega
    have hmul : (xs.length + 1) * B = xs.length * B + B := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-! ### Horner Polynomial Evaluation Denominator Height Bounds -/

/-- Constructive `0 : QRat` (`0 / 1`). -/
def qZero : QRat :=
  { num := 0, den := 1, den_pos := Nat.zero_lt_succ 0 }

theorem denVal_qZero {p : Nat} (hp : 2 ≤ p) :
    denVal p qZero = 0 := by
  unfold denVal qZero
  exact padicValNat_of_not_dvd hp (Nat.zero_lt_succ 0) (fun hdvd => by
    have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hdvd
    omega)

/-- Standard Horner evaluation of `coeffs = [c₀, c₁, ..., c_d]` at `x : QRat`:
    `c₀ + x * (c₁ + x * (...))`. -/
def hornerEval : List QRat → QRat → QRat
  | [], _ => qZero
  | c :: cs, x => c + x * hornerEval cs x

/-- **Horner Polynomial Denominator Height Bound (by coefficient count):**
    If every coefficient `c ∈ coeffs` satisfies `ν_p(c.den) ≤ Bc` and `ν_p(x.den) ≤ Bx`,
    then `ν_p((hornerEval coeffs x).den) ≤ coeffs.length * (Bc + Bx)`. -/
theorem denVal_hornerEval_le {p Bc Bx : Nat} (hp : IsPrime p) (x : QRat)
    (hx : denVal p x ≤ Bx) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, denVal p c ≤ Bc) →
      denVal p (hornerEval coeffs x) ≤ coeffs.length * (Bc + Bx)
  | [], _ => by
    simp only [hornerEval, List.length_nil, Nat.zero_mul]
    rw [denVal_qZero hp.1]
    exact Nat.le_refl 0
  | c :: cs, hall => by
    simp only [hornerEval, List.length_cons]
    have hc : denVal p c ≤ Bc := hall c (List.mem_cons.mpr (Or.inl rfl))
    have hcs : ∀ c' ∈ cs, denVal p c' ≤ Bc := fun c' hc' =>
      hall c' (List.mem_cons.mpr (Or.inr hc'))
    have ih := denVal_hornerEval_le hp x hx cs hcs
    rw [denVal_add hp, denVal_mul hp]
    have hmul : (cs.length + 1) * (Bc + Bx) = cs.length * (Bc + Bx) + (Bc + Bx) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **Horner Polynomial Denominator Height Bound (by polynomial degree `deg`):**
    For a polynomial of degree at most `deg` (`coeffs.length ≤ deg + 1`) with
    coefficient denominator bounds `denVal p c ≤ Bc` and evaluation point bound
    `denVal p x ≤ Bx`, `ν_p((hornerEval coeffs x).den) ≤ (deg + 1) * (Bc + Bx)`. -/
theorem denVal_hornerEval_deg_le {p deg Bc Bx : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x : QRat) (hx : denVal p x ≤ Bx)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    denVal p (hornerEval coeffs x) ≤ (deg + 1) * (Bc + Bx) := by
  have h1 := denVal_hornerEval_le hp x hx coeffs hall
  have h2 : coeffs.length * (Bc + Bx) ≤ (deg + 1) * (Bc + Bx) :=
    Nat.mul_le_mul_right (Bc + Bx) hdeg
  omega

/-- Combined denominator-height ceiling and `p`-adic valuation lower floor for
    `hornerEval coeffs x` of degree at most `deg`. -/
theorem hornerEval_and_pAdicVal_bound {p deg Bc Bx : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x : QRat) (hx : denVal p x ≤ Bx)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    denVal p (hornerEval coeffs x) ≤ (deg + 1) * (Bc + Bx) ∧
    valLe (some (-(Int.ofNat ((deg + 1) * (Bc + Bx)))))
          (pAdicVal p (hornerEval coeffs x)) := by
  have hden := denVal_hornerEval_deg_le hp coeffs hdeg x hx hall
  exact ⟨hden, pAdicVal_ge_neg_of_denVal_le hden⟩

/-- Preservation of `p`-coprime denominators across Horner polynomial evaluation. -/
theorem denVal_hornerEval_eq_zero {p : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (x : QRat) (hx : denVal p x = 0)
    (hall : ∀ c ∈ coeffs, denVal p c = 0) :
    denVal p (hornerEval coeffs x) = 0 := by
  have hle := denVal_hornerEval_le (Bc := 0) (Bx := 0) hp x
    (by omega) coeffs (fun c hc => by have := hall c hc; omega)
  omega

/-- Degree-tight Horner evaluation: avoids multiplying the leading term by `0`,
    saving one cleared-denominator factor of `x.den` (and `0` factors on constants). -/
def hornerEvalTight : List QRat → QRat → QRat
  | [], _ => qZero
  | [c], _ => c
  | c :: c' :: cs, x => c + x * hornerEvalTight (c' :: cs) x

/-- **Degree-Tight Horner Denominator Height Bound (by coefficient count):**
    `ν_p((hornerEvalTight coeffs x).den) ≤ coeffs.length * Bc + (coeffs.length - 1) * Bx`. -/
theorem denVal_hornerEvalTight_le {p Bc Bx : Nat} (hp : IsPrime p) (x : QRat)
    (hx : denVal p x ≤ Bx) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, denVal p c ≤ Bc) →
      denVal p (hornerEvalTight coeffs x) ≤
        coeffs.length * Bc + (coeffs.length - 1) * Bx
  | [], _ => by
    simp only [hornerEvalTight, List.length_nil, Nat.zero_mul]
    rw [denVal_qZero hp.1]
    omega
  | [c], hall => by
    simp only [hornerEvalTight, List.length_singleton]
    have hc : denVal p c ≤ Bc := hall c (List.mem_cons.mpr (Or.inl rfl))
    omega
  | c :: c' :: cs, hall => by
    simp only [hornerEvalTight, List.length_cons]
    have hc : denVal p c ≤ Bc := hall c (List.mem_cons.mpr (Or.inl rfl))
    have htail : ∀ y ∈ c' :: cs, denVal p y ≤ Bc := fun y hy =>
      hall y (List.mem_cons.mpr (Or.inr hy))
    have ih := denVal_hornerEvalTight_le hp x hx (c' :: cs) htail
    simp only [List.length_cons] at ih
    rw [denVal_add hp, denVal_mul hp]
    have hmul1 : (cs.length + 1 + 1) * Bc = (cs.length + 1) * Bc + Bc := by
      rw [Nat.add_mul, Nat.one_mul]
    have hsub1 : cs.length + 1 + 1 - 1 = cs.length + 1 := by omega
    have hsub0 : cs.length + 1 - 1 = cs.length := by omega
    rw [hsub0] at ih
    have hmul2 : (cs.length + 1) * Bx = cs.length * Bx + Bx := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hsub1, hmul1, hmul2]
    omega

/-- **Degree-Tight Horner Denominator Height Bound (by polynomial degree `deg`):**
    For a polynomial of degree at most `deg` (`coeffs.length ≤ deg + 1`),
    `ν_p((hornerEvalTight coeffs x).den) ≤ (deg + 1) * Bc + deg * Bx`. -/
theorem denVal_hornerEvalTight_deg_le {p deg Bc Bx : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x : QRat) (hx : denVal p x ≤ Bx)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    denVal p (hornerEvalTight coeffs x) ≤ (deg + 1) * Bc + deg * Bx := by
  have h1 := denVal_hornerEvalTight_le hp x hx coeffs hall
  have h2 : coeffs.length * Bc ≤ (deg + 1) * Bc :=
    Nat.mul_le_mul_right Bc hdeg
  have h3 : (coeffs.length - 1) * Bx ≤ deg * Bx :=
    Nat.mul_le_mul_right Bx (by omega)
  omega

/-- Combined denominator-height ceiling and `p`-adic valuation lower floor for
    `hornerEvalTight coeffs x` of degree at most `deg`. -/
theorem hornerEvalTight_and_pAdicVal_bound {p deg Bc Bx : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x : QRat) (hx : denVal p x ≤ Bx)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    denVal p (hornerEvalTight coeffs x) ≤ (deg + 1) * Bc + deg * Bx ∧
    valLe (some (-(Int.ofNat ((deg + 1) * Bc + deg * Bx))))
          (pAdicVal p (hornerEvalTight coeffs x)) := by
  have hden := denVal_hornerEvalTight_deg_le hp coeffs hdeg x hx hall
  exact ⟨hden, pAdicVal_ge_neg_of_denVal_le hden⟩

end QuasiRiemann.Valuation

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Ultrametric.lean
