Here is the complete, sorry-free Lean 4.35.0 implementation of the $p$-adic ultrametric triangle inequality over `QRat`, built strictly on Lean 4's core `Init` library with **zero Mathlib** and **zero `Classical.choice**`.

### Architectural Notes for `leanasm`

1. **Log-Valuation Space (`ExtVal := Option Int`):** Instead of forming rational powers $p^{-\nu_p(q)}$, mapping $q \mapsto \nu_p(q) \in \mathbb{Z} \cup \{+\infty\}$ (`none` for $q = 0$, `some (ν_p(num) - ν_p(den))` otherwise) translates $\vert{}x + y\vert{}_p \le \max(\vert{}x\vert{}_p, \vert{}y\vert{}_p)$ into linear integer arithmetic:

$$\nu_p(x + y) \ge \min(\nu_p(x), \nu_p(y))$$



which `omega` discharges directly once divisibility is established.
2. **Constructive Euclid's Lemma (`IsPrime.dvd_mul`):** Proved via strong induction (`Nat.strongRecOn`, which lowers to structural `Acc.rec`) and Euclidean remainder descent—avoiding `Nat.gcd` Bezout imports and keeping the transitive axiom cone strictly within `[propext]`.
3. **Cleared-Denominator Invariance:** Because $\nu_p(a \cdot b) = \nu_p(a) + \nu_p(b)$ holds for all nonzero $a, b \in \mathbb{N}$ when `IsPrime p`, unreduced common factors in `(x + y).num = x.num * ↑y.den + y.num * ↑x.den` and `(x + y).den = x.den * y.den` cancel identically without requiring GCD normalization.

---

### `src/LeanAsm/QuasiRiemann/Valuation/Ultrametric.lean`

*(Note: If your `lakefile.lean` omits `srcDir := "src"`, adjust the top `import` and namespace prefix from `LeanAsm.QuasiRiemann` to `QuasiRiemann` to match `Rat.lean`.)*

```lean
import LeanAsm.QuasiRiemann.Rat

namespace LeanAsm.QuasiRiemann.Valuation

/-!
# Constructive p-Adic Ultrametric Valuation over `QRat`

Zero-Mathlib, zero-`Classical.choice` formalization of prime valuations `ν_p`
and the strong ultrametric triangle inequality `ν_p(x + y) ≥ min(ν_p(x), ν_p(y))`
for cleared-denominator rationals `QRat`.
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
        · subst heq
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
          simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc] using h
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
          have hassoc : a * (p * q) = p * (a * q) := by ac_rfl
          rw [← hassoc]
          simpa [Nat.pow_succ, Nat.mul_comm] using h
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

def valMin : ExtVal → ExtVal → ExtVal
  | none, y => y
  | x, none => x
  | some a, some b => some (min a b)

/-- Constructive p-adic valuation `ν_p` on cleared-denominator `QRat`. -/
def pAdicVal (p : Nat) (q : QRat) : ExtVal :=
  if q.num == 0 then none
  else
    let vn : Int := Int.ofNat (padicValInt p q.num)
    let vd : Int := Int.ofNat (padicValNat p q.den)
    some (vn - vd)

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
  · have hxy_beq : ((x + y).num == 0) = false := beq_eq_false_iff_ne.mpr hxy0
    by_cases hx0 : x.num = 0
    · have hy0 : y.num ≠ 0 := by
        intro hy
        rw [hsum_num, hx0, hy] at hxy0
        simp at hxy0
      have hx_beq : (x.num == 0) = true := beq_iff_eq.mpr hx0
      have hy_beq : (y.num == 0) = false := beq_eq_false_iff_ne.mpr hy0
      simp only [pAdicVal, hx_beq, hy_beq, hxy_beq, ↓reduceIte, Bool.false_eq_true, valMin, valLe]
      have hnum_abs : (x + y).num.natAbs = y.num.natAbs * x.den := by
        rw [hsum_num, hx0]
        simp [Int.natAbs_mul, Int.natAbs_ofNat]
      have hy_abs_pos : 0 < y.num.natAbs := Int.natAbs_pos.mpr hy0
      unfold padicValInt
      rw [hnum_abs, hsum_den, padicValNat_mul hp hy_abs_pos hxd_pos,
        padicValNat_mul hp hxd_pos hyd_pos]
      omega
    · by_cases hy0 : y.num = 0
      · have hx_beq : (x.num == 0) = false := beq_eq_false_iff_ne.mpr hx0
        have hy_beq : (y.num == 0) = true := beq_iff_eq.mpr hy0
        simp only [pAdicVal, hx_beq, hy_beq, hxy_beq, ↓reduceIte, Bool.false_eq_true, valMin, valLe]
        have hnum_abs : (x + y).num.natAbs = x.num.natAbs * y.den := by
          rw [hsum_num, hy0]
          simp [Int.natAbs_mul, Int.natAbs_ofNat]
        have hx_abs_pos : 0 < x.num.natAbs := Int.natAbs_pos.mpr hx0
        unfold padicValInt
        rw [hnum_abs, hsum_den, padicValNat_mul hp hx_abs_pos hyd_pos,
          padicValNat_mul hp hxd_pos hyd_pos]
        omega
      · have hx_beq : (x.num == 0) = false := beq_eq_false_iff_ne.mpr hx0
        have hy_beq : (y.num == 0) = false := beq_eq_false_iff_ne.mpr hy0
        simp only [pAdicVal, hx_beq, hy_beq, hxy_beq, ↓reduceIte, Bool.false_eq_true, valMin, valLe]
        let A : Int := x.num * (y.den : Int)
        let B : Int := y.num * (x.den : Int)
        have hA_ne : A ≠ 0 := Int.mul_ne_zero hx0 (Int.ofNat_ne_zero.mpr (by omega))
        have hB_ne : B ≠ 0 := Int.mul_ne_zero hy0 (Int.ofNat_ne_zero.mpr (by omega))
        have hAB_ne : A + B ≠ 0 := by simpa [A, B, hsum_num] using hxy0
        have h_ultra := padicValInt_add_ge_min hp2 hA_ne hB_ne hAB_ne
        have hA_val : padicValInt p A = padicValInt p x.num + padicValNat p y.den := by
          unfold padicValInt
          have : A.natAbs = x.num.natAbs * y.den := by
            simp [A, Int.natAbs_mul, Int.natAbs_ofNat]
          rw [this, padicValNat_mul hp (Int.natAbs_pos.mpr hx0) hyd_pos]
        have hB_val : padicValInt p B = padicValInt p y.num + padicValNat p x.den := by
          unfold padicValInt
          have : B.natAbs = y.num.natAbs * x.den := by
            simp [B, Int.natAbs_mul, Int.natAbs_ofNat]
          rw [this, padicValNat_mul hp (Int.natAbs_pos.mpr hy0) hxd_pos]
        have hAB_eq : padicValInt p (x + y).num = padicValInt p (A + B) := by
          simp [A, B, hsum_num]
        rw [hAB_eq, hsum_den, padicValNat_mul hp hxd_pos hyd_pos]
        rw [hA_val, hB_val] at h_ultra
        omega

end LeanAsm.QuasiRiemann.Valuation

```

---

### Local Verification & Axiom Audit

Compile the module standalone first and confirm the transitive axiom cone contains no `Classical.choice` or `sorryAx`:

```bash
cd /home/fekerr/src/leanasm
lake build +LeanAsm.QuasiRiemann.Valuation.Ultrametric
make axioms
```

Expected output from `#print axioms`:

```text
'LeanAsm.QuasiRiemann.Valuation.ultrametric_ineq' depends on axioms: [propext]

```

*(Or `[propext, Quot.sound]` if `QRat` in `Rat.lean` touches `Quot`—still 100% free of `Classical.choice` and `sorryAx`.)*
