-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Contraction.lean
-- Constructive p-adic step contraction & telescoping Cauchy bounds over QRat (v1.3.0).
-- ZERO Classical.choice, ZERO sorryAx, ZERO Mathlib dependencies.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.Ultrametric

open _root_.QuasiRiemann

namespace QuasiRiemann.Valuation

/-!
# Constructive p-Adic Step Contraction & Telescoping Cauchy Bounds over `QRat`

Zero-Mathlib, zero-`Classical.choice` formalization of finite-depth `p`-adic
residue contractions and multi-step telescoping Cauchy difference bounds on `QRat`.
-/

theorem valLe_refl (v : ExtVal) : valLe v v := by
  cases v with
  | none => trivial
  | some a => exact Int.le_refl a

theorem valLe_trans {u v w : ExtVal} (h1 : valLe u v) (h2 : valLe v w) : valLe u w := by
  cases u with
  | none =>
    cases v with
    | none => exact h2
    | some _ => exact False.elim h1
  | some a =>
    cases v with
    | none =>
      cases w with
      | none => trivial
      | some _ => exact False.elim h2
    | some b =>
      cases w with
      | none => trivial
      | some c =>
        simp only [valLe] at h1 h2 ⊢
        omega

theorem valLe_valMin {b u v : ExtVal} (hu : valLe b u) (hv : valLe b v) :
    valLe b (valMin u v) := by
  cases b with
  | none =>
    cases u with
    | none => exact hv
    | some _ => exact False.elim hu
  | some a =>
    cases u with
    | none => exact hv
    | some x =>
      cases v with
      | none => exact hu
      | some y =>
        simp only [valLe] at hu hv
        simp only [valMin, valLe]
        omega

theorem valAdd_assoc (u v w : ExtVal) :
    valAdd (valAdd u v) w = valAdd u (valAdd v w) := by
  cases u <;> cases v <;> cases w <;> simp [valAdd, Int.add_assoc]

theorem valAdd_le_add_right {u v : ExtVal} (h : valLe u v) (w : ExtVal) :
    valLe (valAdd u w) (valAdd v w) := by
  cases u with
  | none =>
    cases v with
    | none => exact valLe_refl _
    | some _ => exact False.elim h
  | some a =>
    cases v with
    | none =>
      cases w <;> simp [valAdd, valLe]
    | some b =>
      cases w with
      | none => simp [valAdd, valLe]
      | some c =>
        simp only [valLe] at h
        simp only [valAdd, valLe]
        omega

theorem valLe_valAdd_of_nonneg (v : ExtVal) {s : Int} (hs : 0 ≤ s) :
    valLe v (valAdd v (some s)) := by
  cases v with
  | none => trivial
  | some a =>
    simp only [valAdd, valLe]
    omega

private theorem ofNat_succ_mul (k : Nat) (step : Int) :
    Int.ofNat (k + 1) * step = Int.ofNat k * step + step := by
  have h1 : Int.ofNat (k + 1) = Int.ofNat k + 1 := rfl
  rw [h1, Int.add_mul, Int.one_mul]

private theorem int_ofNat_le_mul_of_nonneg {a b : Nat} (hab : a ≤ b) {s : Int} (hs : 0 ≤ s) :
    Int.ofNat a * s ≤ Int.ofNat b * s := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have h1 : Int.ofNat (a + d) = Int.ofNat a + Int.ofNat d := rfl
  rw [h1, Int.add_mul]
  have hd : (0 : Int) ≤ Int.ofNat d := Int.natCast_nonneg d
  have hnonneg : 0 ≤ Int.ofNat d * s := Int.mul_nonneg hd hs
  omega

/-! ### Cleared-Denominator `QRat` Valuation Invariance & Telescoping Identity -/

private theorem qrat_sub_num (x y : QRat) :
    (x - y).num = x.num * (y.den : Int) - y.num * (x.den : Int) := rfl

private theorem qrat_sub_den (x y : QRat) :
    (x - y).den = x.den * y.den := rfl

theorem pAdicVal_sub_self (p : Nat) (x : QRat) :
    pAdicVal p (x - x) = none := by
  have hnum : (x - x).num = 0 := by
    rw [qrat_sub_num]
    omega
  simp [pAdicVal, hnum]

/-- Valuation invariance under cleared-denominator cross-multiplication equivalence. -/
theorem pAdicVal_eq_of_cross_mul {p : Nat} (hp : IsPrime p) {u v : QRat}
    (h : u.num * (v.den : Int) = v.num * (u.den : Int)) :
    pAdicVal p u = pAdicVal p v := by
  have hud_pos : 0 < u.den := u.den_pos
  have hvd_pos : 0 < v.den := v.den_pos
  by_cases hu0 : u.num = 0
  · have hv0 : v.num = 0 := by
      have h0 : v.num * (u.den : Int) = 0 := by
        rw [← h, hu0, Int.zero_mul]
      rcases Int.mul_eq_zero.mp h0 with hv | hd
      · exact hv
      · omega
    simp [pAdicVal, hu0, hv0]
  · have hv0 : v.num ≠ 0 := by
      intro hv
      have h0 : u.num * (v.den : Int) = 0 := by
        rw [h, hv, Int.zero_mul]
      rcases Int.mul_eq_zero.mp h0 with hu | hd
      · exact hu0 hu
      · omega
    have habs_eq : u.num.natAbs * v.den = v.num.natAbs * u.den := by
      have h1 := congrArg Int.natAbs h
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using h1
    have hval_eq :
        padicValNat p u.num.natAbs + padicValNat p v.den =
        padicValNat p v.num.natAbs + padicValNat p u.den := by
      have hu_pos : 0 < u.num.natAbs := Int.natAbs_pos.mpr hu0
      have hv_pos : 0 < v.num.natAbs := Int.natAbs_pos.mpr hv0
      rw [← padicValNat_mul hp hu_pos hvd_pos,
          ← padicValNat_mul hp hv_pos hud_pos,
          habs_eq]
    simp only [pAdicVal, hu0, hv0, ↓reduceIte, padicValInt]
    congr 1
    omega

private theorem sub_add_sub_cross_mul (a b c : QRat) :
    ((a - b) + (b - c)).num * ((a - c).den : Int) =
    (a - c).num * (((a - b) + (b - c)).den : Int) := by
  have hsum_num :
      ((a - b) + (b - c)).num =
      (a - b).num * ((b - c).den : Int) + (b - c).num * ((a - b).den : Int) := rfl
  have hsum_den :
      ((a - b) + (b - c)).den = (a - b).den * (b - c).den := rfl
  rw [hsum_num, hsum_den, qrat_sub_num a b, qrat_sub_num b c, qrat_sub_num a c,
      qrat_sub_den a b, qrat_sub_den b c, qrat_sub_den a c]
  simp only [Int.natCast_mul]
  let an : Int := a.num
  let bn : Int := b.num
  let cn : Int := c.num
  let ad : Int := (a.den : Int)
  let bd : Int := (b.den : Int)
  let cd : Int := (c.den : Int)
  let M : Int := bd * (bn * ad * cd)
  have h_left_term :
      (an * bd - bn * ad) * (bd * cd) = an * bd * (bd * cd) - M := by
    rw [Int.sub_mul]
    congr 1
    change bn * ad * (bd * cd) = bd * (bn * ad * cd)
    ac_rfl
  have h_right_term :
      (bn * cd - cn * bd) * (ad * bd) = M - cn * bd * (ad * bd) := by
    rw [Int.sub_mul]
    congr 1
    change bn * cd * (ad * bd) = bd * (bn * ad * cd)
    ac_rfl
  have h_cancel :
      (an * bd - bn * ad) * (bd * cd) + (bn * cd - cn * bd) * (ad * bd) =
      an * bd * (bd * cd) - cn * bd * (ad * bd) := by
    rw [h_left_term, h_right_term]
    omega
  change ((an * bd - bn * ad) * (bd * cd) + (bn * cd - cn * bd) * (ad * bd)) * (ad * cd) =
    (an * cd - cn * ad) * (ad * bd * (bd * cd))
  rw [h_cancel, Int.sub_mul, Int.sub_mul]
  congr 1 <;> ac_rfl

theorem pAdicVal_sub_add_sub {p : Nat} (hp : IsPrime p) (a b c : QRat) :
    pAdicVal p ((a - b) + (b - c)) = pAdicVal p (a - c) :=
  pAdicVal_eq_of_cross_mul hp (sub_add_sub_cross_mul a b c)

/-! ### Constructive Step Contraction & Telescoping Cauchy Bounds -/

/-- Constructive `k`-step `p`-adic contraction on `QRat`:
    each application of `f` increases `ν_p(Δx)` by at least `step ≥ 1`. -/
def IsPAdicStepContraction (p : Nat) (step : Int) (f : QRat → QRat) : Prop :=
  1 ≤ step ∧
  ∀ x y : QRat,
    valLe (valAdd (pAdicVal p (x - y)) (some step))
          (pAdicVal p (f x - f y))

/-- **n-Step Ultrametric Valuation Growth Certificate:**
    After `n` iterations, `ν_p(f^{n+1}(x₀) - f^n(x₀)) ≥ ν_p(f(x₀) - x₀) + n * step`. -/
theorem iterate_val_growth (p : Nat) (step : Int) (f : QRat → QRat)
    (h_cont : IsPAdicStepContraction p step f) (x₀ : QRat) :
    ∀ n : Nat,
      valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step)))
            (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) := by
  intro n
  induction n with
  | zero =>
    change valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some ((0 : Int) * step)))
                 (pAdicVal p (f x₀ - x₀))
    cases h0 : pAdicVal p (f x₀ - x₀) with
    | none => simp [valLe]
    | some a =>
      simp only [valAdd, valLe]
      omega
  | succ k ih =>
    have h_step :
        valLe (valAdd (pAdicVal p (Nat.repeat f (k + 1) x₀ - Nat.repeat f k x₀)) (some step))
              (pAdicVal p (Nat.repeat f (k + 2) x₀ - Nat.repeat f (k + 1) x₀)) :=
      h_cont.2 (Nat.repeat f (k + 1) x₀) (Nat.repeat f k x₀)
    have h_ih_step :
        valLe (valAdd (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat k * step))) (some step))
              (valAdd (pAdicVal p (Nat.repeat f (k + 1) x₀ - Nat.repeat f k x₀)) (some step)) :=
      valAdd_le_add_right ih (some step)
    have h_combined :
        valLe (valAdd (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat k * step))) (some step))
              (pAdicVal p (Nat.repeat f (k + 2) x₀ - Nat.repeat f (k + 1) x₀)) :=
      valLe_trans h_ih_step h_step
    rw [valAdd_assoc] at h_combined
    have h_collapse :
        valAdd (pAdicVal p (f x₀ - x₀))
               (valAdd (some (Int.ofNat k * step)) (some step)) =
        valAdd (pAdicVal p (f x₀ - x₀))
               (some (Int.ofNat (k + 1) * step)) := by
      simp only [valAdd, ofNat_succ_mul]
    rw [h_collapse] at h_combined
    exact h_combined

/-- Explicit floor certificate: if `ν_p(f(x₀) - x₀) ≥ m`, then
    `ν_p(f^{n+1}(x₀) - f^n(x₀)) ≥ m + n * step`. -/
theorem iterate_val_ge_of_init (p : Nat) (step m : Int) (f : QRat → QRat)
    (h_cont : IsPAdicStepContraction p step f) (x₀ : QRat)
    (h_init : valLe (some m) (pAdicVal p (f x₀ - x₀))) (n : Nat) :
    valLe (some (m + Int.ofNat n * step))
          (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) := by
  have h1 :
      valLe (valAdd (some m) (some (Int.ofNat n * step)))
            (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step))) :=
    valAdd_le_add_right h_init (some (Int.ofNat n * step))
  exact valLe_trans h1 (iterate_val_growth p step f h_cont x₀ n)

/-- Monotone valuation increase across consecutive iterates. -/
theorem iterate_val_mono (p : Nat) (step : Int) (f : QRat → QRat)
    (h_cont : IsPAdicStepContraction p step f) (x₀ : QRat) (n : Nat) :
    valLe (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀))
          (pAdicVal p (Nat.repeat f (n + 2) x₀ - Nat.repeat f (n + 1) x₀)) := by
  have h_nonneg : 0 ≤ step := by
    have := h_cont.1
    omega
  exact valLe_trans
    (valLe_valAdd_of_nonneg (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) h_nonneg)
    (h_cont.2 (Nat.repeat f (n + 1) x₀) (Nat.repeat f n x₀))

/-- **Telescoping Cauchy Difference Bound:**
    For every `n` and arbitrary lookahead `k`, the cumulative displacement
    `f^{n+k}(x₀) - f^n(x₀)` satisfies
    `ν_p(f^{n+k}(x₀) - f^n(x₀)) ≥ ν_p(f(x₀) - x₀) + n * step`,
    collapsing the `k`-step sum via `ultrametric_ineq` with zero geometric-series slack. -/
theorem iterate_val_range (p : Nat) (hp : IsPrime p) (step : Int) (f : QRat → QRat)
    (h_cont : IsPAdicStepContraction p step f) (x₀ : QRat) (n k : Nat) :
    valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step)))
          (pAdicVal p (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀)) := by
  have h_nonneg : 0 ≤ step := by
    have := h_cont.1
    omega
  induction k with
  | zero =>
    rw [Nat.add_zero, pAdicVal_sub_self]
    trivial
  | succ m ih =>
    have h_step_growth :
        valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step)))
              (pAdicVal p (Nat.repeat f (n + m + 1) x₀ - Nat.repeat f (n + m) x₀)) := by
      have h_le :
          valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step)))
                (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat (n + m) * step))) := by
        cases h0 : pAdicVal p (f x₀ - x₀) with
        | none => simp [valAdd, valLe]
        | some a =>
          simp only [valAdd, valLe]
          have hmul := int_ofNat_le_mul_of_nonneg (by omega : n ≤ n + m) h_nonneg
          omega
      exact valLe_trans h_le (iterate_val_growth p step f h_cont x₀ (n + m))
    have h_min :
        valLe (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step)))
              (valMin
                (pAdicVal p (Nat.repeat f (n + m + 1) x₀ - Nat.repeat f (n + m) x₀))
                (pAdicVal p (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀))) :=
      valLe_valMin h_step_growth ih
    have h_ultra :=
      ultrametric_ineq p hp
        (Nat.repeat f (n + m + 1) x₀ - Nat.repeat f (n + m) x₀)
        (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀)
    have h_combined := valLe_trans h_min h_ultra
    rw [pAdicVal_sub_add_sub hp] at h_combined
    simpa [Nat.add_assoc] using h_combined

/-- Explicit multi-step Cauchy floor: if `ν_p(f(x₀) - x₀) ≥ m`, then for all
    `n` and `k`, `ν_p(f^{n+k}(x₀) - f^n(x₀)) ≥ m + n * step`. -/
theorem iterate_val_range_of_init (p : Nat) (hp : IsPrime p) (step m : Int) (f : QRat → QRat)
    (h_cont : IsPAdicStepContraction p step f) (x₀ : QRat)
    (h_init : valLe (some m) (pAdicVal p (f x₀ - x₀))) (n k : Nat) :
    valLe (some (m + Int.ofNat n * step))
          (pAdicVal p (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀)) := by
  have h1 :
      valLe (valAdd (some m) (some (Int.ofNat n * step)))
            (valAdd (pAdicVal p (f x₀ - x₀)) (some (Int.ofNat n * step))) :=
    valAdd_le_add_right h_init (some (Int.ofNat n * step))
  exact valLe_trans h1 (iterate_val_range p hp step f h_cont x₀ n k)

end QuasiRiemann.Valuation

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Contraction.lean
