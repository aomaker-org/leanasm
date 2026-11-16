-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Hensel.lean
-- Constructive p-adic Hensel / Newton-Schulz modular inverse lifting over QRat (v1.3.0).
-- ZERO Classical.choice, ZERO sorryAx, ZERO Mathlib dependencies.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.Ultrametric
import LeanAsm.QuasiRiemann.Valuation.Contraction

open _root_.QuasiRiemann

namespace QuasiRiemann.Valuation

/-!
# Constructive p-Adic Hensel / Newton-Schulz Modular Inverse Lifting over `QRat`

Zero-Mathlib, zero-`Classical.choice` formalization of:
1. Stationary Newton-Schulz iteration `f(x) = x + u₀ * (1 - a * x)` instantiating
   `IsPAdicStepContraction` and telescoping Cauchy bounds from `Contraction.lean`.
2. Quadratic Newton-Schulz iteration `nsStep(a, x) = x * (2 - a * x)` proving
   exponential `2^n * m` `p`-adic residual lifting and quadratic Cauchy stability.
-/

/-- Constructive `1 : QRat`. -/
def qOne : QRat :=
  { num := 1, den := 1, den_pos := Nat.zero_lt_succ 0 }

/-- Constructive `2 : QRat`. -/
def qTwo : QRat :=
  { num := 2, den := 1, den_pos := Nat.zero_lt_succ 0 }

/-- Cleared-denominator cross-multiplication equivalence on `QRat`. -/
def CrossEq (u v : QRat) : Prop :=
  u.num * (v.den : Int) = v.num * (u.den : Int)

private theorem qrat_add_num (x y : QRat) :
    (x + y).num = x.num * (y.den : Int) + y.num * (x.den : Int) := rfl

private theorem qrat_add_den (x y : QRat) :
    (x + y).den = x.den * y.den := rfl

private theorem qrat_sub_num' (x y : QRat) :
    (x - y).num = x.num * (y.den : Int) - y.num * (x.den : Int) := rfl

private theorem qrat_sub_den' (x y : QRat) :
    (x - y).den = x.den * y.den := rfl

private theorem qrat_mul_num' (x y : QRat) :
    (x * y).num = x.num * y.num := rfl

private theorem qrat_mul_den' (x y : QRat) :
    (x * y).den = x.den * y.den := rfl

private theorem add_sub_cancel_left_cross_eq (u z : QRat) :
    CrossEq ((u + z) - u) z := by
  unfold CrossEq
  rw [qrat_sub_num', qrat_sub_den', qrat_add_num, qrat_add_den]
  simp only [Int.natCast_mul]
  let un : Int := u.num
  let ud : Int := (u.den : Int)
  let zn : Int := z.num
  let zd : Int := (z.den : Int)
  change ((un * zd + zn * ud) * ud - un * (ud * zd)) * zd = zn * (ud * zd * ud)
  have h_cancel :
      (un * zd + zn * ud) * ud - un * (ud * zd) = (zn * ud) * ud := by
    rw [Int.add_mul]
    have h_eq : (un * zd) * ud = un * (ud * zd) := by ac_rfl
    omega
  rw [h_cancel]
  ac_rfl

theorem pAdicVal_sub_eq_add_neg (p : Nat) (x y : QRat) :
    pAdicVal p (x - y) = pAdicVal p (x + (-y)) := by
  apply pAdicVal_eq_of_num_den_eq
  · rw [qrat_sub_num', qrat_add_num]
    have hneg : (-y).num = -y.num := rfl
    have hden : (-y).den = y.den := rfl
    rw [hneg, hden, Int.neg_mul]
    omega
  · rfl

theorem valLe_zero_pAdicVal_qTwo (p : Nat) (hp : IsPrime p) :
    valLe (some 0) (pAdicVal p qTwo) := by
  have hp2 : 2 ≤ p := hp.1
  have h1 : padicValNat p 1 = 0 :=
    padicValNat_of_not_dvd hp2 (Nat.zero_lt_succ 0) (fun hdvd => by
      have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hdvd
      omega)
  simp [pAdicVal, qTwo, padicValInt, h1, valLe]

/-! ### Part 1: Stationary Newton-Schulz Step Contraction -/

/-- Stationary preconditioned Newton-Schulz step with fixed seed `u₀`:
    `f_{a,u₀}(x) = x + u₀ * (1 - a * x)`. -/
def stationaryNewtonStep (a u₀ x : QRat) : QRat :=
  x + u₀ * (qOne - a * x)

private theorem stationary_eval_num_den (a u₀ x : QRat) :
    (stationaryNewtonStep a u₀ x).num =
      (x.den : Int) *
        (x.num * ((u₀.den : Int) * (a.den : Int)) +
          u₀.num * ((a.den : Int) * (x.den : Int) - a.num * x.num)) ∧
    ((stationaryNewtonStep a u₀ x).den : Int) =
      (x.den : Int) * ((u₀.den : Int) * ((a.den : Int) * (x.den : Int))) := by
  unfold stationaryNewtonStep
  rw [qrat_add_num, qrat_add_den, qrat_mul_num', qrat_mul_den',
      qrat_sub_num', qrat_sub_den', qrat_mul_num', qrat_mul_den']
  simp only [qOne, Int.natCast_mul]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let un : Int := u₀.num
  let ud : Int := (u₀.den : Int)
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  change
    xn * (ud * (1 * (ad * xd))) + un * (1 * (ad * xd) - an * xn * 1) * xd =
      xd * (xn * (ud * ad) + un * (ad * xd - an * xn)) ∧
    xd * (ud * (1 * (ad * xd))) = xd * (ud * (ad * xd))
  have h1 : 1 * (ad * xd) - an * xn * 1 = ad * xd - an * xn := by omega
  have h2 : (1 : Int) * (ad * xd) = ad * xd := Int.one_mul (ad * xd)
  rw [h1, h2]
  refine ⟨?_, rfl⟩
  rw [Int.mul_add]
  congr 1 <;> ac_rfl

/-- Algebraic difference identity for stationary Newton-Schulz:
    `f(x) - f(y) ~ (1 - a * u₀) * (x - y)`. -/
theorem stationary_diff_cross_eq (a u₀ x y : QRat) :
    CrossEq (stationaryNewtonStep a u₀ x - stationaryNewtonStep a u₀ y)
            ((qOne - a * u₀) * (x - y)) := by
  unfold CrossEq
  obtain ⟨hfx_num, hfx_den⟩ := stationary_eval_num_den a u₀ x
  obtain ⟨hfy_num, hfy_den⟩ := stationary_eval_num_den a u₀ y
  rw [qrat_sub_num', qrat_sub_den', qrat_mul_num', qrat_mul_den',
      qrat_sub_num' qOne (a * u₀), qrat_sub_den' qOne (a * u₀),
      qrat_mul_num' a u₀, qrat_mul_den' a u₀,
      qrat_sub_num' x y, qrat_sub_den' x y]
  simp only [qOne, Int.natCast_mul]
  rw [hfx_num, hfx_den, hfy_num, hfy_den]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let un : Int := u₀.num
  let ud : Int := (u₀.den : Int)
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  let yn : Int := y.num
  let yd : Int := (y.den : Int)
  let Bx : Int := xn * (ud * ad) + un * (ad * xd - an * xn)
  let By : Int := yn * (ud * ad) + un * (ad * yd - an * yn)
  let K : Int := xd * yd * (ud * ad)
  change
    ((xd * Bx) * (yd * (ud * (ad * yd))) - (yd * By) * (xd * (ud * (ad * xd)))) *
        ((1 : Int) * (ad * ud) * (xd * yd)) =
      ((1 * (ad * ud) - an * un * 1) * (xn * yd - yn * xd)) *
        ((xd * (ud * (ad * xd))) * (yd * (ud * (ad * yd))))
  have hr0 : 1 * (ad * ud) - an * un * 1 = ad * ud - an * un := by omega
  rw [hr0]
  have h_lhs_num :
      (xd * Bx) * (yd * (ud * (ad * yd))) - (yd * By) * (xd * (ud * (ad * xd))) =
      K * (Bx * yd - By * xd) := by
    have t1 : (xd * Bx) * (yd * (ud * (ad * yd))) = K * (Bx * yd) := by
      dsimp [K]; ac_rfl
    have t2 : (yd * By) * (xd * (ud * (ad * xd))) = K * (By * xd) := by
      dsimp [K]; ac_rfl
    rw [t1, t2, ← Int.mul_sub]
  have h_Bx_yd :
      Bx * yd =
      (xn * (ud * ad)) * yd + ((un * (ad * xd)) * yd - (un * (an * xn)) * yd) := by
    dsimp [Bx]
    rw [Int.add_mul, Int.mul_sub, Int.sub_mul]
  have h_By_xd :
      By * xd =
      (yn * (ud * ad)) * xd + ((un * (ad * yd)) * xd - (un * (an * yn)) * xd) := by
    dsimp [By]
    rw [Int.add_mul, Int.mul_sub, Int.sub_mul]
  have h_cross_cancel : (un * (ad * yd)) * xd = (un * (ad * xd)) * yd := by ac_rfl
  have h_bracket :
      Bx * yd - By * xd = (ad * ud - an * un) * (xn * yd - yn * xd) := by
    rw [h_Bx_yd, h_By_xd, h_cross_cancel]
    have h_lin :
        ((xn * (ud * ad)) * yd + ((un * (ad * xd)) * yd - (un * (an * xn)) * yd)) -
        ((yn * (ud * ad)) * xd + ((un * (ad * xd)) * yd - (un * (an * yn)) * xd)) =
        ((xn * (ud * ad)) * yd - (yn * (ud * ad)) * xd) -
        ((un * (an * xn)) * yd - (un * (an * yn)) * xd) := by
      omega
    rw [h_lin]
    have p1 : (xn * (ud * ad)) * yd - (yn * (ud * ad)) * xd =
        (ad * ud) * (xn * yd - yn * xd) := by
      have a1 : (xn * (ud * ad)) * yd = (ad * ud) * (xn * yd) := by ac_rfl
      have a2 : (yn * (ud * ad)) * xd = (ad * ud) * (yn * xd) := by ac_rfl
      rw [a1, a2, ← Int.mul_sub]
    have p2 : (un * (an * xn)) * yd - (un * (an * yn)) * xd =
        (an * un) * (xn * yd - yn * xd) := by
      have b1 : (un * (an * xn)) * yd = (an * un) * (xn * yd) := by ac_rfl
      have b2 : (un * (an * yn)) * xd = (an * un) * (yn * xd) := by ac_rfl
      rw [b1, b2, ← Int.mul_sub]
    rw [p1, p2, ← Int.sub_mul]
  have h_lhs_den :
      (xd * (ud * (ad * xd))) * (yd * (ud * (ad * yd))) =
      K * ((1 : Int) * (ad * ud) * (xd * yd)) := by
    dsimp [K]
    simp only [Int.one_mul]
    ac_rfl
  rw [h_lhs_num, h_bracket, h_lhs_den]
  ac_rfl

/-- Algebraic residual identity for stationary Newton-Schulz:
    `1 - a * f(x) ~ (1 - a * u₀) * (1 - a * x)`. -/
theorem stationary_residual_cross_eq (a u₀ x : QRat) :
    CrossEq (qOne - a * stationaryNewtonStep a u₀ x)
            ((qOne - a * u₀) * (qOne - a * x)) := by
  unfold CrossEq
  obtain ⟨hfx_num, hfx_den⟩ := stationary_eval_num_den a u₀ x
  rw [qrat_sub_num' qOne (a * stationaryNewtonStep a u₀ x),
      qrat_sub_den' qOne (a * stationaryNewtonStep a u₀ x),
      qrat_mul_num' a (stationaryNewtonStep a u₀ x),
      qrat_mul_den' a (stationaryNewtonStep a u₀ x),
      qrat_mul_num' (qOne - a * u₀) (qOne - a * x),
      qrat_mul_den' (qOne - a * u₀) (qOne - a * x),
      qrat_sub_num' qOne (a * u₀), qrat_sub_den' qOne (a * u₀),
      qrat_sub_num' qOne (a * x), qrat_sub_den' qOne (a * x),
      qrat_mul_num' a u₀, qrat_mul_den' a u₀,
      qrat_mul_num' a x, qrat_mul_den' a x]
  simp only [qOne, Int.natCast_mul]
  rw [hfx_num, hfx_den]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let un : Int := u₀.num
  let ud : Int := (u₀.den : Int)
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  let Bx : Int := xn * (ud * ad) + un * (ad * xd - an * xn)
  change
    (1 * (ad * (xd * (ud * (ad * xd)))) - an * (xd * Bx) * 1) *
        ((1 : Int) * (ad * ud) * ((1 : Int) * (ad * xd))) =
      ((1 * (ad * ud) - an * un * 1) * (1 * (ad * xd) - an * xn * 1)) *
        ((1 : Int) * (ad * (xd * (ud * (ad * xd)))))
  have hr0 : 1 * (ad * ud) - an * un * 1 = ad * ud - an * un := by omega
  have hrx : 1 * (ad * xd) - an * xn * 1 = ad * xd - an * xn := by omega
  rw [hr0, hrx]
  have h_lhs_num :
      1 * (ad * (xd * (ud * (ad * xd)))) - an * (xd * Bx) * 1 =
      xd * ((ad * ud - an * un) * (ad * xd - an * xn)) := by
    have h_factor :
        1 * (ad * (xd * (ud * (ad * xd)))) - an * (xd * Bx) * 1 =
        xd * (ad * (ud * (ad * xd)) - an * Bx) := by
      have f1 : 1 * (ad * (xd * (ud * (ad * xd)))) = xd * (ad * (ud * (ad * xd))) := by
        simp only [Int.one_mul]; ac_rfl
      have f2 : an * (xd * Bx) * 1 = xd * (an * Bx) := by
        simp only [Int.mul_one]; ac_rfl
      rw [f1, f2, ← Int.mul_sub]
    rw [h_factor]
    congr 1
    have h_an_Bx :
        an * Bx = (ad * ud) * (an * xn) + (an * un) * (ad * xd - an * xn) := by
      dsimp [Bx]
      rw [Int.mul_add]
      congr 1 <;> ac_rfl
    have h_lead : ad * (ud * (ad * xd)) = (ad * ud) * (ad * xd) := by ac_rfl
    rw [h_lead, h_an_Bx]
    have h_sub1 :
        (ad * ud) * (ad * xd) - ((ad * ud) * (an * xn) + (an * un) * (ad * xd - an * xn)) =
        ((ad * ud) * (ad * xd) - (ad * ud) * (an * xn)) - (an * un) * (ad * xd - an * xn) := by
      omega
    rw [h_sub1, ← Int.mul_sub, ← Int.sub_mul]
  have h_lhs_den :
      (1 : Int) * (ad * (xd * (ud * (ad * xd)))) =
      xd * ((1 : Int) * (ad * ud) * ((1 : Int) * (ad * xd))) := by
    simp only [Int.one_mul]
    ac_rfl
  rw [h_lhs_num, h_lhs_den]
  ac_rfl

/-- **Stationary Newton-Schulz Contraction Theorem:**
    If `ν_p(1 - a * u₀) ≥ step ≥ 1`, then `stationaryNewtonStep a u₀` is a
    global `IsPAdicStepContraction` on `QRat`. -/
theorem stationary_isStepContraction {p : Nat} (hp : IsPrime p) {step : Int}
    (hstep : 1 ≤ step) (a u₀ : QRat)
    (h_seed : valLe (some step) (pAdicVal p (qOne - a * u₀))) :
    IsPAdicStepContraction p step (stationaryNewtonStep a u₀) := by
  refine ⟨hstep, ?_⟩
  intro x y
  rw [pAdicVal_eq_of_cross_mul hp (stationary_diff_cross_eq a u₀ x y),
      pAdicVal_mul p hp (qOne - a * u₀) (x - y)]
  have h_comm :
      valAdd (pAdicVal p (qOne - a * u₀)) (pAdicVal p (x - y)) =
      valAdd (pAdicVal p (x - y)) (pAdicVal p (qOne - a * u₀)) := by
    cases pAdicVal p (qOne - a * u₀) <;> cases pAdicVal p (x - y) <;>
      simp [valAdd, Int.add_comm]
  rw [h_comm]
  cases hv : pAdicVal p (x - y) with
  | none => simp [valAdd, valLe]
  | some d =>
    cases hr : pAdicVal p (qOne - a * u₀) with
    | none => simp [valAdd, valLe]
    | some r =>
      rw [hr] at h_seed
      simp only [valLe] at h_seed
      simp only [valAdd, valLe]
      omega

/-- **Stationary Newton-Schulz Modular Residual Lift:**
    After `n` stationary iterations from `u₀` (with `ν_p(1 - a * u₀) ≥ step`),
    the modular inverse residual satisfies `ν_p(1 - a * x_n) ≥ (n + 1) * step`. -/
theorem stationary_residual_growth {p : Nat} (hp : IsPrime p) {step : Int}
    (_hstep : 1 ≤ step) (a u₀ : QRat)
    (h_seed : valLe (some step) (pAdicVal p (qOne - a * u₀))) (n : Nat) :
    valLe (some (Int.ofNat (n + 1) * step))
          (pAdicVal p (qOne - a * Nat.repeat (stationaryNewtonStep a u₀) n u₀)) := by
  induction n with
  | zero =>
    have h1 : Int.ofNat 1 * step = step := by
      change (1 : Int) * step = step
      omega
    rw [h1]
    exact h_seed
  | succ k ih =>
    let xk := Nat.repeat (stationaryNewtonStep a u₀) k u₀
    change valLe (some (Int.ofNat (k + 2) * step))
                 (pAdicVal p (qOne - a * stationaryNewtonStep a u₀ xk))
    rw [pAdicVal_eq_of_cross_mul hp (stationary_residual_cross_eq a u₀ xk),
        pAdicVal_mul p hp (qOne - a * u₀) (qOne - a * xk)]
    have hcast : Int.ofNat (k + 2) = 1 + Int.ofNat (k + 1) := by
      change ((k + 2 : Nat) : Int) = 1 + ((k + 1 : Nat) : Int)
      omega
    rw [hcast, Int.add_mul, Int.one_mul]
    cases hr0 : pAdicVal p (qOne - a * u₀) with
    | none => simp [valAdd, valLe]
    | some r0 =>
      cases hrk : pAdicVal p (qOne - a * xk) with
      | none => simp [valAdd, valLe]
      | some rk =>
        rw [hr0] at h_seed
        rw [hrk] at ih
        simp only [valLe] at h_seed ih
        simp only [valAdd, valLe]
        omega

/-- **Stationary Newton-Schulz Telescoping Cauchy Certificate:**
    If `ν_p(u₀) ≥ 0` and `ν_p(1 - a * u₀) ≥ step ≥ 1`, then for all `n` and `k`,
    `ν_p(x_{n+k} - x_n) ≥ (n + 1) * step` across arbitrary lookahead `k`. -/
theorem stationary_iterate_cauchy_range {p : Nat} (hp : IsPrime p) {step : Int}
    (hstep : 1 ≤ step) (a u₀ : QRat)
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_seed : valLe (some step) (pAdicVal p (qOne - a * u₀))) (n k : Nat) :
    valLe (some (Int.ofNat (n + 1) * step))
          (pAdicVal p (Nat.repeat (stationaryNewtonStep a u₀) (n + k) u₀ -
                       Nat.repeat (stationaryNewtonStep a u₀) n u₀)) := by
  have h_cont := stationary_isStepContraction hp hstep a u₀ h_seed
  have h_init : valLe (some step) (pAdicVal p (stationaryNewtonStep a u₀ u₀ - u₀)) := by
    unfold stationaryNewtonStep
    rw [pAdicVal_eq_of_cross_mul hp (add_sub_cancel_left_cross_eq u₀ (u₀ * (qOne - a * u₀))),
        pAdicVal_mul p hp u₀ (qOne - a * u₀)]
    cases hu : pAdicVal p u₀ with
    | none => simp [valAdd, valLe]
    | some vu =>
      cases hr : pAdicVal p (qOne - a * u₀) with
      | none => simp [valAdd, valLe]
      | some vr =>
        rw [hu] at hu₀
        rw [hr] at h_seed
        simp only [valLe] at hu₀ h_seed
        simp only [valAdd, valLe]
        omega
  have h_range := iterate_val_range_of_init p hp step step (stationaryNewtonStep a u₀)
    h_cont u₀ h_init n k
  have hcast : Int.ofNat (n + 1) * step = step + Int.ofNat n * step := by
    have h1 : Int.ofNat (n + 1) = 1 + Int.ofNat n := by
      change ((n + 1 : Nat) : Int) = 1 + (n : Int)
      omega
    rw [h1, Int.add_mul, Int.one_mul]
  rw [hcast]
  exact h_range

/-! ### Part 2: Quadratic Newton-Schulz Modular Inverse Lifting -/

/-- Quadratic Newton-Schulz modular inverse refinement step:
    `nsStep(a, x) = x * (2 - a * x)`. -/
def nsStep (a x : QRat) : QRat :=
  x * (qTwo - a * x)

/-- Exact quadratic residual identity for Newton-Schulz:
    `1 - a * nsStep(a, x) ~ (1 - a * x)^2`. -/
theorem nsStep_residual_cross_eq (a x : QRat) :
    CrossEq (qOne - a * nsStep a x) ((qOne - a * x) * (qOne - a * x)) := by
  unfold CrossEq nsStep
  rw [qrat_sub_num' qOne (a * (x * (qTwo - a * x))),
      qrat_sub_den' qOne (a * (x * (qTwo - a * x))),
      qrat_mul_num' a (x * (qTwo - a * x)),
      qrat_mul_den' a (x * (qTwo - a * x)),
      qrat_mul_num' x (qTwo - a * x),
      qrat_mul_den' x (qTwo - a * x),
      qrat_sub_num' qTwo (a * x),
      qrat_sub_den' qTwo (a * x),
      qrat_mul_num' (qOne - a * x) (qOne - a * x),
      qrat_mul_den' (qOne - a * x) (qOne - a * x),
      qrat_sub_num' qOne (a * x),
      qrat_sub_den' qOne (a * x),
      qrat_mul_num' a x,
      qrat_mul_den' a x]
  simp only [qOne, qTwo, Int.natCast_mul, Int.natCast_one, Int.one_mul, Int.mul_one]
  rw [← Int.mul_assoc a.num x.num]
  let P : Int := (a.den : Int) * (x.den : Int)
  let Q : Int := a.num * x.num
  change
    ((a.den : Int) * ((x.den : Int) * P) - Q * (2 * P - Q)) * (P * P) =
      ((P - Q) * (P - Q)) * ((a.den : Int) * ((x.den : Int) * P))
  have h3 : (a.den : Int) * ((x.den : Int) * P) = P * P := by
    dsimp [P]; ac_rfl
  have h4 : Q * (2 * P - Q) = Q * (2 * P) - Q * Q := Int.mul_sub Q (2 * P) Q
  have h5 : (P - Q) * (P - Q) = (P * P - P * Q) - (Q * P - Q * Q) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have h6 : Q * (2 * P) = P * Q + Q * P := by
    have a1 : Q * (2 * P) = 2 * (P * Q) := by ac_rfl
    have a2 : Q * P = P * Q := by ac_rfl
    omega
  rw [h3, h4, h5, h6]
  have h_num_eq : P * P - (P * Q + Q * P - Q * Q) = (P * P - P * Q) - (Q * P - Q * Q) := by
    omega
  rw [h_num_eq]

/-- Quadratic valuation doubling on the modular residual:
    `ν_p(1 - a * nsStep(a, x)) = ν_p(1 - a * x) + ν_p(1 - a * x)`. -/
theorem nsStep_residual_val_double (p : Nat) (hp : IsPrime p) (a x : QRat) :
    pAdicVal p (qOne - a * nsStep a x) =
    valAdd (pAdicVal p (qOne - a * x)) (pAdicVal p (qOne - a * x)) := by
  rw [pAdicVal_eq_of_cross_mul hp (nsStep_residual_cross_eq a x),
      pAdicVal_mul p hp (qOne - a * x) (qOne - a * x)]

/-- **Hensel Quadratic Modular Inverse Lifting Certificate:**
    If `ν_p(1 - a * x₀) ≥ m ≥ 1`, then after `n` Newton-Schulz steps
    `ν_p(1 - a * nsStep^n(x₀)) ≥ 2^n * m`. -/
theorem hensel_newton_schulz_quadratic_residual (p : Nat) (hp : IsPrime p) (m : Int)
    (_hm : 1 ≤ m) (a x₀ : QRat)
    (h_init : valLe (some m) (pAdicVal p (qOne - a * x₀))) (n : Nat) :
    valLe (some (Int.ofNat (2 ^ n) * m))
          (pAdicVal p (qOne - a * Nat.repeat (nsStep a) n x₀)) := by
  induction n with
  | zero =>
    have h0 : Int.ofNat (2 ^ 0) * m = m := by
      change (1 : Int) * m = m
      omega
    rw [h0]
    exact h_init
  | succ k ih =>
    let xk := Nat.repeat (nsStep a) k x₀
    change valLe (some (Int.ofNat (2 ^ (k + 1)) * m))
                 (pAdicVal p (qOne - a * nsStep a xk))
    rw [nsStep_residual_val_double p hp a xk]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [Nat.pow_succ]
      omega
    have hcast : Int.ofNat (2 ^ (k + 1)) = Int.ofNat (2 ^ k) + Int.ofNat (2 ^ k) := by
      rw [hpow]
      rfl
    rw [hcast, Int.add_mul]
    cases hr : pAdicVal p (qOne - a * xk) with
    | none => simp [valAdd, valLe]
    | some r =>
      rw [hr] at ih
      simp only [valLe] at ih
      simp only [valAdd, valLe]
      omega

/-- Exact step-update factorization for Newton-Schulz:
    `nsStep(a, x) - x ~ x * (1 - a * x)`. -/
theorem nsStep_sub_self_cross_eq (a x : QRat) :
    CrossEq (nsStep a x - x) (x * (qOne - a * x)) := by
  unfold CrossEq nsStep
  rw [qrat_sub_num', qrat_sub_den',
      qrat_mul_num' x (qTwo - a * x), qrat_mul_den' x (qTwo - a * x),
      qrat_sub_num' qTwo (a * x), qrat_sub_den' qTwo (a * x),
      qrat_mul_num' x (qOne - a * x), qrat_mul_den' x (qOne - a * x),
      qrat_sub_num' qOne (a * x), qrat_sub_den' qOne (a * x),
      qrat_mul_num' a x, qrat_mul_den' a x]
  simp only [qOne, qTwo, Int.natCast_mul, Int.natCast_one, Int.one_mul, Int.mul_one]
  let P : Int := (a.den : Int) * (x.den : Int)
  let Q : Int := a.num * x.num
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  change
    ((xn * (2 * P - Q)) * xd - xn * (xd * P)) * (xd * P) =
      (xn * (P - Q)) * (xd * P * xd)
  have h_lhs_num :
      (xn * (2 * P - Q)) * xd - xn * (xd * P) = xd * (xn * (P - Q)) := by
    have f1 : (xn * (2 * P - Q)) * xd - xn * (xd * P) =
        xd * (xn * (2 * P - Q) - xn * P) := by
      have a1 : (xn * (2 * P - Q)) * xd = xd * (xn * (2 * P - Q)) := by ac_rfl
      have a2 : xn * (xd * P) = xd * (xn * P) := by ac_rfl
      rw [a1, a2, ← Int.mul_sub]
    have f2 : xn * (2 * P - Q) - xn * P = xn * (P - Q) := by
      have b1 : 2 * P - Q = P + (P - Q) := by omega
      rw [b1, Int.mul_add]
      omega
    rw [f1, f2]
  have h_lhs_den : xd * P * xd = xd * (xd * P) := by ac_rfl
  rw [h_lhs_num, h_lhs_den]
  ac_rfl

/-- `p`-Adic integrality preservation under `nsStep`:
    if `ν_p(a) ≥ 0` and `ν_p(x) ≥ 0`, then `ν_p(nsStep(a, x)) ≥ 0`. -/
theorem nsStep_integrality {p : Nat} (hp : IsPrime p) {a x : QRat}
    (ha : valLe (some 0) (pAdicVal p a)) (hx : valLe (some 0) (pAdicVal p x)) :
    valLe (some 0) (pAdicVal p (nsStep a x)) := by
  unfold nsStep
  have hax : valLe (some 0) (pAdicVal p (a * x)) := by
    rw [pAdicVal_mul p hp a x]
    cases hva : pAdicVal p a with
    | none => simp [valAdd, valLe]
    | some va =>
      cases hvx : pAdicVal p x with
      | none => simp [valAdd, valLe]
      | some vx =>
        rw [hva] at ha
        rw [hvx] at hx
        simp only [valLe] at ha hx
        simp only [valAdd, valLe]
        omega
  have hneg_ax : valLe (some 0) (pAdicVal p (-(a * x))) := by
    rw [pAdicVal_neg]
    exact hax
  have h_two_sub : valLe (some 0) (pAdicVal p (qTwo - a * x)) := by
    rw [pAdicVal_sub_eq_add_neg]
    have h_min : valLe (some 0) (valMin (pAdicVal p qTwo) (pAdicVal p (-(a * x)))) :=
      valLe_valMin (valLe_zero_pAdicVal_qTwo p hp) hneg_ax
    exact valLe_trans h_min (ultrametric_ineq p hp qTwo (-(a * x)))
  rw [pAdicVal_mul p hp x (qTwo - a * x)]
  cases hx' : pAdicVal p x with
  | none => simp [valAdd, valLe]
  | some vx =>
    cases h2' : pAdicVal p (qTwo - a * x) with
    | none => simp [valAdd, valLe]
    | some v2 =>
      rw [hx'] at hx
      rw [h2'] at h_two_sub
      simp only [valLe] at hx h_two_sub
      simp only [valAdd, valLe]
      omega

theorem nsStep_iterate_integrality {p : Nat} (hp : IsPrime p) {a x₀ : QRat}
    (ha : valLe (some 0) (pAdicVal p a)) (hx₀ : valLe (some 0) (pAdicVal p x₀)) (n : Nat) :
    valLe (some 0) (pAdicVal p (Nat.repeat (nsStep a) n x₀)) := by
  induction n with
  | zero => exact hx₀
  | succ _ ih => exact nsStep_integrality hp ha ih

/-- Quadratic step-difference valuation bound:
    `ν_p(nsStep^{n+1}(x₀) - nsStep^n(x₀)) ≥ 2^n * m`. -/
theorem hensel_newton_schulz_step_bound (p : Nat) (hp : IsPrime p) (m : Int)
    (hm : 1 ≤ m) (a x₀ : QRat)
    (ha : valLe (some 0) (pAdicVal p a)) (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (h_init : valLe (some m) (pAdicVal p (qOne - a * x₀))) (n : Nat) :
    valLe (some (Int.ofNat (2 ^ n) * m))
          (pAdicVal p (Nat.repeat (nsStep a) (n + 1) x₀ -
                       Nat.repeat (nsStep a) n x₀)) := by
  let xn := Nat.repeat (nsStep a) n x₀
  change valLe (some (Int.ofNat (2 ^ n) * m)) (pAdicVal p (nsStep a xn - xn))
  rw [pAdicVal_eq_of_cross_mul hp (nsStep_sub_self_cross_eq a xn),
      pAdicVal_mul p hp xn (qOne - a * xn)]
  have h_int_xn := nsStep_iterate_integrality hp ha hx₀ n
  have h_res_xn := hensel_newton_schulz_quadratic_residual p hp m hm a x₀ h_init n
  cases hvx : pAdicVal p xn with
  | none => simp [valAdd, valLe]
  | some vx =>
    cases hvr : pAdicVal p (qOne - a * xn) with
    | none => simp [valAdd, valLe]
    | some vr =>
      rw [hvx] at h_int_xn
      rw [hvr] at h_res_xn
      simp only [valLe] at h_int_xn h_res_xn
      simp only [valAdd, valLe]
      omega

private theorem two_pow_le_add (n : Nat) : ∀ j : Nat, 2 ^ n ≤ 2 ^ (n + j)
  | 0 => Nat.le_refl (2 ^ n)
  | j + 1 => by
    rw [← Nat.add_assoc, Nat.pow_succ]
    exact Nat.le_trans (two_pow_le_add n j)
      (Nat.le_mul_of_pos_right (2 ^ (n + j)) (by decide))

private theorem ofNat_le_mul_of_nonneg {A B : Nat} (hAB : A ≤ B) {m : Int} (hm : 0 ≤ m) :
    Int.ofNat A * m ≤ Int.ofNat B * m := by
  obtain ⟨d, rfl⟩ : ∃ d, B = A + d := ⟨B - A, by omega⟩
  have hcast : Int.ofNat (A + d) = Int.ofNat A + Int.ofNat d := rfl
  rw [hcast, Int.add_mul]
  have hd_nonneg : (0 : Int) ≤ Int.ofNat d := Int.natCast_nonneg d
  have hnonneg : 0 ≤ Int.ofNat d * m := Int.mul_nonneg hd_nonneg hm
  omega

/-- **Quadratic Telescoping Cauchy Certificate for Newton-Schulz:**
    For every `n` and arbitrary lookahead `k`, the cumulative displacement
    `nsStep^{n+k}(x₀) - nsStep^n(x₀)` satisfies
    `ν_p(nsStep^{n+k}(x₀) - nsStep^n(x₀)) ≥ 2^n * m`. -/
theorem hensel_newton_schulz_cauchy_range (p : Nat) (hp : IsPrime p) (m : Int)
    (hm : 1 ≤ m) (a x₀ : QRat)
    (ha : valLe (some 0) (pAdicVal p a)) (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (h_init : valLe (some m) (pAdicVal p (qOne - a * x₀))) (n k : Nat) :
    valLe (some (Int.ofNat (2 ^ n) * m))
          (pAdicVal p (Nat.repeat (nsStep a) (n + k) x₀ -
                       Nat.repeat (nsStep a) n x₀)) := by
  induction k with
  | zero =>
    rw [Nat.add_zero, pAdicVal_sub_self]
    trivial
  | succ j ih =>
    have h_step_j :=
      hensel_newton_schulz_step_bound p hp m hm a x₀ ha hx₀ h_init (n + j)
    have h_mono :
        valLe (some (Int.ofNat (2 ^ n) * m)) (some (Int.ofNat (2 ^ (n + j)) * m)) :=
      ofNat_le_mul_of_nonneg (two_pow_le_add n j)
        (Int.le_trans (by decide : (0 : Int) ≤ 1) hm)
    have h_step_n :
        valLe (some (Int.ofNat (2 ^ n) * m))
              (pAdicVal p (Nat.repeat (nsStep a) (n + j + 1) x₀ -
                           Nat.repeat (nsStep a) (n + j) x₀)) :=
      valLe_trans h_mono h_step_j
    have h_min :
        valLe (some (Int.ofNat (2 ^ n) * m))
              (valMin
                (pAdicVal p (Nat.repeat (nsStep a) (n + j + 1) x₀ -
                             Nat.repeat (nsStep a) (n + j) x₀))
                (pAdicVal p (Nat.repeat (nsStep a) (n + j) x₀ -
                             Nat.repeat (nsStep a) n x₀))) :=
      valLe_valMin h_step_n ih
    have h_ultra :=
      ultrametric_ineq p hp
        (Nat.repeat (nsStep a) (n + j + 1) x₀ - Nat.repeat (nsStep a) (n + j) x₀)
        (Nat.repeat (nsStep a) (n + j) x₀ - Nat.repeat (nsStep a) n x₀)
    have h_combined := valLe_trans h_min h_ultra
    rw [pAdicVal_sub_add_sub hp] at h_combined
    have h_idx : n + (j + 1) = n + j + 1 := (Nat.add_assoc n j 1).symm
    rw [h_idx]
    exact h_combined

/-! ### Part 3: Bundled Hensel / Newton-Schulz Inverse Certificates & Concrete Primes -/

/-- Constructive embedding of `Int` into `QRat`. -/
def qOfInt (n : Int) : QRat :=
  QRat.ofInt n

theorem pAdicVal_qOne (p : Nat) (hp : IsPrime p) :
    pAdicVal p qOne = some 0 := by
  have hp2 : 2 ≤ p := hp.1
  have h1 : padicValNat p 1 = 0 :=
    padicValNat_of_not_dvd hp2 (Nat.zero_lt_succ 0) (fun hdvd => by
      have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hdvd
      omega)
  simp [pAdicVal, qOne, padicValInt, h1]

/-- Single-prime Hensel / Newton-Schulz modular inverse certificate bundling
    primality, quadratic residual lifting, step bounds, and Cauchy stability. -/
structure HenselInverseCert (p : Nat) (m : Int) (a x₀ : QRat) : Prop where
  prime : IsPrime p
  step_pos : 1 ≤ m
  a_int : valLe (some 0) (pAdicVal p a)
  x₀_int : valLe (some 0) (pAdicVal p x₀)
  init_residual : valLe (some m) (pAdicVal p (qOne - a * x₀))
  residual_lift :
    ∀ n : Nat,
      valLe (some (Int.ofNat (2 ^ n) * m))
            (pAdicVal p (qOne - a * Nat.repeat (nsStep a) n x₀))
  step_bound :
    ∀ n : Nat,
      valLe (some (Int.ofNat (2 ^ n) * m))
            (pAdicVal p (Nat.repeat (nsStep a) (n + 1) x₀ -
                         Nat.repeat (nsStep a) n x₀))
  cauchy_range :
    ∀ n k : Nat,
      valLe (some (Int.ofNat (2 ^ n) * m))
            (pAdicVal p (Nat.repeat (nsStep a) (n + k) x₀ -
                         Nat.repeat (nsStep a) n x₀))

/-- Construct a `HenselInverseCert` from initial integrality and residual conditions. -/
theorem mkHenselInverseCert {p : Nat} {m : Int} {a x₀ : QRat}
    (hp : IsPrime p) (hm : 1 ≤ m)
    (ha : valLe (some 0) (pAdicVal p a))
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (h_init : valLe (some m) (pAdicVal p (qOne - a * x₀))) :
    HenselInverseCert p m a x₀ :=
  { prime := hp
    step_pos := hm
    a_int := ha
    x₀_int := hx₀
    init_residual := h_init
    residual_lift := hensel_newton_schulz_quadratic_residual p hp m hm a x₀ h_init
    step_bound := hensel_newton_schulz_step_bound p hp m hm a x₀ ha hx₀ h_init
    cauchy_range := hensel_newton_schulz_cauchy_range p hp m hm a x₀ ha hx₀ h_init }

/-- Kernel-decidable primality certificate for Mersenne prime `M₅ = 31`. -/
theorem prime_mersenne_31 : IsPrime 31 := by decide

/-- Kernel-decidable primality certificate for Mersenne prime `M₇ = 127`. -/
theorem prime_mersenne_127 : IsPrime 127 := by decide

/-! ### Part 4: Two-Prime CRT Combination & Joint Congruence Certificates -/

private theorem prime_not_dvd_prime_pow {p₁ p₂ : Nat}
    (hp₁ : IsPrime p₁) (hp₂ : IsPrime p₂)
    (hne : p₁ ≠ p₂) : ∀ k : Nat, ¬ (p₁ ∣ p₂ ^ k)
  | 0, hdvd => by
    have h1 : p₂ ^ 0 = 1 := rfl
    rw [h1] at hdvd
    have hle : p₁ ≤ 1 := Nat.le_of_dvd (Nat.zero_lt_succ 0) hdvd
    have hp1 : 2 ≤ p₁ := hp₁.1
    omega
  | k + 1, hdvd => by
    have hpow : p₂ ^ (k + 1) = p₂ ^ k * p₂ := Nat.pow_succ p₂ k
    rw [hpow] at hdvd
    rcases hp₁.dvd_mul hdvd with h_prev | h_p2
    · exact prime_not_dvd_prime_pow hp₁ hp₂ hne k h_prev
    · have hp1 : 2 ≤ p₁ := hp₁.1
      have hp2 : 2 ≤ p₂ := hp₂.1
      by_cases hlt : p₁ < p₂
      · exact hp₂.not_dvd_of_lt hp1 hlt h_p2
      · have hle : p₁ ≤ p₂ := Nat.le_of_dvd (by omega) h_p2
        omega

private theorem prime_pow_dvd_of_dvd_mul_prime_pow {p₁ p₂ : Nat}
    (hp₁ : IsPrime p₁) (hp₂ : IsPrime p₂) (hne : p₁ ≠ p₂) :
    ∀ (k₂ q : Nat), p₂ ^ k₂ ∣ p₁ * q → p₂ ^ k₂ ∣ q
  | 0, q, _ => Nat.one_dvd q
  | k + 1, q, hdvd => by
    have hpow : p₂ ^ (k + 1) = p₂ * p₂ ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at hdvd
    have hp2_dvd : p₂ ∣ p₁ * q :=
      Nat.dvd_trans (Nat.dvd_mul_right p₂ (p₂ ^ k)) hdvd
    have h_not_p1 : ¬ (p₂ ∣ p₁) := by
      have h1 := prime_not_dvd_prime_pow hp₂ hp₁ (Ne.symm hne) 1
      simpa using h1
    rcases hp₂.dvd_mul hp2_dvd with hp2_p1 | hp2_q
    · exact False.elim (h_not_p1 hp2_p1)
    · rcases hp2_q with ⟨m, rfl⟩
      have hp2_pos : 0 < p₂ := by
        have := hp₂.1
        omega
      have hk_dvd : p₂ ^ k ∣ p₁ * m := by
        have h1 : p₂ * p₂ ^ k ∣ p₂ * (p₁ * m) := by
          have hassoc : p₁ * (p₂ * m) = p₂ * (p₁ * m) := by ac_rfl
          rwa [← hassoc]
        rcases h1 with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h2 : p₂ * (p₁ * m) = p₂ * (p₂ ^ k * c) := by
          rw [hc, Nat.mul_assoc]
        exact Nat.eq_of_mul_eq_mul_left hp2_pos h2
      have hm_dvd : p₂ ^ k ∣ m :=
        prime_pow_dvd_of_dvd_mul_prime_pow hp₁ hp₂ hne k m hk_dvd
      rcases hm_dvd with ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      rw [hpow]
      ac_rfl

/-- Constructive coprime prime-power divisibility for distinct primes `p₁ ≠ p₂`. -/
theorem prime_pow_dvd_mul_of_ne {p₁ p₂ : Nat} (hp₁ : IsPrime p₁) (hp₂ : IsPrime p₂)
    (hne : p₁ ≠ p₂) :
    ∀ (k₁ k₂ n : Nat), p₁ ^ k₁ ∣ n → p₂ ^ k₂ ∣ n → p₁ ^ k₁ * p₂ ^ k₂ ∣ n
  | 0, k₂, _, _, h2 => by
    have h1 : p₁ ^ 0 * p₂ ^ k₂ = p₂ ^ k₂ := Nat.one_mul (p₂ ^ k₂)
    rwa [h1]
  | k + 1, k₂, n, h1, h2 => by
    have hpow : p₁ ^ (k + 1) = p₁ * p₁ ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at h1
    have hp1_dvd : p₁ ∣ n :=
      Nat.dvd_trans (Nat.dvd_mul_right p₁ (p₁ ^ k)) h1
    rcases hp1_dvd with ⟨q, rfl⟩
    have hp1_pos : 0 < p₁ := by
      have := hp₁.1
      omega
    have hk1_q : p₁ ^ k ∣ q := by
      rcases h1 with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have h_eq : p₁ * q = p₁ * (p₁ ^ k * c) := by
        rw [hc, Nat.mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left hp1_pos h_eq
    have hk2_q : p₂ ^ k₂ ∣ q :=
      prime_pow_dvd_of_dvd_mul_prime_pow hp₁ hp₂ hne k₂ q h2
    have h_ih : p₁ ^ k * p₂ ^ k₂ ∣ q :=
      prime_pow_dvd_mul_of_ne hp₁ hp₂ hne k k₂ q hk1_q hk2_q
    rcases h_ih with ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [hpow]
    ac_rfl

/-- Extract cleared-numerator divisibility `p ^ k ∣ r.num.natAbs` from `ν_p(r) ≥ k`. -/
theorem valLe_nat_implies_pow_dvd_num {p k : Nat} (hp : IsPrime p) {r : QRat}
    (h : valLe (some (Int.ofNat k)) (pAdicVal p r)) :
    p ^ k ∣ r.num.natAbs := by
  by_cases hr0 : r.num = 0
  · rw [hr0]
    exact Nat.dvd_zero (p ^ k)
  · simp only [pAdicVal, hr0, ↓reduceIte, valLe] at h
    have hk_le : k ≤ padicValNat p r.num.natAbs := by
      unfold padicValInt at h
      have hcast : Int.ofNat k = (k : Int) := rfl
      rw [hcast] at h
      omega
    exact (pow_dvd_iff_le_padicValNat hp.1 (Int.natAbs_pos.mpr hr0)).mpr hk_le

/-- Joint two-prime CRT congruence bound on a cleared-denominator rational `r : QRat`. -/
structure JointCrtCongruence (p₁ p₂ k₁ k₂ : Nat) (r : QRat) : Prop where
  val₁ : valLe (some (Int.ofNat k₁)) (pAdicVal p₁ r)
  val₂ : valLe (some (Int.ofNat k₂)) (pAdicVal p₂ r)
  composite_dvd : p₁ ^ k₁ * p₂ ^ k₂ ∣ r.num.natAbs

/-- Combine individual `p₁`-adic and `p₂`-adic valuation floors into a joint CRT bound. -/
theorem mkJointCrtCongruence {p₁ p₂ k₁ k₂ : Nat}
    (hp₁ : IsPrime p₁) (hp₂ : IsPrime p₂)
    (hne : p₁ ≠ p₂) {r : QRat}
    (hv₁ : valLe (some (Int.ofNat k₁)) (pAdicVal p₁ r))
    (hv₂ : valLe (some (Int.ofNat k₂)) (pAdicVal p₂ r)) :
    JointCrtCongruence p₁ p₂ k₁ k₂ r :=
  { val₁ := hv₁
    val₂ := hv₂
    composite_dvd :=
      prime_pow_dvd_mul_of_ne hp₁ hp₂ hne k₁ k₂ r.num.natAbs
        (valLe_nat_implies_pow_dvd_num hp₁ hv₁)
        (valLe_nat_implies_pow_dvd_num hp₂ hv₂) }

/-- Joint two-prime Newton-Schulz certificate certifying simultaneous quadratic residual
    lifting modulo `p₁^(2^n * m₁) * p₂^(2^n * m₂)` and multi-step Cauchy stability. -/
structure JointCrtHenselCert (p₁ p₂ m₁ m₂ : Nat) (a x₀ : QRat) : Prop where
  prime₁ : IsPrime p₁
  prime₂ : IsPrime p₂
  distinct : p₁ ≠ p₂
  step₁_pos : 1 ≤ m₁
  step₂_pos : 1 ≤ m₂
  residual_crt :
    ∀ n : Nat,
      JointCrtCongruence p₁ p₂ (2 ^ n * m₁) (2 ^ n * m₂)
        (qOne - a * Nat.repeat (nsStep a) n x₀)
  cauchy_crt :
    ∀ n k : Nat,
      JointCrtCongruence p₁ p₂ (2 ^ n * m₁) (2 ^ n * m₂)
        (Nat.repeat (nsStep a) (n + k) x₀ - Nat.repeat (nsStep a) n x₀)

/-- **Joint CRT Combination Theorem:**
    Combines two coprime `HenselInverseCert` certificates for `a` at `x₀` into a unified
    `JointCrtHenselCert` lifting precision modulo `p₁^(2^n * m₁) * p₂^(2^n * m₂)`. -/
theorem hensel_joint_crt_combine {p₁ p₂ m₁ m₂ : Nat} {a x₀ : QRat}
    (hne : p₁ ≠ p₂)
    (cert₁ : HenselInverseCert p₁ (Int.ofNat m₁) a x₀)
    (cert₂ : HenselInverseCert p₂ (Int.ofNat m₂) a x₀) :
    JointCrtHenselCert p₁ p₂ m₁ m₂ a x₀ := by
  have hm₁ : 1 ≤ m₁ := Int.ofNat_le.mp cert₁.step_pos
  have hm₂ : 1 ≤ m₂ := Int.ofNat_le.mp cert₂.step_pos
  refine
    { prime₁ := cert₁.prime
      prime₂ := cert₂.prime
      distinct := hne
      step₁_pos := hm₁
      step₂_pos := hm₂
      residual_crt := ?_
      cauchy_crt := ?_ }
  · intro n
    have hv₁ := cert₁.residual_lift n
    have hv₂ := cert₂.residual_lift n
    have hcast₁ : Int.ofNat (2 ^ n * m₁) = Int.ofNat (2 ^ n) * Int.ofNat m₁ := rfl
    have hcast₂ : Int.ofNat (2 ^ n * m₂) = Int.ofNat (2 ^ n) * Int.ofNat m₂ := rfl
    rw [← hcast₁] at hv₁
    rw [← hcast₂] at hv₂
    exact mkJointCrtCongruence cert₁.prime cert₂.prime hne hv₁ hv₂
  · intro n k
    have hv₁ := cert₁.cauchy_range n k
    have hv₂ := cert₂.cauchy_range n k
    have hcast₁ : Int.ofNat (2 ^ n * m₁) = Int.ofNat (2 ^ n) * Int.ofNat m₁ := rfl
    have hcast₂ : Int.ofNat (2 ^ n * m₂) = Int.ofNat (2 ^ n) * Int.ofNat m₂ := rfl
    rw [← hcast₁] at hv₁
    rw [← hcast₂] at hv₂
    exact mkJointCrtCongruence cert₁.prime cert₂.prime hne hv₁ hv₂

/-! #### Constructive CRT Seed Fusion from Two Independent Single-Prime Seeds -/

/-- Algebraic CRT residual decomposition:
    `1 - a * (e₁ * u₁ + e₂ * u₂) ~
     ((1 - e₁) - e₂) + e₁ * (1 - a * u₁) + e₂ * (1 - a * u₂)`. -/
def crtResidualDecomp (a u₁ u₂ e₁ e₂ : QRat) : QRat :=
  ((qOne - e₁) + (-e₂)) + (e₁ * (qOne - a * u₁) + e₂ * (qOne - a * u₂))

theorem crt_residual_decomp_cross_eq (a u₁ u₂ e₁ e₂ : QRat) :
    CrossEq (qOne - a * (e₁ * u₁ + e₂ * u₂)) (crtResidualDecomp a u₁ u₂ e₁ e₂) := by
  unfold CrossEq crtResidualDecomp
  rw [qrat_sub_num' qOne (a * (e₁ * u₁ + e₂ * u₂)),
      qrat_sub_den' qOne (a * (e₁ * u₁ + e₂ * u₂)),
      qrat_mul_num' a (e₁ * u₁ + e₂ * u₂),
      qrat_mul_den' a (e₁ * u₁ + e₂ * u₂),
      qrat_add_num (e₁ * u₁) (e₂ * u₂),
      qrat_add_den (e₁ * u₁) (e₂ * u₂),
      qrat_mul_num' e₁ u₁, qrat_mul_den' e₁ u₁,
      qrat_mul_num' e₂ u₂, qrat_mul_den' e₂ u₂,
      qrat_add_num ((qOne - e₁) + (-e₂)) (e₁ * (qOne - a * u₁) + e₂ * (qOne - a * u₂)),
      qrat_add_den ((qOne - e₁) + (-e₂)) (e₁ * (qOne - a * u₁) + e₂ * (qOne - a * u₂)),
      qrat_add_num (qOne - e₁) (-e₂),
      qrat_add_den (qOne - e₁) (-e₂),
      qrat_sub_num' qOne e₁, qrat_sub_den' qOne e₁,
      qrat_add_num (e₁ * (qOne - a * u₁)) (e₂ * (qOne - a * u₂)),
      qrat_add_den (e₁ * (qOne - a * u₁)) (e₂ * (qOne - a * u₂)),
      qrat_mul_num' e₁ (qOne - a * u₁), qrat_mul_den' e₁ (qOne - a * u₁),
      qrat_mul_num' e₂ (qOne - a * u₂), qrat_mul_den' e₂ (qOne - a * u₂),
      qrat_sub_num' qOne (a * u₁), qrat_sub_den' qOne (a * u₁),
      qrat_sub_num' qOne (a * u₂), qrat_sub_den' qOne (a * u₂),
      qrat_mul_num' a u₁, qrat_mul_den' a u₁,
      qrat_mul_num' a u₂, qrat_mul_den' a u₂]
  have hneg_num : (-e₂).num = -e₂.num := rfl
  have hneg_den : (-e₂).den = e₂.den := rfl
  rw [hneg_num, hneg_den]
  simp only [qOne, Int.natCast_mul]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let u1n : Int := u₁.num
  let u1d : Int := (u₁.den : Int)
  let u2n : Int := u₂.num
  let u2d : Int := (u₂.den : Int)
  let e1n : Int := e₁.num
  let e1d : Int := (e₁.den : Int)
  let e2n : Int := e₂.num
  let e2d : Int := (e₂.den : Int)
  change
    (1 * (ad * (e1d * u1d * (e2d * u2d))) -
      an * (e1n * u1n * (e2d * u2d) + e2n * u2n * (e1d * u1d)) * 1) *
      (1 * e1d * e2d * (e1d * (1 * (ad * u1d)) * (e2d * (1 * (ad * u2d))))) =
    (((1 * e1d - e1n * 1) * e2d + -e2n * (1 * e1d)) *
      (e1d * (1 * (ad * u1d)) * (e2d * (1 * (ad * u2d)))) +
      (e1n * (1 * (ad * u1d) - an * u1n * 1) * (e2d * (1 * (ad * u2d))) +
        e2n * (1 * (ad * u2d) - an * u2n * 1) * (e1d * (1 * (ad * u1d)))) *
        (1 * e1d * e2d)) *
      (1 * (ad * (e1d * u1d * (e2d * u2d))))
  have h1 : 1 * e1d - e1n * 1 = e1d - e1n := by omega
  have h2 : 1 * (ad * u1d) - an * u1n * 1 = ad * u1d - an * u1n := by omega
  have h3 : 1 * (ad * u2d) - an * u2n * 1 = ad * u2d - an * u2n := by omega
  rw [h1, h2, h3]
  let K : Int := e1d * e2d * ad
  have h_rhs_den :
      1 * e1d * e2d * (e1d * (1 * (ad * u1d)) * (e2d * (1 * (ad * u2d)))) =
      K * (1 * (ad * (e1d * u1d * (e2d * u2d)))) := by
    dsimp [K]
    simp only [Int.one_mul]
    ac_rfl
  have h_rhs_num :
      ((e1d - e1n) * e2d + -e2n * (1 * e1d)) *
        (e1d * (1 * (ad * u1d)) * (e2d * (1 * (ad * u2d)))) +
      (e1n * (ad * u1d - an * u1n) * (e2d * (1 * (ad * u2d))) +
        e2n * (ad * u2d - an * u2n) * (e1d * (1 * (ad * u1d)))) *
        (1 * e1d * e2d) =
      K * (1 * (ad * (e1d * u1d * (e2d * u2d))) -
        an * (e1n * u1n * (e2d * u2d) + e2n * u2n * (e1d * u1d)) * 1) := by
    simp only [Int.one_mul, Int.mul_one]
    have t1 :
        ((e1d - e1n) * e2d + -e2n * e1d) * (e1d * (ad * u1d) * (e2d * (ad * u2d))) =
        K * ((e1d * e2d - e1n * e2d - e2n * e1d) * (ad * u1d * u2d)) := by
      have f1 : (e1d - e1n) * e2d + -e2n * e1d =
          e1d * e2d - e1n * e2d - e2n * e1d := by
        rw [Int.sub_mul, Int.neg_mul]
        omega
      have f2 : e1d * (ad * u1d) * (e2d * (ad * u2d)) = K * (ad * u1d * u2d) := by
        dsimp [K]; ac_rfl
      rw [f1, f2]
      ac_rfl
    have t2 :
        (e1n * (ad * u1d - an * u1n) * (e2d * (ad * u2d))) * (e1d * e2d) =
        K * (e1n * ad * u1d * e2d * u2d - an * (e1n * u1n * (e2d * u2d))) := by
      rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_sub]
      congr 1
      · dsimp [K]; ac_rfl
      · dsimp [K]; ac_rfl
    have t3 :
        (e2n * (ad * u2d - an * u2n) * (e1d * (ad * u1d))) * (e1d * e2d) =
        K * (e2n * ad * u2d * e1d * u1d - an * (e2n * u2n * (e1d * u1d))) := by
      rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_sub]
      congr 1
      · dsimp [K]; ac_rfl
      · dsimp [K]; ac_rfl
    rw [t1, Int.add_mul (e1n * (ad * u1d - an * u1n) * (e2d * (ad * u2d)))
          (e2n * (ad * u2d - an * u2n) * (e1d * (ad * u1d))) (e1d * e2d),
        t2, t3, ← Int.mul_add, ← Int.mul_add]
    congr 1
    have b1 :
        (e1d * e2d - e1n * e2d - e2n * e1d) * (ad * u1d * u2d) =
        ad * (e1d * u1d * (e2d * u2d)) - e1n * ad * u1d * e2d * u2d -
          e2n * ad * u2d * e1d * u1d := by
      rw [Int.sub_mul, Int.sub_mul]
      have a1 : e1d * e2d * (ad * u1d * u2d) = ad * (e1d * u1d * (e2d * u2d)) := by ac_rfl
      have a2 : e1n * e2d * (ad * u1d * u2d) = e1n * ad * u1d * e2d * u2d := by ac_rfl
      have a3 : e2n * e1d * (ad * u1d * u2d) = e2n * ad * u2d * e1d * u1d := by ac_rfl
      rw [a1, a2, a3]
    rw [b1, Int.mul_add]
    omega
  rw [h_rhs_num, h_rhs_den]
  ac_rfl

private theorem valLe_zero_mul {p : Nat} (hp : IsPrime p) {x y : QRat}
    (hx : valLe (some 0) (pAdicVal p x)) (hy : valLe (some 0) (pAdicVal p y)) :
    valLe (some 0) (pAdicVal p (x * y)) := by
  rw [pAdicVal_mul p hp x y]
  cases hx' : pAdicVal p x with
  | none => trivial
  | some vx =>
    cases hy' : pAdicVal p y with
    | none => trivial
    | some vy =>
      rw [hx'] at hx
      rw [hy'] at hy
      simp only [valLe] at hx hy
      simp only [valAdd, valLe]
      omega

private theorem valLe_add_of_both {p : Nat} (hp : IsPrime p) {b : Int} {x y : QRat}
    (hx : valLe (some b) (pAdicVal p x)) (hy : valLe (some b) (pAdicVal p y)) :
    valLe (some b) (pAdicVal p (x + y)) :=
  valLe_trans (valLe_valMin hx hy) (ultrametric_ineq p hp x y)

private theorem valLe_mul_right {p : Nat} (hp : IsPrime p) {m : Int} {e r : QRat}
    (he : valLe (some 0) (pAdicVal p e)) (hr : valLe (some m) (pAdicVal p r)) :
    valLe (some m) (pAdicVal p (e * r)) := by
  rw [pAdicVal_mul p hp e r]
  cases he' : pAdicVal p e with
  | none => trivial
  | some ve =>
    cases hr' : pAdicVal p r with
    | none => trivial
    | some vr =>
      rw [he'] at he
      rw [hr'] at hr
      simp only [valLe] at he hr
      simp only [valAdd, valLe]
      omega

private theorem valLe_mul_left {p : Nat} (hp : IsPrime p) {m : Int} {e r : QRat}
    (he : valLe (some m) (pAdicVal p e)) (hr : valLe (some 0) (pAdicVal p r)) :
    valLe (some m) (pAdicVal p (e * r)) := by
  rw [pAdicVal_mul p hp e r]
  cases he' : pAdicVal p e with
  | none => trivial
  | some ve =>
    cases hr' : pAdicVal p r with
    | none => trivial
    | some vr =>
      rw [he'] at he
      rw [hr'] at hr
      simp only [valLe] at he hr
      simp only [valAdd, valLe]
      omega

/-- **CRT Seed Fusion Theorem:**
    Given two independent single-prime inverse certificates `cert₁` (at `p₁^m₁`) and
    `cert₂` (at `p₂^m₂`) for `a`, together with CRT idempotent weights `e₁, e₂`,
    the fused seed `u_crt = e₁ * u₁ + e₂ * u₂` initiates a single joint Newton-Schulz
    trajectory `JointCrtHenselCert p₁ p₂ m₁ m₂ a (e₁ * u₁ + e₂ * u₂)`. -/
theorem crt_fuse_inverse_seeds {p₁ p₂ m₁ m₂ : Nat} {a u₁ u₂ e₁ e₂ : QRat}
    (hne : p₁ ≠ p₂)
    (cert₁ : HenselInverseCert p₁ (Int.ofNat m₁) a u₁)
    (cert₂ : HenselInverseCert p₂ (Int.ofNat m₂) a u₂)
    (ha₁ : valLe (some 0) (pAdicVal p₁ a))
    (ha₂ : valLe (some 0) (pAdicVal p₂ a))
    (hu₁_p1 : valLe (some 0) (pAdicVal p₁ u₁))
    (hu₁_p2 : valLe (some 0) (pAdicVal p₂ u₁))
    (hu₂_p1 : valLe (some 0) (pAdicVal p₁ u₂))
    (hu₂_p2 : valLe (some 0) (pAdicVal p₂ u₂))
    (he₁_int_p1 : valLe (some 0) (pAdicVal p₁ e₁))
    (he₂_int_p2 : valLe (some 0) (pAdicVal p₂ e₂))
    (he₁_p1 : valLe (some (Int.ofNat m₁)) (pAdicVal p₁ (qOne - e₁)))
    (he₂_p1 : valLe (some (Int.ofNat m₁)) (pAdicVal p₁ e₂))
    (he₁_p2 : valLe (some (Int.ofNat m₂)) (pAdicVal p₂ e₁))
    (he₂_p2 : valLe (some (Int.ofNat m₂)) (pAdicVal p₂ (qOne - e₂))) :
    JointCrtHenselCert p₁ p₂ m₁ m₂ a (e₁ * u₁ + e₂ * u₂) := by
  have hp₁ := cert₁.prime
  have hp₂ := cert₂.prime
  have hu_crt_p1 : valLe (some 0) (pAdicVal p₁ (e₁ * u₁ + e₂ * u₂)) := by
    have hm1_0 : valLe (some 0) (some (Int.ofNat m₁)) := Int.natCast_nonneg m₁
    have he₂_0_p1 : valLe (some 0) (pAdicVal p₁ e₂) :=
      valLe_trans hm1_0 he₂_p1
    exact valLe_add_of_both hp₁
      (valLe_zero_mul hp₁ he₁_int_p1 hu₁_p1)
      (valLe_zero_mul hp₁ he₂_0_p1 hu₂_p1)
  have hu_crt_p2 : valLe (some 0) (pAdicVal p₂ (e₁ * u₁ + e₂ * u₂)) := by
    have hm2_0 : valLe (some 0) (some (Int.ofNat m₂)) := Int.natCast_nonneg m₂
    have he₁_0_p2 : valLe (some 0) (pAdicVal p₂ e₁) :=
      valLe_trans hm2_0 he₁_p2
    exact valLe_add_of_both hp₂
      (valLe_zero_mul hp₂ he₁_0_p2 hu₁_p2)
      (valLe_zero_mul hp₂ he₂_int_p2 hu₂_p2)
  have h_res_p1 :
      valLe (some (Int.ofNat m₁)) (pAdicVal p₁ (qOne - a * (e₁ * u₁ + e₂ * u₂))) := by
    rw [pAdicVal_eq_of_cross_mul hp₁ (crt_residual_decomp_cross_eq a u₁ u₂ e₁ e₂)]
    have hr1_0 : valLe (some (Int.ofNat m₁)) (pAdicVal p₁ (qOne - a * u₁)) := by
      have h0 := cert₁.residual_lift 0
      have hpow : Int.ofNat (2 ^ 0) * Int.ofNat m₁ = Int.ofNat m₁ := Int.one_mul _
      rwa [hpow] at h0
    have hr2_0 : valLe (some 0) (pAdicVal p₁ (qOne - a * u₂)) := by
      rw [pAdicVal_sub_eq_add_neg]
      have h1 : valLe (some 0) (pAdicVal p₁ qOne) := by
        rw [pAdicVal_qOne p₁ hp₁]
        exact Int.le_refl 0
      have h2 : valLe (some 0) (pAdicVal p₁ (-(a * u₂))) := by
        rw [pAdicVal_neg]
        exact valLe_zero_mul hp₁ ha₁ hu₂_p1
      exact valLe_add_of_both hp₁ h1 h2
    have hneg_e₂ : valLe (some (Int.ofNat m₁)) (pAdicVal p₁ (-e₂)) := by
      rw [pAdicVal_neg]
      exact he₂_p1
    exact valLe_add_of_both hp₁
      (valLe_add_of_both hp₁ he₁_p1 hneg_e₂)
      (valLe_add_of_both hp₁
        (valLe_mul_right hp₁ he₁_int_p1 hr1_0)
        (valLe_mul_left hp₁ he₂_p1 hr2_0))
  have h_res_p2 :
      valLe (some (Int.ofNat m₂)) (pAdicVal p₂ (qOne - a * (e₁ * u₁ + e₂ * u₂))) := by
    rw [pAdicVal_eq_of_cross_mul hp₂ (crt_residual_decomp_cross_eq a u₁ u₂ e₁ e₂)]
    have hr2_0 : valLe (some (Int.ofNat m₂)) (pAdicVal p₂ (qOne - a * u₂)) := by
      have h0 := cert₂.residual_lift 0
      have hpow : Int.ofNat (2 ^ 0) * Int.ofNat m₂ = Int.ofNat m₂ := Int.one_mul _
      rwa [hpow] at h0
    have hr1_0 : valLe (some 0) (pAdicVal p₂ (qOne - a * u₁)) := by
      rw [pAdicVal_sub_eq_add_neg]
      have h1 : valLe (some 0) (pAdicVal p₂ qOne) := by
        rw [pAdicVal_qOne p₂ hp₂]
        exact Int.le_refl 0
      have h2 : valLe (some 0) (pAdicVal p₂ (-(a * u₁))) := by
        rw [pAdicVal_neg]
        exact valLe_zero_mul hp₂ ha₂ hu₁_p2
      exact valLe_add_of_both hp₂ h1 h2
    have h1_sub_e1_sub_e2 :
        valLe (some (Int.ofNat m₂)) (pAdicVal p₂ ((qOne - e₁) + (-e₂))) := by
      have h_eq : pAdicVal p₂ ((qOne - e₁) + (-e₂)) =
          pAdicVal p₂ ((qOne - e₂) + (-e₁)) := by
        apply pAdicVal_eq_of_num_den_eq
        · rw [qrat_add_num, qrat_add_num, qrat_sub_num', qrat_sub_num',
              qrat_sub_den', qrat_sub_den']
          have hn1 : (-e₁).num = -e₁.num := rfl
          have hd1 : (-e₁).den = e₁.den := rfl
          have hn2 : (-e₂).num = -e₂.num := rfl
          have hd2 : (-e₂).den = e₂.den := rfl
          rw [hn1, hd1, hn2, hd2]
          simp only [qOne, Int.natCast_mul]
          let e1n : Int := e₁.num
          let e1d : Int := (e₁.den : Int)
          let e2n : Int := e₂.num
          let e2d : Int := (e₂.den : Int)
          change (1 * e1d - e1n * 1) * e2d + -e2n * (1 * e1d) =
                 (1 * e2d - e2n * 1) * e1d + -e1n * (1 * e2d)
          have c1 : (1 * e1d - e1n * 1) * e2d + -e2n * (1 * e1d) =
              e1d * e2d - e1n * e2d - e2n * e1d := by
            rw [Int.one_mul, Int.mul_one, Int.sub_mul, Int.neg_mul]
            omega
          have c2 : (1 * e2d - e2n * 1) * e1d + -e1n * (1 * e2d) =
              e2d * e1d - e2n * e1d - e1n * e2d := by
            rw [Int.one_mul, Int.mul_one, Int.sub_mul, Int.neg_mul]
            omega
          have c3 : e1d * e2d = e2d * e1d := Int.mul_comm e1d e2d
          rw [c1, c2, c3]
          omega
        · rw [qrat_add_den, qrat_add_den, qrat_sub_den', qrat_sub_den']
          have hd1 : (-e₁).den = e₁.den := rfl
          have hd2 : (-e₂).den = e₂.den := rfl
          rw [hd1, hd2]
          ac_rfl
      rw [h_eq]
      have hneg_e₁ : valLe (some (Int.ofNat m₂)) (pAdicVal p₂ (-e₁)) := by
        rw [pAdicVal_neg]
        exact he₁_p2
      exact valLe_add_of_both hp₂ he₂_p2 hneg_e₁
    exact valLe_add_of_both hp₂
      h1_sub_e1_sub_e2
      (valLe_add_of_both hp₂
        (valLe_mul_left hp₂ he₁_p2 hr1_0)
        (valLe_mul_right hp₂ he₂_int_p2 hr2_0))
  exact hensel_joint_crt_combine hne
    (mkHenselInverseCert hp₁ cert₁.step_pos ha₁ hu_crt_p1 h_res_p1)
    (mkHenselInverseCert hp₂ cert₂.step_pos ha₂ hu_crt_p2 h_res_p2)

/-! #### Concrete Mersenne CRT Certificate: `5⁻¹ mod (31 * 127)^(2^n) = 3937^(2^n)` -/

/-- **`M₅ × M₇ = 31 × 127 = 3937` Joint CRT Certificate (`by decide`):**
    Combines `5⁻¹ ≡ 25 (mod 31)` and `5⁻¹ ≡ 51 (mod 127)` via CRT seed
    `x₀ = 1575` (`5 * 1575 = 7875 = 2 * 3937 + 1`), certifying for every `n, k : Nat` that
    `31^(2^n) * 127^(2^n)` divides both `(1 - 5 * nsStep^n(5, 1575)).num.natAbs` and
    `(nsStep^(n+k)(5, 1575) - nsStep^n(5, 1575)).num.natAbs`. -/
theorem hensel_crt_inv_5_mod_3937_pow :
    JointCrtHenselCert 31 127 1 1 (qOfInt 5) (qOfInt 1575) :=
  hensel_joint_crt_combine
    (by decide)
    (mkHenselInverseCert prime_mersenne_31 (by decide) (by decide) (by decide) (by decide))
    (mkHenselInverseCert prime_mersenne_127 (by decide) (by decide) (by decide) (by decide))

/-! ### Part 5: Inductive Prime Tower CRT over `List Nat` and `List (Nat × Nat)` -/

/-- Kernel-decidable primality certificate for Mersenne prime `M₃ = 7`. -/
theorem prime_mersenne_7 : IsPrime 7 := by decide

private theorem nat_bne_true_iff (a b : Nat) : (a != b) = true ↔ a ≠ b := by
  change (!(a == b)) = true ↔ a ≠ b
  cases h : (a == b)
  · simp [beq_eq_false_iff_ne.mp h]
  · simp [beq_iff_eq.mp h]

/-- Computable membership-exclusion check on `List Nat`. -/
def notInList (x : Nat) : List Nat → Bool
  | [] => true
  | y :: ys => (x != y) && notInList x ys

theorem notInList_eq_true_iff (x : Nat) :
    ∀ ys : List Nat, notInList x ys = true ↔ ∀ y ∈ ys, x ≠ y
  | [] => by simp [notInList]
  | y :: ys => by
    simp only [notInList, Bool.and_eq_true, nat_bne_true_iff, List.mem_cons]
    rw [notInList_eq_true_iff x ys]
    constructor
    · rintro ⟨hne, hall⟩ z (rfl | hz)
      · exact hne
      · exact hall z hz
    · intro h
      exact ⟨h y (Or.inl rfl), fun z hz => h z (Or.inr hz)⟩

/-- Every element in `ps : List Nat` is a constructive prime (`IsPrime`). -/
def AllPrimes : List Nat → Prop
  | [] => True
  | p :: ps => IsPrime p ∧ AllPrimes ps

instance decidableAllPrimes : (ps : List Nat) → Decidable (AllPrimes ps)
  | [] => inferInstanceAs (Decidable True)
  | p :: ps =>
    haveI := decidableAllPrimes ps
    inferInstanceAs (Decidable (IsPrime p ∧ AllPrimes ps))

/-- Every element in `ps : List Nat` is pairwise distinct. -/
def PairwiseDistinct : List Nat → Prop
  | [] => True
  | p :: ps => notInList p ps = true ∧ PairwiseDistinct ps

instance decidablePairwiseDistinct : (ps : List Nat) → Decidable (PairwiseDistinct ps)
  | [] => inferInstanceAs (Decidable True)
  | p :: ps =>
    haveI := decidablePairwiseDistinct ps
    inferInstanceAs (Decidable (notInList p ps = true ∧ PairwiseDistinct ps))

/-- Product of prime powers `∏_{(q, k) ∈ tower} q ^ k`. -/
def towerModulus : List (Nat × Nat) → Nat
  | [] => 1
  | (q, k) :: rest => q ^ k * towerModulus rest

/-- Uniform-exponent Prime Tower modulus `∏_{p ∈ ps} p ^ k` over `ps : List Nat`. -/
def primeTowerModulus (ps : List Nat) (k : Nat) : Nat :=
  towerModulus (ps.map (fun p => (p, k)))

private theorem prime_pow_dvd_of_dvd_prime_pow_mul {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hpq : p ≠ q) :
    ∀ (k m M : Nat), p ^ m ∣ q ^ k * M → p ^ m ∣ M
  | 0, _, M, hdvd => by
    have h1 : q ^ 0 * M = M := Nat.one_mul M
    rwa [h1] at hdvd
  | k + 1, m, M, hdvd => by
    have hpow : q ^ (k + 1) * M = q * (q ^ k * M) := by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ k) q, Nat.mul_assoc]
    rw [hpow] at hdvd
    have hk_dvd : p ^ m ∣ q ^ k * M :=
      prime_pow_dvd_of_dvd_mul_prime_pow hq hp (Ne.symm hpq) m (q ^ k * M) hdvd
    exact prime_pow_dvd_of_dvd_prime_pow_mul hp hq hpq k m M hk_dvd

private theorem prime_pow_dvd_of_dvd_tower_prod {p : Nat} (hp : IsPrime p) :
    ∀ (tower : List (Nat × Nat)),
      AllPrimes (tower.map Prod.fst) →
      (∀ q ∈ tower.map Prod.fst, p ≠ q) →
      ∀ (m N : Nat), p ^ m ∣ towerModulus tower * N → p ^ m ∣ N
  | [], _, _, _, N, hdvd => by
    have h1 : towerModulus [] * N = N := Nat.one_mul N
    rwa [h1] at hdvd
  | (q, k) :: rest, h_primes, h_dist, m, N, hdvd => by
    simp only [List.map_cons, AllPrimes] at h_primes
    rcases h_primes with ⟨hq, h_rest_primes⟩
    have hpq : p ≠ q := h_dist q (List.mem_cons.mpr (Or.inl rfl))
    have h_rest_dist : ∀ r ∈ rest.map Prod.fst, p ≠ r := fun r hr =>
      h_dist r (List.mem_cons.mpr (Or.inr hr))
    have hassoc : towerModulus ((q, k) :: rest) * N = q ^ k * (towerModulus rest * N) := by
      simp only [towerModulus, Nat.mul_assoc]
    rw [hassoc] at hdvd
    have h_mid : p ^ m ∣ towerModulus rest * N :=
      prime_pow_dvd_of_dvd_prime_pow_mul hp hq hpq k m (towerModulus rest * N) hdvd
    exact prime_pow_dvd_of_dvd_tower_prod hp rest h_rest_primes h_rest_dist m N h_mid

/-- **Inductive Graded Prime Tower Divisibility Theorem:**
    Given any `tower : List (Nat × Nat)` of pairwise-distinct primes `(p_i, k_i)`
    such that `p_i ^ k_i ∣ N` for every entry, the full composite modulus
    `∏_{(p_i, k_i) ∈ tower} p_i ^ k_i` divides `N`. -/
theorem prime_tower_pow_dvd_of_all :
    ∀ (tower : List (Nat × Nat)),
      AllPrimes (tower.map Prod.fst) →
      PairwiseDistinct (tower.map Prod.fst) →
      ∀ (N : Nat),
        (∀ entry ∈ tower, entry.1 ^ entry.2 ∣ N) →
        towerModulus tower ∣ N
  | [], _, _, N, _ => Nat.one_dvd N
  | (p, k) :: rest, h_primes, h_dist, N, h_all => by
    simp only [List.map_cons, AllPrimes, PairwiseDistinct] at h_primes h_dist
    rcases h_primes with ⟨hp, h_rest_primes⟩
    rcases h_dist with ⟨h_not_in, h_rest_dist⟩
    have h_ne_rest : ∀ q ∈ rest.map Prod.fst, p ≠ q :=
      (notInList_eq_true_iff p (rest.map Prod.fst)).mp h_not_in
    have hpk : p ^ k ∣ N := h_all (p, k) (List.mem_cons.mpr (Or.inl rfl))
    have h_rest_all : ∀ entry ∈ rest, entry.1 ^ entry.2 ∣ N := fun entry he =>
      h_all entry (List.mem_cons.mpr (Or.inr he))
    have h_rest_dvd : towerModulus rest ∣ N :=
      prime_tower_pow_dvd_of_all rest h_rest_primes h_rest_dist N h_rest_all
    rcases h_rest_dvd with ⟨M, rfl⟩
    have hpk_M : p ^ k ∣ M :=
      prime_pow_dvd_of_dvd_tower_prod hp rest h_rest_primes h_ne_rest k M hpk
    rcases hpk_M with ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    simp only [towerModulus]
    ac_rfl

private theorem allPrimes_of_map_fst :
    ∀ (tower : List (Nat × Nat)),
      AllPrimes (tower.map Prod.fst) →
      ∀ entry ∈ tower, IsPrime entry.1
  | [], _, _, he => by cases he
  | (_, _) :: rest, h_primes, entry, he => by
    simp only [List.map_cons, AllPrimes] at h_primes
    rcases List.mem_cons.mp he with rfl | hrest
    · exact h_primes.1
    · exact allPrimes_of_map_fst rest h_primes.2 entry hrest

private theorem map_fst_map_pair (ps : List Nat) (k : Nat) :
    (ps.map (fun p => (p, k))).map Prod.fst = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, ih]

/-- **Graded Prime Tower CRT Congruence on `QRat`:**
    If `tower : List (Nat × Nat)` has pairwise-distinct primes `p_i` and
    `ν_{p_i}(r) ≥ k_i` for every `(p_i, k_i) ∈ tower`, then
    `∏_{(p_i, k_i) ∈ tower} p_i ^ k_i ∣ r.num.natAbs`. -/
theorem prime_tower_graded_dvd_num (tower : List (Nat × Nat))
    (h_primes : AllPrimes (tower.map Prod.fst))
    (h_dist : PairwiseDistinct (tower.map Prod.fst))
    (r : QRat)
    (h_vals : ∀ entry ∈ tower, valLe (some (Int.ofNat entry.2)) (pAdicVal entry.1 r)) :
    towerModulus tower ∣ r.num.natAbs := by
  apply prime_tower_pow_dvd_of_all tower h_primes h_dist r.num.natAbs
  intro entry he
  have hp : IsPrime entry.1 := allPrimes_of_map_fst tower h_primes entry he
  exact valLe_nat_implies_pow_dvd_num hp (h_vals entry he)

/-- **Uniform Prime Tower CRT Congruence over `List Nat` on `QRat`:**
    For any list `ps : List Nat` of pairwise-distinct primes, if `ν_p(r) ≥ k`
    for every `p ∈ ps`, then `∏_{p ∈ ps} p ^ k ∣ r.num.natAbs`. -/
theorem prime_tower_list_pow_dvd_num (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (k : Nat) (r : QRat)
    (h_vals : ∀ p ∈ ps, valLe (some (Int.ofNat k)) (pAdicVal p r)) :
    primeTowerModulus ps k ∣ r.num.natAbs := by
  unfold primeTowerModulus
  have h_primes' : AllPrimes ((ps.map (fun p => (p, k))).map Prod.fst) := by
    rwa [map_fst_map_pair]
  have h_dist' : PairwiseDistinct ((ps.map (fun p => (p, k))).map Prod.fst) := by
    rwa [map_fst_map_pair]
  apply prime_tower_graded_dvd_num (ps.map (fun p => (p, k))) h_primes' h_dist' r
  intro entry he
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  exact h_vals p hp

/-- Prime Tower Newton-Schulz certificate across an arbitrary list `ps : List Nat`
    of pairwise-distinct primes. -/
structure PrimeTowerHenselCert (ps : List Nat) (m : Nat) (a x₀ : QRat) : Prop where
  primes : AllPrimes ps
  distinct : PairwiseDistinct ps
  step_pos : 1 ≤ m
  residual_tower_dvd :
    ∀ n : Nat,
      primeTowerModulus ps (2 ^ n * m) ∣
        (qOne - a * Nat.repeat (nsStep a) n x₀).num.natAbs
  cauchy_tower_dvd :
    ∀ n k : Nat,
      primeTowerModulus ps (2 ^ n * m) ∣
        (Nat.repeat (nsStep a) (n + k) x₀ - Nat.repeat (nsStep a) n x₀).num.natAbs

/-- **Inductive Prime Tower Newton-Schulz Lifting Theorem:**
    Combines any finite family of per-prime `HenselInverseCert` certificates
    over `ps : List Nat` into a single `PrimeTowerHenselCert`, proving that
    `∏_{p ∈ ps} p ^ (2 ^ n * m)` divides both the modular residual numerator
    and all multi-step Cauchy difference numerators. -/
theorem hensel_prime_tower_crt (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (m : Nat) (hm : 1 ≤ m) (a x₀ : QRat)
    (h_certs : ∀ p ∈ ps, HenselInverseCert p (Int.ofNat m) a x₀) :
    PrimeTowerHenselCert ps m a x₀ := by
  refine
    { primes := h_primes
      distinct := h_dist
      step_pos := hm
      residual_tower_dvd := ?_
      cauchy_tower_dvd := ?_ }
  · intro n
    apply prime_tower_list_pow_dvd_num ps h_primes h_dist (2 ^ n * m)
    intro p hp
    have hv := (h_certs p hp).residual_lift n
    have hcast : Int.ofNat (2 ^ n * m) = Int.ofNat (2 ^ n) * Int.ofNat m := rfl
    rwa [← hcast] at hv
  · intro n k
    apply prime_tower_list_pow_dvd_num ps h_primes h_dist (2 ^ n * m)
    intro p hp
    have hv := (h_certs p hp).cauchy_range n k
    have hcast : Int.ofNat (2 ^ n * m) = Int.ofNat (2 ^ n) * Int.ofNat m := rfl
    rwa [← hcast] at hv

/-! #### Concrete 3-Prime Mersenne Tower Certificate: `[7, 31, 127]` (`27559^(2^n)`) -/

/-- **`M₃ × M₅ × M₇ = 7 × 31 × 127 = 27559` Prime Tower CRT Certificate (`by decide`):**
    Fuses `5⁻¹ ≡ 3 (mod 7)`, `5⁻¹ ≡ 25 (mod 31)`, and `5⁻¹ ≡ 51 (mod 127)` at
    `x₀ = 5512` (`5 * 5512 = 27560 = 27559 + 1`), certifying that for every
    `n, k : Nat`, `(7 * 31 * 127)^(2^n)` divides both
    `(1 - 5 * nsStep^n(5, 5512)).num.natAbs` and
    `(nsStep^(n+k)(5, 5512) - nsStep^n(5, 5512)).num.natAbs`. -/
theorem hensel_mersenne_tower_inv_5_mod_27559_pow :
    PrimeTowerHenselCert [7, 31, 127] 1 (qOfInt 5) (qOfInt 5512) := by
  apply hensel_prime_tower_crt [7, 31, 127] (by decide) (by decide) 1 (by decide)
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | hnil
  · exact mkHenselInverseCert prime_mersenne_7 (by decide) (by decide) (by decide) (by decide)
  · exact mkHenselInverseCert prime_mersenne_31 (by decide) (by decide) (by decide) (by decide)
  · exact mkHenselInverseCert prime_mersenne_127 (by decide) (by decide) (by decide) (by decide)
  · cases hnil

/-! ### Part 6: Cleared-Denominator & `p`-Adic Equivalence of `hornerEval` and `hornerEvalTight` -/

theorem CrossEq.refl (u : QRat) : CrossEq u u := rfl

theorem CrossEq.symm {u v : QRat} (h : CrossEq u v) : CrossEq v u := Eq.symm h

/-- Left multiplication congruence for cleared-denominator cross-multiplication equivalence. -/
theorem CrossEq.mul_left (x : QRat) {u v : QRat} (h : CrossEq u v) :
    CrossEq (x * u) (x * v) := by
  unfold CrossEq at h ⊢
  rw [qrat_mul_num', qrat_mul_den', qrat_mul_num', qrat_mul_den',
      Int.natCast_mul, Int.natCast_mul]
  calc (x.num * u.num) * ((x.den : Int) * (v.den : Int))
      = (x.num * (x.den : Int)) * (u.num * (v.den : Int)) := by ac_rfl
    _ = (x.num * (x.den : Int)) * (v.num * (u.den : Int)) := by rw [h]
    _ = (x.num * v.num) * ((x.den : Int) * (u.den : Int)) := by ac_rfl

/-- Left addition congruence for cleared-denominator cross-multiplication equivalence. -/
theorem CrossEq.add_left (c : QRat) {u v : QRat} (h : CrossEq u v) :
    CrossEq (c + u) (c + v) := by
  unfold CrossEq at h ⊢
  rw [qrat_add_num, qrat_add_den, qrat_add_num, qrat_add_den,
      Int.natCast_mul, Int.natCast_mul, Int.add_mul, Int.add_mul]
  congr 1
  · ac_rfl
  · calc (u.num * (c.den : Int)) * ((c.den : Int) * (v.den : Int))
        = ((c.den : Int) * (c.den : Int)) * (u.num * (v.den : Int)) := by ac_rfl
      _ = ((c.den : Int) * (c.den : Int)) * (v.num * (u.den : Int)) := by rw [h]
      _ = (v.num * (c.den : Int)) * ((c.den : Int) * (u.den : Int)) := by ac_rfl

private theorem add_mul_qZero_cross_eq (c x : QRat) :
    CrossEq (c + x * qZero) c := by
  unfold CrossEq
  rw [qrat_add_num, qrat_add_den, qrat_mul_num', qrat_mul_den',
      Int.natCast_mul, Int.natCast_mul]
  simp only [qZero, Int.mul_zero, Int.zero_mul, Int.add_zero]
  ac_rfl

/-- **Cleared-Denominator Horner Equivalence:**
    Standard `hornerEval coeffs x` and degree-tight `hornerEvalTight coeffs x`
    represent the exact same rational number (`CrossEq`) for all `coeffs : List QRat`. -/
theorem hornerEval_cross_eq_tight :
    ∀ (coeffs : List QRat) (x : QRat),
      CrossEq (hornerEval coeffs x) (hornerEvalTight coeffs x)
  | [], _ => CrossEq.refl qZero
  | [c], x => add_mul_qZero_cross_eq c x
  | c :: c' :: cs, x =>
    CrossEq.add_left c (CrossEq.mul_left x (hornerEval_cross_eq_tight (c' :: cs) x))

/-- **`p`-Adic Valuation Equivalence of Horner Evaluators:**
    For every prime `p` and coefficient list `coeffs : List QRat`,
    `ν_p(hornerEval coeffs x) = ν_p(hornerEvalTight coeffs x)`. -/
theorem pAdicVal_hornerEval_eq_tight {p : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (x : QRat) :
    pAdicVal p (hornerEval coeffs x) = pAdicVal p (hornerEvalTight coeffs x) :=
  pAdicVal_eq_of_cross_mul hp (hornerEval_cross_eq_tight coeffs x)

/-- **Sharper Valuation Floor Transfer for `hornerEval`:**
    Even though `hornerEval` accumulates up to `(deg + 1) * (Bc + Bx)` prime factors
    in its unreduced denominator, `pAdicVal_hornerEval_eq_tight` transfers the sharper
    `(deg + 1) * Bc + deg * Bx` valuation floor from `hornerEvalTight`. -/
theorem pAdicVal_hornerEval_ge_tight_floor {p deg Bc Bx : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x : QRat) (hx : denVal p x ≤ Bx)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    valLe (some (-(Int.ofNat ((deg + 1) * Bc + deg * Bx))))
          (pAdicVal p (hornerEval coeffs x)) := by
  rw [pAdicVal_hornerEval_eq_tight hp coeffs x]
  exact (hornerEvalTight_and_pAdicVal_bound hp coeffs hdeg x hx hall).2

/-! ### Part 7: Constructive CRT Idempotent & Seed Builder over `List Nat` -/

/-- Cofactor product `∏_{q ∈ ps, q ≠ target} q ^ exp`. -/
def crtCofactor : List Nat → Nat → Nat → Nat
  | [], _, _ => 1
  | q :: qs, target, exp =>
    if q == target then crtCofactor qs target exp
    else q ^ exp * crtCofactor qs target exp

private theorem nat_pow_pos {a : Nat} (ha : 0 < a) : ∀ n : Nat, 0 < a ^ n
  | 0 => Nat.zero_lt_succ 0
  | n + 1 => Nat.mul_pos (nat_pow_pos ha n) ha

theorem crtCofactor_pos {target exp : Nat} :
    ∀ (ps : List Nat), AllPrimes ps → 0 < crtCofactor ps target exp
  | [], _ => Nat.zero_lt_succ 0
  | r :: rs, hprimes => by
    simp only [AllPrimes] at hprimes
    simp only [crtCofactor]
    have hr_pos : 0 < r := by
      have := hprimes.1.1
      omega
    by_cases hrt : (r == target) = true
    · rw [hrt]
      simp only [↓reduceIte]
      exact crtCofactor_pos rs hprimes.2
    · have hrt_f : (r == target) = false := by
        cases h : (r == target) <;> simp_all
      rw [hrt_f]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.mul_pos (nat_pow_pos hr_pos exp) (crtCofactor_pos rs hprimes.2)

/-- Every distinct prime `q ∈ ps` (`q ≠ target`) divides `crtCofactor ps target exp`
    to power `q ^ exp`. -/
theorem pow_dvd_crtCofactor {q target exp : Nat} :
    ∀ (ps : List Nat), q ∈ ps → q ≠ target → q ^ exp ∣ crtCofactor ps target exp
  | [], hmem, _ => by cases hmem
  | r :: rs, hmem, hne => by
    simp only [crtCofactor]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have hbeq : (q == target) = false := beq_eq_false_iff_ne.mpr hne
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.dvd_mul_right (q ^ exp) (crtCofactor rs target exp)
    · by_cases hrt : (r == target) = true
      · rw [hrt]
        simp only [↓reduceIte]
        exact pow_dvd_crtCofactor rs hrest hne
      · have hrt_f : (r == target) = false := by
          cases h : (r == target) <;> simp_all
        rw [hrt_f]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases pow_dvd_crtCofactor rs hrest hne with ⟨c, hc⟩
        refine ⟨r ^ exp * c, ?_⟩
        rw [hc]
        ac_rfl

private theorem valLe_zero_pAdicVal_qOfInt_ofNat (p : Nat) (hp : IsPrime p) (N : Nat) :
    valLe (some 0) (pAdicVal p (qOfInt (Int.ofNat N))) := by
  by_cases hN : N = 0
  · subst hN
    have hnum0 : (qOfInt (Int.ofNat 0)).num = 0 := rfl
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  · have hnum_ne : (qOfInt (Int.ofNat N)).num ≠ 0 := by
      change Int.ofNat N ≠ 0
      exact Int.ofNat_ne_zero.mpr hN
    have hp2 : 2 ≤ p := hp.1
    have h1 : padicValNat p 1 = 0 :=
      padicValNat_of_not_dvd hp2 (Nat.zero_lt_succ 0) (fun hd => by
        have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hd
        omega)
    have hden : (qOfInt (Int.ofNat N)).den = 1 := rfl
    simp only [pAdicVal, hnum_ne, ↓reduceIte, valLe, padicValInt, hden, h1]
    omega

private theorem valLe_of_nat_pow_dvd_qOfInt {q k N : Nat} (hq : IsPrime q)
    (hN : 0 < N) (hdvd : q ^ k ∣ N) :
    valLe (some (Int.ofNat k)) (pAdicVal q (qOfInt (Int.ofNat N))) := by
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  have hnum_ne : (qOfInt (Int.ofNat N)).num ≠ 0 := by
    change Int.ofNat N ≠ 0
    exact Int.ofNat_ne_zero.mpr hN_ne
  have hq2 : 2 ≤ q := hq.1
  have h1 : padicValNat q 1 = 0 :=
    padicValNat_of_not_dvd hq2 (Nat.zero_lt_succ 0) (fun hd => by
      have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hd
      omega)
  have hk_le : k ≤ padicValNat q N :=
    (pow_dvd_iff_le_padicValNat hq.1 hN).mp hdvd
  have hval : padicValInt q (qOfInt (Int.ofNat N)).num = padicValNat q N := rfl
  have hden : (qOfInt (Int.ofNat N)).den = 1 := rfl
  simp only [pAdicVal, hnum_ne, ↓reduceIte, valLe, hval, hden, h1]
  have hcast : Int.ofNat k = (k : Int) := rfl
  rw [hcast]
  omega

/-- Constructive `n`-step lifted CRT idempotent `e_p = M_p * nsStep^n(M_p, w₀)`
    for prime `p ∈ ps`, where `M_p = crtCofactor ps p (2^n * m)`. -/
def crtIdempotent (ps : List Nat) (p m n : Nat) (w₀ : QRat) : QRat :=
  let a := qOfInt (Int.ofNat (crtCofactor ps p (2 ^ n * m)))
  a * Nat.repeat (nsStep a) n w₀

/-- Self-congruence of the lifted CRT idempotent at `p`: `ν_p(1 - e_p) ≥ 2^n * m`. -/
theorem crtIdempotent_self_residual {ps : List Nat} {p m n : Nat} {w₀ : QRat}
    (cert : HenselInverseCert p (Int.ofNat m)
      (qOfInt (Int.ofNat (crtCofactor ps p (2 ^ n * m)))) w₀) :
    valLe (some (Int.ofNat (2 ^ n * m)))
          (pAdicVal p (qOne - crtIdempotent ps p m n w₀)) := by
  have h := cert.residual_lift n
  have hcast : Int.ofNat (2 ^ n * m) = Int.ofNat (2 ^ n) * Int.ofNat m := rfl
  rwa [← hcast] at h

/-- Cross-prime orthogonality of `crtIdempotent`: for every `q ∈ ps` with `q ≠ p`,
    `ν_q(e_p) ≥ 2^n * m`. -/
theorem crtIdempotent_other_val {ps : List Nat} {p q m n : Nat} {w₀ : QRat}
    (h_primes : AllPrimes ps) (hq : IsPrime q) (hq_mem : q ∈ ps) (hne : q ≠ p)
    (hw₀ : valLe (some 0) (pAdicVal q w₀)) :
    valLe (some (Int.ofNat (2 ^ n * m)))
          (pAdicVal q (crtIdempotent ps p m n w₀)) := by
  unfold crtIdempotent
  let a := qOfInt (Int.ofNat (crtCofactor ps p (2 ^ n * m)))
  have ha_pow : valLe (some (Int.ofNat (2 ^ n * m))) (pAdicVal q a) :=
    valLe_of_nat_pow_dvd_qOfInt hq
      (crtCofactor_pos ps h_primes)
      (pow_dvd_crtCofactor ps hq_mem hne)
  have ha_int : valLe (some 0) (pAdicVal q a) :=
    valLe_zero_pAdicVal_qOfInt_ofNat q hq (crtCofactor ps p (2 ^ n * m))
  have hwn_int : valLe (some 0) (pAdicVal q (Nat.repeat (nsStep a) n w₀)) :=
    nsStep_iterate_integrality hq ha_int hw₀ n
  exact valLe_mul_left hq ha_pow hwn_int

private theorem pAdicVal_eq_one_add_neg_one_sub (p : Nat) (e : QRat) :
    pAdicVal p e = pAdicVal p (qOne + (-(qOne - e))) := by
  apply pAdicVal_eq_of_num_den_eq
  · rw [qrat_add_num]
    have hneg : (-(qOne - e)).num = -(qOne - e).num := rfl
    have hden : (-(qOne - e)).den = (qOne - e).den := rfl
    rw [hneg, hden, qrat_sub_num' qOne e, qrat_sub_den' qOne e]
    simp only [qOne, Int.natCast_mul]
    let en : Int := e.num
    let ed : Int := (e.den : Int)
    change en = 1 * (1 * ed) + -(1 * ed - en * 1) * 1
    omega
  · rw [qrat_add_den]
    have hneg : (-(qOne - e)).den = (qOne - e).den := rfl
    rw [hneg, qrat_sub_den' qOne e]
    simp only [qOne, Nat.one_mul]

/-- Global `p`-integrality of `crtIdempotent` across every prime `q ∈ ps` (including `q = p`). -/
theorem crtIdempotent_integrality_all {ps : List Nat} {p q m n : Nat} {w₀ : QRat}
    (h_primes : AllPrimes ps)
    (cert : HenselInverseCert p (Int.ofNat m)
      (qOfInt (Int.ofNat (crtCofactor ps p (2 ^ n * m)))) w₀)
    (hq : IsPrime q) (hq_mem : q ∈ ps)
    (hw₀_other : q ≠ p → valLe (some 0) (pAdicVal q w₀)) :
    valLe (some 0) (pAdicVal q (crtIdempotent ps p m n w₀)) := by
  have hm0 : valLe (some 0) (some (Int.ofNat (2 ^ n * m))) :=
    Int.natCast_nonneg (2 ^ n * m)
  by_cases hqp : q = p
  · subst hqp
    rw [pAdicVal_eq_one_add_neg_one_sub q (crtIdempotent ps q m n w₀)]
    have h1 : valLe (some 0) (pAdicVal q qOne) := by
      rw [pAdicVal_qOne q cert.prime]
      exact Int.le_refl 0
    have h2 : valLe (some 0) (pAdicVal q (-(qOne - crtIdempotent ps q m n w₀))) := by
      rw [pAdicVal_neg]
      exact valLe_trans hm0 (crtIdempotent_self_residual cert)
    exact valLe_add_of_both cert.prime h1 h2
  · exact valLe_trans hm0 (crtIdempotent_other_val h_primes hq hq_mem hqp (hw₀_other hqp))

/-! #### Multi-Prime CRT Seed Reconstruction & Partition of Unity -/

/-- Sum of CRT idempotents `∑_{p ∈ ps} e_p`. -/
def sumCrtIdempotents (ps : List Nat) (e : Nat → QRat) : QRat :=
  ps.foldl (fun acc p => acc + e p) qZero

/-- Constructive CRT seed `∑_{p ∈ ps} e_p * u_p` combining local inverse seeds `u_p`. -/
def buildCrtSeed (ps : List Nat) (e u : Nat → QRat) : QRat :=
  ps.foldl (fun acc p => acc + e p * u p) qZero

/-- Folded addition preserves lower valuation bounds `ν_q(acc) ≥ b`. -/
theorem valLe_foldl_add {q : Nat} (hq : IsPrime q) {b : Int} (f : Nat → QRat) :
    ∀ (qs : List Nat) (acc : QRat),
      valLe (some b) (pAdicVal q acc) →
      (∀ p ∈ qs, valLe (some b) (pAdicVal q (f p))) →
      valLe (some b) (pAdicVal q (qs.foldl (fun s p => s + f p) acc))
  | [], acc, hacc, _ => hacc
  | p :: qs, acc, hacc, hall => by
    simp only [List.foldl_cons]
    apply valLe_foldl_add hq f qs (acc + f p)
    · exact valLe_add_of_both hq hacc (hall p (List.mem_cons.mpr (Or.inl rfl)))
    · intro r hr
      exact hall r (List.mem_cons.mpr (Or.inr hr))

/-- Every CRT seed `buildCrtSeed ps e u` is `q`-adically integral whenever each `e p`
    and `u p` is `q`-adically integral. -/
theorem buildCrtSeed_integrality {q : Nat} (hq : IsPrime q) (ps : List Nat)
    (e u : Nat → QRat)
    (he : ∀ p ∈ ps, valLe (some 0) (pAdicVal q (e p)))
    (hu : ∀ p ∈ ps, valLe (some 0) (pAdicVal q (u p))) :
    valLe (some 0) (pAdicVal q (buildCrtSeed ps e u)) := by
  unfold buildCrtSeed
  have hzero : valLe (some 0) (pAdicVal q qZero) := by
    have hnum0 : qZero.num = 0 := rfl
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  apply valLe_foldl_add hq (fun p => e p * u p) ps qZero hzero
  intro p hp
  exact valLe_zero_mul hq (he p hp) (hu p hp)

private theorem mul_add_cross_eq (a s t : QRat) :
    CrossEq (a * (s + t)) (a * s + a * t) := by
  unfold CrossEq
  rw [qrat_mul_num' a (s + t), qrat_mul_den' a (s + t),
      qrat_add_num s t, qrat_add_den s t,
      qrat_add_num (a * s) (a * t), qrat_add_den (a * s) (a * t),
      qrat_mul_num' a s, qrat_mul_den' a s,
      qrat_mul_num' a t, qrat_mul_den' a t]
  simp only [Int.natCast_mul]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let sn : Int := s.num
  let sd : Int := (s.den : Int)
  let tn : Int := t.num
  let td : Int := (t.den : Int)
  change
    (an * (sn * td + tn * sd)) * (ad * sd * (ad * td)) =
    (an * sn * (ad * td) + an * tn * (ad * sd)) * (ad * (sd * td))
  rw [Int.mul_add]
  have t1 : (an * (sn * td)) * (ad * sd * (ad * td)) =
      (an * sn * (ad * td)) * (ad * (sd * td)) := by ac_rfl
  have t2 : (an * (tn * sd)) * (ad * sd * (ad * td)) =
      (an * tn * (ad * sd)) * (ad * (sd * td)) := by ac_rfl
  rw [Int.add_mul, t1, t2, ← Int.add_mul]

private theorem one_sub_mul_add_cross_eq (a s t : QRat) :
    CrossEq (qOne - a * (s + t)) ((qOne - a * s) + (-(a * t))) := by
  unfold CrossEq
  rw [qrat_sub_num' qOne (a * (s + t)), qrat_sub_den' qOne (a * (s + t)),
      qrat_mul_num' a (s + t), qrat_mul_den' a (s + t),
      qrat_add_num s t, qrat_add_den s t,
      qrat_add_num (qOne - a * s) (-(a * t)), qrat_add_den (qOne - a * s) (-(a * t)),
      qrat_sub_num' qOne (a * s), qrat_sub_den' qOne (a * s),
      qrat_mul_num' a s, qrat_mul_den' a s]
  have hneg_num : (-(a * t)).num = -(a * t).num := rfl
  have hneg_den : (-(a * t)).den = (a * t).den := rfl
  rw [hneg_num, hneg_den, qrat_mul_num' a t, qrat_mul_den' a t]
  simp only [qOne, Int.natCast_mul]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let sn : Int := s.num
  let sd : Int := (s.den : Int)
  let tn : Int := t.num
  let td : Int := (t.den : Int)
  change
    (1 * (ad * (sd * td)) - an * (sn * td + tn * sd) * 1) * (1 * (ad * sd) * (ad * td)) =
    ((1 * (ad * sd) - an * sn * 1) * (ad * td) + -(an * tn) * (1 * (ad * sd))) *
      (1 * (ad * (sd * td)))
  simp only [Int.one_mul, Int.mul_one]
  let K : Int := ad
  have h_rhs_num :
      (ad * sd - an * sn) * (ad * td) + -(an * tn) * (ad * sd) =
      K * (ad * (sd * td) - an * (sn * td + tn * sd)) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_add]
    have a1 : (ad * sd) * (ad * td) = K * (ad * (sd * td)) := by dsimp [K]; ac_rfl
    have a2 : (an * sn) * (ad * td) = K * (an * (sn * td)) := by dsimp [K]; ac_rfl
    have a3 : -(an * tn) * (ad * sd) = -(K * (an * (tn * sd))) := by
      have b1 : -(an * tn) * (ad * sd) = -((an * tn) * (ad * sd)) := Int.neg_mul _ _
      have b2 : (an * tn) * (ad * sd) = K * (an * (tn * sd)) := by dsimp [K]; ac_rfl
      rw [b1, b2]
    rw [a1, a2, a3, Int.mul_add]
    omega
  rw [h_rhs_num]
  dsimp [K]
  ac_rfl

private theorem one_sub_mul_add_at_prime_cross_eq (a s e u : QRat) :
    CrossEq (qOne - a * (s + e * u))
            ((-(a * s)) + ((qOne - e) + e * (qOne - a * u))) := by
  unfold CrossEq
  rw [qrat_sub_num' qOne (a * (s + e * u)), qrat_sub_den' qOne (a * (s + e * u)),
      qrat_mul_num' a (s + e * u), qrat_mul_den' a (s + e * u),
      qrat_add_num s (e * u), qrat_add_den s (e * u),
      qrat_mul_num' e u, qrat_mul_den' e u,
      qrat_add_num (-(a * s)) ((qOne - e) + e * (qOne - a * u)),
      qrat_add_den (-(a * s)) ((qOne - e) + e * (qOne - a * u)),
      qrat_add_num (qOne - e) (e * (qOne - a * u)),
      qrat_add_den (qOne - e) (e * (qOne - a * u)),
      qrat_sub_num' qOne e, qrat_sub_den' qOne e,
      qrat_mul_num' e (qOne - a * u), qrat_mul_den' e (qOne - a * u),
      qrat_sub_num' qOne (a * u), qrat_sub_den' qOne (a * u),
      qrat_mul_num' a u, qrat_mul_den' a u]
  have hneg_num : (-(a * s)).num = -(a * s).num := rfl
  have hneg_den : (-(a * s)).den = (a * s).den := rfl
  rw [hneg_num, hneg_den, qrat_mul_num' a s, qrat_mul_den' a s]
  simp only [qOne, Int.natCast_mul]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let sn : Int := s.num
  let sd : Int := (s.den : Int)
  let en : Int := e.num
  let ed : Int := (e.den : Int)
  let un : Int := u.num
  let ud : Int := (u.den : Int)
  change
    (1 * (ad * (sd * (ed * ud))) - an * (sn * (ed * ud) + en * un * sd) * 1) *
      (ad * sd * (1 * ed * (ed * (1 * (ad * ud))))) =
    (-(an * sn) * (1 * ed * (ed * (1 * (ad * ud)))) +
      ((1 * ed - en * 1) * (ed * (1 * (ad * ud))) +
        en * (1 * (ad * ud) - an * un * 1) * (1 * ed)) *
        (ad * sd)) *
      (1 * (ad * (sd * (ed * ud))))
  simp only [Int.one_mul, Int.mul_one]
  let K : Int := ad * ed
  have h_rhs_den :
      ad * sd * (ed * (ed * (ad * ud))) =
      K * (ad * (sd * (ed * ud))) := by
    dsimp [K]; ac_rfl
  have h_rhs_num :
      -(an * sn) * (ed * (ed * (ad * ud))) +
        ((ed - en) * (ed * (ad * ud)) + en * (ad * ud - an * un) * ed) * (ad * sd) =
      K * (ad * (sd * (ed * ud)) - an * (sn * (ed * ud) + en * un * sd)) := by
    have t1 :
        -(an * sn) * (ed * (ed * (ad * ud))) =
        -(K * (an * (sn * (ed * ud)))) := by
      have b1 : -(an * sn) * (ed * (ed * (ad * ud))) =
          -((an * sn) * (ed * (ed * (ad * ud)))) := Int.neg_mul _ _
      have b2 : (an * sn) * (ed * (ed * (ad * ud))) =
          K * (an * (sn * (ed * ud))) := by dsimp [K]; ac_rfl
      rw [b1, b2]
    have t2 :
        ((ed - en) * (ed * (ad * ud)) + en * (ad * ud - an * un) * ed) * (ad * sd) =
        K * (ad * (sd * (ed * ud)) - an * (en * un * sd)) := by
      rw [Int.sub_mul, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.sub_mul, Int.sub_mul]
      have a1 : ed * (ed * (ad * ud)) * (ad * sd) =
          K * (ad * (sd * (ed * ud))) := by dsimp [K]; ac_rfl
      have a2 : en * (ed * (ad * ud)) * (ad * sd) =
          en * (ad * ud) * ed * (ad * sd) := by ac_rfl
      have a3 : en * (an * un) * ed * (ad * sd) =
          K * (an * (en * un * sd)) := by dsimp [K]; ac_rfl
      rw [a1, a2, a3, Int.mul_sub]
      omega
    rw [t1, t2]
    have h_dist :
        K * (ad * (sd * (ed * ud)) - an * (sn * (ed * ud) + en * un * sd)) =
        K * (ad * (sd * (ed * ud))) - K * (an * (sn * (ed * ud))) -
          K * (an * (en * un * sd)) := by
      rw [Int.mul_sub, Int.mul_add, Int.mul_add]
      omega
    rw [h_dist, Int.mul_sub]
    omega
  rw [h_rhs_num, h_rhs_den]
  ac_rfl

private theorem valLe_mul_foldl_not_mem {q : Nat} (hq : IsPrime q) {k : Int}
    (a : QRat) (ha : valLe (some 0) (pAdicVal q a)) (e u : Nat → QRat) :
    ∀ (qs : List Nat) (s : QRat),
      notInList q qs = true →
      valLe (some k) (pAdicVal q (a * s)) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (u p))) →
      valLe (some k) (pAdicVal q (a * qs.foldl (fun acc p => acc + e p * u p) s))
  | [], s, _, hs, _, _ => hs
  | p :: qs, s, hnot, hs, he, hu => by
    simp only [notInList, Bool.and_eq_true, nat_bne_true_iff] at hnot
    simp only [List.foldl_cons]
    have hqp : q ≠ p := hnot.1
    have hpq : p ≠ q := Ne.symm hqp
    have hep : valLe (some k) (pAdicVal q (e p)) :=
      he p (List.mem_cons.mpr (Or.inl rfl)) hpq
    have hup : valLe (some 0) (pAdicVal q (u p)) :=
      hu p (List.mem_cons.mpr (Or.inl rfl))
    have hstep : valLe (some k) (pAdicVal q (a * (s + e p * u p))) := by
      rw [pAdicVal_eq_of_cross_mul hq (mul_add_cross_eq a s (e p * u p))]
      have haep : valLe (some k) (pAdicVal q (a * (e p * u p))) :=
        valLe_mul_right hq ha (valLe_mul_left hq hep hup)
      exact valLe_add_of_both hq hs haep
    exact valLe_mul_foldl_not_mem hq a ha e u qs (s + e p * u p) hnot.2 hstep
      (fun r hr hneq => he r (List.mem_cons.mpr (Or.inr hr)) hneq)
      (fun r hr => hu r (List.mem_cons.mpr (Or.inr hr)))

private theorem valLe_one_sub_mul_foldl_after_prime {q : Nat} (hq : IsPrime q) {k : Int}
    (a : QRat) (ha : valLe (some 0) (pAdicVal q a)) (e u : Nat → QRat) :
    ∀ (qs : List Nat) (s : QRat),
      notInList q qs = true →
      valLe (some k) (pAdicVal q (qOne - a * s)) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (u p))) →
      valLe (some k) (pAdicVal q (qOne - a * qs.foldl (fun acc p => acc + e p * u p) s))
  | [], s, _, hs, _, _ => hs
  | p :: qs, s, hnot, hs, he, hu => by
    simp only [notInList, Bool.and_eq_true, nat_bne_true_iff] at hnot
    simp only [List.foldl_cons]
    have hpq : p ≠ q := Ne.symm hnot.1
    have hep : valLe (some k) (pAdicVal q (e p)) :=
      he p (List.mem_cons.mpr (Or.inl rfl)) hpq
    have hup : valLe (some 0) (pAdicVal q (u p)) :=
      hu p (List.mem_cons.mpr (Or.inl rfl))
    have hstep : valLe (some k) (pAdicVal q (qOne - a * (s + e p * u p))) := by
      rw [pAdicVal_eq_of_cross_mul hq (one_sub_mul_add_cross_eq a s (e p * u p))]
      have hneg_term : valLe (some k) (pAdicVal q (-(a * (e p * u p)))) := by
        rw [pAdicVal_neg]
        exact valLe_mul_right hq ha (valLe_mul_left hq hep hup)
      exact valLe_add_of_both hq hs hneg_term
    exact valLe_one_sub_mul_foldl_after_prime hq a ha e u qs (s + e p * u p) hnot.2 hstep
      (fun r hr hneq => he r (List.mem_cons.mpr (Or.inr hr)) hneq)
      (fun r hr => hu r (List.mem_cons.mpr (Or.inr hr)))

private theorem valLe_one_sub_mul_foldl_mem {q : Nat} (hq : IsPrime q) {k : Int}
    (a : QRat) (ha : valLe (some 0) (pAdicVal q a)) (e u : Nat → QRat)
    (he_self : valLe (some k) (pAdicVal q (qOne - e q)))
    (he_int : valLe (some 0) (pAdicVal q (e q)))
    (hu_res : valLe (some k) (pAdicVal q (qOne - a * u q))) :
    ∀ (qs : List Nat) (s : QRat),
      PairwiseDistinct qs →
      q ∈ qs →
      valLe (some k) (pAdicVal q (a * s)) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (u p))) →
      valLe (some k) (pAdicVal q (qOne - a * qs.foldl (fun acc p => acc + e p * u p) s))
  | [], _, _, hmem, _, _, _ => by cases hmem
  | p :: qs, s, hdist, hmem, hs, he, hu => by
    simp only [PairwiseDistinct] at hdist
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have h_at_q : valLe (some k) (pAdicVal q (qOne - a * (s + e q * u q))) := by
        rw [pAdicVal_eq_of_cross_mul hq (one_sub_mul_add_at_prime_cross_eq a s (e q) (u q))]
        have hneg_as : valLe (some k) (pAdicVal q (-(a * s))) := by
          rw [pAdicVal_neg]
          exact hs
        have h_eu_res : valLe (some k) (pAdicVal q (e q * (qOne - a * u q))) :=
          valLe_mul_right hq he_int hu_res
        exact valLe_add_of_both hq hneg_as (valLe_add_of_both hq he_self h_eu_res)
      exact valLe_one_sub_mul_foldl_after_prime hq a ha e u qs (s + e q * u q)
        hdist.1 h_at_q
        (fun r hr hneq => he r (List.mem_cons.mpr (Or.inr hr)) hneq)
        (fun r hr => hu r (List.mem_cons.mpr (Or.inr hr)))
    · have hpq : p ≠ q := by
        intro heq
        subst heq
        have hnot := (notInList_eq_true_iff p qs).mp hdist.1 p hrest
        exact hnot rfl
      have hep : valLe (some k) (pAdicVal q (e p)) :=
        he p (List.mem_cons.mpr (Or.inl rfl)) hpq
      have hup : valLe (some 0) (pAdicVal q (u p)) :=
        hu p (List.mem_cons.mpr (Or.inl rfl))
      have hs' : valLe (some k) (pAdicVal q (a * (s + e p * u p))) := by
        rw [pAdicVal_eq_of_cross_mul hq (mul_add_cross_eq a s (e p * u p))]
        have haep : valLe (some k) (pAdicVal q (a * (e p * u p))) :=
          valLe_mul_right hq ha (valLe_mul_left hq hep hup)
        exact valLe_add_of_both hq hs haep
      exact valLe_one_sub_mul_foldl_mem hq a ha e u he_self he_int hu_res qs
        (s + e p * u p) hdist.2 hrest hs'
        (fun r hr hneq => he r (List.mem_cons.mpr (Or.inr hr)) hneq)
        (fun r hr => hu r (List.mem_cons.mpr (Or.inr hr)))

/-- **Per-Prime Residual Certificate for `buildCrtSeed`:**
    For every prime `q ∈ ps`, `ν_q(1 - a * buildCrtSeed ps e u) ≥ k`. -/
theorem buildCrtSeed_residual_at {q : Nat} (hq : IsPrime q) {k : Int}
    (ps : List Nat) (h_dist : PairwiseDistinct ps) (hq_mem : q ∈ ps)
    (a : QRat) (ha : valLe (some 0) (pAdicVal q a))
    (e u : Nat → QRat)
    (he_self : valLe (some k) (pAdicVal q (qOne - e q)))
    (he_int : valLe (some 0) (pAdicVal q (e q)))
    (he_other : ∀ p ∈ ps, p ≠ q → valLe (some k) (pAdicVal q (e p)))
    (hu_int : ∀ p ∈ ps, valLe (some 0) (pAdicVal q (u p)))
    (hu_res : valLe (some k) (pAdicVal q (qOne - a * u q))) :
    valLe (some k) (pAdicVal q (qOne - a * buildCrtSeed ps e u)) := by
  unfold buildCrtSeed
  have hzero : valLe (some k) (pAdicVal q (a * qZero)) := by
    have hnum0 : (a * qZero).num = 0 := by
      rw [qrat_mul_num']
      have h0 : qZero.num = 0 := rfl
      rw [h0, Int.mul_zero]
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  exact valLe_one_sub_mul_foldl_mem hq a ha e u he_self he_int hu_res
    ps qZero h_dist hq_mem hzero he_other hu_int

private theorem one_mul_foldl_cross_eq (e : Nat → QRat) :
    ∀ (qs : List Nat) (s₁ s₂ : QRat),
      CrossEq s₁ s₂ →
      CrossEq (qOne * qs.foldl (fun acc p => acc + e p * qOne) s₁)
              (qs.foldl (fun acc p => acc + e p) s₂)
  | [], s₁, s₂, hcross => by
    simp only [List.foldl_nil]
    unfold CrossEq at hcross ⊢
    rw [qrat_mul_num' qOne s₁, qrat_mul_den' qOne s₁]
    simp only [qOne, Int.one_mul, Nat.one_mul]
    exact hcross
  | p :: qs, s₁, s₂, hcross => by
    simp only [List.foldl_cons]
    apply one_mul_foldl_cross_eq e qs (s₁ + e p * qOne) (s₂ + e p)
    unfold CrossEq at hcross ⊢
    rw [qrat_add_num s₁ (e p * qOne), qrat_add_den s₁ (e p * qOne),
        qrat_mul_num' (e p) qOne, qrat_mul_den' (e p) qOne,
        qrat_add_num s₂ (e p), qrat_add_den s₂ (e p)]
    simp only [qOne, Int.mul_one, Nat.mul_one, Int.natCast_mul, Int.add_mul]
    let epn : Int := (e p).num
    let epd : Int := ((e p).den : Int)
    let s1n : Int := s₁.num
    let s1d : Int := (s₁.den : Int)
    let s2n : Int := s₂.num
    let s2d : Int := (s₂.den : Int)
    change s1n * epd * (s2d * epd) + epn * s1d * (s2d * epd) =
           s2n * epd * (s1d * epd) + epn * s2d * (s1d * epd)
    congr 1
    · calc s1n * epd * (s2d * epd)
          = (epd * epd) * (s1n * s2d) := by ac_rfl
        _ = (epd * epd) * (s2n * s1d) := by rw [hcross]
        _ = s2n * epd * (s1d * epd) := by ac_rfl
    · ac_rfl

private theorem one_sub_sumCrtIdempotents_cross_eq (ps : List Nat) (e : Nat → QRat) :
    CrossEq (qOne - sumCrtIdempotents ps e)
            (qOne - qOne * buildCrtSeed ps e (fun _ => qOne)) := by
  have hfold := one_mul_foldl_cross_eq e ps qZero qZero (CrossEq.refl qZero)
  unfold sumCrtIdempotents buildCrtSeed
  unfold CrossEq at hfold ⊢
  let S₂ := ps.foldl (fun acc p => acc + e p) qZero
  let S₁ := qOne * ps.foldl (fun acc p => acc + e p * qOne) qZero
  change (qOne - S₂).num * ((qOne - S₁).den : Int) =
         (qOne - S₁).num * ((qOne - S₂).den : Int)
  rw [qrat_sub_num' qOne S₂, qrat_sub_den' qOne S₂,
      qrat_sub_num' qOne S₁, qrat_sub_den' qOne S₁]
  simp only [qOne, Int.one_mul, Nat.one_mul]
  let s1n : Int := S₁.num
  let s1d : Int := (S₁.den : Int)
  let s2n : Int := S₂.num
  let s2d : Int := (S₂.den : Int)
  change (s2d - s2n * 1) * s1d = (s1d - s1n * 1) * s2d
  rw [Int.mul_one, Int.mul_one, Int.sub_mul, Int.sub_mul]
  congr 1
  · ac_rfl
  · exact hfold.symm

/-- **Partition of Unity over a Prime Tower (`∑_{p ∈ ps} e_p ≡ 1`):**
    If `w p` witnesses a cofactor inverse `HenselInverseCert` for each `p ∈ ps`,
    then `∏_{p ∈ ps} p ^ (2 ^ n * m)` divides `(1 - sumCrtIdempotents ps e).num.natAbs`. -/
theorem sumCrtIdempotents_tower_dvd (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (m n : Nat) (w : Nat → QRat)
    (h_cof_certs : ∀ p ∈ ps,
      HenselInverseCert p (Int.ofNat m)
        (qOfInt (Int.ofNat (crtCofactor ps p (2 ^ n * m)))) (w p))
    (hw_other : ∀ p ∈ ps, ∀ q ∈ ps, q ≠ p → valLe (some 0) (pAdicVal q (w p))) :
    primeTowerModulus ps (2 ^ n * m) ∣
      (qOne - sumCrtIdempotents ps (fun p => crtIdempotent ps p m n (w p))).num.natAbs := by
  apply prime_tower_list_pow_dvd_num ps h_primes h_dist (2 ^ n * m)
  intro q hq_mem
  have hq : IsPrime q := (h_cof_certs q hq_mem).prime
  let e : Nat → QRat := fun p => crtIdempotent ps p m n (w p)
  rw [pAdicVal_eq_of_cross_mul hq (one_sub_sumCrtIdempotents_cross_eq ps e)]
  have h_one_int : valLe (some 0) (pAdicVal q qOne) := by
    rw [pAdicVal_qOne q hq]
    exact Int.le_refl 0
  exact buildCrtSeed_residual_at hq ps h_dist hq_mem qOne h_one_int e (fun _ => qOne)
    (crtIdempotent_self_residual (h_cof_certs q hq_mem))
    (crtIdempotent_integrality_all h_primes (h_cof_certs q hq_mem) hq hq_mem
      (fun hne => hw_other q hq_mem q hq_mem hne))
    (fun p hp hne =>
      crtIdempotent_other_val h_primes hq hq_mem (Ne.symm hne)
        (hw_other p hp q hq_mem (Ne.symm hne)))
    (fun _ _ => h_one_int)
    (by
      have hres0 : (qOne - qOne * qOne).num = 0 := rfl
      simp only [pAdicVal, hres0, ↓reduceIte]
      trivial)

/-- **Constructive Prime Tower CRT Seed & Lifting Builder:**
    Given per-prime local inverse certificates `h_inv_certs` for `a` at `u p` and
    cofactor inverse certificates `h_cof_certs` at `w p`, constructs the CRT-fused
    seed `u_tower = buildCrtSeed ps (fun p => crtIdempotent ps p m 0 (w p)) u` and
    returns a complete `PrimeTowerHenselCert ps m a u_tower`. -/
theorem hensel_build_prime_tower_crt (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (m : Nat) (hm : 1 ≤ m) (a : QRat)
    (ha_all : ∀ q ∈ ps, valLe (some 0) (pAdicVal q a))
    (u w : Nat → QRat)
    (h_inv_certs : ∀ q ∈ ps, HenselInverseCert q (Int.ofNat m) a (u q))
    (hu_all : ∀ p ∈ ps, ∀ q ∈ ps, valLe (some 0) (pAdicVal q (u p)))
    (h_cof_certs : ∀ p ∈ ps,
      HenselInverseCert p (Int.ofNat m)
        (qOfInt (Int.ofNat (crtCofactor ps p m))) (w p))
    (hw_other : ∀ p ∈ ps, ∀ q ∈ ps, q ≠ p → valLe (some 0) (pAdicVal q (w p))) :
    PrimeTowerHenselCert ps m a
      (buildCrtSeed ps (fun p => crtIdempotent ps p m 0 (w p)) u) := by
  have hm_eq : 2 ^ 0 * m = m := Nat.one_mul m
  let e : Nat → QRat := fun p => crtIdempotent ps p m 0 (w p)
  have h_cof_certs' : ∀ p ∈ ps,
      HenselInverseCert p (Int.ofNat m)
        (qOfInt (Int.ofNat (crtCofactor ps p (2 ^ 0 * m)))) (w p) := by
    intro p hp
    rw [hm_eq]
    exact h_cof_certs p hp
  have he_all : ∀ q ∈ ps, ∀ p ∈ ps, valLe (some 0) (pAdicVal q (e p)) := by
    intro q hq_mem p hp_mem
    have hq := (h_inv_certs q hq_mem).prime
    exact crtIdempotent_integrality_all h_primes (h_cof_certs' p hp_mem) hq hq_mem
      (fun hne => hw_other p hp_mem q hq_mem hne)
  apply hensel_prime_tower_crt ps h_primes h_dist m hm a
  intro q hq_mem
  have hq := (h_inv_certs q hq_mem).prime
  have hu_tower_int : valLe (some 0) (pAdicVal q (buildCrtSeed ps e u)) :=
    buildCrtSeed_integrality hq ps e u (he_all q hq_mem)
      (fun p hp => hu_all p hp q hq_mem)
  have he_self_q : valLe (some (Int.ofNat m)) (pAdicVal q (qOne - e q)) := by
    have h := crtIdempotent_self_residual (h_cof_certs' q hq_mem)
    rwa [hm_eq] at h
  have he_other_q : ∀ p ∈ ps, p ≠ q → valLe (some (Int.ofNat m)) (pAdicVal q (e p)) := by
    intro p hp hne
    have h := crtIdempotent_other_val (p := p) (q := q) (m := m) (n := 0) (w₀ := w p)
      h_primes hq hq_mem (Ne.symm hne) (hw_other p hp q hq_mem (Ne.symm hne))
    rwa [hm_eq] at h
  have hu_res_q : valLe (some (Int.ofNat m)) (pAdicVal q (qOne - a * u q)) := by
    have h := (h_inv_certs q hq_mem).residual_lift 0
    have hcast : Int.ofNat (2 ^ 0) * Int.ofNat m = Int.ofNat m := Int.one_mul _
    rwa [hcast] at h
  have h_res_tower :
      valLe (some (Int.ofNat m)) (pAdicVal q (qOne - a * buildCrtSeed ps e u)) :=
    buildCrtSeed_residual_at hq ps h_dist hq_mem a (ha_all q hq_mem) e u
      he_self_q (he_all q hq_mem q hq_mem) he_other_q
      (fun p hp => hu_all p hp q hq_mem) hu_res_q
  exact mkHenselInverseCert hq (Int.ofNat_le.mpr hm)
    (ha_all q hq_mem) hu_tower_int h_res_tower

/-! #### Concrete 3-Prime Mersenne Tower CRT Seed Builder (`[7, 31, 127]`) -/

def mersenneTower : List Nat := [7, 31, 127]

def mersenneCofactorInv : Nat → QRat
  | 7 => qOfInt 5
  | 31 => qOfInt 3
  | 127 => qOfInt 24
  | _ => qOne

def mersenneFiveInv : Nat → QRat
  | 7 => qOfInt 3
  | 31 => qOfInt 25
  | 127 => qOfInt 51
  | _ => qOne

/-- **Constructive 3-Prime Mersenne CRT Seed Builder Certificate (`by decide`):**
    Computes the CRT idempotents `e₇ = 19685`, `e₃₁ = 2667`, `e₁₂₇ = 5208` and
    fused seed `u_tower = buildCrtSeed [7, 31, 127] e mersenneFiveInv` (`= 391338`)
    for `a = 5` modulo `(7 * 31 * 127)^(2^n) = 27559^(2^n)` via `hensel_build_prime_tower_crt`. -/
theorem hensel_mersenne_tower_crt_built_inv_5 :
    PrimeTowerHenselCert mersenneTower 1 (qOfInt 5)
      (buildCrtSeed mersenneTower
        (fun p => crtIdempotent mersenneTower p 1 0 (mersenneCofactorInv p))
        mersenneFiveInv) := by
  apply hensel_build_prime_tower_crt mersenneTower (by decide) (by decide) 1 (by decide)
    (qOfInt 5)
  · intro q hq
    simp only [mersenneTower, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hnil
    · decide
    · decide
    · decide
    · cases hnil
  · intro q hq
    simp only [mersenneTower, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hnil
    · exact mkHenselInverseCert prime_mersenne_7 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_31 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_127 (by decide) (by decide) (by decide) (by decide)
    · cases hnil
  · intro p hp q hq
    simp only [mersenneTower, List.mem_cons] at hp hq
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hq with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil
    · exact mkHenselInverseCert prime_mersenne_7 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_31 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_127 (by decide) (by decide) (by decide) (by decide)
    · cases hnil
  · intro p hp q hq _hne
    simp only [mersenneTower, List.mem_cons] at hp hq
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hq with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'

/-! ### Part 8: Ultrametric Perturbation Bounds for Horner Polynomial Evaluation -/

/-- Subtraction congruence for cleared-denominator cross-multiplication equivalence. -/
theorem CrossEq.sub {u₁ v₁ u₂ v₂ : QRat} (h₁ : CrossEq u₁ v₁) (h₂ : CrossEq u₂ v₂) :
    CrossEq (u₁ - u₂) (v₁ - v₂) := by
  unfold CrossEq at h₁ h₂ ⊢
  rw [qrat_sub_num' u₁ u₂, qrat_sub_den' u₁ u₂,
      qrat_sub_num' v₁ v₂, qrat_sub_den' v₁ v₂,
      Int.natCast_mul, Int.natCast_mul, Int.sub_mul, Int.sub_mul]
  congr 1
  · calc (u₁.num * (u₂.den : Int)) * ((v₁.den : Int) * (v₂.den : Int))
        = (u₁.num * (v₁.den : Int)) * ((u₂.den : Int) * (v₂.den : Int)) := by ac_rfl
      _ = (v₁.num * (u₁.den : Int)) * ((u₂.den : Int) * (v₂.den : Int)) := by rw [h₁]
      _ = (v₁.num * (v₂.den : Int)) * ((u₁.den : Int) * (u₂.den : Int)) := by ac_rfl
  · calc (u₂.num * (u₁.den : Int)) * ((v₁.den : Int) * (v₂.den : Int))
        = (u₂.num * (v₂.den : Int)) * ((u₁.den : Int) * (v₁.den : Int)) := by ac_rfl
      _ = (v₂.num * (u₂.den : Int)) * ((u₁.den : Int) * (v₁.den : Int)) := by rw [h₂]
      _ = (v₂.num * (v₁.den : Int)) * ((u₁.den : Int) * (u₂.den : Int)) := by ac_rfl

private theorem add_sub_add_cancel_left_cross_eq (c A B : QRat) :
    CrossEq ((c + A) - (c + B)) (A - B) := by
  unfold CrossEq
  rw [qrat_sub_num' (c + A) (c + B), qrat_sub_den' (c + A) (c + B),
      qrat_add_num c A, qrat_add_den c A,
      qrat_add_num c B, qrat_add_den c B,
      qrat_sub_num' A B, qrat_sub_den' A B]
  simp only [Int.natCast_mul]
  let cn : Int := c.num
  let cd : Int := (c.den : Int)
  let an : Int := A.num
  let ad : Int := (A.den : Int)
  let bn : Int := B.num
  let bd : Int := (B.den : Int)
  change
    ((cn * ad + an * cd) * (cd * bd) - (cn * bd + bn * cd) * (cd * ad)) * (ad * bd) =
    (an * bd - bn * ad) * ((cd * ad) * (cd * bd))
  let K : Int := cd * cd
  have h_num :
      (cn * ad + an * cd) * (cd * bd) - (cn * bd + bn * cd) * (cd * ad) =
      K * (an * bd - bn * ad) := by
    rw [Int.add_mul, Int.add_mul, Int.mul_sub]
    have t1 : (cn * ad) * (cd * bd) = (cn * bd) * (cd * ad) := by ac_rfl
    have t2 : (an * cd) * (cd * bd) = K * (an * bd) := by dsimp [K]; ac_rfl
    have t3 : (bn * cd) * (cd * ad) = K * (bn * ad) := by dsimp [K]; ac_rfl
    rw [t1, t2, t3]
    omega
  have h_den : (cd * ad) * (cd * bd) = K * (ad * bd) := by
    dsimp [K]; ac_rfl
  rw [h_num, h_den]
  ac_rfl

private theorem mul_sub_mul_telescoping_cross_eq (x Px y Py : QRat) :
    CrossEq (x * Px - y * Py) ((x - y) * Px + y * (Px - Py)) := by
  unfold CrossEq
  rw [qrat_sub_num' (x * Px) (y * Py), qrat_sub_den' (x * Px) (y * Py),
      qrat_mul_num' x Px, qrat_mul_den' x Px,
      qrat_mul_num' y Py, qrat_mul_den' y Py,
      qrat_add_num ((x - y) * Px) (y * (Px - Py)),
      qrat_add_den ((x - y) * Px) (y * (Px - Py)),
      qrat_mul_num' (x - y) Px, qrat_mul_den' (x - y) Px,
      qrat_sub_num' x y, qrat_sub_den' x y,
      qrat_mul_num' y (Px - Py), qrat_mul_den' y (Px - Py),
      qrat_sub_num' Px Py, qrat_sub_den' Px Py]
  simp only [Int.natCast_mul]
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  let pxn : Int := Px.num
  let pxd : Int := (Px.den : Int)
  let yn : Int := y.num
  let yd : Int := (y.den : Int)
  let pyn : Int := Py.num
  let pyd : Int := (Py.den : Int)
  change
    ((xn * pxn) * (yd * pyd) - (yn * pyn) * (xd * pxd)) *
      ((xd * yd * pxd) * (yd * (pxd * pyd))) =
    ((xn * yd - yn * xd) * pxn * (yd * (pxd * pyd)) +
      yn * (pxn * pyd - pyn * pxd) * (xd * yd * pxd)) *
      ((xd * pxd) * (yd * pyd))
  let K : Int := yd * pxd
  have h_rhs_den :
      (xd * yd * pxd) * (yd * (pxd * pyd)) = K * ((xd * pxd) * (yd * pyd)) := by
    dsimp [K]; ac_rfl
  have h_rhs_num :
      (xn * yd - yn * xd) * pxn * (yd * (pxd * pyd)) +
        yn * (pxn * pyd - pyn * pxd) * (xd * yd * pxd) =
      K * ((xn * pxn) * (yd * pyd) - (yn * pyn) * (xd * pxd)) := by
    have t1 :
        (xn * yd - yn * xd) * pxn * (yd * (pxd * pyd)) =
        K * ((xn * pxn) * (yd * pyd) - (yn * pxn) * (xd * pyd)) := by
      rw [Int.sub_mul, Int.sub_mul, Int.mul_sub]
      congr 1
      · dsimp [K]; ac_rfl
      · dsimp [K]; ac_rfl
    have t2 :
        yn * (pxn * pyd - pyn * pxd) * (xd * yd * pxd) =
        K * ((yn * pxn) * (xd * pyd) - (yn * pyn) * (xd * pxd)) := by
      rw [Int.mul_sub, Int.sub_mul, Int.mul_sub]
      congr 1
      · dsimp [K]; ac_rfl
      · dsimp [K]; ac_rfl
    rw [t1, t2, ← Int.mul_add]
    congr 1
    omega
  rw [h_rhs_num, h_rhs_den]
  ac_rfl

/-- Exact `p`-adic valuation identity for Horner step differences:
    `ν_p(hornerEval (c :: cs) x - hornerEval (c :: cs) y) =`
    `ν_p((x - y) * hornerEval cs x + y * (hornerEval cs x - hornerEval cs y))`. -/
theorem hornerEval_cons_sub_val_eq {p : Nat} (hp : IsPrime p)
    (c : QRat) (cs : List QRat) (x y : QRat) :
    pAdicVal p (hornerEval (c :: cs) x - hornerEval (c :: cs) y) =
    pAdicVal p ((x - y) * hornerEval cs x + y * (hornerEval cs x - hornerEval cs y)) := by
  simp only [hornerEval]
  rw [pAdicVal_eq_of_cross_mul hp
        (add_sub_add_cancel_left_cross_eq c (x * hornerEval cs x) (y * hornerEval cs y)),
      pAdicVal_eq_of_cross_mul hp
        (mul_sub_mul_telescoping_cross_eq x (hornerEval cs x) y (hornerEval cs y))]

/-- **Recursive Ultrametric Horner Perturbation Inequality** (via `ultrametric_ineq`
    and `pAdicVal_mul`):
    `ν_p(hornerEval (c :: cs) x - hornerEval (c :: cs) y) ≥`
    `min(ν_p(x - y) + ν_p(hornerEval cs x), ν_p(y) + ν_p(hornerEval cs x - hornerEval cs y))`. -/
theorem hornerEval_cons_sub_ultrametric {p : Nat} (hp : IsPrime p)
    (c : QRat) (cs : List QRat) (x y : QRat) :
    valLe
      (valMin
        (valAdd (pAdicVal p (x - y)) (pAdicVal p (hornerEval cs x)))
        (valAdd (pAdicVal p y) (pAdicVal p (hornerEval cs x - hornerEval cs y))))
      (pAdicVal p (hornerEval (c :: cs) x - hornerEval (c :: cs) y)) := by
  rw [hornerEval_cons_sub_val_eq hp c cs x y,
      ← pAdicVal_mul p hp (x - y) (hornerEval cs x),
      ← pAdicVal_mul p hp y (hornerEval cs x - hornerEval cs y)]
  exact ultrametric_ineq p hp
    ((x - y) * hornerEval cs x)
    (y * (hornerEval cs x - hornerEval cs y))

/-- Preservation of `p`-adic integrality under `hornerEval` when `ν_p(x) ≥ 0` and
    `ν_p(c) ≥ 0` for all `c ∈ coeffs`. -/
theorem hornerEval_integrality {p : Nat} (hp : IsPrime p) (x : QRat)
    (hx : valLe (some 0) (pAdicVal p x)) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      valLe (some 0) (pAdicVal p (hornerEval coeffs x))
  | [], _ => by
    have hnum0 : (hornerEval [] x).num = 0 := rfl
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  | c :: cs, hall => by
    simp only [hornerEval]
    have hc : valLe (some 0) (pAdicVal p c) :=
      hall c (List.mem_cons.mpr (Or.inl rfl))
    have ih := hornerEval_integrality hp x hx cs
      (fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc')))
    exact valLe_add_of_both hp hc (valLe_zero_mul hp hx ih)

/-- **`p`-Adic Integral Polynomial Non-Expansiveness (1-Lipschitz Bound):**
    For any `p`-integral points `x, y` (`ν_p(x), ν_p(y) ≥ 0`) and `p`-integral
    polynomial `coeffs`, `ν_p(hornerEval coeffs x - hornerEval coeffs y) ≥ ν_p(x - y)`. -/
theorem hornerEval_sub_val_ge_of_integral {p : Nat} (hp : IsPrime p) (x y : QRat)
    (hx : valLe (some 0) (pAdicVal p x))
    (hy : valLe (some 0) (pAdicVal p y)) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      valLe (pAdicVal p (x - y)) (pAdicVal p (hornerEval coeffs x - hornerEval coeffs y))
  | [], _ => by
    simp only [hornerEval]
    rw [pAdicVal_sub_self]
    trivial
  | c :: cs, hall => by
    have hcs : ∀ c' ∈ cs, valLe (some 0) (pAdicVal p c') :=
      fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))
    have h_px : valLe (some 0) (pAdicVal p (hornerEval cs x)) :=
      hornerEval_integrality hp x hx cs hcs
    have ih := hornerEval_sub_val_ge_of_integral hp x y hx hy cs hcs
    have h_term1 :
        valLe (pAdicVal p (x - y))
              (valAdd (pAdicVal p (x - y)) (pAdicVal p (hornerEval cs x))) := by
      cases hd : pAdicVal p (x - y) with
      | none => trivial
      | some d =>
        cases hpx : pAdicVal p (hornerEval cs x) with
        | none => trivial
        | some vx =>
          rw [hpx] at h_px
          simp only [valLe] at h_px
          simp only [valAdd, valLe]
          omega
    have h_term2 :
        valLe (pAdicVal p (x - y))
              (valAdd (pAdicVal p y) (pAdicVal p (hornerEval cs x - hornerEval cs y))) := by
      cases hd : pAdicVal p (x - y) with
      | none =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some _ =>
          cases hdiff : pAdicVal p (hornerEval cs x - hornerEval cs y) with
          | none => trivial
          | some _ =>
            rw [hdiff] at ih
            exact False.elim ih
      | some d =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some vy =>
          rw [hy'] at hy
          simp only [valLe] at hy
          cases hdiff : pAdicVal p (hornerEval cs x - hornerEval cs y) with
          | none => trivial
          | some vd =>
            rw [hdiff] at ih
            simp only [valLe] at ih
            simp only [valAdd, valLe]
            omega
    exact valLe_trans (valLe_valMin h_term1 h_term2)
      (hornerEval_cons_sub_ultrametric hp c cs x y)

/-- **Vanishing-Linear-Term Contraction Bound:**
    If `ν_p(c₁) ≥ s` (`0 ≤ s`), `ν_p(x) ≥ s`, `ν_p(y) ≥ s`, and `ν_p(c) ≥ 0` for all `c ∈ cs`,
    then `ν_p(hornerEval (c₀ :: c₁ :: cs) x - hornerEval (c₀ :: c₁ :: cs) y) ≥ ν_p(x - y) + s`. -/
theorem hornerEval_zero_const_sub_val_ge {p : Nat} (hp : IsPrime p) {s : Int}
    (hs : 0 ≤ s) (c₀ c₁ : QRat) (cs : List QRat) (x y : QRat)
    (hc₁ : valLe (some s) (pAdicVal p c₁))
    (hx : valLe (some s) (pAdicVal p x))
    (hy : valLe (some s) (pAdicVal p y))
    (hcs : ∀ c ∈ cs, valLe (some 0) (pAdicVal p c)) :
    valLe (valAdd (pAdicVal p (x - y)) (some s))
          (pAdicVal p (hornerEval (c₀ :: c₁ :: cs) x -
                       hornerEval (c₀ :: c₁ :: cs) y)) := by
  have hs0 : valLe (some 0) (some s) := hs
  have hx0 : valLe (some 0) (pAdicVal p x) := valLe_trans hs0 hx
  have hy0 : valLe (some 0) (pAdicVal p y) := valLe_trans hs0 hy
  have hc₁0 : valLe (some 0) (pAdicVal p c₁) := valLe_trans hs0 hc₁
  have hcs_all : ∀ c ∈ c₁ :: cs, valLe (some 0) (pAdicVal p c) := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hrest
    · exact hc₁0
    · exact hcs c hrest
  have h_px_cs : valLe (some 0) (pAdicVal p (hornerEval cs x)) :=
    hornerEval_integrality hp x hx0 cs hcs
  have h_px : valLe (some s) (pAdicVal p (hornerEval (c₁ :: cs) x)) := by
    simp only [hornerEval]
    exact valLe_add_of_both hp hc₁ (valLe_mul_left hp hx h_px_cs)
  have h_cs_sub :
      valLe (pAdicVal p (x - y))
            (pAdicVal p (hornerEval (c₁ :: cs) x - hornerEval (c₁ :: cs) y)) :=
    hornerEval_sub_val_ge_of_integral hp x y hx0 hy0 (c₁ :: cs) hcs_all
  have h_term1 :
      valLe (valAdd (pAdicVal p (x - y)) (some s))
            (valAdd (pAdicVal p (x - y)) (pAdicVal p (hornerEval (c₁ :: cs) x))) := by
    cases hd : pAdicVal p (x - y) with
    | none => trivial
    | some d =>
      cases hpx : pAdicVal p (hornerEval (c₁ :: cs) x) with
      | none => trivial
      | some vx =>
        rw [hpx] at h_px
        simp only [valLe] at h_px
        simp only [valAdd, valLe]
        omega
  have h_term2 :
      valLe (valAdd (pAdicVal p (x - y)) (some s))
            (valAdd (pAdicVal p y)
                    (pAdicVal p (hornerEval (c₁ :: cs) x - hornerEval (c₁ :: cs) y))) := by
    cases hd : pAdicVal p (x - y) with
    | none =>
      rw [hd] at h_cs_sub
      cases hy' : pAdicVal p y with
      | none => trivial
      | some _ =>
        cases hdiff : pAdicVal p (hornerEval (c₁ :: cs) x - hornerEval (c₁ :: cs) y) with
        | none => trivial
        | some _ =>
          rw [hdiff] at h_cs_sub
          exact False.elim h_cs_sub
    | some d =>
      rw [hd] at h_cs_sub
      cases hy' : pAdicVal p y with
      | none => trivial
      | some vy =>
        rw [hy'] at hy
        simp only [valLe] at hy
        cases hdiff : pAdicVal p (hornerEval (c₁ :: cs) x - hornerEval (c₁ :: cs) y) with
        | none => trivial
        | some vd =>
          rw [hdiff] at h_cs_sub
          simp only [valLe] at h_cs_sub
          simp only [valAdd, valLe]
          omega
  exact valLe_trans (valLe_valMin h_term1 h_term2)
    (hornerEval_cons_sub_ultrametric hp c₀ (c₁ :: cs) x y)

/-- **General Denominator-Height Perturbation Bound (by coefficient count):**
    For arbitrary `QRat` inputs `x, y` with `denVal p x ≤ B`, `denVal p y ≤ B`, and
    `denVal p c ≤ Bc` for all `c ∈ coeffs`,
    `ν_p(hornerEval coeffs x - hornerEval coeffs y) ≥ ν_p(x - y) - coeffs.length * (Bc + B)`. -/
theorem hornerEval_sub_val_ge_of_denVal {p Bc B : Nat} (hp : IsPrime p) (x y : QRat)
    (hx_den : denVal p x ≤ B) (hy_den : denVal p y ≤ B) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, denVal p c ≤ Bc) →
      valLe (valAdd (pAdicVal p (x - y))
                    (some (-(Int.ofNat (coeffs.length * (Bc + B))))))
            (pAdicVal p (hornerEval coeffs x - hornerEval coeffs y))
  | [], _ => by
    simp only [hornerEval]
    rw [pAdicVal_sub_self]
    trivial
  | c :: cs, hall => by
    simp only [List.length_cons]
    have hcs : ∀ c' ∈ cs, denVal p c' ≤ Bc :=
      fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))
    have h_px :
        valLe (some (-(Int.ofNat (cs.length * (Bc + B)))))
              (pAdicVal p (hornerEval cs x)) :=
      pAdicVal_ge_neg_of_denVal_le (denVal_hornerEval_le hp x hx_den cs hcs)
    have h_y : valLe (some (-(Int.ofNat B))) (pAdicVal p y) :=
      pAdicVal_ge_neg_of_denVal_le hy_den
    have ih := hornerEval_sub_val_ge_of_denVal hp x y hx_den hy_den cs hcs
    have hlen_mul :
        Int.ofNat ((cs.length + 1) * (Bc + B)) =
        Int.ofNat (cs.length * (Bc + B)) + (Int.ofNat Bc + Int.ofNat B) := by
      have h1 : (cs.length + 1) * (Bc + B) = cs.length * (Bc + B) + (Bc + B) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [h1]
      rfl
    have hBc0 : (0 : Int) ≤ Int.ofNat Bc := Int.natCast_nonneg Bc
    have hB0 : (0 : Int) ≤ Int.ofNat B := Int.natCast_nonneg B
    have h_term1 :
        valLe (valAdd (pAdicVal p (x - y))
                      (some (-(Int.ofNat ((cs.length + 1) * (Bc + B))))))
              (valAdd (pAdicVal p (x - y)) (pAdicVal p (hornerEval cs x))) := by
      cases hd : pAdicVal p (x - y) with
      | none => trivial
      | some d =>
        cases hpx : pAdicVal p (hornerEval cs x) with
        | none => trivial
        | some vx =>
          rw [hpx] at h_px
          simp only [valLe] at h_px
          simp only [valAdd, valLe]
          rw [hlen_mul]
          omega
    have h_term2 :
        valLe (valAdd (pAdicVal p (x - y))
                      (some (-(Int.ofNat ((cs.length + 1) * (Bc + B))))))
              (valAdd (pAdicVal p y) (pAdicVal p (hornerEval cs x - hornerEval cs y))) := by
      cases hd : pAdicVal p (x - y) with
      | none =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some _ =>
          cases hdiff : pAdicVal p (hornerEval cs x - hornerEval cs y) with
          | none => trivial
          | some _ =>
            rw [hdiff] at ih
            exact False.elim ih
      | some d =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some vy =>
          rw [hy'] at h_y
          simp only [valLe] at h_y
          cases hdiff : pAdicVal p (hornerEval cs x - hornerEval cs y) with
          | none => trivial
          | some vd =>
            rw [hdiff] at ih
            simp only [valAdd, valLe] at ih ⊢
            rw [hlen_mul]
            omega
    exact valLe_trans (valLe_valMin h_term1 h_term2)
      (hornerEval_cons_sub_ultrametric hp c cs x y)

/-- **General Denominator-Height Perturbation Bound (by polynomial degree `deg`):**
    For a polynomial of degree at most `deg` (`coeffs.length ≤ deg + 1`),
    `ν_p(hornerEval coeffs x - hornerEval coeffs y) ≥ ν_p(x - y) - (deg + 1) * (Bc + B)`. -/
theorem hornerEval_sub_val_ge_of_deg_denVal {p deg Bc B : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (hdeg : coeffs.length ≤ deg + 1)
    (x y : QRat) (hx_den : denVal p x ≤ B) (hy_den : denVal p y ≤ B)
    (hall : ∀ c ∈ coeffs, denVal p c ≤ Bc) :
    valLe (valAdd (pAdicVal p (x - y))
                  (some (-(Int.ofNat ((deg + 1) * (Bc + B))))))
          (pAdicVal p (hornerEval coeffs x - hornerEval coeffs y)) := by
  have h1 := hornerEval_sub_val_ge_of_denVal hp x y hx_den hy_den coeffs hall
  have hmul : coeffs.length * (Bc + B) ≤ (deg + 1) * (Bc + B) :=
    Nat.mul_le_mul_right (Bc + B) hdeg
  have hmul_int :
      Int.ofNat (coeffs.length * (Bc + B)) ≤ Int.ofNat ((deg + 1) * (Bc + B)) :=
    Int.ofNat_le.mpr hmul
  have h_shift :
      valLe (valAdd (pAdicVal p (x - y))
                    (some (-(Int.ofNat ((deg + 1) * (Bc + B))))))
            (valAdd (pAdicVal p (x - y))
                    (some (-(Int.ofNat (coeffs.length * (Bc + B)))))) := by
    cases pAdicVal p (x - y) with
    | none => trivial
    | some d =>
      simp only [valAdd, valLe]
      omega
  exact valLe_trans h_shift h1

/-- Transfer of perturbation valuation equality from `hornerEval` to `hornerEvalTight`. -/
theorem pAdicVal_hornerEvalTight_sub_eq_hornerEval {p : Nat} (hp : IsPrime p)
    (coeffs : List QRat) (x y : QRat) :
    pAdicVal p (hornerEvalTight coeffs x - hornerEvalTight coeffs y) =
    pAdicVal p (hornerEval coeffs x - hornerEval coeffs y) :=
  pAdicVal_eq_of_cross_mul hp
    (CrossEq.sub
      (hornerEval_cross_eq_tight coeffs x).symm
      (hornerEval_cross_eq_tight coeffs y).symm)

/-! ### Part 9: Constructive Hensel Simple-Root Lifting for Arbitrary `hornerEval` Polynomials -/

/-- Embed a natural number `n : Nat` as `n / 1 : QRat`. -/
def qOfNat (n : Nat) : QRat :=
  { num := Int.ofNat n, den := 1, den_pos := Nat.zero_lt_succ 0 }

/-- Stationary Newton operator for an arbitrary polynomial `P(x) = hornerEval coeffs x`
    with fixed derivative-inverse seed `u₀`:
    `polyNewtonStep coeffs u₀ x = x + (-u₀) * hornerEval coeffs x`. -/
def polyNewtonStep (coeffs : List QRat) (u₀ x : QRat) : QRat :=
  x + (-u₀) * hornerEval coeffs x

theorem CrossEq.trans {u v w : QRat} (h₁ : CrossEq u v) (h₂ : CrossEq v w) :
    CrossEq u w := by
  unfold CrossEq at h₁ h₂ ⊢
  have hvd_pos : 0 < v.den := v.den_pos
  have hvd_ne : (v.den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (by omega)
  apply Int.eq_of_mul_eq_mul_right hvd_ne
  calc (u.num * (w.den : Int)) * (v.den : Int)
      = (u.num * (v.den : Int)) * (w.den : Int) := by ac_rfl
    _ = (v.num * (u.den : Int)) * (w.den : Int) := by rw [h₁]
    _ = (v.num * (w.den : Int)) * (u.den : Int) := by ac_rfl
    _ = (w.num * (v.den : Int)) * (u.den : Int) := by rw [h₂]
    _ = (w.num * (u.den : Int)) * (v.den : Int) := by ac_rfl

/-- Connection to `stationaryNewtonStep`: for the linear polynomial `P(x) = -1 + a * x`,
    `polyNewtonStep [-qOne, a] u₀ x` agrees with `stationaryNewtonStep a u₀ x`. -/
theorem polyNewtonStep_linear_cross_eq (a u₀ x : QRat) :
    CrossEq (polyNewtonStep [-qOne, a] u₀ x) (stationaryNewtonStep a u₀ x) := by
  obtain ⟨hstat_num, hstat_den⟩ := stationary_eval_num_den a u₀ x
  unfold CrossEq polyNewtonStep
  simp only [hornerEval]
  rw [qrat_add_num, qrat_add_den, qrat_mul_num' (-u₀), qrat_mul_den' (-u₀),
      qrat_add_num (-qOne), qrat_add_den (-qOne),
      qrat_mul_num' x (a + x * qZero), qrat_mul_den' x (a + x * qZero),
      qrat_add_num a (x * qZero), qrat_add_den a (x * qZero),
      qrat_mul_num' x qZero, qrat_mul_den' x qZero,
      hstat_num, hstat_den]
  have hneg_u : (-u₀).num = -u₀.num := rfl
  have hneg_uden : (-u₀).den = u₀.den := rfl
  have hneg_1 : (-qOne).num = -1 := rfl
  have hneg_1den : (-qOne).den = 1 := rfl
  rw [hneg_u, hneg_uden, hneg_1, hneg_1den]
  simp only [qZero, Int.natCast_mul, Int.mul_zero, Int.zero_mul,
    Int.add_zero, Nat.one_mul, Nat.mul_one]
  let an : Int := a.num
  let ad : Int := (a.den : Int)
  let un : Int := u₀.num
  let ud : Int := (u₀.den : Int)
  let xn : Int := x.num
  let xd : Int := (x.den : Int)
  change
    (xn * (ud * (xd * (ad * xd))) +
      -un * (-1 * (xd * (ad * xd)) + xn * (an * xd) * 1) * xd) *
      (xd * (ud * (ad * xd))) =
    (xd * (xn * (ud * ad) + un * (ad * xd - an * xn))) *
      (xd * (ud * (xd * (ad * xd))))
  rw [Int.mul_one]
  have h_num_collapse :
      xn * (ud * (xd * (ad * xd))) +
        -un * (-1 * (xd * (ad * xd)) + xn * (an * xd)) * xd =
      xd * (xd * (xn * (ud * ad) + un * (ad * xd - an * xn))) := by
    have t1 : xn * (ud * (xd * (ad * xd))) = xd * (xd * (xn * (ud * ad))) := by ac_rfl
    have t2 :
        -un * (-1 * (xd * (ad * xd)) + xn * (an * xd)) * xd =
        xd * (xd * (un * (ad * xd - an * xn))) := by
      have b1 : -1 * (xd * (ad * xd)) + xn * (an * xd) =
          xd * (an * xn - ad * xd) := by
        rw [Int.mul_sub]
        have a1 : -1 * (xd * (ad * xd)) = -(xd * (ad * xd)) := by omega
        have a2 : xn * (an * xd) = xd * (an * xn) := by ac_rfl
        rw [a1, a2]
        omega
      rw [b1]
      have b2 : -un * (xd * (an * xn - ad * xd)) * xd =
          xd * (xd * (-un * (an * xn - ad * xd))) := by ac_rfl
      have b3 : -un * (an * xn - ad * xd) = un * (ad * xd - an * xn) := by
        rw [Int.neg_mul, Int.mul_sub, Int.mul_sub]
        omega
      rw [b2, b3]
    rw [t1, t2, ← Int.mul_add, ← Int.mul_add]
  have h_den_collapse :
      xd * (ud * (xd * (ad * xd))) = xd * (xd * (ud * (ad * xd))) := by ac_rfl
  rw [h_num_collapse, h_den_collapse]
  ac_rfl

/-! #### Divided-Difference Slope and Formal Polynomial Derivative -/

/-- Divided-difference slope `S(x, y)` satisfying `P(x) - P(y) ~ (x - y) * S(x, y)`. -/
def polySlope : List QRat → QRat → QRat → QRat
  | [], _, _ => qZero
  | _ :: cs, x, y => hornerEval cs x + y * polySlope cs x y

/-- Helper computing scaled derivative coefficients `[(idx * c₀), ((idx+1) * c₁), ...]`. -/
def polyDerivCoeffsAux : Nat → List QRat → List QRat
  | _, [] => []
  | idx, c :: cs => qOfNat idx * c :: polyDerivCoeffsAux (idx + 1) cs

/-- Formal derivative coefficient list of `coeffs = [c₀, c₁, c₂, ...]`. -/
def polyDerivCoeffs : List QRat → List QRat
  | [] => []
  | _ :: cs => polyDerivCoeffsAux 1 cs

private theorem mul_comm_assoc_cross_eq (y d z : QRat) :
    CrossEq (y * (d * z)) (d * (y * z)) := by
  unfold CrossEq
  rw [qrat_mul_num' y (d * z), qrat_mul_den' y (d * z),
      qrat_mul_num' d z, qrat_mul_den' d z,
      qrat_mul_num' d (y * z), qrat_mul_den' d (y * z),
      qrat_mul_num' y z, qrat_mul_den' y z,
      Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  ac_rfl

/-- **Exact Divided-Difference Polynomial Factorization:**
    `hornerEval coeffs x - hornerEval coeffs y ~ (x - y) * polySlope coeffs x y`. -/
theorem hornerEval_sub_cross_eq_slope :
    ∀ (coeffs : List QRat) (x y : QRat),
      CrossEq (hornerEval coeffs x - hornerEval coeffs y) ((x - y) * polySlope coeffs x y)
  | [], x, y => by
    unfold CrossEq hornerEval polySlope
    rw [qrat_sub_num' qZero qZero, qrat_mul_num' (x - y) qZero]
    have h0 : qZero.num = 0 := rfl
    rw [h0, Int.zero_mul, Int.sub_zero, Int.zero_mul, Int.mul_zero, Int.zero_mul]
  | c :: cs, x, y => by
    simp only [hornerEval, polySlope]
    have h1 := add_sub_add_cancel_left_cross_eq c (x * hornerEval cs x) (y * hornerEval cs y)
    have h2 := mul_sub_mul_telescoping_cross_eq x (hornerEval cs x) y (hornerEval cs y)
    have ih := hornerEval_sub_cross_eq_slope cs x y
    have h3 :
        CrossEq ((x - y) * hornerEval cs x + y * (hornerEval cs x - hornerEval cs y))
                ((x - y) * hornerEval cs x + (x - y) * (y * polySlope cs x y)) :=
      CrossEq.add_left ((x - y) * hornerEval cs x)
        ((CrossEq.mul_left y ih).trans (mul_comm_assoc_cross_eq y (x - y) (polySlope cs x y)))
    have h4 := (mul_add_cross_eq (x - y) (hornerEval cs x) (y * polySlope cs x y)).symm
    exact h1.trans (h2.trans (h3.trans h4))

private theorem add_add_comm_cross_eq (a b c d : QRat) :
    CrossEq ((a + b) + (c + d)) ((a + c) + (b + d)) := by
  unfold CrossEq
  rw [qrat_add_num (a + b) (c + d), qrat_add_den (a + b) (c + d),
      qrat_add_num a b, qrat_add_den a b,
      qrat_add_num c d, qrat_add_den c d,
      qrat_add_num (a + c) (b + d), qrat_add_den (a + c) (b + d),
      qrat_add_num a c, qrat_add_den a c,
      qrat_add_num b d, qrat_add_den b d]
  simp only [Int.natCast_mul, Int.add_mul]
  have t1 : a.num * (b.den : Int) * ((c.den : Int) * (d.den : Int)) =
      a.num * (c.den : Int) * ((b.den : Int) * (d.den : Int)) := by ac_rfl
  have t2 : b.num * (a.den : Int) * ((c.den : Int) * (d.den : Int)) =
      b.num * (d.den : Int) * ((a.den : Int) * (c.den : Int)) := by ac_rfl
  have t3 : c.num * (d.den : Int) * ((a.den : Int) * (b.den : Int)) =
      c.num * (a.den : Int) * ((b.den : Int) * (d.den : Int)) := by ac_rfl
  have t4 : d.num * (c.den : Int) * ((a.den : Int) * (b.den : Int)) =
      d.num * (b.den : Int) * ((a.den : Int) * (c.den : Int)) := by ac_rfl
  rw [t1, t2, t3, t4]
  have h_den :
      (a.den : Int) * (b.den : Int) * ((c.den : Int) * (d.den : Int)) =
      (a.den : Int) * (c.den : Int) * ((b.den : Int) * (d.den : Int)) := by ac_rfl
  rw [h_den]
  omega

private theorem qOfNat_succ_mul_cross_eq (m : Nat) (c : QRat) :
    CrossEq (qOfNat (m + 1) * c) (qOfNat m * c + c) := by
  unfold CrossEq
  rw [qrat_mul_num' (qOfNat (m + 1)) c, qrat_mul_den' (qOfNat (m + 1)) c,
      qrat_add_num (qOfNat m * c) c, qrat_add_den (qOfNat m * c) c,
      qrat_mul_num' (qOfNat m) c, qrat_mul_den' (qOfNat m) c]
  simp only [qOfNat, Int.natCast_mul, Nat.one_mul]
  have hcast : Int.ofNat (m + 1) = Int.ofNat m + 1 := rfl
  rw [hcast, Int.add_mul, Int.one_mul, Int.add_mul, Int.add_mul]
  congr 1
  · ac_rfl
  · ac_rfl

private theorem qOfNat_one_mul_cross_eq (c : QRat) :
    CrossEq (qOfNat 1 * c) c := by
  unfold CrossEq
  rw [qrat_mul_num' (qOfNat 1) c, qrat_mul_den' (qOfNat 1) c]
  have h1 : (qOfNat 1).num = 1 := rfl
  have h2 : (qOfNat 1).den = 1 := rfl
  rw [h1, h2, Int.one_mul, Nat.one_mul]

private theorem hornerEval_polyDerivCoeffsAux_succ :
    ∀ (k : Nat) (cs : List QRat) (x : QRat),
      CrossEq (hornerEval (polyDerivCoeffsAux (k + 2) cs) x)
              (hornerEval (polyDerivCoeffsAux (k + 1) cs) x + hornerEval cs x)
  | _, [], _ => rfl
  | k, c :: rest, x => by
    simp only [polyDerivCoeffsAux, hornerEval]
    have ih := hornerEval_polyDerivCoeffsAux_succ (k + 1) rest x
    have h_head := qOfNat_succ_mul_cross_eq (k + 1) c
    have h_tail :
        CrossEq (x * hornerEval (polyDerivCoeffsAux (k + 3) rest) x)
                (x * hornerEval (polyDerivCoeffsAux (k + 2) rest) x + x * hornerEval rest x) :=
      (CrossEq.mul_left x ih).trans
        (mul_add_cross_eq x (hornerEval (polyDerivCoeffsAux (k + 2) rest) x) (hornerEval rest x))
    have h_sum :
        CrossEq
          (qOfNat (k + 2) * c + x * hornerEval (polyDerivCoeffsAux (k + 3) rest) x)
          ((qOfNat (k + 1) * c + c) +
            (x * hornerEval (polyDerivCoeffsAux (k + 2) rest) x + x * hornerEval rest x)) := by
      unfold CrossEq at h_head h_tail ⊢
      let A := qOfNat (k + 2) * c
      let B := x * hornerEval (polyDerivCoeffsAux (k + 3) rest) x
      let C := qOfNat (k + 1) * c + c
      let D := x * hornerEval (polyDerivCoeffsAux (k + 2) rest) x + x * hornerEval rest x
      change (A + B).num * ((C + D).den : Int) = (C + D).num * ((A + B).den : Int)
      rw [qrat_add_num A B, qrat_add_den A B,
          qrat_add_num C D, qrat_add_den C D,
          Int.natCast_mul, Int.natCast_mul, Int.add_mul, Int.add_mul]
      congr 1
      · calc A.num * (B.den : Int) * ((C.den : Int) * (D.den : Int))
            = (A.num * (C.den : Int)) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
          _ = (C.num * (A.den : Int)) * ((B.den : Int) * (D.den : Int)) := by rw [h_head]
          _ = C.num * (D.den : Int) * ((A.den : Int) * (B.den : Int)) := by ac_rfl
      · calc B.num * (A.den : Int) * ((C.den : Int) * (D.den : Int))
            = (B.num * (D.den : Int)) * ((A.den : Int) * (C.den : Int)) := by ac_rfl
          _ = (D.num * (B.den : Int)) * ((A.den : Int) * (C.den : Int)) := by rw [h_tail]
          _ = D.num * (C.den : Int) * ((A.den : Int) * (B.den : Int)) := by ac_rfl
    exact h_sum.trans
      (add_add_comm_cross_eq
        (qOfNat (k + 1) * c) c
        (x * hornerEval (polyDerivCoeffsAux (k + 2) rest) x) (x * hornerEval rest x))

private theorem crossEq_add_right {u v : QRat} (w : QRat) (h : CrossEq u v) :
    CrossEq (u + w) (v + w) := by
  unfold CrossEq at h ⊢
  rw [qrat_add_num u w, qrat_add_den u w, qrat_add_num v w, qrat_add_den v w,
      Int.natCast_mul, Int.natCast_mul, Int.add_mul, Int.add_mul]
  congr 1
  · calc u.num * (w.den : Int) * ((v.den : Int) * (w.den : Int))
        = (u.num * (v.den : Int)) * ((w.den : Int) * (w.den : Int)) := by ac_rfl
      _ = (v.num * (u.den : Int)) * ((w.den : Int) * (w.den : Int)) := by rw [h]
      _ = v.num * (w.den : Int) * ((u.den : Int) * (w.den : Int)) := by ac_rfl
  · ac_rfl

/-- **Diagonal Slope = Formal Polynomial Derivative:**
    `polySlope coeffs x x ~ hornerEval (polyDerivCoeffs coeffs) x`. -/
theorem polySlope_diag_cross_eq_deriv :
    ∀ (coeffs : List QRat) (x : QRat),
      CrossEq (polySlope coeffs x x) (hornerEval (polyDerivCoeffs coeffs) x)
  | [], _ => CrossEq.refl qZero
  | [_], x => add_mul_qZero_cross_eq qZero x
  | _ :: c₁ :: rest, x => by
    simp only [polySlope, polyDerivCoeffs, polyDerivCoeffsAux, hornerEval]
    have ih := polySlope_diag_cross_eq_deriv (c₁ :: rest) x
    simp only [polyDerivCoeffs] at ih
    have h_step1 :
        CrossEq
          ((c₁ + x * hornerEval rest x) + x * polySlope (c₁ :: rest) x x)
          ((c₁ + x * hornerEval rest x) + x * hornerEval (polyDerivCoeffsAux 1 rest) x) :=
      CrossEq.add_left (c₁ + x * hornerEval rest x) (CrossEq.mul_left x ih)
    have h_reassoc :
        CrossEq
          ((c₁ + x * hornerEval rest x) + x * hornerEval (polyDerivCoeffsAux 1 rest) x)
          (c₁ + (x * hornerEval (polyDerivCoeffsAux 1 rest) x + x * hornerEval rest x)) := by
      unfold CrossEq
      let A := hornerEval rest x
      let B := hornerEval (polyDerivCoeffsAux 1 rest) x
      change
        ((c₁ + x * A) + x * B).num * ((c₁ + (x * B + x * A)).den : Int) =
        (c₁ + (x * B + x * A)).num * (((c₁ + x * A) + x * B).den : Int)
      rw [qrat_add_num (c₁ + x * A) (x * B), qrat_add_den (c₁ + x * A) (x * B),
          qrat_add_num c₁ (x * A), qrat_add_den c₁ (x * A),
          qrat_add_num c₁ (x * B + x * A), qrat_add_den c₁ (x * B + x * A),
          qrat_add_num (x * B) (x * A), qrat_add_den (x * B) (x * A),
          qrat_mul_num' x A, qrat_mul_den' x A,
          qrat_mul_num' x B, qrat_mul_den' x B]
      simp only [Int.natCast_mul, Int.add_mul]
      let cn : Int := c₁.num
      let cd : Int := (c₁.den : Int)
      let xn : Int := x.num
      let xd : Int := (x.den : Int)
      let an : Int := A.num
      let ad : Int := (A.den : Int)
      let bn : Int := B.num
      let bd : Int := (B.den : Int)
      change
        cn * (xd * ad) * (xd * bd) * (cd * (xd * bd * (xd * ad))) +
          xn * an * cd * (xd * bd) * (cd * (xd * bd * (xd * ad))) +
          xn * bn * (cd * (xd * ad)) * (cd * (xd * bd * (xd * ad))) =
        cn * (xd * bd * (xd * ad)) * (cd * (xd * ad) * (xd * bd)) +
          (xn * bn * (xd * ad) * cd * (cd * (xd * ad) * (xd * bd)) +
            xn * an * (xd * bd) * cd * (cd * (xd * ad) * (xd * bd)))
      have t1 : cn * (xd * ad) * (xd * bd) * (cd * (xd * bd * (xd * ad))) =
          cn * (xd * bd * (xd * ad)) * (cd * (xd * ad) * (xd * bd)) := by ac_rfl
      have t2 : xn * an * cd * (xd * bd) * (cd * (xd * bd * (xd * ad))) =
          xn * an * (xd * bd) * cd * (cd * (xd * ad) * (xd * bd)) := by ac_rfl
      have t3 : xn * bn * (cd * (xd * ad)) * (cd * (xd * bd * (xd * ad))) =
          xn * bn * (xd * ad) * cd * (cd * (xd * ad) * (xd * bd)) := by ac_rfl
      rw [t1, t2, t3]
      omega
    have h_deriv_tail :
        CrossEq
          (c₁ + (x * hornerEval (polyDerivCoeffsAux 1 rest) x + x * hornerEval rest x))
          (qOfNat 1 * c₁ + x * hornerEval (polyDerivCoeffsAux 2 rest) x) :=
      (CrossEq.add_left c₁
        ((mul_add_cross_eq x (hornerEval (polyDerivCoeffsAux 1 rest) x)
          (hornerEval rest x)).symm.trans
          (CrossEq.mul_left x (hornerEval_polyDerivCoeffsAux_succ 0 rest x).symm))).trans
        (crossEq_add_right (x * hornerEval (polyDerivCoeffsAux 2 rest) x)
          (qOfNat_one_mul_cross_eq c₁).symm)
    exact h_step1.trans (h_reassoc.trans h_deriv_tail)

/-! #### Slope Integrality & Perturbation Bounds (via `hornerEval_sub_val_ge_of_integral`) -/

/-- `p`-Adic integrality of `polySlope coeffs x y` for `p`-integral inputs and coefficients. -/
theorem polySlope_integrality {p : Nat} (hp : IsPrime p) (x y : QRat)
    (hx : valLe (some 0) (pAdicVal p x))
    (hy : valLe (some 0) (pAdicVal p y)) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      valLe (some 0) (pAdicVal p (polySlope coeffs x y))
  | [], _ => by
    have hnum0 : (polySlope [] x y).num = 0 := rfl
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  | _ :: cs, hall => by
    simp only [polySlope]
    have hcs : ∀ c' ∈ cs, valLe (some 0) (pAdicVal p c') :=
      fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))
    have h_px := hornerEval_integrality hp x hx cs hcs
    have ih := polySlope_integrality hp x y hx hy cs hcs
    exact valLe_add_of_both hp h_px (valLe_zero_mul hp hy ih)

/-- First-argument perturbation bound for `polySlope` via `hornerEval_sub_val_ge_of_integral`:
    `ν_p(polySlope coeffs x y - polySlope coeffs x₀ y) ≥ ν_p(x - x₀)`. -/
theorem polySlope_sub_left_val_ge {p : Nat} (hp : IsPrime p) (x x₀ y : QRat)
    (hx : valLe (some 0) (pAdicVal p x))
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hy : valLe (some 0) (pAdicVal p y)) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      valLe (pAdicVal p (x - x₀))
            (pAdicVal p (polySlope coeffs x y - polySlope coeffs x₀ y))
  | [], _ => by
    simp only [polySlope]
    rw [pAdicVal_sub_self]
    trivial
  | _ :: cs, hall => by
    simp only [polySlope]
    have hcs : ∀ c' ∈ cs, valLe (some 0) (pAdicVal p c') :=
      fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))
    have h_horner := hornerEval_sub_val_ge_of_integral hp x x₀ hx hx₀ cs hcs
    have ih := polySlope_sub_left_val_ge hp x x₀ y hx hx₀ hy cs hcs
    have h_cross :
        CrossEq
          ((hornerEval cs x + y * polySlope cs x y) -
           (hornerEval cs x₀ + y * polySlope cs x₀ y))
          ((hornerEval cs x - hornerEval cs x₀) +
           y * (polySlope cs x y - polySlope cs x₀ y)) := by
      have h_sub_sum :
          CrossEq
            ((hornerEval cs x + y * polySlope cs x y) -
             (hornerEval cs x₀ + y * polySlope cs x₀ y))
            ((hornerEval cs x - hornerEval cs x₀) +
             (y * polySlope cs x y - y * polySlope cs x₀ y)) := by
        unfold CrossEq
        let A := hornerEval cs x
        let B := y * polySlope cs x y
        let C := hornerEval cs x₀
        let D := y * polySlope cs x₀ y
        change
          ((A + B) - (C + D)).num * (((A - C) + (B - D)).den : Int) =
          ((A - C) + (B - D)).num * (((A + B) - (C + D)).den : Int)
        rw [qrat_sub_num' (A + B) (C + D), qrat_sub_den' (A + B) (C + D),
            qrat_add_num A B, qrat_add_den A B,
            qrat_add_num C D, qrat_add_den C D,
            qrat_add_num (A - C) (B - D), qrat_add_den (A - C) (B - D),
            qrat_sub_num' A C, qrat_sub_den' A C,
            qrat_sub_num' B D, qrat_sub_den' B D]
        simp only [Int.natCast_mul, Int.add_mul, Int.sub_mul]
        have t1 : A.num * (B.den : Int) * ((C.den : Int) * (D.den : Int)) =
            A.num * (C.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
        have t2 : B.num * (A.den : Int) * ((C.den : Int) * (D.den : Int)) =
            B.num * (D.den : Int) * ((A.den : Int) * (C.den : Int)) := by ac_rfl
        have t3 : C.num * (D.den : Int) * ((A.den : Int) * (B.den : Int)) =
            C.num * (A.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
        have t4 : D.num * (C.den : Int) * ((A.den : Int) * (B.den : Int)) =
            D.num * (B.den : Int) * ((A.den : Int) * (C.den : Int)) := by ac_rfl
        rw [t1, t2, t3, t4]
        have h_den :
            (A.den : Int) * (B.den : Int) * ((C.den : Int) * (D.den : Int)) =
            (A.den : Int) * (C.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
        rw [h_den]
        omega
      have h_factor_y :
          CrossEq (y * polySlope cs x y - y * polySlope cs x₀ y)
                  (y * (polySlope cs x y - polySlope cs x₀ y)) := by
        unfold CrossEq
        let U := polySlope cs x y
        let V := polySlope cs x₀ y
        change (y * U - y * V).num * ((y * (U - V)).den : Int) =
               (y * (U - V)).num * ((y * U - y * V).den : Int)
        rw [qrat_sub_num' (y * U) (y * V), qrat_sub_den' (y * U) (y * V),
            qrat_mul_num' y U, qrat_mul_den' y U,
            qrat_mul_num' y V, qrat_mul_den' y V,
            qrat_mul_num' y (U - V), qrat_mul_den' y (U - V),
            qrat_sub_num' U V, qrat_sub_den' U V]
        simp only [Int.natCast_mul]
        have h_num :
            (y.num * U.num) * ((y.den : Int) * (V.den : Int)) -
            (y.num * V.num) * ((y.den : Int) * (U.den : Int)) =
            (y.den : Int) * (y.num * (U.num * (V.den : Int) - V.num * (U.den : Int))) := by
          rw [Int.mul_sub, Int.mul_sub]
          congr 1 <;> ac_rfl
        have h_den :
            ((y.den : Int) * (U.den : Int)) * ((y.den : Int) * (V.den : Int)) =
            (y.den : Int) * ((y.den : Int) * ((U.den : Int) * (V.den : Int))) := by ac_rfl
        rw [h_num, h_den]
        ac_rfl
      exact h_sub_sum.trans
        (CrossEq.add_left (hornerEval cs x - hornerEval cs x₀) h_factor_y)
    rw [pAdicVal_eq_of_cross_mul hp h_cross]
    have h_second :
        valLe (pAdicVal p (x - x₀))
              (pAdicVal p (y * (polySlope cs x y - polySlope cs x₀ y))) := by
      rw [pAdicVal_mul p hp y (polySlope cs x y - polySlope cs x₀ y)]
      cases hd : pAdicVal p (x - x₀) with
      | none =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some _ =>
          cases hdiff : pAdicVal p (polySlope cs x y - polySlope cs x₀ y) with
          | none => trivial
          | some _ =>
            rw [hdiff] at ih
            exact False.elim ih
      | some d =>
        rw [hd] at ih
        cases hy' : pAdicVal p y with
        | none => trivial
        | some vy =>
          rw [hy'] at hy
          simp only [valLe] at hy
          cases hdiff : pAdicVal p (polySlope cs x y - polySlope cs x₀ y) with
          | none => trivial
          | some vd =>
            rw [hdiff] at ih
            simp only [valLe] at ih
            simp only [valAdd, valLe]
            omega
    exact valLe_trans (valLe_valMin h_horner h_second)
      (ultrametric_ineq p hp
        (hornerEval cs x - hornerEval cs x₀)
        (y * (polySlope cs x y - polySlope cs x₀ y)))

/-- Second-argument perturbation bound for `polySlope`:
    `ν_p(polySlope coeffs x₀ y - polySlope coeffs x₀ x₀) ≥ ν_p(y - x₀)`. -/
theorem polySlope_sub_right_val_ge {p : Nat} (hp : IsPrime p) (x₀ y : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hy : valLe (some 0) (pAdicVal p y)) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      valLe (pAdicVal p (y - x₀))
            (pAdicVal p (polySlope coeffs x₀ y - polySlope coeffs x₀ x₀))
  | [], _ => by
    simp only [polySlope]
    rw [pAdicVal_sub_self]
    trivial
  | _ :: cs, hall => by
    simp only [polySlope]
    have hcs : ∀ c' ∈ cs, valLe (some 0) (pAdicVal p c') :=
      fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))
    have h_slope_int := polySlope_integrality hp x₀ y hx₀ hy cs hcs
    have ih := polySlope_sub_right_val_ge hp x₀ y hx₀ hy cs hcs
    have h_cross :
        CrossEq
          ((hornerEval cs x₀ + y * polySlope cs x₀ y) -
           (hornerEval cs x₀ + x₀ * polySlope cs x₀ x₀))
          ((y - x₀) * polySlope cs x₀ y +
           x₀ * (polySlope cs x₀ y - polySlope cs x₀ x₀)) :=
      (add_sub_add_cancel_left_cross_eq (hornerEval cs x₀)
        (y * polySlope cs x₀ y) (x₀ * polySlope cs x₀ x₀)).trans
        (mul_sub_mul_telescoping_cross_eq y (polySlope cs x₀ y) x₀ (polySlope cs x₀ x₀))
    rw [pAdicVal_eq_of_cross_mul hp h_cross]
    have h_t1 :
        valLe (pAdicVal p (y - x₀))
              (pAdicVal p ((y - x₀) * polySlope cs x₀ y)) := by
      rw [pAdicVal_mul p hp (y - x₀) (polySlope cs x₀ y)]
      cases hd : pAdicVal p (y - x₀) with
      | none => trivial
      | some d =>
        cases hs : pAdicVal p (polySlope cs x₀ y) with
        | none => trivial
        | some vs =>
          rw [hs] at h_slope_int
          simp only [valLe] at h_slope_int
          simp only [valAdd, valLe]
          omega
    have h_t2 :
        valLe (pAdicVal p (y - x₀))
              (pAdicVal p (x₀ * (polySlope cs x₀ y - polySlope cs x₀ x₀))) := by
      rw [pAdicVal_mul p hp x₀ (polySlope cs x₀ y - polySlope cs x₀ x₀)]
      cases hd : pAdicVal p (y - x₀) with
      | none =>
        rw [hd] at ih
        cases hx' : pAdicVal p x₀ with
        | none => trivial
        | some _ =>
          cases hdiff : pAdicVal p (polySlope cs x₀ y - polySlope cs x₀ x₀) with
          | none => trivial
          | some _ =>
            rw [hdiff] at ih
            exact False.elim ih
      | some d =>
        rw [hd] at ih
        cases hx' : pAdicVal p x₀ with
        | none => trivial
        | some vx =>
          rw [hx'] at hx₀
          simp only [valLe] at hx₀
          cases hdiff : pAdicVal p (polySlope cs x₀ y - polySlope cs x₀ x₀) with
          | none => trivial
          | some vd =>
            rw [hdiff] at ih
            simp only [valLe] at ih
            simp only [valAdd, valLe]
            omega
    exact valLe_trans (valLe_valMin h_t1 h_t2)
      (ultrametric_ineq p hp
        ((y - x₀) * polySlope cs x₀ y)
        (x₀ * (polySlope cs x₀ y - polySlope cs x₀ x₀)))

private theorem valMin_le_left (a b : ExtVal) : valLe (valMin a b) a := by
  cases a with
  | none => trivial
  | some va =>
    cases b with
    | none => exact Int.le_refl va
    | some vb => exact Int.min_le_left va vb

private theorem valMin_le_right (a b : ExtVal) : valLe (valMin a b) b := by
  cases b with
  | none => trivial
  | some vb =>
    cases a with
    | none => exact Int.le_refl vb
    | some va => exact Int.min_le_right va vb

private theorem valMin_mono {a b c d : ExtVal} (h1 : valLe a c) (h2 : valLe b d) :
    valLe (valMin a b) (valMin c d) :=
  valLe_valMin (valLe_trans (valMin_le_left a b) h1) (valLe_trans (valMin_le_right a b) h2)

/-- **Joint Slope-to-Derivative Perturbation Bound:**
    `ν_p(hornerEval (polyDerivCoeffs coeffs) x₀ - polySlope coeffs x y) ≥`
    `min(ν_p(x - x₀), ν_p(y - x₀))`. -/
theorem polyDeriv_sub_slope_val_ge_min {p : Nat} (hp : IsPrime p) (x y x₀ : QRat)
    (hx : valLe (some 0) (pAdicVal p x))
    (hy : valLe (some 0) (pAdicVal p y))
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) :
    valLe (valMin (pAdicVal p (x - x₀)) (pAdicVal p (y - x₀)))
          (pAdicVal p (hornerEval (polyDerivCoeffs coeffs) x₀ - polySlope coeffs x y)) := by
  rw [pAdicVal_sub_comm p (hornerEval (polyDerivCoeffs coeffs) x₀) (polySlope coeffs x y)]
  have h_diag :
      pAdicVal p (polySlope coeffs x y - hornerEval (polyDerivCoeffs coeffs) x₀) =
      pAdicVal p (polySlope coeffs x y - polySlope coeffs x₀ x₀) :=
    pAdicVal_eq_of_cross_mul hp
      (CrossEq.sub (CrossEq.refl _) (polySlope_diag_cross_eq_deriv coeffs x₀).symm)
  rw [h_diag, ← pAdicVal_sub_add_sub hp (polySlope coeffs x y) (polySlope coeffs x₀ y)
        (polySlope coeffs x₀ x₀)]
  have h1 := polySlope_sub_left_val_ge hp x x₀ y hx hx₀ hy coeffs hcoeffs
  have h2 := polySlope_sub_right_val_ge hp x₀ y hx₀ hy coeffs hcoeffs
  exact valLe_trans (valMin_mono h1 h2)
    (ultrametric_ineq p hp
      (polySlope coeffs x y - polySlope coeffs x₀ y)
      (polySlope coeffs x₀ y - polySlope coeffs x₀ x₀))

/-! #### Stationary Newton-Step Identities and Local Ball Contraction -/

private theorem add_neg_mul_cross_eq (D u₀ S : QRat) :
    CrossEq (D + (-u₀) * (D * S)) (D * (qOne - u₀ * S)) := by
  unfold CrossEq
  rw [qrat_add_num D ((-u₀) * (D * S)), qrat_add_den D ((-u₀) * (D * S)),
      qrat_mul_num' (-u₀) (D * S), qrat_mul_den' (-u₀) (D * S),
      qrat_mul_num' D S, qrat_mul_den' D S,
      qrat_mul_num' D (qOne - u₀ * S), qrat_mul_den' D (qOne - u₀ * S),
      qrat_sub_num' qOne (u₀ * S), qrat_sub_den' qOne (u₀ * S),
      qrat_mul_num' u₀ S, qrat_mul_den' u₀ S]
  have hneg_num : (-u₀).num = -u₀.num := rfl
  have hneg_den : (-u₀).den = u₀.den := rfl
  rw [hneg_num, hneg_den]
  simp only [qOne, Int.natCast_mul, Int.one_mul, Nat.one_mul]
  let dn : Int := D.num
  let dd : Int := (D.den : Int)
  let un : Int := u₀.num
  let ud : Int := (u₀.den : Int)
  let sn : Int := S.num
  let sd : Int := (S.den : Int)
  change
    (dn * (ud * (dd * sd)) + -un * (dn * sn) * dd) * (dd * (ud * sd)) =
    dn * (ud * sd - un * sn * 1) * (dd * (ud * (dd * sd)))
  rw [Int.mul_one]
  have h_num :
      dn * (ud * (dd * sd)) + -un * (dn * sn) * dd =
      dd * (dn * (ud * sd - un * sn)) := by
    rw [Int.mul_sub, Int.mul_sub]
    have t1 : dn * (ud * (dd * sd)) = dd * (dn * (ud * sd)) := by ac_rfl
    have t2 : -un * (dn * sn) * dd = -(dd * (dn * (un * sn))) := by
      have b1 : -un * (dn * sn) = -(un * (dn * sn)) := Int.neg_mul _ _
      rw [b1]
      have b2 : -(un * (dn * sn)) * dd = -(un * (dn * sn) * dd) := Int.neg_mul _ _
      rw [b2]
      congr 1
      ac_rfl
    rw [t1, t2]
    omega
  have h_den : dd * (ud * (dd * sd)) = dd * (dd * (ud * sd)) := by ac_rfl
  rw [h_num, h_den]
  ac_rfl

/-- Exact step-difference factorization for `polyNewtonStep`:
    `polyNewtonStep coeffs u₀ x - polyNewtonStep coeffs u₀ y ~`
    `(x - y) * (1 - u₀ * polySlope coeffs x y)`. -/
theorem polyNewtonStep_sub_cross_eq (coeffs : List QRat) (u₀ x y : QRat) :
    CrossEq (polyNewtonStep coeffs u₀ x - polyNewtonStep coeffs u₀ y)
            ((x - y) * (qOne - u₀ * polySlope coeffs x y)) := by
  unfold polyNewtonStep
  have h_sub_sum :
      CrossEq
        ((x + (-u₀) * hornerEval coeffs x) - (y + (-u₀) * hornerEval coeffs y))
        ((x - y) + ((-u₀) * hornerEval coeffs x - (-u₀) * hornerEval coeffs y)) := by
    unfold CrossEq
    let A := x
    let B := (-u₀) * hornerEval coeffs x
    let C := y
    let D := (-u₀) * hornerEval coeffs y
    change
      ((A + B) - (C + D)).num * (((A - C) + (B - D)).den : Int) =
      ((A - C) + (B - D)).num * (((A + B) - (C + D)).den : Int)
    rw [qrat_sub_num' (A + B) (C + D), qrat_sub_den' (A + B) (C + D),
        qrat_add_num A B, qrat_add_den A B,
        qrat_add_num C D, qrat_add_den C D,
        qrat_add_num (A - C) (B - D), qrat_add_den (A - C) (B - D),
        qrat_sub_num' A C, qrat_sub_den' A C,
        qrat_sub_num' B D, qrat_sub_den' B D]
    simp only [Int.natCast_mul, Int.add_mul, Int.sub_mul]
    have t1 : A.num * (B.den : Int) * ((C.den : Int) * (D.den : Int)) =
        A.num * (C.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
    have t2 : B.num * (A.den : Int) * ((C.den : Int) * (D.den : Int)) =
        B.num * (D.den : Int) * ((A.den : Int) * (C.den : Int)) := by ac_rfl
    have t3 : C.num * (D.den : Int) * ((A.den : Int) * (B.den : Int)) =
        C.num * (A.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
    have t4 : D.num * (C.den : Int) * ((A.den : Int) * (B.den : Int)) =
        D.num * (B.den : Int) * ((A.den : Int) * (C.den : Int)) := by ac_rfl
    rw [t1, t2, t3, t4]
    have h_den :
        (A.den : Int) * (B.den : Int) * ((C.den : Int) * (D.den : Int)) =
        (A.den : Int) * (C.den : Int) * ((B.den : Int) * (D.den : Int)) := by ac_rfl
    rw [h_den]
    omega
  have h2 :
      CrossEq ((-u₀) * hornerEval coeffs x - (-u₀) * hornerEval coeffs y)
              ((-u₀) * (hornerEval coeffs x - hornerEval coeffs y)) := by
    unfold CrossEq
    let A := hornerEval coeffs x
    let B := hornerEval coeffs y
    change ((-u₀) * A - (-u₀) * B).num * (((-u₀) * (A - B)).den : Int) =
           ((-u₀) * (A - B)).num * (((-u₀) * A - (-u₀) * B).den : Int)
    rw [qrat_sub_num' ((-u₀) * A) ((-u₀) * B), qrat_sub_den' ((-u₀) * A) ((-u₀) * B),
        qrat_mul_num' (-u₀) A, qrat_mul_den' (-u₀) A,
        qrat_mul_num' (-u₀) B, qrat_mul_den' (-u₀) B,
        qrat_mul_num' (-u₀) (A - B), qrat_mul_den' (-u₀) (A - B),
        qrat_sub_num' A B, qrat_sub_den' A B]
    simp only [Int.natCast_mul]
    have h_num :
        ((-u₀).num * A.num) * (((-u₀).den : Int) * (B.den : Int)) -
        ((-u₀).num * B.num) * (((-u₀).den : Int) * (A.den : Int)) =
        ((-u₀).den : Int) * ((-u₀).num * (A.num * (B.den : Int) - B.num * (A.den : Int))) := by
      rw [Int.mul_sub, Int.mul_sub]
      congr 1 <;> ac_rfl
    have h_den :
        (((-u₀).den : Int) * (A.den : Int)) * (((-u₀).den : Int) * (B.den : Int)) =
        ((-u₀).den : Int) * (((-u₀).den : Int) * ((A.den : Int) * (B.den : Int))) := by ac_rfl
    rw [h_num, h_den]
    ac_rfl
  have h3 := CrossEq.mul_left (-u₀) (hornerEval_sub_cross_eq_slope coeffs x y)
  have h4 := h_sub_sum.trans (CrossEq.add_left (x - y) (h2.trans h3))
  exact h4.trans (add_neg_mul_cross_eq (x - y) u₀ (polySlope coeffs x y))

/-- Exact polynomial residual transition identity for `polyNewtonStep`:
    `hornerEval coeffs (polyNewtonStep coeffs u₀ x) ~`
    `hornerEval coeffs x * (1 - u₀ * polySlope coeffs (polyNewtonStep coeffs u₀ x) x)`. -/
theorem polyNewtonStep_residual_cross_eq (coeffs : List QRat) (u₀ x : QRat) :
    CrossEq (hornerEval coeffs (polyNewtonStep coeffs u₀ x))
            (hornerEval coeffs x *
              (qOne - u₀ * polySlope coeffs (polyNewtonStep coeffs u₀ x) x)) := by
  let fx := polyNewtonStep coeffs u₀ x
  have h_id : CrossEq (hornerEval coeffs fx)
      (hornerEval coeffs x + (hornerEval coeffs fx - hornerEval coeffs x)) := by
    unfold CrossEq
    let P0 := hornerEval coeffs x
    let P1 := hornerEval coeffs fx
    change P1.num * ((P0 + (P1 - P0)).den : Int) =
           (P0 + (P1 - P0)).num * (P1.den : Int)
    rw [qrat_add_num P0 (P1 - P0), qrat_add_den P0 (P1 - P0),
        qrat_sub_num' P1 P0, qrat_sub_den' P1 P0,
        Int.natCast_mul, Int.natCast_mul]
    have h_num :
        P0.num * ((P1.den : Int) * (P0.den : Int)) +
          (P1.num * (P0.den : Int) - P0.num * (P1.den : Int)) * (P0.den : Int) =
        P1.num * ((P0.den : Int) * (P0.den : Int)) := by
      rw [Int.sub_mul]
      have t1 : P0.num * ((P1.den : Int) * (P0.den : Int)) =
          P0.num * (P1.den : Int) * (P0.den : Int) := by ac_rfl
      have t2 : P1.num * (P0.den : Int) * (P0.den : Int) =
          P1.num * ((P0.den : Int) * (P0.den : Int)) := by ac_rfl
      rw [t1, t2]
      omega
    rw [h_num]
    ac_rfl
  have h_step_diff :
      CrossEq (fx - x) ((-u₀) * hornerEval coeffs x) :=
    add_sub_cancel_left_cross_eq x ((-u₀) * hornerEval coeffs x)
  have h_slope :
      CrossEq (hornerEval coeffs fx - hornerEval coeffs x)
              ((-u₀) * (hornerEval coeffs x * polySlope coeffs fx x)) :=
    (hornerEval_sub_cross_eq_slope coeffs fx x).trans
      ((crossEq_mul_right (polySlope coeffs fx x) h_step_diff).trans
        (mul_assoc_cross_eq (-u₀) (hornerEval coeffs x) (polySlope coeffs fx x)))
  exact h_id.trans
    ((CrossEq.add_left (hornerEval coeffs x) h_slope).trans
      (add_neg_mul_cross_eq (hornerEval coeffs x) u₀ (polySlope coeffs fx x)))
where
  crossEq_mul_right (z : QRat) {u v : QRat} (h : CrossEq u v) :
      CrossEq (u * z) (v * z) := by
    unfold CrossEq at h ⊢
    rw [qrat_mul_num' u z, qrat_mul_den' u z, qrat_mul_num' v z, qrat_mul_den' v z,
        Int.natCast_mul, Int.natCast_mul]
    calc (u.num * z.num) * ((v.den : Int) * (z.den : Int))
        = (u.num * (v.den : Int)) * (z.num * (z.den : Int)) := by ac_rfl
      _ = (v.num * (u.den : Int)) * (z.num * (z.den : Int)) := by rw [h]
      _ = (v.num * z.num) * ((u.den : Int) * (z.den : Int)) := by ac_rfl
  mul_assoc_cross_eq (a b c : QRat) : CrossEq ((a * b) * c) (a * (b * c)) := by
    unfold CrossEq
    rw [qrat_mul_num' (a * b) c, qrat_mul_den' (a * b) c,
        qrat_mul_num' a b, qrat_mul_den' a b,
        qrat_mul_num' a (b * c), qrat_mul_den' a (b * c),
        qrat_mul_num' b c, qrat_mul_den' b c,
        Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
    ac_rfl

private theorem pAdicVal_integrality_of_ball {p : Nat} (hp : IsPrime p) {s : Int}
    (hs : 0 ≤ s) {x x₀ : QRat}
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hball : valLe (some s) (pAdicVal p (x - x₀))) :
    valLe (some 0) (pAdicVal p x) := by
  have h_id : CrossEq x (x₀ + (x - x₀)) := by
    unfold CrossEq
    rw [qrat_add_num x₀ (x - x₀), qrat_add_den x₀ (x - x₀),
        qrat_sub_num' x x₀, qrat_sub_den' x x₀,
        Int.natCast_mul, Int.natCast_mul]
    have h_num :
        x.num * ((x₀.den : Int) * ((x.den : Int) * (x₀.den : Int))) =
        (x₀.num * ((x.den : Int) * (x₀.den : Int)) +
          (x.num * (x₀.den : Int) - x₀.num * (x.den : Int)) * (x₀.den : Int)) *
          (x.den : Int) := by
      rw [Int.sub_mul, Int.add_mul, Int.sub_mul]
      have t1 : x₀.num * ((x.den : Int) * (x₀.den : Int)) * (x.den : Int) =
          x₀.num * (x.den : Int) * (x₀.den : Int) * (x.den : Int) := by ac_rfl
      have t2 : x.num * (x₀.den : Int) * (x₀.den : Int) * (x.den : Int) =
          x.num * ((x₀.den : Int) * ((x.den : Int) * (x₀.den : Int))) := by ac_rfl
      rw [t1, t2]
      omega
    exact h_num
  rw [pAdicVal_eq_of_cross_mul hp h_id]
  have hs0 : valLe (some 0) (some s) := hs
  have hdiff0 : valLe (some 0) (pAdicVal p (x - x₀)) := valLe_trans hs0 hball
  exact valLe_add_of_both hp hx₀ hdiff0

private theorem poly_contraction_factor_val_ge {p : Nat} (hp : IsPrime p) {step : Int}
    (hstep : 1 ≤ step) (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ x y : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv :
      valLe (some step) (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (hx_ball : valLe (some step) (pAdicVal p (x - x₀)))
    (hy_ball : valLe (some step) (pAdicVal p (y - x₀))) :
    valLe (some step) (pAdicVal p (qOne - u₀ * polySlope coeffs x y)) := by
  have hstep0 : 0 ≤ step := Int.le_trans (by decide : (0 : Int) ≤ 1) hstep
  have hx_int := pAdicVal_integrality_of_ball hp hstep0 hx₀ hx_ball
  have hy_int := pAdicVal_integrality_of_ball hp hstep0 hx₀ hy_ball
  let D := hornerEval (polyDerivCoeffs coeffs) x₀
  let S := polySlope coeffs x y
  have h_decomp : CrossEq (qOne - u₀ * S) ((qOne - u₀ * D) + u₀ * (D - S)) := by
    unfold CrossEq
    change (qOne - u₀ * S).num * (((qOne - u₀ * D) + u₀ * (D - S)).den : Int) =
           ((qOne - u₀ * D) + u₀ * (D - S)).num * ((qOne - u₀ * S).den : Int)
    rw [qrat_sub_num' qOne (u₀ * S), qrat_sub_den' qOne (u₀ * S),
        qrat_mul_num' u₀ S, qrat_mul_den' u₀ S,
        qrat_add_num (qOne - u₀ * D) (u₀ * (D - S)),
        qrat_add_den (qOne - u₀ * D) (u₀ * (D - S)),
        qrat_sub_num' qOne (u₀ * D), qrat_sub_den' qOne (u₀ * D),
        qrat_mul_num' u₀ D, qrat_mul_den' u₀ D,
        qrat_mul_num' u₀ (D - S), qrat_mul_den' u₀ (D - S),
        qrat_sub_num' D S, qrat_sub_den' D S]
    simp only [qOne, Int.natCast_mul, Int.one_mul, Nat.one_mul]
    let un : Int := u₀.num
    let ud : Int := (u₀.den : Int)
    let sn : Int := S.num
    let sd : Int := (S.den : Int)
    let dn : Int := D.num
    let dd : Int := (D.den : Int)
    change
      (ud * sd - un * sn * 1) * (ud * dd * (ud * (dd * sd))) =
      ((ud * dd - un * dn * 1) * (ud * (dd * sd)) +
        un * (dn * sd - sn * dd) * (ud * dd)) * (ud * sd)
    rw [Int.mul_one, Int.mul_one]
    let K : Int := ud * dd * dd
    have h_rhs_den :
        ud * dd * (ud * (dd * sd)) = K * (ud * sd) := by
      dsimp [K]; ac_rfl
    have h_rhs_num :
        (ud * dd - un * dn) * (ud * (dd * sd)) +
          un * (dn * sd - sn * dd) * (ud * dd) =
        K * (ud * sd - un * sn) := by
      rw [Int.sub_mul, Int.mul_sub, Int.sub_mul]
      have b1 : (ud * dd) * (ud * (dd * sd)) = K * (ud * sd) := by dsimp [K]; ac_rfl
      have b2 : (un * dn) * (ud * (dd * sd)) = un * dn * sd * (ud * dd) := by ac_rfl
      have b3 : un * (dn * sd) * (ud * dd) = un * dn * sd * (ud * dd) := by ac_rfl
      have b4 : un * (sn * dd) * (ud * dd) = K * (un * sn) := by dsimp [K]; ac_rfl
      rw [b1, b2, b3, b4, Int.mul_sub]
      omega
    rw [h_rhs_num, h_rhs_den]
    ac_rfl
  rw [pAdicVal_eq_of_cross_mul hp h_decomp]
  have h_slope_diff :=
    polyDeriv_sub_slope_val_ge_min hp x y x₀ hx_int hy_int hx₀ coeffs hcoeffs
  have h_ds : valLe (some step) (pAdicVal p (D - S)) :=
    valLe_trans (valLe_valMin hx_ball hy_ball) h_slope_diff
  exact valLe_add_of_both hp h_deriv_inv (valLe_mul_right hp hu₀ h_ds)

/-- **Local Ball Contraction for `polyNewtonStep`:**
    For all `x, y` inside the `p`-adic ball `ν_p(x - x₀) ≥ step`, `ν_p(y - x₀) ≥ step`,
    `ν_p(polyNewtonStep coeffs u₀ x - polyNewtonStep coeffs u₀ y) ≥ ν_p(x - y) + step`. -/
theorem polyNewtonStep_ball_contraction {p : Nat} (hp : IsPrime p) {step : Int}
    (hstep : 1 ≤ step) (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ x y : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv :
      valLe (some step) (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (hx_ball : valLe (some step) (pAdicVal p (x - x₀)))
    (hy_ball : valLe (some step) (pAdicVal p (y - x₀))) :
    valLe (valAdd (pAdicVal p (x - y)) (some step))
          (pAdicVal p (polyNewtonStep coeffs u₀ x - polyNewtonStep coeffs u₀ y)) := by
  rw [pAdicVal_eq_of_cross_mul hp (polyNewtonStep_sub_cross_eq coeffs u₀ x y),
      pAdicVal_mul p hp (x - y) (qOne - u₀ * polySlope coeffs x y)]
  have h_fac :=
    poly_contraction_factor_val_ge hp hstep coeffs hcoeffs x₀ u₀ x y hx₀ hu₀
      h_deriv_inv hx_ball hy_ball
  cases hd : pAdicVal p (x - y) with
  | none => trivial
  | some d =>
    cases hf : pAdicVal p (qOne - u₀ * polySlope coeffs x y) with
    | none => trivial
    | some vf =>
      rw [hf] at h_fac
      simp only [valLe] at h_fac
      simp only [valAdd, valLe]
      omega

private theorem polyNewtonStep_ball_invariant {p : Nat} (hp : IsPrime p) {step m : Int}
    (hstep : 1 ≤ step) (hm : step ≤ m) (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv :
      valLe (some step) (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (h_root_init : valLe (some m) (pAdicVal p (hornerEval coeffs x₀))) :
    ∀ n : Nat,
      valLe (some step) (pAdicVal p (Nat.repeat (polyNewtonStep coeffs u₀) n x₀ - x₀))
  | 0 => by
    change valLe (some step) (pAdicVal p (x₀ - x₀))
    rw [pAdicVal_sub_self]
    trivial
  | k + 1 => by
    let f := polyNewtonStep coeffs u₀
    let xk := Nat.repeat f k x₀
    have ih := polyNewtonStep_ball_invariant hp hstep hm coeffs hcoeffs x₀ u₀
      hx₀ hu₀ h_deriv_inv h_root_init k
    have hx₀_ball : valLe (some step) (pAdicVal p (x₀ - x₀)) := by
      rw [pAdicVal_sub_self]; trivial
    have h_step1 : valLe (some step) (pAdicVal p (f xk - f x₀)) := by
      have h_cont := polyNewtonStep_ball_contraction hp hstep coeffs hcoeffs x₀ u₀ xk x₀
        hx₀ hu₀ h_deriv_inv ih hx₀_ball
      cases hd : pAdicVal p (xk - x₀) with
      | none =>
        rw [hd] at h_cont
        cases hf : pAdicVal p (f xk - f x₀) with
        | none => trivial
        | some _ =>
          rw [hf] at h_cont
          exact False.elim h_cont
      | some d =>
        rw [hd] at ih h_cont
        simp only [valLe] at ih
        cases hf : pAdicVal p (f xk - f x₀) with
        | none => trivial
        | some vf =>
          rw [hf] at h_cont
          simp only [valAdd, valLe] at h_cont ⊢
          omega
    have h_step0 : valLe (some step) (pAdicVal p (f x₀ - x₀)) := by
      dsimp [f, polyNewtonStep]
      rw [pAdicVal_eq_of_cross_mul hp
            (add_sub_cancel_left_cross_eq x₀ ((-u₀) * hornerEval coeffs x₀)),
          pAdicVal_mul p hp (-u₀) (hornerEval coeffs x₀),
          pAdicVal_neg]
      cases hu : pAdicVal p u₀ with
      | none => trivial
      | some vu =>
        cases hr : pAdicVal p (hornerEval coeffs x₀) with
        | none => trivial
        | some vr =>
          rw [hu] at hu₀
          rw [hr] at h_root_init
          simp only [valLe] at hu₀ h_root_init
          simp only [valAdd, valLe]
          omega
    have h_comb :=
      valLe_trans (valLe_valMin h_step1 h_step0)
        (ultrametric_ineq p hp (f xk - f x₀) (f x₀ - x₀))
    rwa [pAdicVal_sub_add_sub hp] at h_comb

/-- **Hensel Simple-Root Lifting Theorem for Arbitrary `QRat` Polynomials:**
    Let `P(x) = hornerEval coeffs x` have `p`-integral coefficients, `x₀` be a `p`-integral
    approximate root (`ν_p(P(x₀)) ≥ m`), and `u₀` be a `p`-integral approximate inverse of
    `P'(x₀)` (`ν_p(1 - u₀ * P'(x₀)) ≥ step`, with `1 ≤ step ≤ m`).
    Then the stationary Newton sequence `x_n = Nat.repeat (polyNewtonStep coeffs u₀) n x₀`
    satisfies for all `n, k : Nat`:
    1. `ν_p(x_{n+1} - x_n) ≥ m + n * step` (exponential step contraction),
    2. `ν_p(x_{n+k} - x_n) ≥ m + n * step` (telescoping Cauchy root stability),
    3. `ν_p(hornerEval coeffs x_n) ≥ m + n * step` (simple-root lifting). -/
theorem hensel_poly_simple_root_lift {p : Nat} (hp : IsPrime p) {step m : Int}
    (hstep : 1 ≤ step) (hm : step ≤ m) (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv :
      valLe (some step) (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (h_root_init : valLe (some m) (pAdicVal p (hornerEval coeffs x₀))) :
    let f := polyNewtonStep coeffs u₀
    (∀ n : Nat,
      valLe (some (m + Int.ofNat n * step))
            (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀))) ∧
    (∀ n k : Nat,
      valLe (some (m + Int.ofNat n * step))
            (pAdicVal p (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀))) ∧
    (∀ n : Nat,
      valLe (some (m + Int.ofNat n * step))
            (pAdicVal p (hornerEval coeffs (Nat.repeat f n x₀)))) := by
  intro f
  have h_ball := polyNewtonStep_ball_invariant hp hstep hm coeffs hcoeffs x₀ u₀
    hx₀ hu₀ h_deriv_inv h_root_init
  have h_res_lift :
      ∀ n : Nat,
        valLe (some (m + Int.ofNat n * step))
              (pAdicVal p (hornerEval coeffs (Nat.repeat f n x₀))) := by
    intro n
    induction n with
    | zero =>
      have h0 : m + Int.ofNat 0 * step = m := by
        have hz : Int.ofNat 0 * step = 0 := Int.zero_mul step
        rw [hz, Int.add_zero]
      rw [h0]
      exact h_root_init
    | succ j ih =>
      let xj := Nat.repeat f j x₀
      change valLe (some (m + Int.ofNat (j + 1) * step))
                   (pAdicVal p (hornerEval coeffs (f xj)))
      rw [pAdicVal_eq_of_cross_mul hp (polyNewtonStep_residual_cross_eq coeffs u₀ xj),
          pAdicVal_mul p hp (hornerEval coeffs xj)
            (qOne - u₀ * polySlope coeffs (f xj) xj)]
      have h_fac := poly_contraction_factor_val_ge hp hstep coeffs hcoeffs x₀ u₀ (f xj) xj
        hx₀ hu₀ h_deriv_inv (h_ball (j + 1)) (h_ball j)
      have hcast : Int.ofNat (j + 1) * step = Int.ofNat j * step + step := by
        have h1 : Int.ofNat (j + 1) = Int.ofNat j + 1 := rfl
        rw [h1, Int.add_mul, Int.one_mul]
      rw [hcast]
      cases hr : pAdicVal p (hornerEval coeffs xj) with
      | none => trivial
      | some vr =>
        cases hf : pAdicVal p (qOne - u₀ * polySlope coeffs (f xj) xj) with
        | none => trivial
        | some vf =>
          rw [hr] at ih
          rw [hf] at h_fac
          simp only [valLe] at ih h_fac
          simp only [valAdd, valLe]
          omega
  have h_step_growth :
      ∀ n : Nat,
        valLe (some (m + Int.ofNat n * step))
              (pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) := by
    intro n
    let xn := Nat.repeat f n x₀
    change valLe (some (m + Int.ofNat n * step)) (pAdicVal p (f xn - xn))
    have h_diff : CrossEq (f xn - xn) ((-u₀) * hornerEval coeffs xn) :=
      add_sub_cancel_left_cross_eq xn ((-u₀) * hornerEval coeffs xn)
    rw [pAdicVal_eq_of_cross_mul hp h_diff,
        pAdicVal_mul p hp (-u₀) (hornerEval coeffs xn),
        pAdicVal_neg]
    have h_rn := h_res_lift n
    cases hu : pAdicVal p u₀ with
    | none => trivial
    | some vu =>
      cases hr : pAdicVal p (hornerEval coeffs xn) with
      | none => trivial
      | some vr =>
        rw [hu] at hu₀
        rw [hr] at h_rn
        simp only [valLe] at hu₀ h_rn
        simp only [valAdd, valLe]
        omega
  have h_cauchy :
      ∀ n k : Nat,
        valLe (some (m + Int.ofNat n * step))
              (pAdicVal p (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀)) := by
    intro n k
    induction k with
    | zero =>
      rw [Nat.add_zero, pAdicVal_sub_self]
      trivial
    | succ j ih =>
      have h_sj := h_step_growth (n + j)
      have h_mono :
          valLe (some (m + Int.ofNat n * step))
                (some (m + Int.ofNat (n + j) * step)) := by
        have hstep0 : 0 ≤ step := Int.le_trans (by decide : (0 : Int) ≤ 1) hstep
        have h1 := ofNat_le_mul_of_nonneg (Nat.le_add_right n j) hstep0
        exact Int.add_le_add_left h1 m
      have h_sn :
          valLe (some (m + Int.ofNat n * step))
                (pAdicVal p (Nat.repeat f (n + j + 1) x₀ - Nat.repeat f (n + j) x₀)) :=
        valLe_trans h_mono h_sj
      have h_combined :=
        valLe_trans (valLe_valMin h_sn ih)
          (ultrametric_ineq p hp
            (Nat.repeat f (n + j + 1) x₀ - Nat.repeat f (n + j) x₀)
            (Nat.repeat f (n + j) x₀ - Nat.repeat f n x₀))
      rw [pAdicVal_sub_add_sub hp] at h_combined
      have h_idx : n + (j + 1) = n + j + 1 := (Nat.add_assoc n j 1).symm
      rw [h_idx]
      exact h_combined
  exact ⟨h_step_growth, h_cauchy, h_res_lift⟩

/-- **Integer Prime-Power Divisibility Corollary for Simple Polynomial Roots:**
    When `m = Int.ofNat m₀` and `step = Int.ofNat s₀`, `p ^ (m₀ + n * s₀)` divides
    `(hornerEval coeffs (Nat.repeat (polyNewtonStep coeffs u₀) n x₀)).num.natAbs`
    and all multi-step Cauchy differences for every `n, k : Nat`. -/
theorem hensel_poly_simple_root_pow_dvd {p s₀ m₀ : Nat} (hp : IsPrime p)
    (hs₀ : 1 ≤ s₀) (hm₀ : s₀ ≤ m₀) (coeffs : List QRat)
    (hcoeffs : ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ : QRat)
    (hx₀ : valLe (some 0) (pAdicVal p x₀))
    (hu₀ : valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv :
      valLe (some (Int.ofNat s₀))
            (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (h_root_init : valLe (some (Int.ofNat m₀)) (pAdicVal p (hornerEval coeffs x₀))) :
    let f := polyNewtonStep coeffs u₀
    (∀ n : Nat,
      p ^ (m₀ + n * s₀) ∣ (hornerEval coeffs (Nat.repeat f n x₀)).num.natAbs) ∧
    (∀ n k : Nat,
      p ^ (m₀ + n * s₀) ∣
        (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀).num.natAbs) := by
  intro f
  obtain ⟨_, h_cauchy, h_res⟩ :=
    hensel_poly_simple_root_lift hp
      (Int.ofNat_le.mpr hs₀) (Int.ofNat_le.mpr hm₀) coeffs hcoeffs x₀ u₀
      hx₀ hu₀ h_deriv_inv h_root_init
  have hcast : ∀ n : Nat,
      Int.ofNat (m₀ + n * s₀) = Int.ofNat m₀ + Int.ofNat n * Int.ofNat s₀ := fun _ => rfl
  refine ⟨fun n => ?_, fun n k => ?_⟩
  · apply valLe_nat_implies_pow_dvd_num hp
    rw [hcast n]
    exact h_res n
  · apply valLe_nat_implies_pow_dvd_num hp
    rw [hcast n]
    exact h_cauchy n k

/-! #### Concrete `by decide` Polynomial Root-Lifting Certificate: `√2 mod 7^(n+1)` -/

/-- **Concrete `7`-Adic Simple-Root Lifting Certificate (`P(x) = x^2 - 2`, `by decide`):**
    Starting at `x₀ = 3` (`P(3) = 7 ≡ 0 (mod 7)`) with derivative inverse `u₀ = 6`
    (`P'(3) = 6`, `1 - 6 * 6 = -35 ≡ 0 (mod 7)`), lifts the `7`-adic square root of `2`
    so that `7^(n + 1)` divides `(hornerEval [-2, 0, 1] x_n).num.natAbs` and all
    multi-step Cauchy differences `(x_{n+k} - x_n).num.natAbs` for every `n, k : Nat`. -/
theorem hensel_sqrt2_mod_pow_7 :
    let P := [qOfInt (-2), qZero, qOne]
    let f := polyNewtonStep P (qOfInt 6)
    (∀ n : Nat,
      7 ^ (1 + n * 1) ∣ (hornerEval P (Nat.repeat f n (qOfInt 3))).num.natAbs) ∧
    (∀ n k : Nat,
      7 ^ (1 + n * 1) ∣
        (Nat.repeat f (n + k) (qOfInt 3) - Nat.repeat f n (qOfInt 3)).num.natAbs) := by
  apply hensel_poly_simple_root_pow_dvd prime_mersenne_7 (by decide) (by decide)
    [qOfInt (-2), qZero, qOne]
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | hnil
    · decide
    · decide
    · decide
    · cases hnil
  · decide
  · decide
  · decide
  · decide

/-! ### Part 10: Prime Tower CRT Simple-Root Lifting over `List Nat` -/

private theorem allPrimes_mem :
    ∀ (ps : List Nat), AllPrimes ps → ∀ p ∈ ps, IsPrime p
  | [], _, _, hmem => by cases hmem
  | p :: ps, hp, q, hmem => by
    simp only [AllPrimes] at hp
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact hp.1
    · exact allPrimes_mem ps hp.2 q hrest

private theorem mem_map_pair_elim {k : Nat} :
    ∀ {ps : List Nat} {entry : Nat × Nat},
      entry ∈ ps.map (fun p => (p, k)) → entry.1 ∈ ps ∧ entry.2 = k
  | [], _, h => by cases h
  | p :: ps, entry, h => by
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with rfl | hrest
    · exact ⟨List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨h1, h2⟩ := mem_map_pair_elim hrest
      exact ⟨List.mem_cons.mpr (Or.inr h1), h2⟩

/-- Lift per-prime divisibility `∀ p ∈ ps, p ^ k ∣ N` across a pairwise-distinct
    prime list `ps : List Nat` to `primeTowerModulus ps k ∣ N`. -/
theorem prime_tower_list_pow_dvd_of_all (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (k N : Nat)
    (h_all : ∀ p ∈ ps, p ^ k ∣ N) :
    primeTowerModulus ps k ∣ N := by
  unfold primeTowerModulus
  have h_primes' : AllPrimes ((ps.map (fun p => (p, k))).map Prod.fst) := by
    rwa [map_fst_map_pair]
  have h_dist' : PairwiseDistinct ((ps.map (fun p => (p, k))).map Prod.fst) := by
    rwa [map_fst_map_pair]
  apply prime_tower_pow_dvd_of_all (ps.map (fun p => (p, k))) h_primes' h_dist' N
  intro entry he
  obtain ⟨hp_mem, hk_eq⟩ := mem_map_pair_elim he
  rw [hk_eq]
  exact h_all entry.1 hp_mem

/-- Prime Tower CRT simple-root lifting certificate for `P(x) = hornerEval coeffs x`
    under stationary Newton iteration `f = polyNewtonStep coeffs u₀`. -/
structure PrimeTowerPolyRootCert (ps : List Nat) (s₀ m₀ : Nat)
    (coeffs : List QRat) (x₀ u₀ : QRat) : Prop where
  primes : AllPrimes ps
  distinct : PairwiseDistinct ps
  step_pos : 1 ≤ s₀
  init_ge_step : s₀ ≤ m₀
  root_tower_dvd :
    ∀ n : Nat,
      primeTowerModulus ps (m₀ + n * s₀) ∣
        (hornerEval coeffs (Nat.repeat (polyNewtonStep coeffs u₀) n x₀)).num.natAbs
  cauchy_tower_dvd :
    ∀ n k : Nat,
      primeTowerModulus ps (m₀ + n * s₀) ∣
        (Nat.repeat (polyNewtonStep coeffs u₀) (n + k) x₀ -
         Nat.repeat (polyNewtonStep coeffs u₀) n x₀).num.natAbs
  step_tower_dvd :
    ∀ n : Nat,
      primeTowerModulus ps (m₀ + n * s₀) ∣
        (Nat.repeat (polyNewtonStep coeffs u₀) (n + 1) x₀ -
         Nat.repeat (polyNewtonStep coeffs u₀) n x₀).num.natAbs

/-- **Prime Tower CRT Simple-Root Lifting Theorem:**
    Combines `hensel_poly_simple_root_pow_dvd` across every prime `p ∈ ps`. -/
theorem hensel_poly_prime_tower_crt (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (s₀ m₀ : Nat) (hs₀ : 1 ≤ s₀) (hm₀ : s₀ ≤ m₀)
    (coeffs : List QRat)
    (hcoeffs : ∀ p ∈ ps, ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (x₀ u₀ : QRat)
    (hx₀ : ∀ p ∈ ps, valLe (some 0) (pAdicVal p x₀))
    (hu₀ : ∀ p ∈ ps, valLe (some 0) (pAdicVal p u₀))
    (h_deriv_inv : ∀ p ∈ ps,
      valLe (some (Int.ofNat s₀))
            (pAdicVal p (qOne - u₀ * hornerEval (polyDerivCoeffs coeffs) x₀)))
    (h_root_init : ∀ p ∈ ps,
      valLe (some (Int.ofNat m₀)) (pAdicVal p (hornerEval coeffs x₀))) :
    PrimeTowerPolyRootCert ps s₀ m₀ coeffs x₀ u₀ := by
  have h_per_prime :
      ∀ p ∈ ps,
        (∀ n : Nat,
          p ^ (m₀ + n * s₀) ∣
            (hornerEval coeffs (Nat.repeat (polyNewtonStep coeffs u₀) n x₀)).num.natAbs) ∧
        (∀ n k : Nat,
          p ^ (m₀ + n * s₀) ∣
            (Nat.repeat (polyNewtonStep coeffs u₀) (n + k) x₀ -
             Nat.repeat (polyNewtonStep coeffs u₀) n x₀).num.natAbs) := by
    intro p hp
    exact hensel_poly_simple_root_pow_dvd
      (allPrimes_mem ps h_primes p hp) hs₀ hm₀ coeffs (hcoeffs p hp)
      x₀ u₀ (hx₀ p hp) (hu₀ p hp) (h_deriv_inv p hp) (h_root_init p hp)
  have h_cauchy :
      ∀ n k : Nat,
        primeTowerModulus ps (m₀ + n * s₀) ∣
          (Nat.repeat (polyNewtonStep coeffs u₀) (n + k) x₀ -
           Nat.repeat (polyNewtonStep coeffs u₀) n x₀).num.natAbs := by
    intro n k
    apply prime_tower_list_pow_dvd_of_all ps h_primes h_dist (m₀ + n * s₀)
    intro p hp
    exact (h_per_prime p hp).2 n k
  refine
    { primes := h_primes
      distinct := h_dist
      step_pos := hs₀
      init_ge_step := hm₀
      root_tower_dvd := ?_
      cauchy_tower_dvd := h_cauchy
      step_tower_dvd := fun n => h_cauchy n 1 }
  intro n
  apply prime_tower_list_pow_dvd_of_all ps h_primes h_dist (m₀ + n * s₀)
  intro p hp
  exact (h_per_prime p hp).1 n

/-! #### Constructive CRT Seed Fusion for Multi-Prime Simple-Root Lifting -/

private theorem add_sub_right_cross_eq (s t r : QRat) :
    CrossEq ((s + t) - r) ((s - r) + t) := by
  unfold CrossEq
  rw [qrat_sub_num' (s + t) r, qrat_sub_den' (s + t) r,
      qrat_add_num s t, qrat_add_den s t,
      qrat_add_num (s - r) t, qrat_add_den (s - r) t,
      qrat_sub_num' s r, qrat_sub_den' s r,
      Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  simp only [Int.natCast_mul]
  have hN :
      ((s.num * (t.den : Int) + t.num * (s.den : Int)) * (r.den : Int) -
        r.num * ((s.den : Int) * (t.den : Int))) =
      ((s.num * (r.den : Int) - r.num * (s.den : Int)) * (t.den : Int) +
        t.num * ((s.den : Int) * (r.den : Int))) := by
    rw [Int.add_mul, Int.sub_mul]
    have a1 : s.num * (t.den : Int) * (r.den : Int) =
        s.num * (r.den : Int) * (t.den : Int) := by ac_rfl
    have a2 : t.num * (s.den : Int) * (r.den : Int) =
        t.num * ((s.den : Int) * (r.den : Int)) := by ac_rfl
    have a3 : r.num * ((s.den : Int) * (t.den : Int)) =
        r.num * (s.den : Int) * (t.den : Int) := by ac_rfl
    rw [a1, a2, a3]
    omega
  have hD :
      (s.den : Int) * (r.den : Int) * (t.den : Int) =
      (s.den : Int) * (t.den : Int) * (r.den : Int) := by ac_rfl
  rw [hN, hD]

private theorem add_mul_sub_self_cross_eq (s e r : QRat) :
    CrossEq ((s + e * r) - r) (s + (-(qOne - e)) * r) := by
  unfold CrossEq
  rw [qrat_sub_num' (s + e * r) r, qrat_sub_den' (s + e * r) r,
      qrat_add_num s (e * r), qrat_add_den s (e * r),
      qrat_mul_num' e r, qrat_mul_den' e r,
      qrat_add_num s ((-(qOne - e)) * r), qrat_add_den s ((-(qOne - e)) * r),
      qrat_mul_num' (-(qOne - e)) r, qrat_mul_den' (-(qOne - e)) r]
  have hneg_num : (-(qOne - e)).num = -(qOne - e).num := rfl
  have hneg_den : (-(qOne - e)).den = (qOne - e).den := rfl
  rw [hneg_num, hneg_den, qrat_sub_num' qOne e, qrat_sub_den' qOne e]
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  simp only [qOne, Int.natCast_mul, h1, Int.one_mul, Int.mul_one]
  have hneg : -((e.den : Int) - e.num) = e.num - (e.den : Int) := by omega
  rw [hneg]
  have hN :
      (s.num * ((e.den : Int) * (r.den : Int)) + e.num * r.num * (s.den : Int)) *
        (r.den : Int) - r.num * ((s.den : Int) * ((e.den : Int) * (r.den : Int))) =
      (r.den : Int) *
        (s.num * ((e.den : Int) * (r.den : Int)) +
          (e.num - (e.den : Int)) * r.num * (s.den : Int)) := by
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
    have t1 : s.num * ((e.den : Int) * (r.den : Int)) * (r.den : Int) =
        (r.den : Int) * (s.num * ((e.den : Int) * (r.den : Int))) := by ac_rfl
    have t2 : e.num * r.num * (s.den : Int) * (r.den : Int) =
        (r.den : Int) * (e.num * r.num * (s.den : Int)) := by ac_rfl
    have t3 : r.num * ((s.den : Int) * ((e.den : Int) * (r.den : Int))) =
        (r.den : Int) * ((e.den : Int) * r.num * (s.den : Int)) := by ac_rfl
    rw [t1, t2, t3]
    omega
  rw [hN]
  ac_rfl

private theorem valLe_foldl_not_mem {q : Nat} (hq : IsPrime q) {k : Int}
    (e r : Nat → QRat) :
    ∀ (qs : List Nat) (s : QRat),
      notInList q qs = true →
      valLe (some k) (pAdicVal q s) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (r p))) →
      valLe (some k) (pAdicVal q (qs.foldl (fun acc p => acc + e p * r p) s))
  | [], s, _, hs, _, _ => hs
  | p :: qs, s, hnot, hs, he, hr => by
    simp only [notInList, Bool.and_eq_true, nat_bne_true_iff] at hnot
    simp only [List.foldl_cons]
    have hpq : p ≠ q := Ne.symm hnot.1
    have hep : valLe (some k) (pAdicVal q (e p)) :=
      he p (List.mem_cons.mpr (Or.inl rfl)) hpq
    have hrp : valLe (some 0) (pAdicVal q (r p)) :=
      hr p (List.mem_cons.mpr (Or.inl rfl))
    have hstep : valLe (some k) (pAdicVal q (s + e p * r p)) :=
      valLe_add_of_both hq hs (valLe_mul_left hq hep hrp)
    exact valLe_foldl_not_mem hq e r qs (s + e p * r p) hnot.2 hstep
      (fun x hx hneq => he x (List.mem_cons.mpr (Or.inr hx)) hneq)
      (fun x hx => hr x (List.mem_cons.mpr (Or.inr hx)))

private theorem valLe_foldl_sub_after_prime {q : Nat} (hq : IsPrime q) {k : Int}
    (e r : Nat → QRat) (target : QRat) :
    ∀ (qs : List Nat) (s : QRat),
      notInList q qs = true →
      valLe (some k) (pAdicVal q (s - target)) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (r p))) →
      valLe (some k) (pAdicVal q (qs.foldl (fun acc p => acc + e p * r p) s - target))
  | [], s, _, hs, _, _ => hs
  | p :: qs, s, hnot, hs, he, hr => by
    simp only [notInList, Bool.and_eq_true, nat_bne_true_iff] at hnot
    simp only [List.foldl_cons]
    have hpq : p ≠ q := Ne.symm hnot.1
    have hep : valLe (some k) (pAdicVal q (e p)) :=
      he p (List.mem_cons.mpr (Or.inl rfl)) hpq
    have hrp : valLe (some 0) (pAdicVal q (r p)) :=
      hr p (List.mem_cons.mpr (Or.inl rfl))
    have hstep : valLe (some k) (pAdicVal q ((s + e p * r p) - target)) := by
      rw [pAdicVal_eq_of_cross_mul hq (add_sub_right_cross_eq s (e p * r p) target)]
      exact valLe_add_of_both hq hs (valLe_mul_left hq hep hrp)
    exact valLe_foldl_sub_after_prime hq e r target qs (s + e p * r p) hnot.2 hstep
      (fun x hx hneq => he x (List.mem_cons.mpr (Or.inr hx)) hneq)
      (fun x hx => hr x (List.mem_cons.mpr (Or.inr hx)))

private theorem valLe_foldl_sub_mem {q : Nat} (hq : IsPrime q) {k : Int}
    (e r : Nat → QRat)
    (he_self : valLe (some k) (pAdicVal q (qOne - e q)))
    (hr_self : valLe (some 0) (pAdicVal q (r q))) :
    ∀ (qs : List Nat) (s : QRat),
      PairwiseDistinct qs →
      q ∈ qs →
      valLe (some k) (pAdicVal q s) →
      (∀ p ∈ qs, p ≠ q → valLe (some k) (pAdicVal q (e p))) →
      (∀ p ∈ qs, valLe (some 0) (pAdicVal q (r p))) →
      valLe (some k) (pAdicVal q (qs.foldl (fun acc p => acc + e p * r p) s - r q))
  | [], _, _, hmem, _, _, _ => by cases hmem
  | p :: qs, s, hdist, hmem, hs, he, hr => by
    simp only [PairwiseDistinct] at hdist
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have h_at_q : valLe (some k) (pAdicVal q ((s + e q * r q) - r q)) := by
        rw [pAdicVal_eq_of_cross_mul hq (add_mul_sub_self_cross_eq s (e q) (r q))]
        have hneg_e : valLe (some k) (pAdicVal q (-(qOne - e q))) := by
          rw [pAdicVal_neg]; exact he_self
        exact valLe_add_of_both hq hs (valLe_mul_left hq hneg_e hr_self)
      exact valLe_foldl_sub_after_prime hq e r (r q) qs (s + e q * r q)
        hdist.1 h_at_q
        (fun x hx hneq => he x (List.mem_cons.mpr (Or.inr hx)) hneq)
        (fun x hx => hr x (List.mem_cons.mpr (Or.inr hx)))
    · have hpq : p ≠ q := by
        intro heq
        subst heq
        exact (notInList_eq_true_iff p qs).mp hdist.1 p hrest rfl
      have hqp : q ≠ p := Ne.symm hpq
      have hnot_single : notInList q [p] = true := by
        simp [notInList, hqp]
      have hs' : valLe (some k) (pAdicVal q (s + e p * r p)) :=
        valLe_foldl_not_mem hq e r [p] s hnot_single hs
          (fun x hx hneq => by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hnil
            · exact he x (List.mem_cons.mpr (Or.inl rfl)) hneq
            · cases hnil)
          (fun x hx => by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hnil
            · exact hr x (List.mem_cons.mpr (Or.inl rfl))
            · cases hnil)
      exact valLe_foldl_sub_mem hq e r he_self hr_self qs
        (s + e p * r p) hdist.2 hrest hs'
        (fun x hx hneq => he x (List.mem_cons.mpr (Or.inr hx)) hneq)
        (fun x hx => hr x (List.mem_cons.mpr (Or.inr hx)))

/-- **Per-Prime Congruence of `buildCrtSeed` to Local Witness `r q`:**
    For every prime `q ∈ ps`, `ν_q(buildCrtSeed ps e r - r q) ≥ k`. -/
theorem buildCrtSeed_approx_at {q : Nat} (hq : IsPrime q) {k : Int}
    (ps : List Nat) (h_dist : PairwiseDistinct ps) (hq_mem : q ∈ ps)
    (e r : Nat → QRat)
    (he_self : valLe (some k) (pAdicVal q (qOne - e q)))
    (he_other : ∀ p ∈ ps, p ≠ q → valLe (some k) (pAdicVal q (e p)))
    (hr_int : ∀ p ∈ ps, valLe (some 0) (pAdicVal q (r p))) :
    valLe (some k) (pAdicVal q (buildCrtSeed ps e r - r q)) := by
  unfold buildCrtSeed
  have hzero : valLe (some k) (pAdicVal q qZero) := by
    simp [pAdicVal, qZero, valLe]
  exact valLe_foldl_sub_mem hq e r he_self (hr_int q hq_mem)
    ps qZero h_dist hq_mem hzero he_other hr_int

private theorem valLe_zero_qOfNat {p : Nat} (hp : IsPrime p) (n : Nat) :
    valLe (some 0) (pAdicVal p (qOfNat n)) := by
  by_cases hn : n = 0
  · subst hn
    have hnum0 : (qOfNat 0).num = 0 := rfl
    simp only [pAdicVal, hnum0, ↓reduceIte]
    trivial
  · have hnum_ne : (qOfNat n).num ≠ 0 := Int.ofNat_ne_zero.mpr hn
    have hd : (qOfNat n).den = 1 := rfl
    have hp2 : 2 ≤ p := hp.1
    have h1 : padicValNat p 1 = 0 :=
      padicValNat_of_not_dvd hp2 (Nat.zero_lt_succ 0) (fun hd => by
        have := Nat.le_of_dvd (Nat.zero_lt_succ 0) hd
        omega)
    simp only [pAdicVal, hnum_ne, ↓reduceIte, hd, h1, valLe]
    omega

private theorem polyDerivCoeffsAux_integrality {p : Nat} (hp : IsPrime p) :
    ∀ (idx : Nat) (cs : List QRat),
      (∀ c ∈ cs, valLe (some 0) (pAdicVal p c)) →
      ∀ c ∈ polyDerivCoeffsAux idx cs, valLe (some 0) (pAdicVal p c)
  | _, [], _, _, hmem => by cases hmem
  | idx, c :: cs, hall, d, hmem => by
    simp only [polyDerivCoeffsAux, List.mem_cons] at hmem
    rcases hmem with rfl | hrest
    · exact valLe_zero_mul hp (valLe_zero_qOfNat hp idx)
        (hall c (List.mem_cons.mpr (Or.inl rfl)))
    · exact polyDerivCoeffsAux_integrality hp (idx + 1) cs
        (fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))) d hrest

theorem polyDerivCoeffs_integrality {p : Nat} (hp : IsPrime p) :
    ∀ (coeffs : List QRat),
      (∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c)) →
      ∀ c ∈ polyDerivCoeffs coeffs, valLe (some 0) (pAdicVal p c)
  | [], _, _, hmem => by cases hmem
  | _ :: cs, hall, d, hmem =>
    polyDerivCoeffsAux_integrality hp 1 cs
      (fun c' hc' => hall c' (List.mem_cons.mpr (Or.inr hc'))) d hmem

private theorem pAdicVal_one_sub_mul_comm {p : Nat} (_hp : IsPrime p) (x y : QRat) :
    pAdicVal p (qOne - x * y) = pAdicVal p (qOne - y * x) := by
  apply pAdicVal_eq_of_num_den_eq
  · rw [qrat_sub_num' qOne (x * y), qrat_sub_num' qOne (y * x),
        qrat_mul_num' x y, qrat_mul_den' x y,
        qrat_mul_num' y x, qrat_mul_den' y x]
    have h1 : ((1 : Nat) : Int) = 1 := rfl
    simp only [qOne, Int.natCast_mul, h1, Int.one_mul, Int.mul_one]
    have ha : (y.den : Int) * (x.den : Int) = (x.den : Int) * (y.den : Int) := by ac_rfl
    have hb : y.num * x.num = x.num * y.num := by ac_rfl
    rw [ha, hb]
  · rw [qrat_sub_den' qOne (x * y), qrat_sub_den' qOne (y * x),
        qrat_mul_den' x y, qrat_mul_den' y x]
    simp only [qOne, Nat.one_mul]
    exact Nat.mul_comm x.den y.den

private theorem one_sub_mul_perturbation_cross_eq (u₀ D S : QRat) :
    CrossEq (qOne - u₀ * S) ((qOne - u₀ * D) + u₀ * (D - S)) := by
  unfold CrossEq
  rw [qrat_sub_num' qOne (u₀ * S), qrat_sub_den' qOne (u₀ * S),
      qrat_mul_num' u₀ S, qrat_mul_den' u₀ S,
      qrat_add_num (qOne - u₀ * D) (u₀ * (D - S)),
      qrat_add_den (qOne - u₀ * D) (u₀ * (D - S)),
      qrat_sub_num' qOne (u₀ * D), qrat_sub_den' qOne (u₀ * D),
      qrat_mul_num' u₀ D, qrat_mul_den' u₀ D,
      qrat_mul_num' u₀ (D - S), qrat_mul_den' u₀ (D - S),
      qrat_sub_num' D S, qrat_sub_den' D S]
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  simp only [qOne, Int.natCast_mul, h1, Int.one_mul, Int.mul_one]
  have hN :
      (u₀.den * D.den - u₀.num * D.num : Int) * (u₀.den * (D.den * S.den)) +
        u₀.num * (D.num * S.den - S.num * D.den) * (u₀.den * D.den) =
      ((u₀.den : Int) * D.den * D.den) * ((u₀.den : Int) * S.den - u₀.num * S.num) := by
    simp only [Int.sub_mul, Int.mul_sub]
    have m1 : (u₀.den : Int) * D.den * ((u₀.den : Int) * (D.den * S.den)) =
        (u₀.den : Int) * D.den * D.den * ((u₀.den : Int) * S.den) := by ac_rfl
    have m2 : u₀.num * D.num * ((u₀.den : Int) * (D.den * S.den)) =
        u₀.num * (D.num * (S.den : Int)) * ((u₀.den : Int) * D.den) := by ac_rfl
    have m3 : u₀.num * (S.num * (D.den : Int)) * ((u₀.den : Int) * D.den) =
        (u₀.den : Int) * D.den * D.den * (u₀.num * S.num) := by ac_rfl
    rw [m1, m2, m3]
    omega
  rw [hN]
  ac_rfl

private theorem self_eq_add_sub_cross_eq (a b : QRat) :
    CrossEq a (b + (a - b)) := by
  unfold CrossEq
  rw [qrat_add_num b (a - b), qrat_add_den b (a - b),
      qrat_sub_num' a b, qrat_sub_den' a b,
      Int.natCast_mul, Int.natCast_mul]
  have h_num :
      b.num * ((a.den : Int) * (b.den : Int)) +
        (a.num * (b.den : Int) - b.num * (a.den : Int)) * (b.den : Int) =
      (a.num * (b.den : Int)) * (b.den : Int) := by
    rw [Int.sub_mul]
    have t1 : b.num * ((a.den : Int) * (b.den : Int)) =
        (b.num * (a.den : Int)) * (b.den : Int) := by ac_rfl
    rw [t1]
    omega
  rw [h_num]
  ac_rfl

/-- **Constructive Multi-Prime Polynomial CRT Seed & Root-Lifting Builder.** -/
theorem hensel_poly_build_prime_tower_crt (ps : List Nat)
    (h_primes : AllPrimes ps) (h_dist : PairwiseDistinct ps)
    (s₀ m₀ : Nat) (hs₀ : 1 ≤ s₀) (hm₀ : s₀ ≤ m₀)
    (coeffs : List QRat)
    (hcoeffs : ∀ p ∈ ps, ∀ c ∈ coeffs, valLe (some 0) (pAdicVal p c))
    (r u w : Nat → QRat)
    (hr_all : ∀ p ∈ ps, ∀ q ∈ ps, valLe (some 0) (pAdicVal q (r p)))
    (hu_all : ∀ p ∈ ps, ∀ q ∈ ps, valLe (some 0) (pAdicVal q (u p)))
    (h_root_local : ∀ q ∈ ps,
      valLe (some (Int.ofNat m₀)) (pAdicVal q (hornerEval coeffs (r q))))
    (h_deriv_local : ∀ q ∈ ps,
      valLe (some (Int.ofNat s₀))
            (pAdicVal q (qOne - u q * hornerEval (polyDerivCoeffs coeffs) (r q))))
    (h_cof_certs : ∀ p ∈ ps,
      HenselInverseCert p (Int.ofNat m₀)
        (qOfInt (Int.ofNat (crtCofactor ps p m₀))) (w p))
    (hw_other : ∀ p ∈ ps, ∀ q ∈ ps, q ≠ p → valLe (some 0) (pAdicVal q (w p))) :
    let e : Nat → QRat := fun p => crtIdempotent ps p m₀ 0 (w p)
    PrimeTowerPolyRootCert ps s₀ m₀ coeffs
      (buildCrtSeed ps e r)
      (buildCrtSeed ps e u) := by
  intro e
  have hsm : Int.ofNat s₀ ≤ Int.ofNat m₀ := Int.ofNat_le.mpr hm₀
  have hm₀_eq : 2 ^ 0 * m₀ = m₀ := Nat.one_mul m₀
  have h_cof_certs' : ∀ p ∈ ps,
      HenselInverseCert p (Int.ofNat m₀)
        (qOfInt (Int.ofNat (crtCofactor ps p (2 ^ 0 * m₀)))) (w p) := by
    intro p hp
    rw [hm₀_eq]
    exact h_cof_certs p hp
  have he_all : ∀ q ∈ ps, ∀ p ∈ ps, valLe (some 0) (pAdicVal q (e p)) := by
    intro q hq_mem p hp_mem
    exact crtIdempotent_integrality_all h_primes (h_cof_certs' p hp_mem)
      (allPrimes_mem ps h_primes q hq_mem) hq_mem
      (fun hne => hw_other p hp_mem q hq_mem hne)
  have hx₀_all : ∀ q ∈ ps, valLe (some 0) (pAdicVal q (buildCrtSeed ps e r)) :=
    fun q hq => buildCrtSeed_integrality (allPrimes_mem ps h_primes q hq) ps e r
      (he_all q hq) (fun p hp => hr_all p hp q hq)
  have hu₀_all : ∀ q ∈ ps, valLe (some 0) (pAdicVal q (buildCrtSeed ps e u)) :=
    fun q hq => buildCrtSeed_integrality (allPrimes_mem ps h_primes q hq) ps e u
      (he_all q hq) (fun p hp => hu_all p hp q hq)
  have he_self : ∀ q ∈ ps, valLe (some (Int.ofNat m₀)) (pAdicVal q (qOne - e q)) := by
    intro q hq
    have h := crtIdempotent_self_residual (h_cof_certs' q hq)
    rwa [hm₀_eq] at h
  have he_other :
      ∀ q ∈ ps, ∀ p ∈ ps, p ≠ q → valLe (some (Int.ofNat m₀)) (pAdicVal q (e p)) := by
    intro q hq p hp hne
    have h := crtIdempotent_other_val (m := m₀) (n := 0) h_primes (allPrimes_mem ps h_primes q hq) hq
      (Ne.symm hne) (hw_other p hp q hq (Ne.symm hne))
    rwa [hm₀_eq] at h
  have hx₀_approx :
      ∀ q ∈ ps, valLe (some (Int.ofNat m₀)) (pAdicVal q (buildCrtSeed ps e r - r q)) :=
    fun q hq => buildCrtSeed_approx_at (allPrimes_mem ps h_primes q hq) ps h_dist hq
      e r (he_self q hq) (he_other q hq) (fun p hp => hr_all p hp q hq)
  apply hensel_poly_prime_tower_crt ps h_primes h_dist s₀ m₀ hs₀ hm₀ coeffs hcoeffs
    (buildCrtSeed ps e r) (buildCrtSeed ps e u) hx₀_all hu₀_all
  · intro q hq
    have hq_prime := allPrimes_mem ps h_primes q hq
    let D_rq := hornerEval (polyDerivCoeffs coeffs) (r q)
    let D_x0 := hornerEval (polyDerivCoeffs coeffs) (buildCrtSeed ps e r)
    have h_dcoeffs := polyDerivCoeffs_integrality hq_prime coeffs (hcoeffs q hq)
    have hD_rq_int : valLe (some 0) (pAdicVal q D_rq) :=
      hornerEval_integrality hq_prime (r q) (hr_all q hq q hq)
        (polyDerivCoeffs coeffs) h_dcoeffs
    have h_u0_Drq : valLe (some (Int.ofNat s₀)) (pAdicVal q (qOne - buildCrtSeed ps e u * D_rq)) := by
      have he_self_s₀ : valLe (some (Int.ofNat s₀)) (pAdicVal q (qOne - e q)) := by
        have hs := he_self q hq
        cases h : pAdicVal q (qOne - e q) with
        | none => trivial
        | some v =>
          rw [h] at hs
          simp only [valLe] at hs ⊢
          omega
      have he_other_s₀ :
          ∀ p ∈ ps, p ≠ q → valLe (some (Int.ofNat s₀)) (pAdicVal q (e p)) := by
        intro p hp hne
        have hs := he_other q hq p hp hne
        cases h : pAdicVal q (e p) with
        | none => trivial
        | some v =>
          rw [h] at hs
          simp only [valLe] at hs ⊢
          omega
      have hu_res_comm : valLe (some (Int.ofNat s₀)) (pAdicVal q (qOne - D_rq * u q)) := by
        rw [pAdicVal_one_sub_mul_comm hq_prime]
        exact h_deriv_local q hq
      rw [pAdicVal_one_sub_mul_comm hq_prime]
      exact buildCrtSeed_residual_at hq_prime ps h_dist hq D_rq hD_rq_int e u
        he_self_s₀ (he_all q hq q hq) he_other_s₀
        (fun p hp => hu_all p hp q hq) hu_res_comm
    have h_D_diff : valLe (some (Int.ofNat s₀)) (pAdicVal q (D_rq - D_x0)) := by
      have h_sub := hornerEval_sub_val_ge_of_integral hq_prime (r q) (buildCrtSeed ps e r)
        (hr_all q hq q hq) (hx₀_all q hq) (polyDerivCoeffs coeffs) h_dcoeffs
      have h_ap := hx₀_approx q hq
      rw [pAdicVal_sub_comm] at h_ap
      have h_s0_le_m0 : valLe (some (Int.ofNat s₀)) (pAdicVal q (r q - buildCrtSeed ps e r)) := by
        cases h : pAdicVal q (r q - buildCrtSeed ps e r) with
        | none => trivial
        | some v =>
          rw [h] at h_ap
          simp only [valLe] at h_ap ⊢
          omega
      exact valLe_trans h_s0_le_m0 h_sub
    rw [pAdicVal_eq_of_cross_mul hq_prime
          (one_sub_mul_perturbation_cross_eq (buildCrtSeed ps e u) D_rq D_x0)]
    exact valLe_add_of_both hq_prime h_u0_Drq
      (valLe_mul_right hq_prime (hu₀_all q hq) h_D_diff)
  · intro q hq
    have hq_prime := allPrimes_mem ps h_primes q hq
    let P_rq := hornerEval coeffs (r q)
    let P_x0 := hornerEval coeffs (buildCrtSeed ps e r)
    rw [pAdicVal_eq_of_cross_mul hq_prime (self_eq_add_sub_cross_eq P_x0 P_rq)]
    have h_diff : valLe (some (Int.ofNat m₀)) (pAdicVal q (P_x0 - P_rq)) := by
      rw [pAdicVal_eq_of_cross_mul hq_prime
            (hornerEval_sub_cross_eq_slope coeffs (buildCrtSeed ps e r) (r q))]
      have h_slope_int := polySlope_integrality hq_prime (buildCrtSeed ps e r) (r q)
        (hx₀_all q hq) (hr_all q hq q hq) coeffs (hcoeffs q hq)
      exact valLe_mul_left hq_prime (hx₀_approx q hq) h_slope_int
    exact valLe_add_of_both hq_prime (h_root_local q hq) h_diff

/-! #### Concrete 3-Prime Mersenne Tower Root Lifting: `√2 mod 27559^(n+1)` -/

theorem hensel_mersenne_tower_sqrt2_lift :
    PrimeTowerPolyRootCert mersenneTower 1 1
      [qOfInt (-2), qZero, qOne]
      (qOfInt 25924) (qOfInt 6481) := by
  apply hensel_poly_prime_tower_crt mersenneTower (by decide) (by decide) 1 1
    (by decide) (by decide) [qOfInt (-2), qZero, qOne]
  · intro p hp c hc
    simp only [mersenneTower, List.mem_cons] at hp hc
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hc with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil <;> first | decide | cases hnil
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil <;> first | decide | cases hnil
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil <;> first | decide | cases hnil
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil <;> first | decide | cases hnil

def mersenneSqrt2RootSeed : Nat → QRat
  | 7 => qOfInt 3
  | 31 => qOfInt 8
  | 127 => qOfInt 16
  | _ => qZero

def mersenneSqrt2DerivInvSeed : Nat → QRat
  | 7 => qOfInt 6
  | 31 => qOfInt 2
  | 127 => qOfInt 4
  | _ => qOne

theorem hensel_mersenne_tower_sqrt2_built :
    let e : Nat → QRat := fun p => crtIdempotent mersenneTower p 1 0 (mersenneCofactorInv p)
    PrimeTowerPolyRootCert mersenneTower 1 1
      [qOfInt (-2), qZero, qOne]
      (buildCrtSeed mersenneTower e mersenneSqrt2RootSeed)
      (buildCrtSeed mersenneTower e mersenneSqrt2DerivInvSeed) := by
  refine hensel_poly_build_prime_tower_crt mersenneTower (by decide) (by decide) 1 1
    (by decide) (by decide) [qOfInt (-2), qZero, qOne] ?_
    mersenneSqrt2RootSeed mersenneSqrt2DerivInvSeed mersenneCofactorInv
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc
    simp only [mersenneTower, List.mem_cons] at hp hc
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hc with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'
  · intro p hp q hq
    simp only [mersenneTower, List.mem_cons] at hp hq
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hq with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'
  · intro p hp q hq
    simp only [mersenneTower, List.mem_cons] at hp hq
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hq with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'
  · intro q hq
    simp only [mersenneTower, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hnil <;> first | decide | cases hnil
  · intro q hq
    simp only [mersenneTower, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hnil <;> first | decide | cases hnil
  · intro p hp
    simp only [mersenneTower, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | hnil
    · exact mkHenselInverseCert prime_mersenne_7 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_31 (by decide) (by decide) (by decide) (by decide)
    · exact mkHenselInverseCert prime_mersenne_127 (by decide) (by decide) (by decide) (by decide)
    · cases hnil
  · intro p hp q hq hne
    simp only [mersenneTower, List.mem_cons] at hp hq
    rcases hp with rfl | rfl | rfl | hnil <;>
    rcases hq with rfl | rfl | rfl | hnil' <;>
    first | decide | cases hnil | cases hnil'

end QuasiRiemann.Valuation

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/Hensel.lean
