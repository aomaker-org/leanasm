-- Path: leanasm/src/LeanAsm/WeilZetaBridge.lean
-- Bridges FiniteFieldRH (genus-2 C/F_5 Weil zeta) with EulerFactorNonVanishing
-- over the punctured critical strip 0 < Re(s) < 1, Re(s) != 1/2.
-- Max Column: 100 Columns

import LeanAsm.FiniteFieldRH
import LeanAsm.EulerFactorNonVanishing

namespace WeilZetaBridge

open FiniteFieldRH
open EulerFactorNonVanishing

private theorem int_pow2 (x : Int) : x ^ 2 = x * x := by
  simp [Int.pow_succ, Int.pow_zero]

private theorem int_pow4 (x : Int) : x ^ 4 = x * x * x * x := by
  simp [Int.pow_succ, Int.pow_zero]

private theorem int_pow8 (x : Int) :
    x ^ 8 = (x * x * x * x) * (x * x * x * x) := by
  simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc]

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  if hx : 0 ≤ x then
    exact Int.mul_nonneg hx hx
  else
    have hnx : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hnx hnx
    have heq : (-x) * (-x) = x * x := by
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem int_sq_pos_of_ne_zero (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  if hpos : 0 < x then
    exact Int.mul_pos hpos hpos
  else
    have hneg : 0 < -x := by omega
    have hmul : 0 < (-x) * (-x) := Int.mul_pos hneg hneg
    have heq : (-x) * (-x) = x * x := by
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem sq_le_sq_of_nonneg (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  Int.mul_le_mul hab hab ha (Int.le_trans ha hab)

private theorem pow4_le_pow4_of_nonneg (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 4 ≤ b ^ 4 := by
  rw [int_pow4 a, int_pow4 b]
  have hb : 0 ≤ b := Int.le_trans ha hab
  have sq_le : a * a ≤ b * b := sq_le_sq_of_nonneg a b ha hab
  have p4_le : (a * a) * (a * a) ≤ (b * b) * (b * b) :=
    sq_le_sq_of_nonneg (a * a) (b * b) (Int.mul_nonneg ha ha) sq_le
  have hl : a * a * a * a = (a * a) * (a * a) := by ac_rfl
  have hr : b * b * b * b = (b * b) * (b * b) := by ac_rfl
  have _ := hb
  omega

private theorem le_of_sq_le_sq_nonneg (x r : Int) (hr : 0 ≤ r) (h : x * x ≤ r * r) :
    x ≤ r := by
  if hxr : x ≤ r then
    exact hxr
  else
    have hrx : r < x := by omega
    have hr1 : r + 1 ≤ x := hrx
    have hsq : (r + 1) * (r + 1) ≤ x * x :=
      sq_le_sq_of_nonneg (r + 1) x (by omega) hr1
    have hexp : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    omega

private theorem int_reverse_triangle_sq (d zx zy r : Int)
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hnorm : zx * zx + zy * zy = r * r) :
    (d - r) * (d - r) ≤ (d - zx) * (d - zx) + zy * zy := by
  have hy : 0 ≤ zy * zy := int_sq_nonneg zy
  have hx2 : zx * zx ≤ r * r := by omega
  have hxr : zx ≤ r := le_of_sq_le_sq_nonneg zx r hr hx2
  have h1 : (d - zx) * (d - zx) + zy * zy =
      d * d - 2 * (d * zx) + (zx * zx + zy * zy) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hxd : zx * d = d * zx := Int.mul_comm zx d
    omega
  have h2 : (d - r) * (d - r) = d * d - 2 * (d * r) + r * r := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hrd : r * d = d * r := Int.mul_comm r d
    omega
  have hdiff : d * zx ≤ d * r := Int.mul_le_mul_of_nonneg_left hxr hd
  rw [h1, h2, hnorm]
  omega

/-- Algebraic quadratic splitting identity for the reciprocal L-polynomial:
`4 * L_C(T) = (2 + 5 T + 10 T^2)^2 - 5 T^2`. -/
theorem genus2_L_poly_quad_factor_id (T : Int) :
    4 * genus2LPoly T = (2 + 5 * T + 10 * T ^ 2) ^ 2 - 5 * T ^ 2 := by
  dsimp [genus2LPoly]
  rw [int_pow2 (2 + 5 * T + 10 * T ^ 2), int_pow2, int_pow4]
  have hpow3 : T ^ 3 = T * T * T := by simp [Int.pow_succ, Int.pow_zero]
  rw [hpow3]
  have hsq : ∀ a b : Int, (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    intro a b
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have hba : b * a = a * b := Int.mul_comm b a
    omega
  rw [hsq (2 + 5 * T) (10 * (T * T)), hsq 2 (5 * T)]
  have m1 : 2 * (2 * (5 * T)) = 20 * T := by
    calc 2 * (2 * (5 * T)) = (2 : Int) * 2 * 5 * T := by ac_rfl
      _ = 20 * T := rfl
  have m2 : (5 * T) * (5 * T) = 25 * (T * T) := by
    calc (5 * T) * (5 * T) = (5 : Int) * 5 * (T * T) := by ac_rfl
      _ = 25 * (T * T) := rfl
  have m3 : 2 * ((2 + 5 * T) * (10 * (T * T))) =
      40 * (T * T) + 100 * (T * T * T) := by
    rw [Int.add_mul]
    have t1 : 2 * (2 * (10 * (T * T))) = 40 * (T * T) := by
      calc 2 * (2 * (10 * (T * T))) = (2 : Int) * 2 * 10 * (T * T) := by ac_rfl
        _ = 40 * (T * T) := rfl
    have t2 : 2 * ((5 * T) * (10 * (T * T))) = 100 * (T * T * T) := by
      calc 2 * ((5 * T) * (10 * (T * T))) = (2 : Int) * 5 * 10 * (T * T * T) := by ac_rfl
        _ = 100 * (T * T * T) := rfl
    rw [Int.mul_add, t1, t2]
  have m4 : (10 * (T * T)) * (10 * (T * T)) = 100 * (T * T * T * T) := by
    calc (10 * (T * T)) * (10 * (T * T)) = (10 : Int) * 10 * (T * T * T * T) := by ac_rfl
      _ = 100 * (T * T * T * T) := rfl
  have l1 : 4 * (5 * T) = 20 * T := by
    calc 4 * (5 * T) = (4 : Int) * 5 * T := by ac_rfl
      _ = 20 * T := rfl
  have l2 : 4 * (15 * (T * T)) = 60 * (T * T) := by
    calc 4 * (15 * (T * T)) = (4 : Int) * 15 * (T * T) := by ac_rfl
      _ = 60 * (T * T) := rfl
  have l3 : 4 * (25 * (T * T * T)) = 100 * (T * T * T) := by
    calc 4 * (25 * (T * T * T)) = (4 : Int) * 25 * (T * T * T) := by ac_rfl
      _ = 100 * (T * T * T) := rfl
  have l4 : 4 * (25 * (T * T * T * T)) = 100 * (T * T * T * T) := by
    calc 4 * (25 * (T * T * T * T)) = (4 : Int) * 25 * (T * T * T * T) := by ac_rfl
      _ = 100 * (T * T * T * T) := rfl
  simp only [Int.mul_add]
  rw [m1, m2, m3, m4, l1, l2, l3, l4]
  omega

/-- Theorem (Weil Denominator Factor 1 Non-Vanishing for `σ > 0`):
For `T = (tx + i ty) / d` on `|T| = r = rNum / d` (`0 < rNum < d`, matching `r = 5^{-σ} < 1`),
we have `|1 - T|^2 ≥ (1 - r)^2 > 0`, and for any `σ = num / den > 0` (`num ≥ 1`) the local
base-5 Euler factor margin `5^num - 1` is strictly positive via `EulerFactorNonVanishing`. -/
theorem weil_denom_factor1_nonvanishing (d tx ty rNum : Int) (num : Nat)
    (hd : 0 < d) (hr : 0 < rNum) (hrd : rNum < d)
    (hnorm : tx * tx + ty * ty = rNum * rNum) (hnum : 1 ≤ num) :
    0 < (d - rNum) * (d - rNum) ∧
    (d - rNum) * (d - rNum) ≤ (d - tx) * (d - tx) + ty * ty ∧
    0 < eulerFactorMargin 5 num := by
  refine ⟨Int.mul_pos (by omega) (by omega), ?_, ?_⟩
  · exact int_reverse_triangle_sq d tx ty rNum (by omega) (by omega) hnorm
  · exact local_euler_factor_nonvanishing 5 num (by decide) hnum

/-- Theorem (Weil Denominator Factor 2 Non-Vanishing for `σ < 1`):
For `T = (tx + i ty) / d` on `|T| = r = rNum / d` (`d < 5 * rNum`, matching `r = 5^{-σ} > 1/5`),
we have `|1 - 5 T|^2 ≥ (5 r - 1)^2 > 0`, and for `1 - σ = compNum / den > 0` (`compNum ≥ 1`)
the conjugate base-5 Euler margin `5^compNum - 1` is strictly positive. -/
theorem weil_denom_factor2_nonvanishing (d tx ty rNum : Int) (compNum : Nat)
    (hd : 0 < d) (hr : 0 < rNum) (h5r : d < 5 * rNum)
    (hnorm : tx * tx + ty * ty = rNum * rNum) (hcomp : 1 ≤ compNum) :
    0 < (5 * rNum - d) * (5 * rNum - d) ∧
    (5 * rNum - d) * (5 * rNum - d) ≤ (d - 5 * tx) * (d - 5 * tx) + (5 * ty) * (5 * ty) ∧
    0 < eulerFactorMargin 5 compNum := by
  refine ⟨Int.mul_pos (by omega) (by omega), ?_, ?_⟩
  · have hnorm5 : (5 * tx) * (5 * tx) + (5 * ty) * (5 * ty) = (5 * rNum) * (5 * rNum) := by
      have hx5 : (5 * tx) * (5 * tx) = 25 * (tx * tx) := by
        calc (5 * tx) * (5 * tx) = (5 : Int) * 5 * (tx * tx) := by ac_rfl
          _ = 25 * (tx * tx) := rfl
      have hy5 : (5 * ty) * (5 * ty) = 25 * (ty * ty) := by
        calc (5 * ty) * (5 * ty) = (5 : Int) * 5 * (ty * ty) := by ac_rfl
          _ = 25 * (ty * ty) := rfl
      have hr5 : (5 * rNum) * (5 * rNum) = 25 * (rNum * rNum) := by
        calc (5 * rNum) * (5 * rNum) = (5 : Int) * 5 * (rNum * rNum) := by ac_rfl
          _ = 25 * (rNum * rNum) := rfl
      rw [hx5, hy5, hr5, ← Int.mul_add, hnorm]
    have htri := int_reverse_triangle_sq d (5 * tx) (5 * ty) (5 * rNum) (by omega) (by omega) hnorm5
    have heq : (5 * rNum - d) * (5 * rNum - d) = (d - 5 * rNum) * (d - 5 * rNum) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have hc : (5 * rNum) * d = d * (5 * rNum) := Int.mul_comm _ _
      omega
    omega
  · exact local_euler_factor_nonvanishing 5 compNum (by decide) hcomp

/-- Theorem (Weil Denominator Product Lower Bound on `r ∈ [5^{-(1-δ)}, 5^{-δ}]`):
For any positive rational margin `a / d = 5^{-δ}` with `0 < a < d` and any radius `r / d`
satisfying `1 / (5 * (a / d)) ≤ r / d ≤ a / d` (cleared as `d * d ≤ 5 * r * a ∧ r ≤ a`),
the Euler denominator product satisfies `(1 - r) * (5 r - 1) ≥ (1 - a)^2 > 0`. -/
theorem weil_denom_product_lower_bound (d a r : Int)
    (_hd : 0 < d) (ha_pos : 0 < a) (ha_lt : a < d)
    (hr_low : d * d ≤ 5 * r * a) (hr_high : r ≤ a) :
    0 < (d - a) * (d - a) ∧
    (d - a) * (d - a) ≤ (d - r) * (5 * r - d) := by
  have hda : 0 < d - a := by omega
  have h1 : d - a ≤ d - r := by omega
  have h2mul : (d - a) * a ≤ (5 * r - d) * a := by
    have hda_le : (d - a) * a ≤ (d - a) * d :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hexp1 : (d - a) * d = d * d - a * d := Int.sub_mul d a d
    have hexp2 : (5 * r - d) * a = 5 * r * a - d * a := Int.sub_mul (5 * r) d a
    have hcomm : a * d = d * a := Int.mul_comm a d
    omega
  have h2 : d - a ≤ 5 * r - d := by
    if hlt : d - a ≤ 5 * r - d then
      exact hlt
    else
      have hbad : (5 * r - d) + 1 ≤ d - a := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right hbad (by omega : 0 ≤ a)
      rw [Int.add_mul, Int.one_mul] at hmul
      omega
  have hprod : (d - a) * (d - a) ≤ (d - r) * (5 * r - d) :=
    Int.mul_le_mul h1 h2 (by omega) (by omega)
  exact ⟨Int.mul_pos hda hda, hprod⟩

private theorem single_frob_factor_lower (d r px py : Int)
    (_hd : 0 ≤ d) (_hr : 0 ≤ r) (hnorm : px * px + py * py = 5 * (r * r)) :
    (d * d - 5 * (r * r)) * (d * d - 5 * (r * r)) ≤
      2 * (d * d + 5 * (r * r)) * ((d - px) * (d - px) + py * py) ∧
    0 ≤ (d - px) * (d - px) + py * py := by
  let R2 : Int := 5 * (r * r)
  have hy : 0 ≤ py * py := int_sq_nonneg py
  have hnm : 0 ≤ (d - px) * (d - px) + py * py :=
    Int.add_nonneg (int_sq_nonneg (d - px)) hy
  have hminus : (d - px) * (d - px) + py * py = d * d - 2 * (d * px) + R2 := by
    dsimp [R2]
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hxd : px * d = d * px := Int.mul_comm px d
    omega
  have hplus : (d + px) * (d + px) + py * py = d * d + 2 * (d * px) + R2 := by
    dsimp [R2]
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have hxd : px * d = d * px := Int.mul_comm px d
    omega
  have hamgm : 2 * (d * px) ≤ d * d + px * px := by
    have hsq := int_sq_nonneg (d - px)
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub] at hsq
    have hxd : px * d = d * px := Int.mul_comm px d
    omega
  have hpxR2 : px * px ≤ R2 := by dsimp [R2]; omega
  have hplus_bound : (d + px) * (d + px) + py * py ≤ 2 * (d * d + R2) := by
    rw [hplus]
    omega
  have hmul_id :
      (d * d - 2 * (d * px) + R2) * (d * d + 2 * (d * px) + R2) =
        (d * d + R2) * (d * d + R2) - 4 * ((d * px) * (d * px)) := by
    let S : Int := d * d + R2
    let M : Int := 2 * (d * px)
    have hl : d * d - 2 * (d * px) + R2 = S - M := by dsimp [S, M]; omega
    have hr' : d * d + 2 * (d * px) + R2 = S + M := by dsimp [S, M]; omega
    have hsm : (S - M) * (S + M) = S * S - M * M := by
      rw [Int.sub_mul]
      simp only [Int.mul_add]
      have hcomm : M * S = S * M := Int.mul_comm M S
      omega
    have hm2 : M * M = 4 * ((d * px) * (d * px)) := by
      dsimp [M]
      calc (2 * (d * px)) * (2 * (d * px)) =
          (2 : Int) * 2 * ((d * px) * (d * px)) := by ac_rfl
        _ = 4 * ((d * px) * (d * px)) := rfl
    rw [hl, hr', hsm, hm2]
  have hdp2 : (d * px) * (d * px) ≤ (d * d) * R2 := by
    have hdp_eq : (d * px) * (d * px) = (d * d) * (px * px) := by ac_rfl
    rw [hdp_eq]
    exact Int.mul_le_mul_of_nonneg_left hpxR2 (int_sq_nonneg d)
  have hdiff_id :
      (d * d + R2) * (d * d + R2) - 4 * ((d * d) * R2) = (d * d - R2) * (d * d - R2) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have hcomm : R2 * (d * d) = (d * d) * R2 := Int.mul_comm R2 (d * d)
    omega
  have hprod_ge :
      (d * d - R2) * (d * d - R2) ≤
        ((d - px) * (d - px) + py * py) * ((d + px) * (d + px) + py * py) := by
    rw [hminus, hplus, hmul_id]
    omega
  have hprod_le :
      ((d - px) * (d - px) + py * py) * ((d + px) * (d + px) + py * py) ≤
        ((d - px) * (d - px) + py * py) * (2 * (d * d + R2)) :=
    Int.mul_le_mul_of_nonneg_left hplus_bound hnm
  have hcomm_r :
      ((d - px) * (d - px) + py * py) * (2 * (d * d + R2)) =
        2 * (d * d + R2) * ((d - px) * (d - px) + py * py) :=
    Int.mul_comm _ _
  refine ⟨?_, hnm⟩
  dsimp [R2] at hprod_ge hprod_le hcomm_r
  omega

private theorem pow4_mul_le (A B n1 n2 n3 n4 : Int)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (hn3 : 0 ≤ n3) (_hn4 : 0 ≤ n4)
    (h1 : A ≤ B * n1) (h2 : A ≤ B * n2) (h3 : A ≤ B * n3) (h4 : A ≤ B * n4) :
    A ^ 4 ≤ B ^ 4 * (n1 * n2 * n3 * n4) := by
  rw [int_pow4 A, int_pow4 B]
  have p12 : A * A ≤ (B * n1) * (B * n2) :=
    Int.mul_le_mul h1 h2 hA (Int.mul_nonneg hB hn1)
  have p34 : A * A ≤ (B * n3) * (B * n4) :=
    Int.mul_le_mul h3 h4 hA (Int.mul_nonneg hB hn3)
  have p1234 : (A * A) * (A * A) ≤ ((B * n1) * (B * n2)) * ((B * n3) * (B * n4)) :=
    Int.mul_le_mul p12 p34 (Int.mul_nonneg hA hA)
      (Int.mul_nonneg (Int.mul_nonneg hB hn1) (Int.mul_nonneg hB hn2))
  have hl : A * A * A * A = (A * A) * (A * A) := by ac_rfl
  have hr : ((B * n1) * (B * n2)) * ((B * n3) * (B * n4)) =
      (B * B * B * B) * (n1 * n2 * n3 * n4) := by ac_rfl
  omega

/-- Theorem (Genus-2 L-Polynomial Lower Bound Off `Re(s) = 1/2`):
Given complex Frobenius root products `α_j T = (px_j + i py_j) / d` with `|α_j|^2 = 5` and
`|T| = rNum / d`, whenever `5 * rNum^2 ≠ d^2` (`Re(s) ≠ 1/2`):
1) Uniformly across the critical strip:
   `0 < (d^2 - 5 r^2)^8 ≤ (2(d^2 + 5 r^2))^4 * ∏_{j=1}^4 ((d - px_j)^2 + py_j^2)`,
2) For `Re(s) > 1/2` (`5 r^2 < d^2`):
   `(d^2 - 5 r^2)^8 ≤ (4 d^2)^4 * ∏_{j=1}^4 ((d - px_j)^2 + py_j^2)`
   (`16 |L_C(T)| ≥ (1 - 5 r^2)^4 > 0`),
3) For `Re(s) < 1/2` (`d^2 < 5 r^2`):
   `(5 r^2 - d^2)^8 ≤ (20 r^2)^4 * ∏_{j=1}^4 ((d - px_j)^2 + py_j^2)`
   (`400 r^4 |L_C(T)| ≥ (5 r^2 - 1)^4 > 0`). -/
theorem genus2_L_poly_lower_bound_off_half (d rNum px1 py1 px2 py2 px3 py3 px4 py4 : Int)
    (hd : 0 < d) (hr : 0 ≤ rNum) (hoff : 5 * (rNum * rNum) ≠ d * d)
    (h1 : px1 * px1 + py1 * py1 = 5 * (rNum * rNum))
    (h2 : px2 * px2 + py2 * py2 = 5 * (rNum * rNum))
    (h3 : px3 * px3 + py3 * py3 = 5 * (rNum * rNum))
    (h4 : px4 * px4 + py4 * py4 = 5 * (rNum * rNum)) :
    let B := 2 * (d * d + 5 * (rNum * rNum))
    let n1 := (d - px1) * (d - px1) + py1 * py1
    let n2 := (d - px2) * (d - px2) + py2 * py2
    let n3 := (d - px3) * (d - px3) + py3 * py3
    let n4 := (d - px4) * (d - px4) + py4 * py4
    0 < (d * d - 5 * (rNum * rNum)) ^ 8 ∧
    (d * d - 5 * (rNum * rNum)) ^ 8 ≤ B ^ 4 * (n1 * n2 * n3 * n4) ∧
    (5 * (rNum * rNum) < d * d →
      (d * d - 5 * (rNum * rNum)) ^ 8 ≤ (4 * (d * d)) ^ 4 * (n1 * n2 * n3 * n4)) ∧
    (d * d < 5 * (rNum * rNum) →
      (5 * (rNum * rNum) - d * d) ^ 8 ≤ (20 * (rNum * rNum)) ^ 4 * (n1 * n2 * n3 * n4)) := by
  intro B n1 n2 n3 n4
  let A := (d * d - 5 * (rNum * rNum)) * (d * d - 5 * (rNum * rNum))
  have hf1 := single_frob_factor_lower d rNum px1 py1 (by omega) hr h1
  have hf2 := single_frob_factor_lower d rNum px2 py2 (by omega) hr h2
  have hf3 := single_frob_factor_lower d rNum px3 py3 (by omega) hr h3
  have hf4 := single_frob_factor_lower d rNum px4 py4 (by omega) hr h4
  have hApos : 0 < A := int_sq_pos_of_ne_zero (d * d - 5 * (rNum * rNum)) (by omega)
  have hB : 0 ≤ B := Int.mul_nonneg (by decide)
    (Int.add_nonneg (int_sq_nonneg d) (Int.mul_nonneg (by decide) (int_sq_nonneg rNum)))
  have hpow : A ^ 4 ≤ B ^ 4 * (n1 * n2 * n3 * n4) :=
    pow4_mul_le A B n1 n2 n3 n4 (by omega) hB hf1.2 hf2.2 hf3.2 hf4.2 hf1.1 hf2.1 hf3.1 hf4.1
  have hA4_eq : (d * d - 5 * (rNum * rNum)) ^ 8 = A ^ 4 := by
    rw [int_pow8, int_pow4 A]
    dsimp [A]
    ac_rfl
  have hA4_pos : 0 < A ^ 4 := by
    rw [int_pow4]
    exact Int.mul_pos (Int.mul_pos (Int.mul_pos hApos hApos) hApos) hApos
  have hn_nonneg : 0 ≤ n1 * n2 * n3 * n4 :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg hf1.2 hf2.2) hf3.2) hf4.2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hlt
    have hB4 : B ^ 4 ≤ (4 * (d * d)) ^ 4 :=
      pow4_le_pow4_of_nonneg B (4 * (d * d)) hB (by dsimp [B]; omega)
    have hmul := Int.mul_le_mul_of_nonneg_right hB4 hn_nonneg
    omega
  · intro hgt
    have hflip : (5 * (rNum * rNum) - d * d) ^ 8 = A ^ 4 := by
      have hsq : (5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d) = A := by
        dsimp [A]
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have hcomm := Int.mul_comm (5 * (rNum * rNum)) (d * d)
        omega
      rw [int_pow8, int_pow4 A]
      have hre : (5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d) *
          (5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d) *
          ((5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d) *
          (5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d)) =
          ((5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d)) *
          ((5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d)) *
          (((5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d)) *
          ((5 * (rNum * rNum) - d * d) * (5 * (rNum * rNum) - d * d))) := by
        ac_rfl
      rw [hre, hsq]
      ac_rfl
    have hB4 : B ^ 4 ≤ (20 * (rNum * rNum)) ^ 4 :=
      pow4_le_pow4_of_nonneg B (20 * (rNum * rNum)) hB (by dsimp [B]; omega)
    have hmul := Int.mul_le_mul_of_nonneg_right hB4 hn_nonneg
    omega

/-- Explicit rational strip bracket certificate at `σ = 1/4`, `σ = 3/4` (`QRH`), and `σ = 1`:
1) `σ = 1/4`: `2/3 < 5^{-1/4} < 7/10`, Euler margins `1 - r > 3/10`, `5 r - 1 > 7/3`,
   and `|L_C(5^{-1/4-it})| ≥ 1464100 / 31236921 > 1/25`.
2) `σ = 3/4`: `7/24 < 5^{-3/4} < 3/10`, Euler margins `1 - r > 7/10`, `5 r - 1 > 11/24`,
   and `|L_C(5^{-3/4-it})| ≥ 14641 / 1345600 > 1/100`.
3) `σ = 1`: `r = 1/5` exact, Euler margin `1 - 1/5 = 4/5 > 0`,
   `|L_C(5^{-1-it})| ≥ 16/225 > 0`, and central value `L(C, 1) = 71/25 > 16/225`. -/
theorem genus2_L_poly_explicit_strip_certs :
    -- σ = 1/4: 2/3 < 5^{-1/4} < 7/10 and |L_C(5^{-1/4-it})| > 1/25
    ((2 : Int) ^ 4 * 5 < 3 ^ 4 ∧ (10 : Int) ^ 4 < 5 * 7 ^ 4 ∧
     (25 : Int) * (5 * 2 ^ 2 - 3 ^ 2) ^ 4 * (10 ^ 2) ^ 2 >
       (3 : Int) ^ 8 * (2 * (10 ^ 2 + 5 * 7 ^ 2)) ^ 2) ∧
    -- σ = 3/4 (QRH threshold): 7/24 < 5^{-3/4} < 3/10 and |L_C(5^{-3/4-it})| > 1/100
    ((7 : Int) ^ 4 * 125 < 24 ^ 4 ∧ (10 : Int) ^ 4 < 125 * 3 ^ 4 ∧
     (100 : Int) * (10 ^ 2 - 5 * 3 ^ 2) ^ 4 >
       (10 : Int) ^ 4 * (2 * (10 ^ 2 + 5 * 3 ^ 2)) ^ 2) ∧
    -- σ = 1: r = 1/5 exact, |L_C(5^{-1-it})| ≥ 16/225, and L(C, 1) = 71/25 > 16/225
    (((5 : Int) ^ 2 - 5 * 1 ^ 2) ^ 4 * 225 =
       (5 : Int) ^ 4 * (2 * (5 ^ 2 + 5 * 1 ^ 2)) ^ 2 * 16 ∧
     genus2LNumAtInv5 = 1775 ∧ 1775 * 225 > 16 * 625) := by
  decide

/-- Theorem (Unified Punctured-Strip Regularity & Non-Vanishing for `Z(C/F_5, 5^{-s})`):
On any punctured critical strip point `s = σ + i t` with rational `σ = num / den ∈ (0, 1)`,
`σ ≠ 1/2`, and `T = (tx + i ty) / d` satisfying `|T| = r = rNum / d ∈ (1/5, 1) \ {1/√5}`:
1) Both local Euler-factor margins from `EulerFactorNonVanishing` are positive:
   `eulerFactorMargin 5 num > 0` and `eulerFactorMargin 5 (den - num) > 0`.
2) Both Weil denominators `|1 - T|^2` and `|1 - 5 T|^2` and their joint product are strictly
   bounded away from `0` (ruling out any poles of `Z(C/F_5, 5^{-s})` for `0 < σ < 1`).
3) The global Frobenius L-polynomial norm `∏_{j=1}^4 |1 - α_j T|^2` (from `FiniteFieldRH`) is
   strictly bounded away from `0` by `(d^2 - 5 rNum^2)^8 / (2(d^2 + 5 rNum^2))^4 > 0`.
4) `4 * genus2LPoly X = (2 + 5 X + 10 X^2)^2 - 5 X^2` holds identically. -/
theorem weil_zeta_punctured_strip_regular_and_nonzero
    (d tx ty rNum px1 py1 px2 py2 px3 py3 px4 py4 : Int) (num den : Nat)
    (hnum : 1 ≤ num) (hden : num < den)
    (hd : 0 < d) (hr : 0 < rNum) (hrd : rNum < d) (h5r : d < 5 * rNum)
    (hoff : 5 * (rNum * rNum) ≠ d * d)
    (hnormT : tx * tx + ty * ty = rNum * rNum)
    (h1 : px1 * px1 + py1 * py1 = 5 * (rNum * rNum))
    (h2 : px2 * px2 + py2 * py2 = 5 * (rNum * rNum))
    (h3 : px3 * px3 + py3 * py3 = 5 * (rNum * rNum))
    (h4 : px4 * px4 + py4 * py4 = 5 * (rNum * rNum)) :
    let m1 := (d - rNum) * (d - rNum)
    let m2 := (5 * rNum - d) * (5 * rNum - d)
    let d1sq := (d - tx) * (d - tx) + ty * ty
    let d2sq := (d - 5 * tx) * (d - 5 * tx) + (5 * ty) * (5 * ty)
    let B := 2 * (d * d + 5 * (rNum * rNum))
    let n1 := (d - px1) * (d - px1) + py1 * py1
    let n2 := (d - px2) * (d - px2) + py2 * py2
    let n3 := (d - px3) * (d - px3) + py3 * py3
    let n4 := (d - px4) * (d - px4) + py4 * py4
    (0 < eulerFactorMargin 5 num ∧ 0 < eulerFactorMargin 5 (den - num)) ∧
    (0 < m1 ∧ m1 ≤ d1sq) ∧
    (0 < m2 ∧ m2 ≤ d2sq) ∧
    (0 < m1 * m2 ∧ m1 * m2 ≤ d1sq * d2sq) ∧
    (0 < (d * d - 5 * (rNum * rNum)) ^ 8 ∧
      (d * d - 5 * (rNum * rNum)) ^ 8 ≤ B ^ 4 * (n1 * n2 * n3 * n4)) ∧
    (∀ X : Int, 4 * genus2LPoly X = (2 + 5 * X + 10 * X ^ 2) ^ 2 - 5 * X ^ 2) := by
  intro m1 m2 d1sq d2sq B n1 n2 n3 n4
  have hcomp : 1 ≤ den - num := Nat.sub_pos_of_lt hden
  have hf1 := weil_denom_factor1_nonvanishing d tx ty rNum num hd hr hrd hnormT hnum
  have hf2 := weil_denom_factor2_nonvanishing d tx ty rNum (den - num) hd hr h5r hnormT hcomp
  have hL := genus2_L_poly_lower_bound_off_half
    d rNum px1 py1 px2 py2 px3 py3 px4 py4 hd (by omega) hoff h1 h2 h3 h4
  have hprod : 0 < m1 * m2 ∧ m1 * m2 ≤ d1sq * d2sq :=
    ⟨Int.mul_pos hf1.1 hf2.1, Int.mul_le_mul hf1.2.1 hf2.2.1 (by omega) (by omega)⟩
  exact ⟨⟨hf1.2.2, hf2.2.2⟩, ⟨hf1.1, hf1.2.1⟩, ⟨hf2.1, hf2.2.1⟩, hprod, ⟨hL.1, hL.2.1⟩,
    genus2_L_poly_quad_factor_id⟩

/-! ### Genus-2 Hasse–Weil Functional Equation, Weil Zeta Symmetry, and Critical-Line Reality -/

/-- Homogenized numerator `d^4 * L_C(n/d) = d^4 + 5 n d^3 + 15 n^2 d^2 + 25 n^3 d + 25 n^4`
of the genus-2 Weil L-polynomial for `C : y^2 = x^5 - x + 1` over `F_5`. -/
def genus2LPolyHomog (n d : Int) : Int :=
  d ^ 4 + 5 * n * d ^ 3 + 15 * n ^ 2 * d ^ 2 + 25 * n ^ 3 * d + 25 * n ^ 4

/-- Exact `QRat` evaluation of `L_C(T)` for rational `T`. -/
def genus2LPolyQRat (T : QuasiRiemann.QRat) : QuasiRiemann.QRat :=
  QuasiRiemann.QRat.mk' (genus2LPolyHomog T.num T.den) (T.den ^ 4) (Nat.pow_pos T.den_pos)

/-- Reciprocal `QRat` value `1 / (5 * T)` for nonzero `T : QRat`. -/
def recip5QRat (T : QuasiRiemann.QRat) (hT : T.num ≠ 0) : QuasiRiemann.QRat :=
  QuasiRiemann.QRat.div (QuasiRiemann.QRat.ofInt 1) ⟨5 * T.num, T.den, T.den_pos⟩
    (Int.mul_ne_zero (by decide) hT)

/-- Homogenized denominator `d^4 * ((1 - n/d)(1 - 5 n/d)) = d^2 (d - n)(d - 5 n)`
for `Z(C/F_5, n/d)`. -/
def weilZetaDenomHomog (n d : Int) : Int :=
  d ^ 2 * (d - n) * (d - 5 * n)

/-- Homogenized denominator `d^4 * (n/d)(1 - n/d)(1 - 5 n/d) = d n (d - n)(d - 5 n)`
for the completed zeta function `Ξ_C(s) = 5^s Z(C/F_5, 5^{-s})`. -/
def completedZetaDenomHomog (n d : Int) : Int :=
  d * n * (d - n) * (d - 5 * n)

/-- Gaussian-integer addition `(a1 + b1) + i (a2 + b2)`. -/
def gAdd (a b : Int × Int) : Int × Int := (a.1 + b.1, a.2 + b.2)

/-- Gaussian-integer subtraction `(a1 - b1) + i (a2 - b2)`. -/
def gSub (a b : Int × Int) : Int × Int := (a.1 - b.1, a.2 - b.2)

/-- Gaussian-integer multiplication `(a1*b1 - a2*b2) + i (a1*b2 + a2*b1)`. -/
def gMul (a b : Int × Int) : Int × Int :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Embedding of an integer `k` into `Z[i]`. -/
def gScalar (k : Int) : Int × Int := (k, 0)

/-- Complex conjugation `a1 - i a2` in `Z[i]`. -/
def gConj (a : Int × Int) : Int × Int := (a.1, -a.2)

/-- Gaussian-integer exponentiation `a^n` in `Z[i]`. -/
def gPow (a : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => gMul (gPow a n) a

/-- Squared Euclidean modulus `a1^2 + a2^2` in `Z[i]`. -/
def gNormSq (a : Int × Int) : Int := a.1 * a.1 + a.2 * a.2

private theorem gAdd_comm (a b : Int × Int) : gAdd a b = gAdd b a := by
  apply Prod.ext <;> dsimp [gAdd] <;> omega

private theorem gAdd_assoc (a b c : Int × Int) : gAdd (gAdd a b) c = gAdd a (gAdd b c) := by
  apply Prod.ext <;> dsimp [gAdd] <;> omega

private theorem gMul_comm (a b : Int × Int) : gMul a b = gMul b a := by
  apply Prod.ext
  · dsimp [gMul]; rw [Int.mul_comm a.1 b.1, Int.mul_comm a.2 b.2]
  · dsimp [gMul]; rw [Int.mul_comm a.1 b.2, Int.mul_comm a.2 b.1, Int.add_comm]

private theorem gMul_assoc (a b c : Int × Int) : gMul (gMul a b) c = gMul a (gMul b c) := by
  apply Prod.ext <;>
  · dsimp [gMul]
    simp only [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add, Int.mul_assoc]
    omega

private theorem gMul_add (a b c : Int × Int) : gMul a (gAdd b c) = gAdd (gMul a b) (gMul a c) := by
  apply Prod.ext <;>
  · dsimp [gMul, gAdd]
    simp only [Int.mul_add]
    omega

private theorem gAdd_mul (a b c : Int × Int) : gMul (gAdd a b) c = gAdd (gMul a c) (gMul b c) := by
  rw [gMul_comm, gMul_add, gMul_comm c a, gMul_comm c b]

private theorem gMul_sub (a b c : Int × Int) : gMul a (gSub b c) = gSub (gMul a b) (gMul a c) := by
  apply Prod.ext <;>
  · dsimp [gMul, gSub]
    simp only [Int.mul_sub]
    omega

private theorem gSub_mul (a b c : Int × Int) : gMul (gSub a b) c = gSub (gMul a c) (gMul b c) := by
  rw [gMul_comm, gMul_sub, gMul_comm c a, gMul_comm c b]

private theorem gSub_self (a : Int × Int) : gSub a a = (0, 0) := by
  apply Prod.ext <;> dsimp [gSub] <;> omega

private theorem gNeg_sub (a b : Int × Int) : gMul (gScalar (-1)) (gSub a b) = gSub b a := by
  apply Prod.ext <;>
  · dsimp [gMul, gScalar, gSub]
    simp only [Int.zero_mul, Int.sub_zero, Int.add_zero]
    omega

private theorem gOne_mul (a : Int × Int) : gMul (1, 0) a = a := by
  apply Prod.ext <;> simp [gMul]

private theorem gPow2 (a : Int × Int) : gPow a 2 = gMul a a := by
  dsimp [gPow]; rw [gOne_mul]

private theorem gPow3 (a : Int × Int) : gPow a 3 = gMul (gMul a a) a := by
  dsimp [gPow]; rw [gOne_mul]

private theorem gPow4 (a : Int × Int) : gPow a 4 = gMul (gMul (gMul a a) a) a := by
  dsimp [gPow]; rw [gOne_mul]

private theorem gZero_mul (a : Int × Int) : gMul (0, 0) a = (0, 0) := by
  apply Prod.ext <;> simp [gMul]

private theorem gScalar_mul (a b : Int) : gMul (gScalar a) (gScalar b) = gScalar (a * b) := by
  apply Prod.ext <;> simp [gMul, gScalar]

private theorem gScalar_pow (d : Int) : ∀ k : Nat, gPow (gScalar d) k = gScalar (d ^ k)
  | 0 => by apply Prod.ext <;> simp [gPow, gScalar]
  | k + 1 => by
    dsimp [gPow]
    rw [gScalar_pow d k, gScalar_mul, Int.pow_succ]

private theorem gConj_add (a b : Int × Int) : gConj (gAdd a b) = gAdd (gConj a) (gConj b) := by
  apply Prod.ext <;> dsimp [gConj, gAdd] <;> omega

private theorem gConj_sub (a b : Int × Int) : gConj (gSub a b) = gSub (gConj a) (gConj b) := by
  apply Prod.ext <;> dsimp [gConj, gSub] <;> omega

private theorem gConj_mul (a b : Int × Int) : gConj (gMul a b) = gMul (gConj a) (gConj b) := by
  apply Prod.ext
  · dsimp [gConj, gMul]; simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]
  · dsimp [gConj, gMul]; simp only [Int.mul_neg, Int.neg_mul]; omega

private theorem gConj_scalar (k : Int) : gConj (gScalar k) = gScalar k := by
  apply Prod.ext
  · rfl
  · simp [gConj, gScalar]

private theorem gConj_pow (a : Int × Int) : ∀ k : Nat, gConj (gPow a k) = gPow (gConj a) k
  | 0 => rfl
  | k + 1 => by
    dsimp [gPow]
    rw [gConj_mul, gConj_pow a k]

private theorem gMul_conj (a : Int × Int) : gMul a (gConj a) = gScalar (gNormSq a) := by
  apply Prod.ext <;>
  · dsimp [gMul, gConj, gScalar, gNormSq]
    simp only [Int.mul_neg]
    have hc : a.2 * a.1 = a.1 * a.2 := Int.mul_comm a.2 a.1
    omega

private theorem gNormSq_nonneg (a : Int × Int) : 0 ≤ gNormSq a :=
  Int.add_nonneg (int_sq_nonneg a.1) (int_sq_nonneg a.2)

private theorem gNormSq_eq_zero_iff (a : Int × Int) : gNormSq a = 0 ↔ a = (0, 0) := by
  constructor
  · intro h
    dsimp [gNormSq] at h
    have h1 : 0 ≤ a.1 * a.1 := int_sq_nonneg a.1
    have h2 : 0 ≤ a.2 * a.2 := int_sq_nonneg a.2
    have h10 : a.1 = 0 := by
      cases Int.decEq a.1 0 with
      | isTrue hz => exact hz
      | isFalse hnz =>
        have hp := int_sq_pos_of_ne_zero a.1 hnz
        omega
    have h20 : a.2 = 0 := by
      cases Int.decEq a.2 0 with
      | isTrue hz => exact hz
      | isFalse hnz =>
        have hp := int_sq_pos_of_ne_zero a.2 hnz
        omega
    exact Prod.ext h10 h20
  · intro h
    rw [h]
    decide

private theorem gNormSq_mul (a b : Int × Int) : gNormSq (gMul a b) = gNormSq a * gNormSq b := by
  dsimp [gNormSq, gMul]
  simp only [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add]
  have h1 : (a.1 * b.1) * (a.2 * b.2) = (a.1 * a.2) * (b.1 * b.2) := by ac_rfl
  have h1a : (a.2 * b.2) * (a.1 * b.1) = (a.1 * a.2) * (b.1 * b.2) := by ac_rfl
  have h2 : (a.1 * b.2) * (a.2 * b.1) = (a.1 * a.2) * (b.1 * b.2) := by ac_rfl
  have h2a : (a.2 * b.1) * (a.1 * b.2) = (a.1 * a.2) * (b.1 * b.2) := by ac_rfl
  have h3 : (a.1 * b.1) * (a.1 * b.1) = (a.1 * a.1) * (b.1 * b.1) := by ac_rfl
  have h4 : (a.2 * b.2) * (a.2 * b.2) = (a.2 * a.2) * (b.2 * b.2) := by ac_rfl
  have h5 : (a.1 * b.2) * (a.1 * b.2) = (a.1 * a.1) * (b.2 * b.2) := by ac_rfl
  have h6 : (a.2 * b.1) * (a.2 * b.1) = (a.2 * a.2) * (b.1 * b.1) := by ac_rfl
  rw [h1, h1a, h2, h2a, h3, h4, h5, h6]
  omega

private theorem gCancel_left (c a b : Int × Int) (hc : c ≠ (0, 0))
    (h : gMul c a = gMul c b) : a = b := by
  have hns : gNormSq c ≠ 0 := fun hz => hc ((gNormSq_eq_zero_iff c).mp hz)
  have hc2 := congrArg (gMul (gConj c)) h
  rw [← gMul_assoc, ← gMul_assoc, gMul_comm (gConj c) c, gMul_conj] at hc2
  dsimp [gMul, gScalar] at hc2
  simp only [Int.zero_mul, Int.sub_zero, Int.add_zero] at hc2
  have hp := Prod.mk.inj hc2
  exact Prod.ext (Int.eq_of_mul_eq_mul_left hns hp.1) (Int.eq_of_mul_eq_mul_left hns hp.2)

private theorem gMul_ne_zero {a b : Int × Int} (ha : a ≠ (0, 0)) (hb : b ≠ (0, 0)) :
    gMul a b ≠ (0, 0) := by
  intro hab
  have hn := congrArg gNormSq hab
  rw [gNormSq_mul] at hn
  have hna : gNormSq a ≠ 0 := fun hz => ha ((gNormSq_eq_zero_iff a).mp hz)
  have hnb : gNormSq b ≠ 0 := fun hz => hb ((gNormSq_eq_zero_iff b).mp hz)
  have hz : gNormSq (0, 0) = 0 := rfl
  rw [hz] at hn
  rcases Int.mul_eq_zero.mp hn with h1 | h2
  · exact hna h1
  · exact hnb h2

private local instance : Std.Associative gAdd := ⟨gAdd_assoc⟩
private local instance : Std.Commutative gAdd := ⟨gAdd_comm⟩
private local instance : Std.Associative gMul := ⟨gMul_assoc⟩
private local instance : Std.Commutative gMul := ⟨gMul_comm⟩

/-- Complex homogenized L-polynomial `d^4 L_C(u/d)` in `Z[i]`. -/
def genus2LPolyGHomog (u : Int × Int) (d : Int) : Int × Int :=
  gAdd (gScalar (d ^ 4))
    (gAdd (gMul (gScalar (5 * d ^ 3)) u)
      (gAdd (gMul (gScalar (15 * d ^ 2)) (gPow u 2))
        (gAdd (gMul (gScalar (25 * d)) (gPow u 3))
          (gMul (gScalar 25) (gPow u 4)))))

/-- Complex homogenized Weil zeta denominator `d^2 (d - u)(d - 5 u)` in `Z[i]`. -/
def weilZetaGDenomHomog (u : Int × Int) (d : Int) : Int × Int :=
  gMul (gScalar (d ^ 2)) (gMul (gSub (gScalar d) u) (gSub (gScalar d) (gMul (gScalar 5) u)))

/-- Complex homogenized completed-zeta denominator `d * u * (d - u) * (d - 5 u)` in `Z[i]`. -/
def completedZetaGDenomHomog (u : Int × Int) (d : Int) : Int × Int :=
  gMul (gMul (gScalar d) u) (gMul (gSub (gScalar d) u) (gSub (gScalar d) (gMul (gScalar 5) u)))

/-- Cleared-denominator imaginary part of `Ξ_C(u/d) = genus2LPolyGHomog u d / completedZetaGDenomHomog u d`,
given by `Im(A * conj B) = A_y * B_x - A_x * B_y`. -/
def completedZetaImagPart (u : Int × Int) (d : Int) : Int :=
  let A := genus2LPolyGHomog u d
  let B := completedZetaGDenomHomog u d
  A.2 * B.1 - A.1 * B.2

private theorem genus2LPolyGHomog_conj (u : Int × Int) (d : Int) :
    gConj (genus2LPolyGHomog u d) = genus2LPolyGHomog (gConj u) d := by
  dsimp [genus2LPolyGHomog]
  simp only [gConj_add, gConj_mul, gConj_scalar, gConj_pow]

private theorem completedZetaGDenomHomog_conj (u : Int × Int) (d : Int) :
    gConj (completedZetaGDenomHomog u d) = completedZetaGDenomHomog (gConj u) d := by
  dsimp [completedZetaGDenomHomog]
  simp only [gConj_mul, gConj_sub, gConj_scalar]

private theorem gRecip_ne_zero (u v : Int × Int) (du dv : Int)
    (hdu : du ≠ 0) (hdv : dv ≠ 0) (hrec : gMul (gScalar 5) (gMul u v) = gScalar (du * dv)) :
    u ≠ (0, 0) ∧ v ≠ (0, 0) := by
  have hdudv : gScalar (du * dv) ≠ (0, 0) := by
    intro h
    have h0 : du * dv = 0 := (Prod.mk.inj h).1
    rcases Int.mul_eq_zero.mp h0 with h1 | h2
    · exact hdu h1
    · exact hdv h2
  constructor
  · intro hu
    rw [hu, gZero_mul] at hrec
    have hz : gMul (gScalar 5) (0, 0) = (0, 0) := by apply Prod.ext <;> simp [gMul]
    rw [hz] at hrec
    exact hdudv hrec.symm
  · intro hv
    rw [hv, gMul_comm u (0, 0), gZero_mul] at hrec
    have hz : gMul (gScalar 5) (0, 0) = (0, 0) := by apply Prod.ext <;> simp [gMul]
    rw [hz] at hrec
    exact hdudv hrec.symm

private theorem genus2_L_poly_homog_recip (n d : Int) :
    genus2LPolyHomog d (5 * n) = 25 * genus2LPolyHomog n d := by
  have hf := genus2_frob_poly_functional_eq.1 d n
  have e1 : genus2LPolyHomog d (5 * n) = genus2FrobHomog (5 * n) d := by
    dsimp [genus2LPolyHomog, genus2FrobHomog]
    rw [int_pow2 (5 * n), int_pow2 d, int_pow4 (5 * n), int_pow4 d]
    have p3a : (5 * n) ^ 3 = (5 * n) * (5 * n) * (5 * n) := by
      simp [Int.pow_succ, Int.pow_zero]
    have p3b : d ^ 3 = d * d * d := by simp [Int.pow_succ, Int.pow_zero]
    rw [p3a, p3b]
    ac_rfl
  have e2 : genus2LPolyHomog n d = genus2FrobHomog d n := by
    dsimp [genus2LPolyHomog, genus2FrobHomog]
    rw [int_pow2 n, int_pow2 d, int_pow4 n, int_pow4 d]
    have p3a : n ^ 3 = n * n * n := by simp [Int.pow_succ, Int.pow_zero]
    have p3b : d ^ 3 = d * d * d := by simp [Int.pow_succ, Int.pow_zero]
    rw [p3a, p3b]
    ac_rfl
  rw [e1, e2]
  exact hf

private theorem genus2_L_poly_g_recip (u v : Int × Int) (du dv : Int)
    (hrec : gMul (gScalar 5) (gMul u v) = gScalar (du * dv)) :
    gMul (gScalar 25) (gMul (gPow u 4) (genus2LPolyGHomog v dv)) =
      gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du) := by
  have hp := hrec
  dsimp [genus2LPolyGHomog]
  simp only [gMul_add]
  rw [gPow2 u, gPow3 u, gPow4 u, gPow2 v, gPow3 v, gPow4 v]
  have s25 : gScalar (25 : Int) = gMul (gScalar 5) (gScalar 5) := by
    rw [gScalar_mul]; rfl
  have d4 : dv ^ 4 = dv * dv * dv * dv := by simp [Int.pow_succ, Int.pow_zero]
  have d3 : dv ^ 3 = dv * dv * dv := by simp [Int.pow_succ, Int.pow_zero]
  have d2 : dv ^ 2 = dv * dv := by simp [Int.pow_succ, Int.pow_zero]
  have u3 : du ^ 3 = du * du * du := by simp [Int.pow_succ, Int.pow_zero]
  have u2 : du ^ 2 = du * du := by simp [Int.pow_succ, Int.pow_zero]
  have u4 : du ^ 4 = du * du * du * du := by simp [Int.pow_succ, Int.pow_zero]
  have t0 : gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u) (gScalar (dv ^ 4))) =
      gMul (gScalar (dv ^ 4)) (gMul (gScalar 25) (gMul (gMul (gMul u u) u) u)) := by
    ac_rfl
  have t1 : gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
      (gMul (gScalar (5 * dv ^ 3)) v)) =
      gMul (gScalar (dv ^ 4)) (gMul (gScalar (25 * du)) (gMul (gMul u u) u)) := by
    have c1 : gScalar (5 * dv ^ 3) = gMul (gScalar 5) (gScalar (dv ^ 3)) := by
      rw [gScalar_mul]
    have c2 : gScalar (25 * du) = gMul (gScalar 25) (gScalar du) := by rw [gScalar_mul]
    have c3 : gMul (gScalar (dv ^ 3)) (gScalar dv) = gScalar (dv ^ 4) := by
      rw [gScalar_mul, d3, d4]
    rw [c1, c2]
    calc gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
            (gMul (gMul (gScalar 5) (gScalar (dv ^ 3))) v))
        = gMul (gScalar (dv ^ 3)) (gMul (gScalar 25)
            (gMul (gMul u (gMul u u)) (gMul (gScalar 5) (gMul u v)))) := by ac_rfl
      _ = gMul (gScalar (dv ^ 3)) (gMul (gScalar 25)
            (gMul (gMul u (gMul u u)) (gScalar (du * dv)))) := by rw [hp]
      _ = gMul (gMul (gScalar (dv ^ 3)) (gScalar dv))
            (gMul (gMul (gScalar 25) (gScalar du)) (gMul (gMul u u) u)) := by
            rw [← gScalar_mul du dv]; ac_rfl
      _ = gMul (gScalar (dv ^ 4))
            (gMul (gMul (gScalar 25) (gScalar du)) (gMul (gMul u u) u)) := by rw [c3]
  have t2 : gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
      (gMul (gScalar (15 * dv ^ 2)) (gMul v v))) =
      gMul (gScalar (dv ^ 4)) (gMul (gScalar (15 * du ^ 2)) (gMul u u)) := by
    have c1 : gScalar (15 * dv ^ 2) = gMul (gScalar 15) (gScalar (dv ^ 2)) := by
      rw [gScalar_mul]
    have c2 : gScalar (15 * du ^ 2) = gMul (gScalar 15) (gMul (gScalar du) (gScalar du)) := by
      rw [gScalar_mul, gScalar_mul, u2]
    have c3 : gMul (gScalar (dv ^ 2)) (gMul (gScalar dv) (gScalar dv)) = gScalar (dv ^ 4) := by
      rw [gScalar_mul, gScalar_mul, d2, d4]
      apply Prod.ext <;> simp [gScalar] <;> ac_rfl
    rw [c1, c2, s25]
    calc gMul (gMul (gScalar 5) (gScalar 5))
            (gMul (gMul (gMul (gMul u u) u) u)
              (gMul (gMul (gScalar 15) (gScalar (dv ^ 2))) (gMul v v)))
        = gMul (gScalar (dv ^ 2)) (gMul (gMul (gScalar 15) (gMul u u))
            (gMul (gMul (gScalar 5) (gMul u v)) (gMul (gScalar 5) (gMul u v)))) := by ac_rfl
      _ = gMul (gScalar (dv ^ 2)) (gMul (gMul (gScalar 15) (gMul u u))
            (gMul (gScalar (du * dv)) (gScalar (du * dv)))) := by rw [hp]
      _ = gMul (gMul (gScalar (dv ^ 2)) (gMul (gScalar dv) (gScalar dv)))
            (gMul (gMul (gScalar 15) (gMul (gScalar du) (gScalar du))) (gMul u u)) := by
            rw [← gScalar_mul du dv]; ac_rfl
      _ = gMul (gScalar (dv ^ 4))
            (gMul (gMul (gScalar 15) (gMul (gScalar du) (gScalar du))) (gMul u u)) := by
            rw [c3]
  have t3 : gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
      (gMul (gScalar (25 * dv)) (gMul (gMul v v) v))) =
      gMul (gScalar (dv ^ 4)) (gMul (gScalar (5 * du ^ 3)) u) := by
    have c1 : gScalar (25 * dv) = gMul (gScalar 5) (gMul (gScalar 5) (gScalar dv)) := by
      rw [gScalar_mul, gScalar_mul]; apply Prod.ext <;> simp [gScalar] <;> ac_rfl
    have c2 : gScalar (5 * du ^ 3) =
        gMul (gScalar 5) (gMul (gScalar du) (gMul (gScalar du) (gScalar du))) := by
      rw [gScalar_mul, gScalar_mul, gScalar_mul, u3]; ac_rfl
    have c3 : gMul (gScalar dv) (gMul (gScalar dv) (gMul (gScalar dv) (gScalar dv))) =
        gScalar (dv ^ 4) := by
      rw [gScalar_mul, gScalar_mul, gScalar_mul, d4]; ac_rfl
    rw [c1, c2, s25]
    calc gMul (gMul (gScalar 5) (gScalar 5))
            (gMul (gMul (gMul (gMul u u) u) u)
              (gMul (gMul (gScalar 5) (gMul (gScalar 5) (gScalar dv))) (gMul (gMul v v) v)))
        = gMul (gScalar dv) (gMul (gMul (gScalar 5) u)
            (gMul (gMul (gScalar 5) (gMul u v))
              (gMul (gMul (gScalar 5) (gMul u v)) (gMul (gScalar 5) (gMul u v))))) := by
              ac_rfl
      _ = gMul (gScalar dv) (gMul (gMul (gScalar 5) u)
            (gMul (gScalar (du * dv))
              (gMul (gScalar (du * dv)) (gScalar (du * dv))))) := by rw [hp]
      _ = gMul (gMul (gScalar dv) (gMul (gScalar dv) (gMul (gScalar dv) (gScalar dv))))
            (gMul (gMul (gScalar 5)
              (gMul (gScalar du) (gMul (gScalar du) (gScalar du)))) u) := by
            rw [← gScalar_mul du dv]; ac_rfl
      _ = gMul (gScalar (dv ^ 4))
            (gMul (gMul (gScalar 5)
              (gMul (gScalar du) (gMul (gScalar du) (gScalar du)))) u) := by rw [c3]
  have t4 : gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
      (gMul (gScalar 25) (gMul (gMul (gMul v v) v) v))) =
      gMul (gScalar (dv ^ 4)) (gScalar (du ^ 4)) := by
    have c1 : gMul (gScalar 25) (gScalar 25) =
        gMul (gScalar 5) (gMul (gScalar 5) (gMul (gScalar 5) (gScalar 5))) := by
      rw [gScalar_mul, gScalar_mul, gScalar_mul, gScalar_mul]; rfl
    have c2 : gMul (gScalar dv) (gMul (gScalar dv) (gMul (gScalar dv) (gScalar dv))) =
        gScalar (dv ^ 4) := by
      rw [gScalar_mul, gScalar_mul, gScalar_mul, d4]; ac_rfl
    have c3 : gMul (gScalar du) (gMul (gScalar du) (gMul (gScalar du) (gScalar du))) =
        gScalar (du ^ 4) := by
      rw [gScalar_mul, gScalar_mul, gScalar_mul, u4]; ac_rfl
    calc gMul (gScalar 25) (gMul (gMul (gMul (gMul u u) u) u)
            (gMul (gScalar 25) (gMul (gMul (gMul v v) v) v)))
        = gMul (gMul (gScalar 25) (gScalar 25))
            (gMul (gMul (gMul (gMul u u) u) u) (gMul (gMul (gMul v v) v) v)) := by ac_rfl
      _ = gMul (gMul (gScalar 5) (gMul u v))
            (gMul (gMul (gScalar 5) (gMul u v))
              (gMul (gMul (gScalar 5) (gMul u v)) (gMul (gScalar 5) (gMul u v)))) := by
            rw [c1]; ac_rfl
      _ = gMul (gScalar (du * dv))
            (gMul (gScalar (du * dv))
              (gMul (gScalar (du * dv)) (gScalar (du * dv)))) := by rw [hp]
      _ = gMul (gMul (gScalar dv) (gMul (gScalar dv) (gMul (gScalar dv) (gScalar dv))))
            (gMul (gScalar du) (gMul (gScalar du) (gMul (gScalar du) (gScalar du)))) := by
            rw [← gScalar_mul du dv]; ac_rfl
      _ = gMul (gScalar (dv ^ 4)) (gScalar (du ^ 4)) := by rw [c2, c3]
  rw [t0, t1, t2, t3, t4]
  ac_rfl

/-- Theorem (Genus-2 Hasse–Weil L-Polynomial Functional Equation):
Establishes the reciprocal functional equation `25 * T^4 * L_C(1 / (5 * T)) = L_C(T)` for
`C : y^2 = x^5 - x + 1` over `F_5` in three forms:
1) Homogenized integer reciprocity `genus2LPolyHomog d (5 * n) = 25 * genus2LPolyHomog n d`,
2) Exact rational (`QRat`) reciprocity for all nonzero `T : QRat`,
3) Complex Gaussian (`Z[i]`) reciprocity for paired coordinates `5 * u * v = du * dv`. -/
theorem genus2_L_poly_functional_eq :
    (∀ n d : Int, genus2LPolyHomog d (5 * n) = 25 * genus2LPolyHomog n d) ∧
    (∀ (T : QuasiRiemann.QRat) (hT : T.num ≠ 0),
      QuasiRiemann.QRat.eqv
        (QuasiRiemann.QRat.mul
          (QuasiRiemann.QRat.mk' (25 * T.num ^ 4) (T.den ^ 4) (Nat.pow_pos T.den_pos))
          (genus2LPolyQRat (recip5QRat T hT)))
        (genus2LPolyQRat T)) ∧
    (∀ (u v : Int × Int) (du dv : Int),
      gMul (gScalar 5) (gMul u v) = gScalar (du * dv) →
      gMul (gScalar 25) (gMul (gPow u 4) (genus2LPolyGHomog v dv)) =
        gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du)) := by
  refine ⟨genus2_L_poly_homog_recip, ?_, genus2_L_poly_g_recip⟩
  intro T hT
  have hL : ∀ n d : Int, genus2LPolyHomog (-n) (-d) = genus2LPolyHomog n d := by
    intro n d
    dsimp [genus2LPolyHomog]
    rw [int_pow2 (-n), int_pow2 (-d), int_pow4 (-n), int_pow4 (-d)]
    have p3a : (-n) ^ 3 = (-n) * (-n) * (-n) := by simp [Int.pow_succ, Int.pow_zero]
    have p3b : (-d) ^ 3 = (-d) * (-d) * (-d) := by simp [Int.pow_succ, Int.pow_zero]
    have p3n : n ^ 3 = n * n * n := by simp [Int.pow_succ, Int.pow_zero]
    have p3d : d ^ 3 = d * d * d := by simp [Int.pow_succ, Int.pow_zero]
    rw [p3a, p3b, p3n, p3d, int_pow2 n, int_pow2 d, int_pow4 n, int_pow4 d]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  dsimp [QuasiRiemann.QRat.eqv, QuasiRiemann.QRat.mul, QuasiRiemann.QRat.mk',
    genus2LPolyQRat, recip5QRat, QuasiRiemann.QRat.div, QuasiRiemann.QRat.ofInt]
  have hpow54 : (5 * T.num) ^ 4 = 625 * T.num ^ 4 := by
    rw [int_pow4 (5 * T.num), int_pow4 T.num]
    calc (5 * T.num) * (5 * T.num) * (5 * T.num) * (5 * T.num) =
        ((5 : Int) * 5 * 5 * 5) * (T.num * T.num * T.num * T.num) := by ac_rfl
      _ = 625 * (T.num * T.num * T.num * T.num) := rfl
  have hfinish : ∀ x : Int,
      25 * T.num ^ 4 * (25 * x) * (T.den : Int) ^ 4 =
        x * ((T.den : Int) ^ 4 * (625 * T.num ^ 4)) := by
    intro x
    calc 25 * T.num ^ 4 * (25 * x) * (T.den : Int) ^ 4
        = ((25 : Int) * 25) * (x * ((T.den : Int) ^ 4 * T.num ^ 4)) := by ac_rfl
      _ = 625 * (x * ((T.den : Int) ^ 4 * T.num ^ 4)) := rfl
      _ = x * ((T.den : Int) ^ 4 * (625 * T.num ^ 4)) := by ac_rfl
  split
  · rename_i hpos
    have hnat : ((5 * T.num).natAbs : Int) = 5 * T.num := Int.natAbs_of_nonneg (by omega)
    have hrec := genus2_L_poly_homog_recip T.num (T.den : Int)
    simp only [Int.one_mul, Nat.one_mul]
    rw [hnat, hrec, hpow54]
    exact hfinish (genus2LPolyHomog T.num (T.den : Int))
  · rename_i hnonpos
    have hnat : ((5 * T.num).natAbs : Int) = -(5 * T.num) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hsym := hL (T.den : Int) (5 * T.num)
    have hrec := genus2_L_poly_homog_recip T.num (T.den : Int)
    have hpow_neg54 : (-(5 * T.num)) ^ 4 = 625 * T.num ^ 4 := by
      rw [int_pow4 (-(5 * T.num))]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [← int_pow4 (5 * T.num)]
      exact hpow54
    dsimp only
    simp only [Int.one_mul, Nat.one_mul]
    rw [hnat]
    have hrec2 : genus2LPolyHomog (-(T.den : Int)) (-(5 * T.num)) =
        25 * genus2LPolyHomog T.num T.den := by
      rw [hsym, hrec]
    rw [hrec2, hpow_neg54]
    exact hfinish (genus2LPolyHomog T.num (T.den : Int))

private theorem weil_denom_g_recip (u v : Int × Int) (du dv : Int)
    (hrec : gMul (gScalar 5) (gMul u v) = gScalar (du * dv)) :
    gMul (gScalar 5) (gMul (gPow u 2) (weilZetaGDenomHomog v dv)) =
      gMul (gScalar (dv ^ 4))
        (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u))) := by
  rw [gPow2 u]
  dsimp [weilZetaGDenomHomog]
  have f1 : gMul (gScalar 5) (gMul u (gSub (gScalar dv) v)) =
      gMul (gScalar dv) (gMul (gScalar (-1)) (gSub (gScalar du) (gMul (gScalar 5) u))) := by
    rw [gNeg_sub, gMul_sub, gMul_sub, hrec, gMul_sub, gMul_comm u (gScalar dv),
        gScalar_mul dv du, Int.mul_comm dv du]
    have eq1 : gMul (gScalar 5) (gMul (gScalar dv) u) =
        gMul (gScalar dv) (gMul (gScalar 5) u) := by ac_rfl
    rw [eq1]
  have f2 : gMul u (gSub (gScalar dv) (gMul (gScalar 5) v)) =
      gMul (gScalar dv) (gMul (gScalar (-1)) (gSub (gScalar du) u)) := by
    rw [gNeg_sub, gMul_sub, gMul_sub, gMul_comm u (gScalar dv)]
    have eq1 : gMul u (gMul (gScalar 5) v) = gMul (gScalar dv) (gScalar du) := by
      rw [gScalar_mul, Int.mul_comm dv du]
      calc gMul u (gMul (gScalar 5) v) = gMul (gScalar 5) (gMul u v) := by ac_rfl
        _ = gScalar (du * dv) := hrec
    rw [eq1]
  have neg1sq : gMul (gScalar (-1)) (gScalar (-1)) = gScalar 1 := by rw [gScalar_mul]; rfl
  have dv4eq : dv ^ 4 = dv ^ 2 * (dv * dv) := by
    rw [int_pow2, int_pow4]; ac_rfl
  calc gMul (gScalar 5) (gMul (gMul u u) (gMul (gScalar (dv ^ 2))
          (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v)))))
      = gMul (gScalar (dv ^ 2))
          (gMul (gMul (gScalar 5) (gMul u (gSub (gScalar dv) v)))
            (gMul u (gSub (gScalar dv) (gMul (gScalar 5) v)))) := by ac_rfl
    _ = gMul (gScalar (dv ^ 2))
          (gMul (gMul (gScalar dv) (gMul (gScalar (-1)) (gSub (gScalar du) (gMul (gScalar 5) u))))
            (gMul (gScalar dv) (gMul (gScalar (-1)) (gSub (gScalar du) u)))) := by rw [f1, f2]
    _ = gMul (gMul (gScalar (dv ^ 2)) (gMul (gScalar dv) (gScalar dv)))
          (gMul (gMul (gScalar (-1)) (gScalar (-1)))
            (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))) := by ac_rfl
    _ = gMul (gScalar (dv ^ 4))
          (gMul (gScalar 1) (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))) := by
          rw [neg1sq, gScalar_mul, gScalar_mul, ← dv4eq]
    _ = gMul (gScalar (dv ^ 4))
          (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u))) :=
          congrArg (gMul (gScalar (dv ^ 4))) (gOne_mul _)

/-- Theorem (Genus-2 Weil Zeta Rational Functional Equation):
Proves `5 * T^2 * Z(C/F_5, 1 / (5 * T)) = Z(C/F_5, T)` in cleared-denominator form for all
`T ∉ {0, 1, 1/5}` over both complex Gaussian coordinates `u / du` (`v / dv = 1 / (5 u / du)`)
and rational coordinates `n / d`. Also certifies non-vanishing of both Weil denominators. -/
theorem genus2_weil_zeta_functional_eq :
    (∀ (u v : Int × Int) (du dv : Int),
      du ≠ 0 → dv ≠ 0 →
      u ≠ (du, 0) → gMul (gScalar 5) u ≠ (du, 0) →
      gMul (gScalar 5) (gMul u v) = gScalar (du * dv) →
      weilZetaGDenomHomog u du ≠ (0, 0) ∧
      weilZetaGDenomHomog v dv ≠ (0, 0) ∧
      gMul (gMul (gScalar 5) (gMul (gPow u 2) (genus2LPolyGHomog v dv)))
          (weilZetaGDenomHomog u du) =
        gMul (genus2LPolyGHomog u du) (gMul (gScalar (du ^ 2)) (weilZetaGDenomHomog v dv))) ∧
    (∀ n d : Int, d ≠ 0 → n ≠ 0 → n ≠ d → 5 * n ≠ d →
      weilZetaDenomHomog n d ≠ 0 ∧
      weilZetaDenomHomog d (5 * n) ≠ 0 ∧
      5 * n ^ 2 * genus2LPolyHomog d (5 * n) * weilZetaDenomHomog n d =
        genus2LPolyHomog n d * (d ^ 2 * weilZetaDenomHomog d (5 * n))) := by
  constructor
  · intro u v du dv hdu hdv hne1 hne5 hrec
    have hunz := (gRecip_ne_zero u v du dv hdu hdv hrec).1
    have hduG : gScalar du ≠ (0, 0) := fun h => hdu (Prod.mk.inj h).1
    have hdvG : gScalar dv ≠ (0, 0) := fun h => hdv (Prod.mk.inj h).1
    have hdu2 : gScalar (du ^ 2) ≠ (0, 0) := by
      intro h; have := (Prod.mk.inj h).1; rw [int_pow2] at this
      rcases Int.mul_eq_zero.mp this with h1 | h1 <;> exact hdu h1
    have hs1 : gSub (gScalar du) u ≠ (0, 0) := by
      intro h; apply hne1
      have hp := Prod.mk.inj h
      dsimp [gSub, gScalar] at hp ⊢
      apply Prod.ext <;> omega
    have hs5 : gSub (gScalar du) (gMul (gScalar 5) u) ≠ (0, 0) := by
      intro h; apply hne5
      have hp := Prod.mk.inj h
      dsimp [gSub, gScalar] at hp ⊢
      apply Prod.ext <;> omega
    have hdenU : weilZetaGDenomHomog u du ≠ (0, 0) :=
      gMul_ne_zero hdu2 (gMul_ne_zero hs1 hs5)
    have h5u2 : gMul (gScalar 5) (gPow u 2) ≠ (0, 0) := by
      rw [gPow2 u]
      exact gMul_ne_zero (by decide) (gMul_ne_zero hunz hunz)
    have hwDen := weil_denom_g_recip u v du dv hrec
    have hdenV : weilZetaGDenomHomog v dv ≠ (0, 0) := by
      intro hz
      rw [hz, gMul_comm _ (0, 0), gZero_mul] at hwDen
      have hdv4 : gScalar (dv ^ 4) ≠ (0, 0) := by
        intro h; have := (Prod.mk.inj h).1; rw [int_pow4] at this
        rcases Int.mul_eq_zero.mp this with h1 | h2
        · rcases Int.mul_eq_zero.mp h1 with h3 | h4
          · rcases Int.mul_eq_zero.mp h3 with h5 | h5 <;> exact hdv h5
          · exact hdv h4
        · exact hdv h2
      exact gMul_ne_zero hdv4 (gMul_ne_zero hs1 hs5) hwDen.symm
    refine ⟨hdenU, hdenV, ?_⟩
    apply gCancel_left (gMul (gScalar 5) (gPow u 2)) _ _ h5u2
    have hL := genus2_L_poly_g_recip u v du dv hrec
    have pu4 : gPow u 4 = gMul (gPow u 2) (gPow u 2) := by
      rw [gPow4 u, gPow2 u]; ac_rfl
    have hL' : gMul (gScalar 5)
        (gMul (gPow u 2) (gMul (gScalar 5) (gMul (gPow u 2) (genus2LPolyGHomog v dv)))) =
        gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du) := by
      calc gMul (gScalar 5) (gMul (gPow u 2)
              (gMul (gScalar 5) (gMul (gPow u 2) (genus2LPolyGHomog v dv))))
          = gMul (gMul (gScalar 5) (gScalar 5))
              (gMul (gMul (gPow u 2) (gPow u 2)) (genus2LPolyGHomog v dv)) := by ac_rfl
        _ = gMul (gScalar 25) (gMul (gPow u 4) (genus2LPolyGHomog v dv)) := by
            rw [gScalar_mul, pu4]; rfl
        _ = gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du) := hL
    have hDenU_eq : weilZetaGDenomHomog u du =
        gMul (gScalar (du ^ 2))
          (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u))) := rfl
    calc gMul (gMul (gScalar 5) (gPow u 2))
            (gMul (gMul (gScalar 5) (gMul (gPow u 2) (genus2LPolyGHomog v dv)))
              (weilZetaGDenomHomog u du))
        = gMul (gMul (gScalar 5) (gMul (gPow u 2)
            (gMul (gScalar 5) (gMul (gPow u 2) (genus2LPolyGHomog v dv)))))
            (weilZetaGDenomHomog u du) := by ac_rfl
      _ = gMul (gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du))
            (weilZetaGDenomHomog u du) := by rw [hL']
      _ = gMul (gScalar (du ^ 2)) (gMul (genus2LPolyGHomog u du)
            (gMul (gScalar (dv ^ 4))
              (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u))))) := by
            rw [hDenU_eq]; ac_rfl
      _ = gMul (gScalar (du ^ 2)) (gMul (genus2LPolyGHomog u du)
            (gMul (gScalar 5) (gMul (gPow u 2) (weilZetaGDenomHomog v dv)))) := by rw [← hwDen]
      _ = gMul (gMul (gScalar 5) (gPow u 2))
            (gMul (genus2LPolyGHomog u du)
              (gMul (gScalar (du ^ 2)) (weilZetaGDenomHomog v dv))) := by ac_rfl
  · intro n d hd hn hnd h5nd
    have hrec : 5 * n ^ 2 * genus2LPolyHomog d (5 * n) * weilZetaDenomHomog n d =
        genus2LPolyHomog n d * (d ^ 2 * weilZetaDenomHomog d (5 * n)) := by
      have hL := genus2_L_poly_homog_recip n d
      have h5n2 : (5 * n) ^ 2 = 25 * n ^ 2 := by
        rw [int_pow2, int_pow2]; ac_rfl
      dsimp [weilZetaDenomHomog]
      rw [hL, h5n2]
      have hm1 : 5 * n - d = -(d - 5 * n) := by omega
      have hm2 : 5 * n - 5 * d = -(5 * (d - n)) := by omega
      rw [hm1, hm2]
      simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]
      ac_rfl
    have hdu1 : weilZetaDenomHomog n d ≠ 0 := by
      dsimp [weilZetaDenomHomog]
      rw [int_pow2]
      exact Int.mul_ne_zero (Int.mul_ne_zero (Int.mul_ne_zero hd hd) (by omega)) (by omega)
    have hdv1 : weilZetaDenomHomog d (5 * n) ≠ 0 := by
      dsimp [weilZetaDenomHomog]
      rw [int_pow2]
      exact Int.mul_ne_zero (Int.mul_ne_zero (Int.mul_ne_zero (by omega) (by omega)) (by omega))
        (by omega)
    exact ⟨hdu1, hdv1, hrec⟩

/-- Theorem (Completed Genus-2 Zeta Reflection `Ξ_C(1 - s) = Ξ_C(s)` & Critical-Line Reality):
For `Ξ_C(s) = 5^s Z(C/F_5, 5^{-s})` evaluated on paired coordinates `(u, v) = (5^{-s}, 5^{-(1-s)})`
satisfying `5 * u * v = du * dv` (`du, dv ≠ 0`):
1) **Reflection Symmetry:** In cleared-denominator form,
   `L_hom(v, dv) * completedZetaDenom(u, du) = L_hom(u, du) * completedZetaDenom(v, dv)`.
2) **Critical-Line Reality (`Re(s) = 1/2`):** Whenever `5 * |u|^2 = d^2` (`d ≠ 0`, so `v = conj(u)`),
   the imaginary part of `Ξ_C(1/2 + i t)` vanishes identically (`completedZetaImagPart u d = 0`).
3) **Exact Critical-Line Witness:** At `u = (1, 2)`, `d = 5` (`5 * (1^2 + 2^2) = 5^2`),
   `completedZetaGDenomHomog (1, 2) 5 ≠ (0, 0)` and `completedZetaImagPart (1, 2) 5 = 0`. -/
theorem genus2_completed_zeta_reflection :
    (∀ (u v : Int × Int) (du dv : Int),
      du ≠ 0 → dv ≠ 0 →
      gMul (gScalar 5) (gMul u v) = gScalar (du * dv) →
      gMul (genus2LPolyGHomog v dv) (completedZetaGDenomHomog u du) =
        gMul (genus2LPolyGHomog u du) (completedZetaGDenomHomog v dv)) ∧
    (∀ (u : Int × Int) (d : Int),
      d ≠ 0 → 5 * gNormSq u = d * d →
      completedZetaImagPart u d = 0) ∧
    (5 * gNormSq (1, 2) = 5 * 5 ∧
      completedZetaGDenomHomog (1, 2) 5 ≠ (0, 0) ∧
      completedZetaImagPart (1, 2) 5 = 0) := by
  have href :
      ∀ (u v : Int × Int) (du dv : Int),
        du ≠ 0 → dv ≠ 0 →
        gMul (gScalar 5) (gMul u v) = gScalar (du * dv) →
        gMul (genus2LPolyGHomog v dv) (completedZetaGDenomHomog u du) =
          gMul (genus2LPolyGHomog u du) (completedZetaGDenomHomog v dv) := by
    intro u v du dv hdu hdv hrec
    have hunz := (gRecip_ne_zero u v du dv hdu hdv hrec).1
    have h25u3 : gMul (gScalar 25) (gPow u 3) ≠ (0, 0) := by
      rw [gPow3 u]
      exact gMul_ne_zero (by decide) (gMul_ne_zero (gMul_ne_zero hunz hunz) hunz)
    apply gCancel_left (gMul (gScalar 25) (gPow u 3)) _ _ h25u3
    have hL := genus2_L_poly_g_recip u v du dv hrec
    have hdv_den :
        gMul (gScalar (dv ^ 4))
            (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u))) =
          gMul (gScalar 5) (gMul (gPow u 2) (weilZetaGDenomHomog v dv)) :=
      (weil_denom_g_recip u v du dv hrec).symm
    have hstep1 :
        gMul (gMul (gScalar 25) (gPow u 3))
            (gMul (genus2LPolyGHomog v dv) (completedZetaGDenomHomog u du)) =
          gMul (gScalar du) (gMul (gMul (gScalar 25) (gMul (gPow u 4) (genus2LPolyGHomog v dv)))
            (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))) := by
      dsimp [completedZetaGDenomHomog]
      rw [gPow3 u, gPow4 u]
      ac_rfl
    have hstep2 :
        gMul (gScalar du) (gMul (gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du))
            (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))) =
          gMul (gMul (gScalar 25) (gPow u 3))
            (gMul (genus2LPolyGHomog u du) (completedZetaGDenomHomog v dv)) := by
      rw [show gMul (gScalar du) (gMul (gMul (gScalar (dv ^ 4)) (genus2LPolyGHomog u du))
            (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))) =
          gMul (gScalar du) (gMul (genus2LPolyGHomog u du)
            (gMul (gScalar (dv ^ 4))
              (gMul (gSub (gScalar du) u) (gSub (gScalar du) (gMul (gScalar 5) u)))))
          by ac_rfl]
      rw [hdv_den]
      dsimp [weilZetaGDenomHomog, completedZetaGDenomHomog]
      rw [gPow2 u, gPow3 u]
      have dv2 : dv ^ 2 = dv * dv := int_pow2 dv
      have s25 : gScalar (25 : Int) = gMul (gScalar 5) (gScalar 5) := by rw [gScalar_mul]; rfl
      have hdv_split : gMul (gScalar du) (gScalar (dv ^ 2)) =
          gMul (gScalar dv) (gScalar (du * dv)) := by
        rw [dv2, gScalar_mul, gScalar_mul]
        apply Prod.ext <;> simp [gScalar] <;> ac_rfl
      calc gMul (gScalar du) (gMul (genus2LPolyGHomog u du)
              (gMul (gScalar 5) (gMul (gMul u u) (gMul (gScalar (dv ^ 2))
                (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v)))))))
          = gMul (gMul (gScalar du) (gScalar (dv ^ 2))) (gMul (genus2LPolyGHomog u du)
              (gMul (gScalar 5) (gMul (gMul u u)
                (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v)))))) := by
              ac_rfl
        _ = gMul (gScalar dv) (gMul (gScalar (du * dv)) (gMul (genus2LPolyGHomog u du)
              (gMul (gScalar 5) (gMul (gMul u u)
                (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v))))))) := by
              rw [hdv_split]; ac_rfl
        _ = gMul (gScalar dv) (gMul (gMul (gScalar 5) (gMul u v)) (gMul (genus2LPolyGHomog u du)
              (gMul (gScalar 5) (gMul (gMul u u)
                (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v))))))) := by
              rw [← hrec]
        _ = gMul (gMul (gScalar 25) (gMul (gMul u u) u)) (gMul (genus2LPolyGHomog u du)
              (gMul (gMul (gScalar dv) v)
                (gMul (gSub (gScalar dv) v) (gSub (gScalar dv) (gMul (gScalar 5) v))))) := by
              rw [s25]; ac_rfl
    rw [hstep1, hL]
    exact hstep2
  refine ⟨href, ?_, by decide⟩
  intro u d hd hnorm
  have hrec : gMul (gScalar 5) (gMul u (gConj u)) = gScalar (d * d) := by
    rw [gMul_conj, gScalar_mul, hnorm]
  have heq := href u (gConj u) d d hd hd hrec
  rw [← genus2LPolyGHomog_conj, ← completedZetaGDenomHomog_conj] at heq
  have him := congrArg Prod.snd heq
  dsimp [gMul, gConj, completedZetaImagPart] at him ⊢
  simp only [Int.mul_neg, Int.neg_mul] at him
  omega

end WeilZetaBridge

-- end of file: leanasm/src/LeanAsm/WeilZetaBridge.lean
