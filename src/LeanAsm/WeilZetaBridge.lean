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

end WeilZetaBridge

-- end of file: leanasm/src/LeanAsm/WeilZetaBridge.lean
