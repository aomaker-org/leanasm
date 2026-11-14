-- Path: leanasm/src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean
-- Constructive dyadic-octave log envelope, explicit de la Vallee Poussin asymptotic zero-free
-- region (sigma > 1 - c / ln t), and Dirichlet-polynomial L^2 diagonal dominance bounds.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat

namespace QuasiRiemann

-- =============================================================================
-- Foundational Constructive Order & Equivalence Lemmas for QRat
-- =============================================================================

private theorem qrat_den_pos_int (a : QRat) : (0 : Int) < (a.den : Int) :=
  Int.natCast_pos.mpr a.den_pos

private theorem qrat_eqv_refl (a : QRat) : QRat.eqv a a := rfl

private theorem qrat_eqv_symm {a b : QRat} (h : QRat.eqv a b) : QRat.eqv b a :=
  h.symm

private theorem qrat_eqv_trans {a b c : QRat}
    (hab : QRat.eqv a b) (hbc : QRat.eqv b c) : QRat.eqv a c := by
  dsimp [QRat.eqv] at *
  have hb : (0 : Int) < (b.den : Int) := qrat_den_pos_int b
  have h : a.num * (c.den : Int) * (b.den : Int) =
      c.num * (a.den : Int) * (b.den : Int) := by
    calc a.num * (c.den : Int) * (b.den : Int)
        = (a.num * (b.den : Int)) * (c.den : Int) := by ac_rfl
      _ = (b.num * (a.den : Int)) * (c.den : Int) := by rw [hab]
      _ = (b.num * (c.den : Int)) * (a.den : Int) := by ac_rfl
      _ = (c.num * (b.den : Int)) * (a.den : Int) := by rw [hbc]
      _ = c.num * (a.den : Int) * (b.den : Int) := by ac_rfl
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hb) h

theorem qrat_le_refl (a : QRat) : a ≤ a :=
  Int.le_refl _

private theorem qrat_le_iff (a b : QRat) :
    a ≤ b ↔ a.num * (b.den : Int) ≤ b.num * (a.den : Int) := Iff.rfl

theorem qrat_le_of_lt {a b : QRat} (h : a < b) : a ≤ b :=
  Int.le_of_lt h

theorem qrat_le_trans {a b c : QRat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  change a.num * (c.den : Int) ≤ c.num * (a.den : Int)
  change a.num * (b.den : Int) ≤ b.num * (a.den : Int) at hab
  change b.num * (c.den : Int) ≤ c.num * (b.den : Int) at hbc
  have ha : (0 : Int) ≤ (a.den : Int) := Int.le_of_lt (qrat_den_pos_int a)
  have hb : (0 : Int) < (b.den : Int) := qrat_den_pos_int b
  have hc : (0 : Int) ≤ (c.den : Int) := Int.le_of_lt (qrat_den_pos_int c)
  have h1 := Int.mul_le_mul_of_nonneg_right hab hc
  have h2 := Int.mul_le_mul_of_nonneg_right hbc ha
  have hm : a.num * (c.den : Int) * (b.den : Int) ≤
      c.num * (a.den : Int) * (b.den : Int) := by
    calc a.num * (c.den : Int) * (b.den : Int)
        = a.num * (b.den : Int) * (c.den : Int) := by ac_rfl
      _ ≤ b.num * (a.den : Int) * (c.den : Int) := h1
      _ = b.num * (c.den : Int) * (a.den : Int) := by ac_rfl
      _ ≤ c.num * (b.den : Int) * (a.den : Int) := h2
      _ = c.num * (a.den : Int) * (b.den : Int) := by ac_rfl
  exact Int.le_of_mul_le_mul_right hm hb

private theorem qrat_lt_iff (a b : QRat) :
    a < b ↔ 0 < b.num * (a.den : Int) - a.num * (b.den : Int) :=
  ⟨fun h => Int.sub_pos.mpr h, fun h => Int.sub_pos.mp h⟩

theorem qrat_lt_of_le_of_lt {a b c : QRat} (hab : a ≤ b) (hbc : b < c) : a < c := by
  change a.num * (c.den : Int) < c.num * (a.den : Int)
  change a.num * (b.den : Int) ≤ b.num * (a.den : Int) at hab
  change b.num * (c.den : Int) < c.num * (b.den : Int) at hbc
  have ha : (0 : Int) < (a.den : Int) := qrat_den_pos_int a
  have hb : (0 : Int) < (b.den : Int) := qrat_den_pos_int b
  have hc : (0 : Int) < (c.den : Int) := qrat_den_pos_int c
  have h1 := Int.mul_le_mul_of_nonneg_right hab (Int.le_of_lt hc)
  have h2 := Int.mul_lt_mul_of_pos_right hbc ha
  have hm : a.num * (c.den : Int) * (b.den : Int) <
      c.num * (a.den : Int) * (b.den : Int) := by
    calc a.num * (c.den : Int) * (b.den : Int)
        = a.num * (b.den : Int) * (c.den : Int) := by ac_rfl
      _ ≤ b.num * (a.den : Int) * (c.den : Int) := h1
      _ = b.num * (c.den : Int) * (a.den : Int) := by ac_rfl
      _ < c.num * (b.den : Int) * (a.den : Int) := h2
      _ = c.num * (a.den : Int) * (b.den : Int) := by ac_rfl
  exact Int.lt_of_mul_lt_mul_right hm (Int.le_of_lt hb)

theorem qrat_lt_of_lt_of_le {a b c : QRat} (hab : a < b) (hbc : b ≤ c) : a < c := by
  change a.num * (c.den : Int) < c.num * (a.den : Int)
  change a.num * (b.den : Int) < b.num * (a.den : Int) at hab
  change b.num * (c.den : Int) ≤ c.num * (b.den : Int) at hbc
  have ha : (0 : Int) < (a.den : Int) := qrat_den_pos_int a
  have hb : (0 : Int) < (b.den : Int) := qrat_den_pos_int b
  have hc : (0 : Int) < (c.den : Int) := qrat_den_pos_int c
  have h1 := Int.mul_lt_mul_of_pos_right hab hc
  have h2 := Int.mul_le_mul_of_nonneg_right hbc (Int.le_of_lt ha)
  have hm : a.num * (c.den : Int) * (b.den : Int) <
      c.num * (a.den : Int) * (b.den : Int) := by
    calc a.num * (c.den : Int) * (b.den : Int)
        = a.num * (b.den : Int) * (c.den : Int) := by ac_rfl
      _ < b.num * (a.den : Int) * (c.den : Int) := h1
      _ = b.num * (c.den : Int) * (a.den : Int) := by ac_rfl
      _ ≤ c.num * (b.den : Int) * (a.den : Int) := h2
      _ = c.num * (a.den : Int) * (b.den : Int) := by ac_rfl
  exact Int.lt_of_mul_lt_mul_right hm (Int.le_of_lt hb)

theorem qrat_le_of_eqv_left {a a' b : QRat} (h : QRat.eqv a a') (hle : a ≤ b) :
    a' ≤ b := by
  have ha : a' ≤ a := by
    change a'.num * (a.den : Int) ≤ a.num * (a'.den : Int)
    dsimp [QRat.eqv] at h
    omega
  exact qrat_le_trans ha hle

theorem qrat_le_of_eqv_right {a b b' : QRat} (h : QRat.eqv b b') (hle : a ≤ b) :
    a ≤ b' := by
  have hb : b ≤ b' := by
    change b.num * (b'.den : Int) ≤ b'.num * (b.den : Int)
    dsimp [QRat.eqv] at h
    omega
  exact qrat_le_trans hle hb

private theorem qrat_add_num (a b : QRat) :
    (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
private theorem qrat_add_den (a b : QRat) : (a + b).den = a.den * b.den := rfl
private theorem qrat_sub_num (a b : QRat) :
    (a - b).num = a.num * (b.den : Int) - b.num * (a.den : Int) := rfl
private theorem qrat_sub_den (a b : QRat) : (a - b).den = a.den * b.den := rfl
private theorem qrat_neg_num (a : QRat) : (-a).num = -a.num := rfl
private theorem qrat_neg_den (a : QRat) : (-a).den = a.den := rfl
private theorem qrat_mul_num (a b : QRat) : (a * b).num = a.num * b.num := rfl
private theorem qrat_mul_den (a b : QRat) : (a * b).den = a.den * b.den := rfl
private theorem qrat_abs_num (a : QRat) : (QRat.abs a).num = (a.num.natAbs : Int) := rfl
private theorem qrat_abs_den (a : QRat) : (QRat.abs a).den = a.den := rfl
private theorem qrat_ofInt_num (n : Int) : (QRat.ofInt n).num = n := rfl
private theorem qrat_ofInt_den (n : Int) : (QRat.ofInt n).den = 1 := rfl
private theorem qrat_mk'_num (n : Int) (d : Nat) (h : 0 < d) : (QRat.mk' n d h).num = n := rfl
private theorem qrat_mk'_den (n : Int) (d : Nat) (h : 0 < d) : (QRat.mk' n d h).den = d := rfl

private theorem qrat_div_pos_num (a b : QRat) (hb : b.num ≠ 0) (hp : 0 < b.num) :
    (QRat.div a b hb).num = a.num * (b.den : Int) := by
  dsimp [QRat.div]; simp [hp]

private theorem qrat_div_pos_den (a b : QRat) (hb : b.num ≠ 0) (hp : 0 < b.num) :
    (QRat.div a b hb).den = a.den * b.num.natAbs := by
  dsimp [QRat.div]; simp [hp]

private theorem qrat_add_eqv_congr {a a' b b' : QRat}
    (ha : QRat.eqv a a') (hb : QRat.eqv b b') :
    QRat.eqv (a + b) (a' + b') := by
  dsimp [QRat.eqv] at ha hb ⊢
  simp only [qrat_add_num, qrat_add_den, Int.natCast_mul]
  rw [Int.add_mul, Int.add_mul]
  have l1 : a.num * (b.den : Int) * ((a'.den : Int) * (b'.den : Int)) =
      a'.num * (a.den : Int) * ((b.den : Int) * (b'.den : Int)) := by
    calc a.num * (b.den : Int) * ((a'.den : Int) * (b'.den : Int))
        = (a.num * (a'.den : Int)) * ((b.den : Int) * (b'.den : Int)) := by ac_rfl
      _ = (a'.num * (a.den : Int)) * ((b.den : Int) * (b'.den : Int)) := by rw [ha]
      _ = a'.num * (a.den : Int) * ((b.den : Int) * (b'.den : Int)) := rfl
  have l2 : b.num * (a.den : Int) * ((a'.den : Int) * (b'.den : Int)) =
      b'.num * (b.den : Int) * ((a.den : Int) * (a'.den : Int)) := by
    calc b.num * (a.den : Int) * ((a'.den : Int) * (b'.den : Int))
        = (b.num * (b'.den : Int)) * ((a.den : Int) * (a'.den : Int)) := by ac_rfl
      _ = (b'.num * (b.den : Int)) * ((a.den : Int) * (a'.den : Int)) := by rw [hb]
      _ = b'.num * (b.den : Int) * ((a.den : Int) * (a'.den : Int)) := rfl
  have r1 : a'.num * (b'.den : Int) * ((a.den : Int) * (b.den : Int)) =
      a'.num * (a.den : Int) * ((b.den : Int) * (b'.den : Int)) := by ac_rfl
  have r2 : b'.num * (a'.den : Int) * ((a.den : Int) * (b.den : Int)) =
      b'.num * (b.den : Int) * ((a.den : Int) * (a'.den : Int)) := by ac_rfl
  rw [l1, l2, r1, r2]

private theorem qrat_mul_eqv_congr {a a' b b' : QRat}
    (ha : QRat.eqv a a') (hb : QRat.eqv b b') :
    QRat.eqv (a * b) (a' * b') := by
  dsimp [QRat.eqv] at ha hb ⊢
  simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
  calc a.num * b.num * ((a'.den : Int) * (b'.den : Int))
      = (a.num * (a'.den : Int)) * (b.num * (b'.den : Int)) := by ac_rfl
    _ = (a'.num * (a.den : Int)) * (b'.num * (b.den : Int)) := by rw [ha, hb]
    _ = a'.num * b'.num * ((a.den : Int) * (b.den : Int)) := by ac_rfl

private theorem qrat_neg_eqv_congr {a a' : QRat} (ha : QRat.eqv a a') :
    QRat.eqv (-a) (-a') := by
  dsimp [QRat.eqv] at ha ⊢
  simp only [qrat_neg_num, qrat_neg_den, Int.neg_mul]
  omega

private theorem qrat_sub_eqv_congr {a a' b b' : QRat}
    (ha : QRat.eqv a a') (hb : QRat.eqv b b') :
    QRat.eqv (a - b) (a' - b') := by
  have hs1 : QRat.eqv (a - b) (a + (-b)) := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den,
      qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]
  have hs2 : QRat.eqv (a' + (-b')) (a' - b') := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den,
      qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]
  exact qrat_eqv_trans hs1
    (qrat_eqv_trans (qrat_add_eqv_congr ha (qrat_neg_eqv_congr hb)) hs2)

theorem qrat_add_comm_eqv (a b : QRat) : QRat.eqv (a + b) (b + a) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, Int.natCast_mul]
  rw [Int.add_mul, Int.add_mul]
  have t1 : a.num * (b.den : Int) * ((b.den : Int) * (a.den : Int)) =
      a.num * (a.den : Int) * ((b.den : Int) * (b.den : Int)) := by ac_rfl
  have t2 : b.num * (a.den : Int) * ((b.den : Int) * (a.den : Int)) =
      b.num * (b.den : Int) * ((a.den : Int) * (a.den : Int)) := by ac_rfl
  have t3 : b.num * (a.den : Int) * ((a.den : Int) * (b.den : Int)) =
      b.num * (b.den : Int) * ((a.den : Int) * (a.den : Int)) := by ac_rfl
  have t4 : a.num * (b.den : Int) * ((a.den : Int) * (b.den : Int)) =
      a.num * (a.den : Int) * ((b.den : Int) * (b.den : Int)) := by ac_rfl
  rw [t1, t2, t3, t4, Int.add_comm]

theorem qrat_add_assoc_eqv (a b c : QRat) : QRat.eqv ((a + b) + c) (a + (b + c)) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, Int.natCast_mul]
  rw [Int.add_mul, Int.add_mul, Int.add_mul, Int.add_mul]
  have l1 : a.num * (b.den : Int) * (c.den : Int) *
      ((a.den : Int) * ((b.den : Int) * (c.den : Int))) =
      a.num * ((b.den : Int) * (c.den : Int)) *
        ((a.den : Int) * (b.den : Int) * (c.den : Int)) := by ac_rfl
  have l2 : b.num * (a.den : Int) * (c.den : Int) *
      ((a.den : Int) * ((b.den : Int) * (c.den : Int))) =
      b.num * (c.den : Int) * (a.den : Int) *
        ((a.den : Int) * (b.den : Int) * (c.den : Int)) := by ac_rfl
  have l3 : c.num * ((a.den : Int) * (b.den : Int)) *
      ((a.den : Int) * ((b.den : Int) * (c.den : Int))) =
      c.num * (b.den : Int) * (a.den : Int) *
        ((a.den : Int) * (b.den : Int) * (c.den : Int)) := by ac_rfl
  rw [l1, l2, l3, Int.add_assoc]
  congr 1
  rw [← Int.add_mul]
  congr 1
  rw [← Int.add_mul]

theorem qrat_mul_add_eqv (a b c : QRat) : QRat.eqv (a * (b + c)) (a * b + a * c) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den, Int.natCast_mul]
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  have l1 : a.num * (b.num * (c.den : Int)) * ((a.den : Int) * (b.den : Int) *
      ((a.den : Int) * (c.den : Int))) =
      a.num * b.num * ((a.den : Int) * (c.den : Int)) *
        ((a.den : Int) * ((b.den : Int) * (c.den : Int))) := by ac_rfl
  have l2 : a.num * (c.num * (b.den : Int)) * ((a.den : Int) * (b.den : Int) *
      ((a.den : Int) * (c.den : Int))) =
      a.num * c.num * ((a.den : Int) * (b.den : Int)) *
        ((a.den : Int) * ((b.den : Int) * (c.den : Int))) := by ac_rfl
  rw [l1, l2]

theorem qrat_add_le_add {a b c d : QRat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  change (a.num * (c.den : Int) + c.num * (a.den : Int)) * ((b.den * d.den : Nat) : Int) ≤
    (b.num * (d.den : Int) + d.num * (b.den : Int)) * ((a.den * c.den : Nat) : Int)
  change a.num * (b.den : Int) ≤ b.num * (a.den : Int) at hab
  change c.num * (d.den : Int) ≤ d.num * (c.den : Int) at hcd
  have hbc : (0 : Int) ≤ (c.den : Int) * (d.den : Int) :=
    Int.mul_nonneg (Int.le_of_lt (qrat_den_pos_int c)) (Int.le_of_lt (qrat_den_pos_int d))
  have had : (0 : Int) ≤ (a.den : Int) * (b.den : Int) :=
    Int.mul_nonneg (Int.le_of_lt (qrat_den_pos_int a)) (Int.le_of_lt (qrat_den_pos_int b))
  have h1 := Int.mul_le_mul_of_nonneg_right hab hbc
  have h2 := Int.mul_le_mul_of_nonneg_right hcd had
  simp only [Int.natCast_mul]
  have l1 : (a.num * (c.den : Int) + c.num * (a.den : Int)) * ((b.den : Int) * (d.den : Int)) =
      a.num * (b.den : Int) * ((c.den : Int) * (d.den : Int)) +
      c.num * (d.den : Int) * ((a.den : Int) * (b.den : Int)) := by
    rw [Int.add_mul]
    have t1 : a.num * (c.den : Int) * ((b.den : Int) * (d.den : Int)) =
        a.num * (b.den : Int) * ((c.den : Int) * (d.den : Int)) := by ac_rfl
    have t2 : c.num * (a.den : Int) * ((b.den : Int) * (d.den : Int)) =
        c.num * (d.den : Int) * ((a.den : Int) * (b.den : Int)) := by ac_rfl
    rw [t1, t2]
  have r1 : (b.num * (d.den : Int) + d.num * (b.den : Int)) * ((a.den : Int) * (c.den : Int)) =
      b.num * (a.den : Int) * ((c.den : Int) * (d.den : Int)) +
      d.num * (c.den : Int) * ((a.den : Int) * (b.den : Int)) := by
    rw [Int.add_mul]
    have t1 : b.num * (d.den : Int) * ((a.den : Int) * (c.den : Int)) =
        b.num * (a.den : Int) * ((c.den : Int) * (d.den : Int)) := by ac_rfl
    have t2 : d.num * (b.den : Int) * ((a.den : Int) * (c.den : Int)) =
        d.num * (c.den : Int) * ((a.den : Int) * (b.den : Int)) := by ac_rfl
    rw [t1, t2]
  rw [l1, r1]
  exact Int.add_le_add h1 h2

theorem qrat_sub_le_sub {a b c d : QRat} (hab : a ≤ b) (hdc : d ≤ c) :
    a - c ≤ b - d := by
  have hneg : -c ≤ -d := by
    change (-c.num) * (d.den : Int) ≤ (-d.num) * (c.den : Int)
    change d.num * (c.den : Int) ≤ c.num * (d.den : Int) at hdc
    simp only [Int.neg_mul]
    omega
  have heqvL : QRat.eqv (a - c) (a + (-c)) := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den,
      qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]
  have heqvR : QRat.eqv (b - d) (b + (-d)) := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den,
      qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]
  exact qrat_le_of_eqv_left (qrat_eqv_symm heqvL)
    (qrat_le_of_eqv_right (qrat_eqv_symm heqvR) (qrat_add_le_add hab hneg))

theorem qrat_zero_le_sub_iff (a b : QRat) :
    QRat.ofInt 0 ≤ b - a ↔ a ≤ b := by
  change (0 : Int) * ((b.den * a.den : Nat) : Int) ≤
    (b.num * (a.den : Int) - a.num * (b.den : Int)) * 1 ↔
    a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  simp only [Int.zero_mul, Int.mul_one]
  exact ⟨fun h => Int.sub_nonneg.mp h, fun h => Int.sub_nonneg.mpr h⟩

theorem qrat_le_of_zero_le_add_neg {x y : QRat} (h : QRat.ofInt 0 ≤ x + (-y)) :
    y ≤ x := by
  have heqv : QRat.eqv (x + (-y)) (x - y) := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den,
      qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]
  exact (qrat_zero_le_sub_iff y x).mp (qrat_le_of_eqv_right heqv h)

theorem qrat_nonneg_iff (a : QRat) : QRat.ofInt 0 ≤ a ↔ 0 ≤ a.num := by
  change (0 : Int) * (a.den : Int) ≤ a.num * (1 : Int) ↔ 0 ≤ a.num
  simp

theorem qrat_pos_iff (a : QRat) : QRat.ofInt 0 < a ↔ 0 < a.num := by
  change (0 : Int) * (a.den : Int) < a.num * (1 : Int) ↔ 0 < a.num
  simp

theorem qrat_mul_nonneg {a b : QRat} (ha : QRat.ofInt 0 ≤ a) (hb : QRat.ofInt 0 ≤ b) :
    QRat.ofInt 0 ≤ a * b := by
  rw [qrat_nonneg_iff] at ha hb ⊢
  exact Int.mul_nonneg ha hb

theorem qrat_mul_pos {a b : QRat} (ha : QRat.ofInt 0 < a) (hb : QRat.ofInt 0 < b) :
    QRat.ofInt 0 < a * b := by
  rw [qrat_pos_iff] at ha hb ⊢
  exact Int.mul_pos ha hb

theorem qrat_mul_le_mul_of_nonneg_left {a b c : QRat}
    (hab : a ≤ b) (hc : QRat.ofInt 0 ≤ c) : c * a ≤ c * b := by
  change (c.num * a.num) * ((c.den * b.den : Nat) : Int) ≤
    (c.num * b.num) * ((c.den * a.den : Nat) : Int)
  change a.num * (b.den : Int) ≤ b.num * (a.den : Int) at hab
  rw [qrat_nonneg_iff] at hc
  have hcd : (0 : Int) ≤ c.num * (c.den : Int) :=
    Int.mul_nonneg hc (Int.le_of_lt (qrat_den_pos_int c))
  simp only [Int.natCast_mul]
  have l1 : c.num * a.num * ((c.den : Int) * (b.den : Int)) =
      (a.num * (b.den : Int)) * (c.num * (c.den : Int)) := by ac_rfl
  have r1 : c.num * b.num * ((c.den : Int) * (a.den : Int)) =
      (b.num * (a.den : Int)) * (c.num * (c.den : Int)) := by ac_rfl
  rw [l1, r1]
  exact Int.mul_le_mul_of_nonneg_right hab hcd

theorem qrat_mul_le_mul_of_nonneg_right {a b c : QRat}
    (hab : a ≤ b) (hc : QRat.ofInt 0 ≤ c) : a * c ≤ b * c := by
  have hcL : QRat.eqv (a * c) (c * a) := by
    dsimp [QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
    ac_rfl
  have hcR : QRat.eqv (b * c) (c * b) := by
    dsimp [QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
    ac_rfl
  exact qrat_le_of_eqv_left (qrat_eqv_symm hcL)
    (qrat_le_of_eqv_right (qrat_eqv_symm hcR) (qrat_mul_le_mul_of_nonneg_left hab hc))

theorem qrat_sq_nonneg (a : QRat) : QRat.ofInt 0 ≤ a * a := by
  rw [qrat_nonneg_iff]
  change 0 ≤ a.num * a.num
  if ha : 0 ≤ a.num then
    exact Int.mul_nonneg ha ha
  else
    have hna : 0 ≤ -a.num := by omega
    have hm := Int.mul_nonneg hna hna
    have heq : (-a.num) * (-a.num) = a.num * a.num := by
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

theorem qrat_abs_nonneg (a : QRat) : QRat.ofInt 0 ≤ QRat.abs a := by
  rw [qrat_nonneg_iff]
  exact Int.natCast_nonneg _

theorem qrat_abs_sq_eqv (a : QRat) : QRat.eqv (QRat.abs a * QRat.abs a) (a * a) := by
  dsimp [QRat.eqv]
  simp only [qrat_mul_num, qrat_mul_den, qrat_abs_num, qrat_abs_den]
  have hsq : (a.num.natAbs : Int) * (a.num.natAbs : Int) = a.num * a.num := by
    rcases Int.natAbs_eq a.num with h | h
    · have h' : (a.num.natAbs : Int) = a.num := by omega
      rw [h']
    · have h' : (a.num.natAbs : Int) = -a.num := by omega
      rw [h']
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  rw [hsq]

private theorem qrat_div_pos {a b : QRat} (ha : QRat.ofInt 0 < a) (hb : QRat.ofInt 0 < b) :
    QRat.ofInt 0 < QRat.div a b (by rw [qrat_pos_iff] at hb; omega) := by
  rw [qrat_pos_iff] at ha hb ⊢
  rw [qrat_div_pos_num a b _ hb]
  exact Int.mul_pos ha (qrat_den_pos_int b)

theorem qrat_div_mul_cancel_eqv (a b : QRat) (hb : b.num ≠ 0) :
    QRat.eqv (QRat.div a b hb * b) a := by
  dsimp [QRat.eqv, QRat.div]
  split
  case isTrue hpos =>
    simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
    have habs : (b.num.natAbs : Int) = b.num := Int.natAbs_of_nonneg (by omega)
    rw [habs]
    ac_rfl
  case isFalse hnon =>
    simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul, Int.neg_mul]
    have habs : (b.num.natAbs : Int) = -b.num := by
      rcases Int.natAbs_eq b.num with h | h <;> omega
    rw [habs]
    simp only [Int.neg_mul, Int.mul_neg]
    ac_rfl

theorem qrat_le_div_of_mul_le {a b c : QRat}
    (hb : QRat.ofInt 0 < b) (hmul : a * b ≤ c) :
    a ≤ QRat.div c b (by rw [qrat_pos_iff] at hb; omega) := by
  have hb_pos := (qrat_pos_iff b).mp hb
  have hb_abs : (b.num.natAbs : Int) = b.num := Int.natAbs_of_nonneg (by omega)
  change (a.num * b.num) * (c.den : Int) ≤ c.num * ((a.den * b.den : Nat) : Int) at hmul
  change a.num * ((QRat.div c b _).den : Int) ≤ (QRat.div c b _).num * (a.den : Int)
  rw [qrat_div_pos_num c b _ hb_pos, qrat_div_pos_den c b _ hb_pos]
  simp only [Int.natCast_mul, hb_abs] at hmul ⊢
  have l' : a.num * ((c.den : Int) * b.num) = a.num * b.num * (c.den : Int) := by ac_rfl
  have r' : c.num * (b.den : Int) * (a.den : Int) =
      c.num * ((a.den : Int) * (b.den : Int)) := by ac_rfl
  rw [l', r']
  exact hmul

theorem qrat_div_le_of_le_mul {a b c : QRat}
    (hb : QRat.ofInt 0 < b) (hmul : c ≤ a * b) :
    QRat.div c b (by rw [qrat_pos_iff] at hb; omega) ≤ a := by
  have hb_pos := (qrat_pos_iff b).mp hb
  have hb_abs : (b.num.natAbs : Int) = b.num := Int.natAbs_of_nonneg (by omega)
  change c.num * ((a.den * b.den : Nat) : Int) ≤ (a.num * b.num) * (c.den : Int) at hmul
  change (QRat.div c b _).num * (a.den : Int) ≤ a.num * ((QRat.div c b _).den : Int)
  rw [qrat_div_pos_num c b _ hb_pos, qrat_div_pos_den c b _ hb_pos]
  simp only [Int.natCast_mul, hb_abs] at hmul ⊢
  have l' : c.num * (b.den : Int) * (a.den : Int) =
      c.num * ((a.den : Int) * (b.den : Int)) := by ac_rfl
  have r' : a.num * ((c.den : Int) * b.num) = a.num * b.num * (c.den : Int) := by ac_rfl
  rw [l', r']
  exact hmul

-- =============================================================================
-- 1. Constructive Dyadic-Octave Logarithm Envelope (octaveLnUpper36)
-- =============================================================================

/-- Certified 36-digit upper bound `(lnInterval36 2).hi` for `ln(2) * 10^36`. -/
def ln2Upper36Scaled : Int :=
  693147180559945309417232121458176622

/-- Certified 36-digit rational upper bound for `ln(2)`. -/
def ln2Upper36QRat : QRat :=
  QRat.mk' ln2Upper36Scaled (10 ^ 36) (by decide)

/-- Dyadic-octave integer upper bound `(Nat.log2 t + 1) * ln2Upper36Scaled ≥ ln(t) * 10^36`. -/
def octaveLnUpper36 (t : Nat) : Int :=
  ((Nat.log2 t + 1 : Nat) : Int) * ln2Upper36Scaled

/-- Rational dyadic-octave upper bound `(Nat.log2 t + 1) * ln2Upper36QRat ≥ ln(t)`. -/
def octaveLnUpper36QRat (t : Nat) : QRat :=
  QRat.mk' (octaveLnUpper36 t) (10 ^ 36) (by decide)

/-- Theorem (Dyadic Octave Bracket):
For every height `t ≥ 2`, `k := Nat.log2 t ≥ 1` satisfies `2^k ≤ t < 2^(k + 1)`. -/
theorem octave_bracket_pow2 (t : Nat) (ht : 2 ≤ t) :
    2 ^ Nat.log2 t ≤ t ∧ t < 2 ^ (Nat.log2 t + 1) ∧ 1 ≤ Nat.log2 t := by
  have hnz : t ≠ 0 := by omega
  have h1 : 2 ^ Nat.log2 t ≤ t := Nat.log2_self_le hnz
  have h2 : t < 2 ^ (Nat.log2 t + 1) := (Nat.log2_lt hnz).mp (Nat.lt_succ_self _)
  have h3 : 1 ≤ Nat.log2 t := (Nat.le_log2 hnz).mpr (by simpa using ht)
  exact ⟨h1, h2, h3⟩

/-- Theorem (Positivity of Dyadic-Octave Log Upper Bound):
For all `t : Nat`, `octaveLnUpper36 t ≥ ln2Upper36Scaled > 0` in both `Int` and `QRat`. -/
theorem octaveLnUpper36_pos (t : Nat) :
    0 < octaveLnUpper36 t ∧ QRat.ofInt 0 < octaveLnUpper36QRat t ∧
    ln2Upper36Scaled ≤ octaveLnUpper36 t := by
  have hge1 : (1 : Int) ≤ ((Nat.log2 t + 1 : Nat) : Int) := by omega
  have hpos2 : (0 : Int) < ln2Upper36Scaled := by decide
  have hle : ln2Upper36Scaled ≤ octaveLnUpper36 t := by
    dsimp [octaveLnUpper36]
    calc ln2Upper36Scaled = (1 : Int) * ln2Upper36Scaled := (Int.one_mul _).symm
      _ ≤ ((Nat.log2 t + 1 : Nat) : Int) * ln2Upper36Scaled :=
        Int.mul_le_mul_of_nonneg_right hge1 (Int.le_of_lt hpos2)
  have hpos : 0 < octaveLnUpper36 t := Int.lt_of_lt_of_le hpos2 hle
  have hq : QRat.ofInt 0 < octaveLnUpper36QRat t := by
    rw [qrat_pos_iff]
    exact hpos
  exact ⟨hpos, hq, hle⟩

/-- Theorem (Monotonicity of Dyadic-Octave Log Upper Bound):
For `m ≤ n`, `octaveLnUpper36 m ≤ octaveLnUpper36 n` in both `Int` and `QRat`. -/
theorem octaveLnUpper36_mono (m n : Nat) (hmn : m ≤ n) :
    octaveLnUpper36 m ≤ octaveLnUpper36 n ∧
    octaveLnUpper36QRat m ≤ octaveLnUpper36QRat n := by
  have hlog : Nat.log2 m ≤ Nat.log2 n := by
    if hm : m = 0 then
      subst hm
      have hz : Nat.log2 0 = 0 := by rw [Nat.log2]; decide
      rw [hz]
      exact Nat.zero_le _
    else
      have hn : n ≠ 0 := by omega
      exact (Nat.le_log2 hn).mpr (Nat.le_trans (Nat.log2_self_le hm) hmn)
  have hsucc : ((Nat.log2 m + 1 : Nat) : Int) ≤ ((Nat.log2 n + 1 : Nat) : Int) := by omega
  have hpos2 : (0 : Int) ≤ ln2Upper36Scaled := by decide
  have hint : octaveLnUpper36 m ≤ octaveLnUpper36 n := by
    dsimp [octaveLnUpper36]
    exact Int.mul_le_mul_of_nonneg_right hsucc hpos2
  have hq : octaveLnUpper36QRat m ≤ octaveLnUpper36QRat n := by
    change octaveLnUpper36 m * ((10 ^ 36 : Nat) : Int) ≤
      octaveLnUpper36 n * ((10 ^ 36 : Nat) : Int)
    exact Int.mul_le_mul_of_nonneg_right hint (by decide)
  exact ⟨hint, hq⟩

/-- Concrete envelope checks: `ln2Upper36QRat < 7/10` and `octaveLnUpper36 16 = 5 * ln2`. -/
theorem ln2Upper36_envelope_certs :
    ln2Upper36QRat < QRat.mk' 7 10 ∧
    octaveLnUpper36 16 = 5 * ln2Upper36Scaled := by
  have hlo : 4 ≤ Nat.log2 16 := (Nat.le_log2 (by decide)).mpr (by decide)
  have hhi : Nat.log2 16 < 5 := (Nat.log2_lt (by decide)).mpr (by decide)
  have hlog : Nat.log2 16 = 4 := by omega
  refine ⟨by decide, ?_⟩
  unfold octaveLnUpper36
  rw [hlog, show ((4 + 1 : Nat) : Int) = 5 from rfl]

-- =============================================================================
-- 2. 3-4-1 Trigonometric Positivity & de la Vallee Poussin Zero-Free Region
-- =============================================================================

/-- Algebraic identity: `3 + 4 c + (2 c^2 - 1) = 2 (1 + c)^2` (`cos 2θ = 2 cos^2 θ - 1`). -/
theorem trig_341_identity (c : Int) :
    3 + 4 * c + (2 * c * c - 1) = 2 * (1 + c) * (1 + c) := by
  calc
    3 + 4 * c + (2 * c * c - 1) = 2 + 4 * c + 2 * c * c := by omega
    _ = (2 + 2 * c) * 1 + (2 + 2 * c) * c := by
      rw [Int.mul_one, Int.add_mul]
      have hm : 2 * c * c = (2 * c) * c := rfl
      omega
    _ = (2 + 2 * c) * (1 + c) := by rw [← Int.mul_add]
    _ = 2 * (1 + c) * (1 + c) := by
      have h2 : 2 + 2 * c = 2 * (1 + c) := by rw [Int.mul_add, Int.mul_one]
      rw [h2]

/-- Constructive 3-4-1 positivity over `Int`: `3 + 4 c + (2 c^2 - 1) ≥ 0`. -/
theorem trig_341_positivity (c : Int) :
    0 ≤ 3 + 4 * c + (2 * c * c - 1) := by
  rw [trig_341_identity]
  have hsq : 0 ≤ (1 + c) * (1 + c) := by
    if hc : 0 ≤ 1 + c then
      exact Int.mul_nonneg hc hc
    else
      have hnc : 0 ≤ -(1 + c) := by omega
      have hm := Int.mul_nonneg hnc hnc
      have heq : (-(1 + c)) * (-(1 + c)) = (1 + c) * (1 + c) := by
        simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
  have hassoc : 2 * (1 + c) * (1 + c) = 2 * ((1 + c) * (1 + c)) := Int.mul_assoc _ _ _
  rw [hassoc]
  exact Int.mul_nonneg (by decide) hsq

/-- Constructive 3-4-1 positivity over `QRat`: `3 + 4 c + (2 c^2 - 1) ≥ 0`. -/
theorem trig_341_positivity_qrat (c : QRat) :
    QRat.ofInt 0 ≤
      QRat.ofInt 3 + QRat.ofInt 4 * c + (QRat.ofInt 2 * c * c - QRat.ofInt 1) := by
  have hc : 0 ≤ 3 * (c.den : Int) * (c.den : Int) + 4 * c.num * (c.den : Int) +
      (2 * c.num * c.num - (c.den : Int) * (c.den : Int)) := by
    have hsq : 0 ≤ (c.num + (c.den : Int)) * (c.num + (c.den : Int)) := by
      if hp : 0 ≤ c.num + (c.den : Int) then
        exact Int.mul_nonneg hp hp
      else
        have hnp : 0 ≤ -(c.num + (c.den : Int)) := by omega
        have hm := Int.mul_nonneg hnp hnp
        have heq : (-(c.num + (c.den : Int))) * (-(c.num + (c.den : Int))) =
            (c.num + (c.den : Int)) * (c.num + (c.den : Int)) := by
          simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
        omega
    have hid :
        3 * (c.den : Int) * (c.den : Int) + 4 * c.num * (c.den : Int) +
          (2 * c.num * c.num - (c.den : Int) * (c.den : Int)) =
        2 * ((c.num + (c.den : Int)) * (c.num + (c.den : Int))) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
      have t1 : (c.den : Int) * c.num = c.num * (c.den : Int) := Int.mul_comm _ _
      have a1 : 2 * c.num * c.num = 2 * (c.num * c.num) := Int.mul_assoc _ _ _
      have a2 : 3 * (c.den : Int) * (c.den : Int) = 3 * ((c.den : Int) * (c.den : Int)) :=
        Int.mul_assoc _ _ _
      have a3 : 4 * c.num * (c.den : Int) = 4 * (c.num * (c.den : Int)) := Int.mul_assoc _ _ _
      rw [t1, a1, a2, a3]
      omega
    rw [hid]
    exact Int.mul_nonneg (by decide) hsq
  rw [qrat_nonneg_iff]
  simp only [qrat_add_num, qrat_add_den, qrat_sub_num, qrat_sub_den, qrat_mul_num, qrat_mul_den,
    qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.one_mul, Int.mul_one]
  have heq :
      (3 * (c.den : Int) + 4 * c.num) * ((c.den : Int) * (c.den : Int)) +
        (2 * c.num * c.num - (c.den : Int) * (c.den : Int)) * (c.den : Int) =
      (c.den : Int) * (3 * (c.den : Int) * (c.den : Int) + 4 * c.num * (c.den : Int) +
        (2 * c.num * c.num - (c.den : Int) * (c.den : Int))) := by
    rw [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_sub]
    have t1 : (3 * (c.den : Int)) * ((c.den : Int) * (c.den : Int)) =
        (c.den : Int) * (3 * (c.den : Int) * (c.den : Int)) := by ac_rfl
    have t2 : (4 * c.num) * ((c.den : Int) * (c.den : Int)) =
        (c.den : Int) * (4 * c.num * (c.den : Int)) := by ac_rfl
    have t3 : (2 * c.num * c.num) * (c.den : Int) =
        (c.den : Int) * (2 * c.num * c.num) := by ac_rfl
    have t4 : ((c.den : Int) * (c.den : Int)) * (c.den : Int) =
        (c.den : Int) * ((c.den : Int) * (c.den : Int)) := by ac_rfl
    rw [t1, t2, t3, t4]
  have hd : 0 ≤ (c.den : Int) := Int.le_of_lt (qrat_den_pos_int c)
  have hcd := Int.mul_nonneg hd hc
  rw [heq]
  exact hcd

/-- Any finite Dirichlet cosine sum `∑ w_n (3 + 4 c_n + (2 c_n^2 - 1))` with non-negative
weights `w_n ≥ 0` is constructively non-negative. -/
theorem trig_341_dirichlet_weighted_sum_nonneg (terms : List (QRat × QRat))
    (hw : ∀ p ∈ terms, QRat.ofInt 0 ≤ p.1) :
    QRat.ofInt 0 ≤ terms.foldl
      (fun acc p => acc + p.1 * (QRat.ofInt 3 + QRat.ofInt 4 * p.2 +
        (QRat.ofInt 2 * p.2 * p.2 - QRat.ofInt 1)))
      (QRat.ofInt 0) := by
  let stepFn : QRat → QRat × QRat → QRat := fun acc p =>
    acc + p.1 * (QRat.ofInt 3 + QRat.ofInt 4 * p.2 +
      (QRat.ofInt 2 * p.2 * p.2 - QRat.ofInt 1))
  suffices h : ∀ (ts : List (QRat × QRat)) (init : QRat),
      QRat.ofInt 0 ≤ init → (∀ p ∈ ts, QRat.ofInt 0 ≤ p.1) →
      QRat.ofInt 0 ≤ ts.foldl stepFn init by
    exact h terms (QRat.ofInt 0) (qrat_le_refl _) hw
  intro ts
  induction ts with
  | nil =>
    intro init hinit _
    exact hinit
  | cons p rest ih =>
    intro init hinit hwp
    have hp : QRat.ofInt 0 ≤ p.1 := hwp p (List.Mem.head _)
    have htrig : QRat.ofInt 0 ≤ QRat.ofInt 3 + QRat.ofInt 4 * p.2 +
        (QRat.ofInt 2 * p.2 * p.2 - QRat.ofInt 1) :=
      trig_341_positivity_qrat p.2
    have hterm : QRat.ofInt 0 ≤ p.1 * (QRat.ofInt 3 + QRat.ofInt 4 * p.2 +
        (QRat.ofInt 2 * p.2 * p.2 - QRat.ofInt 1)) :=
      qrat_mul_nonneg hp htrig
    have hnext : QRat.ofInt 0 ≤ stepFn init p := by
      have hz : QRat.eqv (QRat.ofInt 0 + QRat.ofInt 0) (QRat.ofInt 0) := by decide
      exact qrat_le_of_eqv_left hz (qrat_add_le_add hinit hterm)
    have hrest : ∀ q ∈ rest, QRat.ofInt 0 ≤ q.1 := fun q hq => hwp q (List.Mem.tail _ hq)
    exact ih (stepFn init p) hnext hrest

/-- Explicit constructive de la Vallee Poussin constant `c_dvp = 1 / 56`. -/
def cDvp : QRat :=
  QRat.mk' 1 56 (by decide)

/-- Height threshold `t_0 = 16` (`Nat.log2 t ≥ 4`) for the explicit de la Vallee Poussin bound. -/
def dvpThresholdT0 : Nat := 16

/-- Constructive probe offset `δ(t) = 1 / (8 * octaveLnUpper36QRat t)`. -/
def dvpDelta (t : Nat) : QRat :=
  QRat.mk' (10 ^ 36) (8 * (Nat.log2 t + 1) * 693147180559945309417232121458176622) (by
    have h1 : 0 < 8 * (Nat.log2 t + 1) := Nat.mul_pos (by decide) (Nat.succ_pos _)
    exact Nat.mul_pos h1 (by decide))

private theorem dvpDelta_pos (t : Nat) : QRat.ofInt 0 < dvpDelta t := by
  rw [qrat_pos_iff]
  dsimp [dvpDelta, QRat.mk']
  decide

private theorem dvp_invDelta_eqv_8L (t : Nat)
    (hδne : (dvpDelta t).num ≠ 0) :
    QRat.eqv (QRat.div (QRat.ofInt 1) (dvpDelta t) hδne)
      (QRat.ofInt 8 * octaveLnUpper36QRat t) := by
  have hpos : (0 : Int) < (dvpDelta t).num := by
    dsimp [dvpDelta, QRat.mk']; decide
  dsimp [QRat.eqv]
  rw [qrat_div_pos_num _ _ hδne hpos, qrat_div_pos_den _ _ hδne hpos]
  dsimp [dvpDelta, octaveLnUpper36QRat, octaveLnUpper36, ln2Upper36Scaled]
  simp only [qrat_mul_num, qrat_mul_den, qrat_ofInt_num, qrat_ofInt_den, qrat_mk'_num, qrat_mk'_den,
    Int.natCast_mul, Int.one_mul]
  change (8 : Int) * ((Nat.log2 t + 1 : Nat) : Int) * 693147180559945309417232121458176622 *
      (1 * 1000000000000000000000000000000000000) =
    8 * (((Nat.log2 t + 1 : Nat) : Int) * 693147180559945309417232121458176622) *
      (1 * 1000000000000000000000000000000000000)
  ac_rfl

private theorem dvp_log_envelope_factor (k1 L2 S : Int)
    (hk_L2 : 5 * L2 ≤ k1 * L2) (h5 : 12 * S ≤ 20 * L2) (hSpos : 0 ≤ S) :
    ((3 * (2 * S) + 4 * (k1 * L2)) * (4 * (S * S)) +
      3 * (k1 * L2 * S + L2 * S) * (2 * S)) * S ≤
    4 * (k1 * L2) * (2 * S * (4 * (S * S))) := by
  have hnum_ineq : 3 * 4 * S + 8 * (k1 * L2) + 3 * (k1 * L2 + L2) ≤ 4 * (k1 * L2) * 4 := by
    omega
  have h2S2_nonneg : (0 : Int) ≤ 2 * (S * S) :=
    Int.mul_nonneg (by decide) (Int.mul_nonneg hSpos hSpos)
  have hmulS : 2 * (S * S) * (3 * 4 * S + 8 * (k1 * L2) + 3 * (k1 * L2 + L2)) ≤
      2 * (S * S) * (4 * (k1 * L2) * 4) :=
    Int.mul_le_mul_of_nonneg_left hnum_ineq h2S2_nonneg
  have hm2 := Int.mul_le_mul_of_nonneg_right hmulS hSpos
  have h1 : (3 * (2 * S) + 4 * (k1 * L2)) * (4 * (S * S)) * S =
      2 * (S * S) * (3 * 4 * S + 8 * (k1 * L2)) * S := by
    rw [Int.add_mul, Int.add_mul]
    rw [show 2 * (S * S) * (3 * 4 * S + 8 * (k1 * L2)) * S =
        2 * (S * S) * (3 * 4 * S) * S + 2 * (S * S) * (8 * (k1 * L2)) * S by
      rw [Int.mul_add, Int.add_mul]]
    congr 1
    · ac_rfl
    · rw [show (8 : Int) = 2 * 4 from rfl]
      ac_rfl
  have h2 : 3 * (k1 * L2 * S + L2 * S) * (2 * S) * S =
      2 * (S * S) * (3 * (k1 * L2 + L2)) * S := by
    rw [← Int.add_mul]
    ac_rfl
  have hLfactor :
      ((3 * (2 * S) + 4 * (k1 * L2)) * (4 * (S * S)) +
        3 * (k1 * L2 * S + L2 * S) * (2 * S)) * S =
      2 * (S * S) * (3 * 4 * S + 8 * (k1 * L2) + 3 * (k1 * L2 + L2)) * S := by
    rw [Int.add_mul, h1, h2]
    rw [← Int.add_mul, ← Int.mul_add]
  have hRfactor :
      4 * (k1 * L2) * (2 * S * (4 * (S * S))) =
      2 * (S * S) * (4 * (k1 * L2) * 4) * S := by
    ac_rfl
  rw [hLfactor, hRfactor]
  exact hm2

private theorem dvp_log_envelope_t0 (t : Nat) (ht : dvpThresholdT0 ≤ t) :
    QRat.ofInt 3 * QRat.ofInt 1 +
      QRat.ofInt 4 * (QRat.mk' 1 2 * octaveLnUpper36QRat t) +
      QRat.mk' 3 4 * (octaveLnUpper36QRat t + ln2Upper36QRat) ≤
    QRat.ofInt 4 * octaveLnUpper36QRat t := by
  have hk : 4 ≤ Nat.log2 t := by
    have hnz : t ≠ 0 := by dsimp [dvpThresholdT0] at ht; omega
    exact (Nat.le_log2 hnz).mpr (by dsimp [dvpThresholdT0] at ht; simpa using ht)
  have hk_int : (5 : Int) ≤ ((Nat.log2 t + 1 : Nat) : Int) := by omega
  rw [qrat_le_iff]
  simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den, qrat_ofInt_num, qrat_ofInt_den,
    qrat_mk'_num, qrat_mk'_den]
  dsimp [octaveLnUpper36QRat, octaveLnUpper36, ln2Upper36QRat, ln2Upper36Scaled]
  simp only [qrat_mk'_num, qrat_mk'_den, Int.mul_one, Int.one_mul]
  let k1 : Int := ((Nat.log2 t + 1 : Nat) : Int)
  let L2 : Int := 693147180559945309417232121458176622
  let S : Int := ((10 ^ 36 : Nat) : Int)
  have hk_L2 : 5 * L2 ≤ k1 * L2 :=
    Int.mul_le_mul_of_nonneg_right hk_int (by dsimp [L2]; decide)
  have h5 : 12 * S ≤ 20 * L2 := by dsimp [S, L2]; decide
  have hSpos : (0 : Int) ≤ S := by dsimp [S]; decide
  exact dvp_log_envelope_factor k1 L2 S hk_L2 h5 hSpos

private theorem qrat_sum_rearrange (A B1 B2 C D : QRat) :
    QRat.eqv ((A + B1) + (B2 + (-C)) + D) ((A + (B1 + B2 + D)) + (-C)) := by
  have s1 : QRat.eqv ((A + B1) + (B2 + (-C))) (((A + B1) + B2) + (-C)) :=
    qrat_eqv_symm (qrat_add_assoc_eqv (A + B1) B2 (-C))
  have s2 : QRat.eqv ((A + B1) + (B2 + (-C)) + D) ((((A + B1) + B2) + (-C)) + D) :=
    qrat_add_eqv_congr s1 (qrat_eqv_refl D)
  have s3 : QRat.eqv ((((A + B1) + B2) + (-C)) + D) (((A + B1) + B2) + ((-C) + D)) :=
    qrat_add_assoc_eqv ((A + B1) + B2) (-C) D
  have s4 : QRat.eqv (((A + B1) + B2) + ((-C) + D)) (((A + B1) + B2) + (D + (-C))) :=
    qrat_add_eqv_congr (qrat_eqv_refl _) (qrat_add_comm_eqv (-C) D)
  have s5 : QRat.eqv (((A + B1) + B2) + (D + (-C))) ((((A + B1) + B2) + D) + (-C)) :=
    qrat_eqv_symm (qrat_add_assoc_eqv ((A + B1) + B2) D (-C))
  have s6a : QRat.eqv ((A + B1) + B2 + D) (A + (B1 + B2) + D) :=
    qrat_add_eqv_congr (qrat_add_assoc_eqv A B1 B2) (qrat_eqv_refl D)
  have s6b : QRat.eqv (A + (B1 + B2) + D) (A + ((B1 + B2) + D)) :=
    qrat_add_assoc_eqv A (B1 + B2) D
  have s6 : QRat.eqv ((((A + B1) + B2) + D) + (-C)) ((A + (B1 + B2 + D)) + (-C)) :=
    qrat_add_eqv_congr (qrat_eqv_trans s6a s6b) (qrat_eqv_refl (-C))
  exact qrat_eqv_trans s2 (qrat_eqv_trans s3 (qrat_eqv_trans s4 (qrat_eqv_trans s5 s6)))

private theorem qrat_3_8_4_28 (L : QRat) :
    QRat.eqv (QRat.ofInt 3 * (QRat.ofInt 8 * L) + QRat.ofInt 4 * L) (QRat.ofInt 28 * L) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den,
    qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.one_mul]
  rw [Int.add_mul]
  have h1 : 3 * (8 * L.num) * (L.den : Int) * (L.den : Int) =
      24 * (L.num * ((L.den : Int) * (L.den : Int))) := by
    rw [show (24 : Int) = 3 * 8 from rfl]
    ac_rfl
  have h2 : 4 * L.num * (L.den : Int) * (L.den : Int) =
      4 * (L.num * ((L.den : Int) * (L.den : Int))) := by
    ac_rfl
  rw [h1, h2, ← Int.add_mul, show (24 : Int) + 4 = 28 from rfl]
  ac_rfl

private theorem qrat_sub_cancel_add_eqv (A β : QRat) :
    QRat.eqv ((A - β) + β) A := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_sub_num, qrat_sub_den, Int.natCast_mul]
  simp only [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul]
  rw [show A.num * (β.den : Int) * (β.den : Int) * (A.den : Int) =
      A.num * ((A.den : Int) * (β.den : Int) * (β.den : Int)) by ac_rfl]
  rw [show β.num * (A.den : Int) * (β.den : Int) * (A.den : Int) =
      β.num * ((A.den : Int) * (β.den : Int)) * (A.den : Int) by ac_rfl]
  omega

private theorem qrat_sub_add_assoc_eqv (A M β : QRat) :
    QRat.eqv ((A - M) - β) (A - (β + M)) := by
  dsimp [QRat.eqv]
  simp only [qrat_sub_num, qrat_sub_den, qrat_add_num, qrat_add_den, Int.natCast_mul]
  have hneg_add : ∀ a b : Int, -(a + b) = -a + -b := fun a b => by omega
  simp only [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul, hneg_add]
  ac_rfl

private theorem qrat_add_sub_assoc_eqv (x y z : QRat) :
    QRat.eqv ((x + y) - z) (x + (y - z)) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_sub_num, qrat_sub_den, Int.natCast_mul]
  simp only [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul]
  ac_rfl

private theorem qrat_add_neg_eqv_sub (x z : QRat) :
    QRat.eqv (x + (-z)) (x - z) := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_sub_num, qrat_sub_den,
    qrat_neg_num, qrat_neg_den, Int.neg_mul, Int.sub_eq_add_neg]

private theorem dvp_inv7L_eqv (L : QRat) (hLpos : QRat.ofInt 0 < L)
    (hLne : L.num ≠ 0) (h28Lne : (QRat.ofInt 28 * L).num ≠ 0) :
    QRat.eqv (QRat.div (QRat.ofInt 4) (QRat.ofInt 28 * L) h28Lne)
      (QRat.div (QRat.mk' 1 7 (by decide)) L hLne) := by
  have h1 : (0 : Int) < (QRat.ofInt 28 * L).num := by
    have h28 : QRat.ofInt 0 < QRat.ofInt 28 * L := qrat_mul_pos (by decide) hLpos
    exact (qrat_pos_iff _).mp h28
  have h2 : (0 : Int) < L.num := (qrat_pos_iff _).mp hLpos
  dsimp [QRat.eqv]
  rw [qrat_div_pos_num _ _ h28Lne h1, qrat_div_pos_den _ _ h28Lne h1,
    qrat_div_pos_num _ _ hLne h2, qrat_div_pos_den _ _ hLne h2]
  have ha1 : (((QRat.ofInt 28 * L).num).natAbs : Int) = 28 * L.num := by
    have hp : (QRat.ofInt 28 * L).num = 28 * L.num := rfl
    rw [hp]
    exact Int.natAbs_of_nonneg (Int.le_of_lt (by rw [← hp]; exact h1))
  have ha2 : (L.num.natAbs : Int) = L.num := Int.natAbs_of_nonneg (Int.le_of_lt h2)
  have hden28 : (((QRat.ofInt 28 * L).den) : Int) = (L.den : Int) := by
    simp only [qrat_mul_den, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.one_mul]
  simp only [qrat_ofInt_num, qrat_ofInt_den, qrat_mk'_num, qrat_mk'_den, Int.natCast_mul,
    Int.one_mul]
  rw [hden28, ha1, ha2]
  ac_rfl

private theorem dvp_inv8_sub_inv7_eqv (L : QRat) (hLpos : QRat.ofInt 0 < L)
    (hLne : L.num ≠ 0) :
    QRat.eqv (QRat.div (QRat.mk' 1 8 (by decide)) L hLne -
        QRat.div (QRat.mk' 1 7 (by decide)) L hLne)
      (-(QRat.div cDvp L hLne)) := by
  have hLp : (0 : Int) < L.num := (qrat_pos_iff _).mp hLpos
  dsimp [QRat.eqv]
  simp only [qrat_sub_num, qrat_sub_den, qrat_neg_num, qrat_neg_den]
  rw [qrat_div_pos_num _ _ hLne hLp, qrat_div_pos_den _ _ hLne hLp,
    qrat_div_pos_num _ _ hLne hLp, qrat_div_pos_den _ _ hLne hLp,
    qrat_div_pos_num _ _ hLne hLp, qrat_div_pos_den _ _ hLne hLp]
  dsimp [cDvp]
  simp only [qrat_mk'_num, qrat_mk'_den, Int.one_mul, Int.neg_mul]
  have ha : (L.num.natAbs : Int) = L.num := Int.natAbs_of_nonneg (Int.le_of_lt hLp)
  rw [ha]
  change ((L.den : Int) * (7 * L.num) - (L.den : Int) * (8 * L.num)) * ((56 : Int) * L.num) =
    -((L.den : Int) * ((8 * L.num) * (7 * L.num)))
  rw [← Int.mul_sub]
  rw [show (7 : Int) * L.num - (8 : Int) * L.num = -L.num by omega]
  simp only [Int.mul_neg, Int.neg_mul]
  ac_rfl

private theorem dvp_delta_eqv_inv8L (t : Nat) (hLne : (octaveLnUpper36QRat t).num ≠ 0)
    (hLpos : QRat.ofInt 0 < octaveLnUpper36QRat t) :
    QRat.eqv (dvpDelta t)
      (QRat.div (QRat.mk' 1 8 (by decide)) (octaveLnUpper36QRat t) hLne) := by
  have hL_num : 0 < (octaveLnUpper36QRat t).num := (qrat_pos_iff _).mp hLpos
  dsimp [QRat.eqv]
  rw [qrat_div_pos_num _ _ hLne hL_num, qrat_div_pos_den _ _ hLne hL_num]
  dsimp [dvpDelta, octaveLnUpper36QRat, octaveLnUpper36, ln2Upper36Scaled]
  simp only [qrat_mk'_num, qrat_mk'_den]
  have habs : ((((Nat.log2 t + 1 : Nat) : Int) *
      693147180559945309417232121458176622).natAbs : Int) =
      ((Nat.log2 t + 1 : Nat) : Int) * 693147180559945309417232121458176622 :=
    Int.natAbs_of_nonneg (Int.le_of_lt hL_num)
  simp only [Int.natCast_mul, Int.one_mul]
  change 1000000000000000000000000000000000000 *
      (8 * ((((Nat.log2 t + 1 : Nat) : Int) * 693147180559945309417232121458176622).natAbs : Int)) =
    1000000000000000000000000000000000000 *
      ((8 * ((Nat.log2 t + 1 : Nat) : Int) * 693147180559945309417232121458176622))
  rw [habs]
  ac_rfl

/-- Theorem (Explicit de la Vallee Poussin Asymptotic Zero-Free Region):
For every height `t ≥ t_0 = 16`, `c_dvp = 1/56 > 0` certifies the asymptotic zero-free strip:
any real zero coordinate `β` (`0 < gap := 1 + δ(t) - β`, `δ(t) = 1 / (8 L(t))`) satisfying
the 3-4-1 inequality `3 S0 + 4 S1 + S2 ≥ 0` and Hadamard/Jensen bounds `S0 ≤ 1/δ + 1`,
`S1 ≤ -1/gap + (1/2) L(t)`, and `S2 ≤ (3/4)(L(t) + ln2)` must satisfy
`β ≤ 1 - c_dvp / octaveLnUpper36QRat t < 1`.
Constructively proved with ZERO `Classical.choice` and ZERO `sorryAx`. -/
theorem dvp_asymptotic_zero_free_region (t : Nat) (ht : dvpThresholdT0 ≤ t)
    (β S0 S1 S2 : QRat)
    (hgap : QRat.ofInt 0 < QRat.ofInt 1 + dvpDelta t - β)
    (hpos341 : QRat.ofInt 0 ≤ QRat.ofInt 3 * S0 + QRat.ofInt 4 * S1 + S2)
    (hS0 : S0 ≤ QRat.div (QRat.ofInt 1) (dvpDelta t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (dvpDelta_pos t))) + QRat.ofInt 1)
    (hS1 : S1 ≤ -(QRat.div (QRat.ofInt 1) (QRat.ofInt 1 + dvpDelta t - β)
      (Int.ne_of_gt ((qrat_pos_iff _).mp hgap))) + QRat.mk' 1 2 * octaveLnUpper36QRat t)
    (hS2 : S2 ≤ QRat.mk' 3 4 * (octaveLnUpper36QRat t + ln2Upper36QRat)) :
    QRat.ofInt 0 < cDvp ∧
    β ≤ QRat.ofInt 1 - QRat.div cDvp (octaveLnUpper36QRat t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (octaveLnUpper36_pos t).2.1)) ∧
    β < QRat.ofInt 1 := by
  let L := octaveLnUpper36QRat t
  let δ := dvpDelta t
  let gap := QRat.ofInt 1 + δ - β
  have hLpos : QRat.ofInt 0 < L := (octaveLnUpper36_pos t).2.1
  have hLne : L.num ≠ 0 := Int.ne_of_gt ((qrat_pos_iff _).mp hLpos)
  have hδpos : QRat.ofInt 0 < δ := dvpDelta_pos t
  have hδne : δ.num ≠ 0 := Int.ne_of_gt ((qrat_pos_iff _).mp hδpos)
  have hgne : gap.num ≠ 0 := Int.ne_of_gt ((qrat_pos_iff _).mp hgap)
  let invδ := QRat.div (QRat.ofInt 1) δ hδne
  let invGap := QRat.div (QRat.ofInt 1) gap hgne
  have h3S0 : QRat.ofInt 3 * S0 ≤ QRat.ofInt 3 * (invδ + QRat.ofInt 1) :=
    qrat_mul_le_mul_of_nonneg_left hS0 (by decide)
  have h4S1 : QRat.ofInt 4 * S1 ≤ QRat.ofInt 4 * (-invGap + QRat.mk' 1 2 * L) :=
    qrat_mul_le_mul_of_nonneg_left hS1 (by decide)
  have hsum :
      QRat.ofInt 0 ≤
        QRat.ofInt 3 * (invδ + QRat.ofInt 1) +
        QRat.ofInt 4 * (-invGap + QRat.mk' 1 2 * L) +
        QRat.mk' 3 4 * (L + ln2Upper36QRat) :=
    qrat_le_trans hpos341 (qrat_add_le_add (qrat_add_le_add h3S0 h4S1) hS2)
  have h4neg : QRat.eqv (QRat.ofInt 4 * (-invGap)) (-(QRat.ofInt 4 * invGap)) := by
    dsimp [QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, qrat_neg_num, qrat_neg_den, Int.mul_neg, Int.neg_mul]
  have ha_eq : QRat.eqv (QRat.ofInt 3 * (invδ + QRat.ofInt 1))
      (QRat.ofInt 3 * invδ + QRat.ofInt 3 * QRat.ofInt 1) := qrat_mul_add_eqv _ _ _
  have hb_eq : QRat.eqv (QRat.ofInt 4 * (-invGap + QRat.mk' 1 2 * L))
      (QRat.ofInt 4 * (QRat.mk' 1 2 * L) + (-(QRat.ofInt 4 * invGap))) :=
    qrat_eqv_trans (qrat_mul_add_eqv _ _ _)
      (qrat_eqv_trans (qrat_add_comm_eqv _ _)
        (qrat_add_eqv_congr (qrat_eqv_refl _) h4neg))
  have hfront := qrat_add_eqv_congr (qrat_add_eqv_congr ha_eq hb_eq)
    (qrat_eqv_refl (QRat.mk' 3 4 (by decide) * (L + ln2Upper36QRat)))
  have hrear := qrat_sum_rearrange (QRat.ofInt 3 * invδ) (QRat.ofInt 3 * QRat.ofInt 1)
    (QRat.ofInt 4 * (QRat.mk' 1 2 * L)) (QRat.ofInt 4 * invGap)
    (QRat.mk' 3 4 * (L + ln2Upper36QRat))
  have h0le := qrat_le_of_eqv_right (qrat_eqv_trans hfront hrear) hsum
  have h4invGap_raw := qrat_le_of_zero_le_add_neg h0le
  have henv := dvp_log_envelope_t0 t ht
  have h4invGap_step : QRat.ofInt 4 * invGap ≤ QRat.ofInt 3 * invδ + QRat.ofInt 4 * L :=
    qrat_le_trans h4invGap_raw (qrat_add_le_add (qrat_le_refl _) henv)
  have hinvδ_eq : QRat.eqv invδ (QRat.ofInt 8 * L) := dvp_invDelta_eqv_8L t hδne
  have h3invδ_eq : QRat.eqv (QRat.ofInt 3 * invδ + QRat.ofInt 4 * L) (QRat.ofInt 28 * L) := by
    have h1 := qrat_add_eqv_congr (qrat_mul_eqv_congr (qrat_eqv_refl (QRat.ofInt 3)) hinvδ_eq)
      (qrat_eqv_refl (QRat.ofInt 4 * L))
    exact qrat_eqv_trans h1 (qrat_3_8_4_28 L)
  have h4invGap : QRat.ofInt 4 * invGap ≤ QRat.ofInt 28 * L :=
    qrat_le_of_eqv_right h3invδ_eq h4invGap_step
  have hmul_gap : (QRat.ofInt 4 * invGap) * gap ≤ (QRat.ofInt 28 * L) * gap :=
    qrat_mul_le_mul_of_nonneg_right h4invGap (qrat_le_of_lt hgap)
  have hcancel : QRat.eqv ((QRat.ofInt 4 * invGap) * gap) (QRat.ofInt 4) := by
    have hassoc : QRat.eqv ((QRat.ofInt 4 * invGap) * gap) (QRat.ofInt 4 * (invGap * gap)) := by
      dsimp [QRat.eqv]
      simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
      ac_rfl
    have hg1 : QRat.eqv (invGap * gap) (QRat.ofInt 1) :=
      qrat_div_mul_cancel_eqv (QRat.ofInt 1) gap hgne
    have hm1 : QRat.eqv (QRat.ofInt 4 * QRat.ofInt 1) (QRat.ofInt 4) := by decide
    exact qrat_eqv_trans hassoc (qrat_eqv_trans (qrat_mul_eqv_congr (qrat_eqv_refl _) hg1) hm1)
  have h4_le : QRat.ofInt 4 ≤ (QRat.ofInt 28 * L) * gap :=
    qrat_le_of_eqv_left hcancel hmul_gap
  have h28Lpos : QRat.ofInt 0 < QRat.ofInt 28 * L := qrat_mul_pos (by decide) hLpos
  have hgap_ge_raw : QRat.div (QRat.ofInt 4) (QRat.ofInt 28 * L)
      (Int.ne_of_gt ((qrat_pos_iff _).mp h28Lpos)) ≤ gap := by
    have hcomm : QRat.eqv ((QRat.ofInt 28 * L) * gap) (gap * (QRat.ofInt 28 * L)) := by
      dsimp [QRat.eqv]
      simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
      ac_rfl
    exact qrat_div_le_of_le_mul h28Lpos (qrat_le_of_eqv_right hcomm h4_le)
  have hinv7L_eq : QRat.eqv (QRat.div (QRat.ofInt 4) (QRat.ofInt 28 * L)
      (Int.ne_of_gt ((qrat_pos_iff _).mp h28Lpos)))
      (QRat.div (QRat.mk' 1 7 (by decide)) L hLne) :=
    dvp_inv7L_eqv L hLpos hLne (Int.ne_of_gt ((qrat_pos_iff _).mp h28Lpos))
  have hinv7L_le_gap : QRat.div (QRat.mk' 1 7 (by decide)) L hLne ≤ gap :=
    qrat_le_of_eqv_left hinv7L_eq hgap_ge_raw
  have hβ_raw : β ≤ (QRat.ofInt 1 + δ) - QRat.div (QRat.mk' 1 7 (by decide)) L hLne := by
    have h1 := qrat_add_le_add hinv7L_le_gap (qrat_le_refl β)
    have hg_eq : QRat.eqv (gap + β) (QRat.ofInt 1 + δ) :=
      qrat_sub_cancel_add_eqv (QRat.ofInt 1 + δ) β
    have h2 : QRat.div (QRat.mk' 1 7 (by decide)) L hLne + β ≤ QRat.ofInt 1 + δ :=
      qrat_le_of_eqv_right hg_eq h1
    have h4 :
        QRat.ofInt 0 ≤ ((QRat.ofInt 1 + δ) - QRat.div (QRat.mk' 1 7 (by decide)) L hLne) - β := by
      have hcomm : QRat.eqv (QRat.div (QRat.mk' 1 7 (by decide)) L hLne + β)
          (β + QRat.div (QRat.mk' 1 7 (by decide)) L hLne) := qrat_add_comm_eqv _ _
      have h2' := qrat_le_of_eqv_left hcomm h2
      have hd := qrat_sub_add_assoc_eqv (QRat.ofInt 1 + δ)
        (QRat.div (QRat.mk' 1 7 (by decide)) L hLne) β
      exact qrat_le_of_eqv_right (qrat_eqv_symm hd) ((qrat_zero_le_sub_iff _ _).mpr h2')
    exact (qrat_zero_le_sub_iff _ _).mp h4
  have hident : QRat.eqv
      ((QRat.ofInt 1 + δ) - QRat.div (QRat.mk' 1 7 (by decide)) L hLne)
      (QRat.ofInt 1 - QRat.div cDvp L hLne) := by
    have hδ8_eq : QRat.eqv δ (QRat.div (QRat.mk' 1 8 (by decide)) L hLne) :=
      dvp_delta_eqv_inv8L t hLne hLpos
    have hc_eq : QRat.eqv
        (QRat.div (QRat.mk' 1 8 (by decide)) L hLne - QRat.div (QRat.mk' 1 7 (by decide)) L hLne)
        (-(QRat.div cDvp L hLne)) :=
      dvp_inv8_sub_inv7_eqv L hLpos hLne
    have hs1 : QRat.eqv ((QRat.ofInt 1 + δ) - QRat.div (QRat.mk' 1 7 (by decide)) L hLne)
        ((QRat.ofInt 1 + QRat.div (QRat.mk' 1 8 (by decide)) L hLne) -
          QRat.div (QRat.mk' 1 7 (by decide)) L hLne) :=
      qrat_sub_eqv_congr (qrat_add_eqv_congr (qrat_eqv_refl _) hδ8_eq) (qrat_eqv_refl _)
    have hs2 := qrat_add_sub_assoc_eqv (QRat.ofInt 1)
      (QRat.div (QRat.mk' 1 8 (by decide)) L hLne)
      (QRat.div (QRat.mk' 1 7 (by decide)) L hLne)
    have hs3 : QRat.eqv
        (QRat.ofInt 1 +
          (QRat.div (QRat.mk' 1 8 (by decide)) L hLne - QRat.div (QRat.mk' 1 7 (by decide)) L hLne))
        (QRat.ofInt 1 + (-(QRat.div cDvp L hLne))) :=
      qrat_add_eqv_congr (qrat_eqv_refl _) hc_eq
    have hs4 := qrat_add_neg_eqv_sub (QRat.ofInt 1) (QRat.div cDvp L hLne)
    exact qrat_eqv_trans hs1 (qrat_eqv_trans hs2 (qrat_eqv_trans hs3 hs4))
  have hβ_zfr : β ≤ QRat.ofInt 1 - QRat.div cDvp L hLne :=
    qrat_le_of_eqv_right hident hβ_raw
  have hcDvp_pos : QRat.ofInt 0 < cDvp := by decide
  have hcDiv_pos : QRat.ofInt 0 < QRat.div cDvp L hLne := qrat_div_pos hcDvp_pos hLpos
  have hsub_lt1 : QRat.ofInt 1 - QRat.div cDvp L hLne < QRat.ofInt 1 := by
    rw [qrat_lt_iff]
    rw [qrat_pos_iff] at hcDiv_pos
    simp only [qrat_sub_num, qrat_sub_den, qrat_ofInt_num, qrat_ofInt_den,
      Int.natCast_mul, Int.one_mul]
    have hd : (0 : Int) < ((QRat.div cDvp L hLne).den : Int) := qrat_den_pos_int _
    omega
  exact ⟨hcDvp_pos, hβ_zfr, qrat_lt_of_le_of_lt hβ_zfr hsub_lt1⟩

-- ============================================================================
-- Part 3: Constructive Dirichlet L^2 Diagonal Dominance & M-V Sandwich
-- ============================================================================

/-- Positive integer index list `[1, 2, ..., N]` for a finite Dirichlet polynomial. -/
def dirichletTerms (N : Nat) : List Nat :=
  (List.range N).map (· + 1)

/-- Diagonal `L^2` energy `∑_{n=1}^N a_n^2` of a finite Dirichlet polynomial. -/
def dirichletDiagEnergy (N : Nat) (a : Nat → QRat) : QRat :=
  (dirichletTerms N).foldl (fun acc n => acc + a n * a n) (QRat.ofInt 0)

private theorem dirichletDiagEnergy_step_nonneg (a : Nat → QRat) (ns : List Nat) (init : QRat)
    (hinit : QRat.ofInt 0 ≤ init) :
    QRat.ofInt 0 ≤ ns.foldl (fun acc n => acc + a n * a n) init := by
  induction ns generalizing init with
  | nil => exact hinit
  | cons n rest ih =>
    have hsq : QRat.ofInt 0 ≤ a n * a n := qrat_sq_nonneg (a n)
    have hz : QRat.eqv (QRat.ofInt 0 + QRat.ofInt 0) (QRat.ofInt 0) := by decide
    have hnext : QRat.ofInt 0 ≤ init + a n * a n :=
      qrat_le_of_eqv_left hz (qrat_add_le_add hinit hsq)
    exact ih (init + a n * a n) hnext

/-- Diagonal `L^2` energy `∑_{n=1}^N a_n^2` is always non-negative. -/
theorem dirichletDiagEnergy_nonneg (N : Nat) (a : Nat → QRat) :
    QRat.ofInt 0 ≤ dirichletDiagEnergy N a :=
  dirichletDiagEnergy_step_nonneg a (dirichletTerms N) (QRat.ofInt 0) (qrat_le_refl _)

/-- Lower rational envelope `(n - m) / n` for `ln(n / m)` when `1 ≤ m < n`. -/
def dirichletLogRatioLower (m n : Nat) : QRat :=
  QRat.mk' ((n : Int) - (m : Int)) (max 1 n)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 n))

/-- The `k`-th Taylor term `x^k / k!` for `exp(x)` over `QRat`. -/
def expTaylorTerm (x : QRat) : Nat → QRat
  | 0 => QRat.ofInt 1
  | k + 1 => expTaylorTerm x k * x * QRat.mk' 1 (k + 1) (Nat.succ_pos k)

/-- The `k`-th geometric series term `x^k` over `QRat`. -/
def geomSeriesTerm (x : QRat) : Nat → QRat
  | 0 => QRat.ofInt 1
  | k + 1 => geomSeriesTerm x k * x

/-- Partial sum `∑_{k=0}^{M} x^k / k!` of `exp(x)` over `QRat`. -/
def expTaylorPartial (x : QRat) : Nat → QRat
  | 0 => expTaylorTerm x 0
  | M + 1 => expTaylorPartial x M + expTaylorTerm x (M + 1)

/-- Partial sum `∑_{k=0}^{M} x^k` of `1 / (1 - x)` over `QRat`. -/
def geomSeriesPartial (x : QRat) : Nat → QRat
  | 0 => geomSeriesTerm x 0
  | M + 1 => geomSeriesPartial x M + geomSeriesTerm x (M + 1)

private theorem expTaylorTerm_le_geomSeriesTerm (x : QRat) (hx : QRat.ofInt 0 ≤ x) :
    ∀ k, QRat.ofInt 0 ≤ expTaylorTerm x k ∧ expTaylorTerm x k ≤ geomSeriesTerm x k
  | 0 => by
    dsimp [expTaylorTerm, geomSeriesTerm]
    exact ⟨by decide, qrat_le_refl _⟩
  | k + 1 => by
    have ih := expTaylorTerm_le_geomSeriesTerm x hx k
    have hinv_pos : QRat.ofInt 0 ≤ QRat.mk' 1 (k + 1) (Nat.succ_pos k) := by
      change (0 : Int) * ((k + 1 : Nat) : Int) ≤ 1 * 1
      omega
    have hinv_le1 : QRat.mk' 1 (k + 1) (Nat.succ_pos k) ≤ QRat.ofInt 1 := by
      change 1 * 1 ≤ 1 * ((k + 1 : Nat) : Int)
      omega
    have htx_nonneg : QRat.ofInt 0 ≤ expTaylorTerm x k * x := qrat_mul_nonneg ih.1 hx
    have hnonneg : QRat.ofInt 0 ≤ (expTaylorTerm x k * x) * QRat.mk' 1 (k + 1) (Nat.succ_pos k) :=
      qrat_mul_nonneg htx_nonneg hinv_pos
    have hle1 : (expTaylorTerm x k * x) * QRat.mk' 1 (k + 1) (Nat.succ_pos k) ≤
        (expTaylorTerm x k * x) * QRat.ofInt 1 :=
      qrat_mul_le_mul_of_nonneg_left hinv_le1 htx_nonneg
    have hmul1 : QRat.eqv ((expTaylorTerm x k * x) * QRat.ofInt 1) (expTaylorTerm x k * x) := by
      dsimp [QRat.eqv]
      simp only [qrat_mul_num, qrat_mul_den, qrat_ofInt_num, qrat_ofInt_den,
        Nat.mul_one, Int.mul_one]
    have htx_le : expTaylorTerm x k * x ≤ geomSeriesTerm x k * x :=
      qrat_mul_le_mul_of_nonneg_right ih.2 hx
    exact ⟨hnonneg, qrat_le_trans (qrat_le_of_eqv_right hmul1 hle1) htx_le⟩

private theorem expTaylorPartial_le_geomSeriesPartial (x : QRat) (hx : QRat.ofInt 0 ≤ x) :
    ∀ M, expTaylorPartial x M ≤ geomSeriesPartial x M
  | 0 => (expTaylorTerm_le_geomSeriesTerm x hx 0).2
  | M + 1 =>
    qrat_add_le_add (expTaylorPartial_le_geomSeriesPartial x hx M)
      (expTaylorTerm_le_geomSeriesTerm x hx (M + 1)).2

private theorem qrat_add_mul_eqv (a b c : QRat) : QRat.eqv ((a + b) * c) (a * c + b * c) := by
  have hc1 : QRat.eqv ((a + b) * c) (c * (a + b)) := by
    dsimp [QRat.eqv]; simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]; ac_rfl
  have hdist := qrat_mul_add_eqv c a b
  have hc2 : QRat.eqv (c * a) (a * c) := by
    dsimp [QRat.eqv]; simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]; ac_rfl
  have hc3 : QRat.eqv (c * b) (b * c) := by
    dsimp [QRat.eqv]; simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]; ac_rfl
  exact qrat_eqv_trans hc1 (qrat_eqv_trans hdist (qrat_add_eqv_congr hc2 hc3))

private theorem qrat_mul_sub_add_mul_cancel (u x : QRat) :
    QRat.eqv (u * (QRat.ofInt 1 - x) + u * x) u := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den, qrat_sub_num, qrat_sub_den,
    qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.one_mul, Int.mul_one]
  have t1 : (u.num * ((x.den : Int) - x.num) * ((u.den : Int) * (x.den : Int)) +
      u.num * x.num * ((u.den : Int) * (x.den : Int))) * (u.den : Int) =
      (u.num * ((x.den : Int) - x.num) + u.num * x.num) *
        ((u.den : Int) * (u.den : Int) * (x.den : Int)) := by
    simp only [Int.add_mul]
    ac_rfl
  have t2 : u.num * ((x.den : Int) - x.num) + u.num * x.num = u.num * (x.den : Int) := by
    rw [← Int.mul_add]
    rw [show (x.den : Int) - x.num + x.num = (x.den : Int) by omega]
  have t3 : u.num * ((u.den : Int) * (x.den : Int) * ((u.den : Int) * (x.den : Int))) =
      u.num * (x.den : Int) * ((u.den : Int) * (u.den : Int) * (x.den : Int)) := by ac_rfl
  rw [t1, t2, t3]

private theorem geomSeriesPartial_telescope (x : QRat) :
    ∀ M, QRat.eqv
      (geomSeriesPartial x M * (QRat.ofInt 1 - x) + geomSeriesTerm x (M + 1))
      (QRat.ofInt 1)
  | 0 => by
    dsimp [geomSeriesPartial, geomSeriesTerm]
    have h1 := qrat_mul_sub_add_mul_cancel (QRat.ofInt 1) x
    dsimp [QRat.eqv] at h1 ⊢
    simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den, qrat_sub_num, qrat_sub_den,
      qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.one_mul,
      Int.mul_one] at h1 ⊢
    exact h1
  | M + 1 => by
    have ih := geomSeriesPartial_telescope x M
    dsimp [geomSeriesPartial, geomSeriesTerm]
    have hdist : QRat.eqv
        ((geomSeriesPartial x M + geomSeriesTerm x (M + 1)) * (QRat.ofInt 1 - x) +
          geomSeriesTerm x (M + 1) * x)
        (geomSeriesPartial x M * (QRat.ofInt 1 - x) +
          (geomSeriesTerm x (M + 1) * (QRat.ofInt 1 - x) + geomSeriesTerm x (M + 1) * x)) :=
      qrat_eqv_trans
        (qrat_add_eqv_congr (qrat_add_mul_eqv _ _ _) (qrat_eqv_refl _))
        (qrat_add_assoc_eqv _ _ _)
    have hstep := qrat_mul_sub_add_mul_cancel (geomSeriesTerm x (M + 1)) x
    have hs := qrat_eqv_trans hdist (qrat_add_eqv_congr (qrat_eqv_refl _) hstep)
    exact qrat_eqv_trans hs ih

private theorem geomSeriesTerm_pos (x : QRat) (hx : QRat.ofInt 0 < x) :
    ∀ k, QRat.ofInt 0 < geomSeriesTerm x k
  | 0 => by dsimp [geomSeriesTerm]; decide
  | k + 1 => qrat_mul_pos (geomSeriesTerm_pos x hx k) hx

/-- Theorem (Elementary Rational Logarithmic Spacing Lower Bound):
For all integers `1 ≤ m < n`, the ratio gap `x = (n - m) / n` satisfies `0 < x`,
`expTaylorPartial x M < n / m` for every truncation order `M` (establishing
`(n - m) / n < ln(n / m)` constructively without `Real.log`), and `(n - m) / n ≤ (n - m) / m`. -/
theorem dirichlet_log_ratio_lower (m n : Nat) (hm : 1 ≤ m) (hmn : m < n) (M : Nat) :
    QRat.ofInt 0 < dirichletLogRatioLower m n ∧
    expTaylorPartial (dirichletLogRatioLower m n) M < QRat.mk' n m hm ∧
    dirichletLogRatioLower m n ≤ QRat.mk' ((n : Int) - m) m hm := by
  let x := dirichletLogRatioLower m n
  have hmax : max 1 n = n := Nat.max_eq_right (Nat.le_trans hm (Nat.le_of_lt hmn))
  have hx_num : x.num = (n : Int) - m := rfl
  have hx_den : x.den = n := by dsimp [x, dirichletLogRatioLower, QRat.mk']; rw [hmax]
  have hxpos : QRat.ofInt 0 < x := by
    rw [qrat_pos_iff, hx_num]
    omega
  have hx_nonneg : QRat.ofInt 0 ≤ x := qrat_le_of_lt hxpos
  have hexp_le : expTaylorPartial x M ≤ geomSeriesPartial x M :=
    expTaylorPartial_le_geomSeriesPartial x hx_nonneg M
  have h1mx_eq :
      QRat.eqv (QRat.ofInt 1 - x) (QRat.mk' m n (Nat.lt_of_lt_of_le hm (Nat.le_of_lt hmn))) := by
    dsimp [QRat.eqv]
    simp only [qrat_sub_num, qrat_sub_den, qrat_ofInt_num, qrat_ofInt_den,
      qrat_mk'_num, qrat_mk'_den, hx_num, hx_den, Int.ofNat_one, Int.one_mul, Int.mul_one,
      Nat.one_mul]
    rw [show (n : Int) - ((n : Int) - (m : Int)) = (m : Int) by omega]
  have h1mx_pos : QRat.ofInt 0 < QRat.ofInt 1 - x := by
    rw [qrat_pos_iff]
    simp only [qrat_sub_num, qrat_ofInt_num, qrat_ofInt_den, hx_num, hx_den,
      Int.ofNat_one, Int.one_mul, Int.mul_one]
    omega
  have htel := geomSeriesPartial_telescope x M
  have hrem_pos := geomSeriesTerm_pos x hxpos (M + 1)
  have hlt1 : geomSeriesPartial x M * (QRat.ofInt 1 - x) < QRat.ofInt 1 := by
    have hlt_add : geomSeriesPartial x M * (QRat.ofInt 1 - x) <
        geomSeriesPartial x M * (QRat.ofInt 1 - x) + geomSeriesTerm x (M + 1) := by
      rw [qrat_lt_iff]
      rw [qrat_pos_iff] at hrem_pos
      simp only [qrat_add_num, qrat_add_den, Int.natCast_mul]
      have hd : (0 : Int) < ((geomSeriesPartial x M * (QRat.ofInt 1 - x)).den : Int) :=
        qrat_den_pos_int _
      let p := geomSeriesPartial x M * (QRat.ofInt 1 - x)
      let r := geomSeriesTerm x (M + 1)
      change 0 < (p.num * (r.den : Int) + r.num * (p.den : Int)) * (p.den : Int) -
        p.num * ((p.den : Int) * (r.den : Int))
      rw [Int.add_mul]
      rw [show p.num * (r.den : Int) * (p.den : Int) =
          p.num * ((p.den : Int) * (r.den : Int)) by ac_rfl]
      rw [show ∀ a b : Int, a + b - a = b from fun a b => by omega]
      exact Int.mul_pos (Int.mul_pos hrem_pos hd) hd
    have htel_le : geomSeriesPartial x M * (QRat.ofInt 1 - x) + geomSeriesTerm x (M + 1) ≤
        QRat.ofInt 1 := qrat_le_of_eqv_left (qrat_eqv_symm htel) (qrat_le_refl _)
    exact qrat_lt_of_lt_of_le hlt_add htel_le
  have hdiv_lt : geomSeriesPartial x M < QRat.mk' n m hm := by
    have hmul := hlt1
    rw [qrat_lt_iff] at hmul ⊢
    simp only [qrat_sub_num, qrat_sub_den, qrat_mul_num, qrat_mul_den,
      qrat_ofInt_num, qrat_ofInt_den, qrat_mk'_num, qrat_mk'_den,
      hx_num, hx_den, Int.ofNat_one, Int.one_mul, Int.mul_one, Nat.one_mul,
      Int.natCast_mul] at hmul ⊢
    rw [show (n : Int) - ((n : Int) - m) = (m : Int) by omega] at hmul
    have hc1 : (n : Int) * ((geomSeriesPartial x M).den : Int) =
        ((geomSeriesPartial x M).den : Int) * (n : Int) := Int.mul_comm _ _
    have hc2 : (geomSeriesPartial x M).num * (m : Int) =
        (m : Int) * (geomSeriesPartial x M).num := Int.mul_comm _ _
    omega
  have hratio_le : x ≤ QRat.mk' ((n : Int) - m) m hm := by
    dsimp [LE.le, QRat.le]
    rw [hx_num, hx_den]
    simp only [qrat_mk'_num, qrat_mk'_den]
    have hnm : (0 : Int) ≤ (n : Int) - m := by omega
    exact Int.mul_le_mul_of_nonneg_left (by omega) hnm
  exact ⟨hxpos, qrat_lt_of_le_of_lt hexp_le hdiv_lt, hratio_le⟩

/-- Distinct off-diagonal pair magnitude `|a_m * a_n|` (`0` when `m = n`). -/
def dirichletOffDiagTerm (a : Nat → QRat) (m n : Nat) : QRat :=
  if m = n then QRat.ofInt 0 else QRat.abs (a m * a n)

private theorem int_sq_nonneg (z : Int) : 0 ≤ z * z := by
  if h : 0 ≤ z then
    exact Int.mul_nonneg h h
  else
    have hn : 0 ≤ -z := by omega
    have hm := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem int_two_abs_mul_le_sq_add_sq (a b : Int) :
    2 * Int.ofNat (a * b).natAbs ≤ a * a + b * b := by
  have h1 : 0 ≤ (a - b) * (a - b) := int_sq_nonneg (a - b)
  have h2 : 0 ≤ (a + b) * (a + b) := int_sq_nonneg (a + b)
  have e1 : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]; omega
  have e2 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]; omega
  rcases Int.natAbs_eq (a * b) with hpos | hneg
  · have hab : Int.ofNat (a * b).natAbs = a * b := by
      rw [Int.ofNat_eq_natCast]; exact hpos.symm
    rw [e1] at h1
    rw [hab]
    omega
  · have hab : Int.ofNat (a * b).natAbs = -(a * b) := by
      rw [Int.ofNat_eq_natCast]; omega
    rw [e2] at h2
    rw [hab]
    omega

private theorem qrat_abs_prod_le_half_sq_sum (u v : QRat) :
    QRat.abs (u * v) ≤ QRat.mk' 1 2 (by decide) * (u * u + v * v) := by
  rw [qrat_le_iff]
  simp only [qrat_abs_num, qrat_abs_den, qrat_mul_num, qrat_mul_den,
    qrat_add_num, qrat_add_den, qrat_mk'_num, qrat_mk'_den,
    Int.natCast_mul, Int.one_mul]
  let a : Int := u.num * (v.den : Int)
  let b : Int := v.num * (u.den : Int)
  have hineq := int_two_abs_mul_le_sq_add_sq a b
  rw [Int.ofNat_eq_natCast] at hineq
  have hab : ((u.num * v.num).natAbs : Int) * ((u.den : Int) * (v.den : Int)) =
      ((a * b).natAbs : Int) := by
    have hmul : a * b = (u.num * v.num) * ((u.den : Int) * (v.den : Int)) := by
      dsimp [a, b]; ac_rfl
    have hd : (((u.den : Int) * (v.den : Int)).natAbs : Int) = (u.den : Int) * (v.den : Int) :=
      Int.natAbs_of_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
    have hh : (a * b).natAbs = (u.num * v.num).natAbs * ((u.den : Int) * (v.den : Int)).natAbs := by
      rw [hmul, Int.natAbs_mul]
    exact (by
      rw [hh, Int.natCast_mul, hd] :
      ((a * b).natAbs : Int) =
        ((u.num * v.num).natAbs : Int) * ((u.den : Int) * (v.den : Int))).symm
  have hsqa : a * a = u.num * u.num * ((v.den : Int) * (v.den : Int)) := by
    dsimp [a]; ac_rfl
  have hsqb : b * b = v.num * v.num * ((u.den : Int) * (u.den : Int)) := by
    dsimp [b]; ac_rfl
  have hden : (0 : Int) ≤ (u.den : Int) * (v.den : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hm := Int.mul_le_mul_of_nonneg_right hineq hden
  have hL : ((u.num * v.num).natAbs : Int) *
      (((2 : Nat) : Int) * ((u.den : Int) * (u.den : Int) * ((v.den : Int) * (v.den : Int)))) =
      2 * ((a * b).natAbs : Int) * ((u.den : Int) * (v.den : Int)) := by
    rw [← hab, show ((2 : Nat) : Int) = (2 : Int) from rfl]
    ac_rfl
  have hR : (u.num * u.num * ((v.den : Int) * (v.den : Int)) +
        v.num * v.num * ((u.den : Int) * (u.den : Int))) *
      ((u.den : Int) * (v.den : Int)) =
      (a * a + b * b) * ((u.den : Int) * (v.den : Int)) := by
    rw [hsqa, hsqb]
  rw [hL, hR]
  exact hm

/-- Sum of off-diagonal magnitudes `∑_{m=1}^N ∑_{n≠m} |a_m a_n|`. -/
def dirichletOffDiagSum (N : Nat) (a : Nat → QRat) : QRat :=
  (dirichletTerms N).foldl
    (fun acc m =>
      acc + (dirichletTerms N).foldl (fun inner n => inner + dirichletOffDiagTerm a m n)
        (QRat.ofInt 0))
    (QRat.ofInt 0)

/-- Canonical right-associated sum over a `List Nat` for clean inductions. -/
def qratSum (f : Nat → QRat) : List Nat → QRat
  | [] => QRat.ofInt 0
  | n :: ns => f n + qratSum f ns

private theorem qrat_add_zero_eqv (a : QRat) : QRat.eqv (a + QRat.ofInt 0) a := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_ofInt_num, qrat_ofInt_den,
    Int.zero_mul, Int.add_zero, Int.ofNat_one, Int.mul_one, Nat.mul_one]

private theorem qrat_zero_add_eqv (a : QRat) : QRat.eqv (QRat.ofInt 0 + a) a := by
  dsimp [QRat.eqv]
  simp only [qrat_add_num, qrat_add_den, qrat_ofInt_num, qrat_ofInt_den,
    Int.zero_mul, Int.zero_add, Int.ofNat_one, Nat.one_mul, Int.mul_one]

private theorem foldl_add_init_eqv_qratSum (f : Nat → QRat) (ns : List Nat) (init : QRat) :
    QRat.eqv (ns.foldl (fun acc x => acc + f x) init) (init + qratSum f ns) := by
  induction ns generalizing init with
  | nil =>
    exact qrat_eqv_symm (qrat_add_zero_eqv init)
  | cons n rest ih =>
    dsimp [List.foldl, qratSum]
    have h1 := ih (init + f n)
    have h2 := qrat_add_assoc_eqv init (f n) (qratSum f rest)
    exact qrat_eqv_trans h1 h2

private theorem foldl_add_eqv_qratSum (f : Nat → QRat) (ns : List Nat) :
    QRat.eqv (ns.foldl (fun acc x => acc + f x) (QRat.ofInt 0)) (qratSum f ns) :=
  qrat_eqv_trans (foldl_add_init_eqv_qratSum f ns (QRat.ofInt 0))
    (qrat_zero_add_eqv (qratSum f ns))

private theorem qratSum_le_qratSum (f g : Nat → QRat) (ns : List Nat)
    (h : ∀ x ∈ ns, f x ≤ g x) :
    qratSum f ns ≤ qratSum g ns := by
  induction ns with
  | nil => exact qrat_le_refl _
  | cons n rest ih =>
    dsimp [qratSum]
    exact qrat_add_le_add (h n (List.Mem.head _))
      (ih (fun x hx => h x (List.Mem.tail _ hx)))

private theorem qratSum_add_eqv (f g : Nat → QRat) (ns : List Nat) :
    QRat.eqv (qratSum (fun x => f x + g x) ns) (qratSum f ns + qratSum g ns) := by
  induction ns with
  | nil =>
    dsimp [qratSum]
    exact qrat_eqv_symm (qrat_add_zero_eqv (QRat.ofInt 0))
  | cons n rest ih =>
    dsimp [qratSum]
    have hstep := qrat_add_eqv_congr (qrat_eqv_refl (f n + g n)) ih
    have hrearr : QRat.eqv ((f n + g n) + (qratSum f rest + qratSum g rest))
        ((f n + qratSum f rest) + (g n + qratSum g rest)) := by
      have s1 := qrat_add_assoc_eqv (f n) (g n) (qratSum f rest + qratSum g rest)
      have s2 : QRat.eqv (g n + (qratSum f rest + qratSum g rest))
          (qratSum f rest + (g n + qratSum g rest)) := by
        have a1 := qrat_eqv_symm (qrat_add_assoc_eqv (g n) (qratSum f rest) (qratSum g rest))
        have a2 := qrat_add_eqv_congr (qrat_add_comm_eqv (g n) (qratSum f rest))
          (qrat_eqv_refl (qratSum g rest))
        have a3 := qrat_add_assoc_eqv (qratSum f rest) (g n) (qratSum g rest)
        exact qrat_eqv_trans a1 (qrat_eqv_trans a2 a3)
      have s3 := qrat_eqv_symm (qrat_add_assoc_eqv (f n) (qratSum f rest) (g n + qratSum g rest))
      exact qrat_eqv_trans s1 (qrat_eqv_trans (qrat_add_eqv_congr (qrat_eqv_refl _) s2) s3)
    exact qrat_eqv_trans hstep hrearr

private theorem qratSum_const_eqv (c : QRat) (ns : List Nat) :
    QRat.eqv (qratSum (fun _ => c) ns) (QRat.ofInt ns.length * c) := by
  induction ns with
  | nil =>
    dsimp [qratSum, List.length, QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, qrat_ofInt_num, qrat_ofInt_den, Int.zero_mul]
  | cons _ rest ih =>
    dsimp [qratSum, List.length]
    have hstep := qrat_add_eqv_congr (qrat_eqv_refl c) ih
    have hcomb : QRat.eqv (c + QRat.ofInt rest.length * c)
        (QRat.ofInt (rest.length + 1) * c) := by
      dsimp [QRat.eqv]
      simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den,
        qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one]
      have hl : (c.num * (1 * (c.den : Int)) + ↑rest.length * c.num * (c.den : Int)) *
          (1 * (c.den : Int)) =
          ((↑rest.length + 1) * c.num) * ((c.den : Int) * (1 * (c.den : Int))) := by
        simp only [Int.one_mul, Int.add_mul]
        ac_rfl
      exact hl
    exact qrat_eqv_trans hstep hcomb

private theorem qratSum_mul_left_eqv (c : QRat) (f : Nat → QRat) (ns : List Nat) :
    QRat.eqv (qratSum (fun x => c * f x) ns) (c * qratSum f ns) := by
  induction ns with
  | nil =>
    dsimp [qratSum, QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, qrat_ofInt_num, qrat_ofInt_den,
      Int.mul_zero, Int.zero_mul]
  | cons n rest ih =>
    dsimp [qratSum]
    have hstep := qrat_add_eqv_congr (qrat_eqv_refl (c * f n)) ih
    exact qrat_eqv_trans hstep (qrat_eqv_symm (qrat_mul_add_eqv c (f n) (qratSum f rest)))

private theorem dirichlet_offdiag_inner_bound (N m : Nat) (a : Nat → QRat) :
    (dirichletTerms N).foldl (fun inner n => inner + dirichletOffDiagTerm a m n) (QRat.ofInt 0) ≤
    QRat.mk' 1 2 (by decide) * (QRat.ofInt N * (a m * a m) + dirichletDiagEnergy N a) := by
  let half := QRat.mk' 1 2 (by decide)
  have hterm : ∀ n, dirichletOffDiagTerm a m n ≤ half * (a m * a m + a n * a n) := by
    intro n
    dsimp [dirichletOffDiagTerm]
    split
    · have h0 : QRat.ofInt 0 ≤ a m * a m + a n * a n := by
        have hz : QRat.eqv (QRat.ofInt 0 + QRat.ofInt 0) (QRat.ofInt 0) := by decide
        exact qrat_le_of_eqv_left hz (qrat_add_le_add (qrat_sq_nonneg _) (qrat_sq_nonneg _))
      exact qrat_mul_nonneg (by decide) h0
    · exact qrat_abs_prod_le_half_sq_sum (a m) (a n)
  have h1 : (dirichletTerms N).foldl (fun inner n => inner + dirichletOffDiagTerm a m n)
      (QRat.ofInt 0) ≤ qratSum (fun n => half * (a m * a m + a n * a n)) (dirichletTerms N) :=
    qrat_le_of_eqv_left
      (qrat_eqv_symm (foldl_add_eqv_qratSum (fun n => dirichletOffDiagTerm a m n)
        (dirichletTerms N)))
      (qratSum_le_qratSum _ _ _ (fun n _ => hterm n))
  have hmul := qratSum_mul_left_eqv half (fun n => a m * a m + a n * a n) (dirichletTerms N)
  have hadd := qratSum_add_eqv (fun _ => a m * a m) (fun n => a n * a n) (dirichletTerms N)
  have hconst := qratSum_const_eqv (a m * a m) (dirichletTerms N)
  have hlen : (dirichletTerms N).length = N := by simp [dirichletTerms]
  rw [hlen] at hconst
  have hdiag : QRat.eqv (qratSum (fun n => a n * a n) (dirichletTerms N))
      (dirichletDiagEnergy N a) :=
    qrat_eqv_symm (foldl_add_eqv_qratSum (fun n => a n * a n) (dirichletTerms N))
  have hinner_eq := qrat_eqv_trans hmul
    (qrat_mul_eqv_congr (qrat_eqv_refl half)
      (qrat_eqv_trans hadd (qrat_add_eqv_congr hconst hdiag)))
  exact qrat_le_of_eqv_right hinner_eq h1

private theorem qrat_half_double_eqv (P : QRat) :
    QRat.eqv (QRat.mk' 1 2 (by decide) * (P + P)) P := by
  dsimp [QRat.eqv]
  simp only [qrat_mul_num, qrat_mul_den, qrat_add_num, qrat_add_den,
    qrat_mk'_num, qrat_mk'_den, Int.one_mul, Int.natCast_mul]
  change (P.num * (P.den : Int) + P.num * (P.den : Int)) * (P.den : Int) =
    P.num * (((2 : Nat) : Int) * ((P.den : Int) * (P.den : Int)))
  rw [Int.add_mul, show ((2 : Nat) : Int) = (2 : Int) from rfl]
  have h2 : P.num * (P.den : Int) * (P.den : Int) + P.num * (P.den : Int) * (P.den : Int) =
      2 * (P.num * (P.den : Int) * (P.den : Int)) := by omega
  rw [h2]
  ac_rfl

/-- Theorem (Off-Diagonal Pairwise Interference Sum Bound):
The total off-diagonal magnitude sum `∑_{m=1}^N ∑_{n≠m} |a_m a_n|` is bounded by
`N * ∑_{n=1}^N a_n^2`. -/
theorem dirichlet_offdiag_sum_bound (N : Nat) (a : Nat → QRat) :
    dirichletOffDiagSum N a ≤ QRat.ofInt N * dirichletDiagEnergy N a := by
  let half := QRat.mk' 1 2 (by decide)
  let innerFn : Nat → QRat := fun m =>
    (dirichletTerms N).foldl (fun inner n => inner + dirichletOffDiagTerm a m n) (QRat.ofInt 0)
  have houter := qrat_le_of_eqv_left
    (qrat_eqv_symm (foldl_add_eqv_qratSum innerFn (dirichletTerms N)))
    (qratSum_le_qratSum innerFn
      (fun m => half * (QRat.ofInt N * (a m * a m) + dirichletDiagEnergy N a))
      (dirichletTerms N) (fun m _ => dirichlet_offdiag_inner_bound N m a))
  have hm := qratSum_mul_left_eqv half
    (fun m => QRat.ofInt N * (a m * a m) + dirichletDiagEnergy N a) (dirichletTerms N)
  have ha := qratSum_add_eqv (fun m => QRat.ofInt N * (a m * a m))
    (fun _ => dirichletDiagEnergy N a) (dirichletTerms N)
  have hmN := qratSum_mul_left_eqv (QRat.ofInt N) (fun m => a m * a m) (dirichletTerms N)
  have hdiag := qrat_eqv_symm (foldl_add_eqv_qratSum (fun m => a m * a m) (dirichletTerms N))
  have hc := qratSum_const_eqv (dirichletDiagEnergy N a) (dirichletTerms N)
  have hlen : (dirichletTerms N).length = N := by simp [dirichletTerms]
  rw [hlen] at hc
  have hcomb : QRat.eqv
      (qratSum (fun m => half * (QRat.ofInt N * (a m * a m) + dirichletDiagEnergy N a))
        (dirichletTerms N))
      (QRat.ofInt N * dirichletDiagEnergy N a) := by
    have hs1 := qrat_eqv_trans hm (qrat_mul_eqv_congr (qrat_eqv_refl half)
      (qrat_eqv_trans ha (qrat_add_eqv_congr
        (qrat_eqv_trans hmN (qrat_mul_eqv_congr (qrat_eqv_refl _) hdiag)) hc)))
    have hs2 : QRat.eqv
        (half * (QRat.ofInt N * dirichletDiagEnergy N a +
          QRat.ofInt N * dirichletDiagEnergy N a))
        (QRat.ofInt N * dirichletDiagEnergy N a) :=
      qrat_half_double_eqv (QRat.ofInt N * dirichletDiagEnergy N a)
    exact qrat_eqv_trans hs1 hs2
  exact qrat_le_of_eqv_right hcomb houter

/-- Constructive Montgomery-Vaughan off-diagonal interference envelope `(2 N / H) * offDiagSum`
for a window length `H ≥ 4 N^2`. -/
def dirichletOffDiagEnvelope (N H : Nat) (a : Nat → QRat) : QRat :=
  QRat.mk' (2 * (N : Int)) (max 1 H)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 H)) *
  dirichletOffDiagSum N a

private theorem dirichletOffDiagSum_nonneg (N : Nat) (a : Nat → QRat) :
    QRat.ofInt 0 ≤ dirichletOffDiagSum N a := by
  let f : Nat → QRat := fun m =>
    (dirichletTerms N).foldl (fun inner n => inner + dirichletOffDiagTerm a m n) (QRat.ofInt 0)
  have hf : ∀ m, QRat.ofInt 0 ≤ f m := by
    intro m
    suffices hs : ∀ (ns : List Nat) (init : QRat), QRat.ofInt 0 ≤ init →
        QRat.ofInt 0 ≤ ns.foldl (fun inner n => inner + dirichletOffDiagTerm a m n) init from
      hs (dirichletTerms N) (QRat.ofInt 0) (qrat_le_refl _)
    intro ns
    induction ns with
    | nil => intro init hi; exact hi
    | cons n rest ih =>
      intro init hi
      have ht : QRat.ofInt 0 ≤ dirichletOffDiagTerm a m n := by
        dsimp [dirichletOffDiagTerm]
        split
        · exact qrat_le_refl _
        · exact qrat_abs_nonneg _
      have hz : QRat.eqv (QRat.ofInt 0 + QRat.ofInt 0) (QRat.ofInt 0) := by decide
      exact ih _ (qrat_le_of_eqv_left hz (qrat_add_le_add hi ht))
  suffices ho : ∀ (ms : List Nat) (init : QRat), QRat.ofInt 0 ≤ init →
      QRat.ofInt 0 ≤ ms.foldl (fun acc m => acc + f m) init from
    ho (dirichletTerms N) (QRat.ofInt 0) (qrat_le_refl _)
  intro ms
  induction ms with
  | nil => intro init hi; exact hi
  | cons m rest ih =>
    intro init hi
    have hz : QRat.eqv (QRat.ofInt 0 + QRat.ofInt 0) (QRat.ofInt 0) := by decide
    exact ih _ (qrat_le_of_eqv_left hz (qrat_add_le_add hi (hf m)))

/-- Upper bound `dirichletOffDiagEnvelope N H a ≤ (1/2) * diagEnergy` whenever `4 N^2 ≤ H`. -/
theorem dirichlet_offdiag_envelope_le_half_diag (N H : Nat) (hH : 4 * N * N ≤ H)
    (a : Nat → QRat) :
    dirichletOffDiagEnvelope N H a ≤ QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a := by
  have hsum := dirichlet_offdiag_sum_bound N a
  have hcoeff_nonneg : QRat.ofInt 0 ≤
      QRat.mk' (2 * (N : Int)) (max 1 H)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 H)) := by
    change (0 : Int) * ((max 1 H : Nat) : Int) ≤ (2 * (N : Int)) * 1
    omega
  have hmul1 := qrat_mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
  have hprod_le :
      QRat.mk' (2 * (N : Int)) (max 1 H)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 H)) * QRat.ofInt N ≤
      QRat.mk' 1 2 (by decide) := by
    rw [qrat_le_iff]
    simp only [qrat_mul_num, qrat_mul_den, qrat_mk'_num, qrat_mk'_den,
      qrat_ofInt_num, qrat_ofInt_den, Int.natCast_mul, Int.ofNat_one, Int.mul_one, Int.one_mul]
    have h4NN : ((4 * N * N : Nat) : Int) ≤ ((max 1 H : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.le_trans hH (Nat.le_max_right 1 H))
    have hlin : 2 * (N : Int) * (N : Int) * ((2 : Nat) : Int) = ((4 * N * N : Nat) : Int) := by
      simp only [Int.natCast_mul]
      rw [show ((2 : Nat) : Int) = (2 : Int) from rfl, show ((4 : Nat) : Int) = 2 * 2 from rfl]
      ac_rfl
    rw [hlin]
    exact h4NN
  have hassoc : QRat.eqv
      (QRat.mk' (2 * (N : Int)) (max 1 H)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 H)) *
        (QRat.ofInt N * dirichletDiagEnergy N a))
      ((QRat.mk' (2 * (N : Int)) (max 1 H)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 H)) * QRat.ofInt N) *
        dirichletDiagEnergy N a) := by
    dsimp [QRat.eqv]
    simp only [qrat_mul_num, qrat_mul_den, Int.natCast_mul]
    ac_rfl
  have hdiag_nonneg := dirichletDiagEnergy_nonneg N a
  have hmul2 := qrat_mul_le_mul_of_nonneg_right hprod_le hdiag_nonneg
  exact qrat_le_trans (qrat_le_of_eqv_right hassoc hmul1) hmul2

/-- Theorem (Constructive Dirichlet `L^2` Diagonal-Dominance & Montgomery-Vaughan Sandwich):
For any Dirichlet polynomial `D(t) = ∑_{n=1}^N a_n n^{-it}`, any averaging window `H ≥ 4 N^2`,
and any oscillatory off-diagonal time-average residual `offDiagVal` certified by
`QRat.abs offDiagVal ≤ dirichletOffDiagEnvelope N H a`, the time-averaged mean square
`meanSq := dirichletDiagEnergy N a + offDiagVal` satisfies the 1/2 .. 3/2 sandwich
`(1/2) * ∑ a_n^2 ≤ meanSq ≤ (3/2) * ∑ a_n^2`. -/
theorem dirichlet_l2_diagonal_dominance_sandwich (N H : Nat) (hH : 4 * N * N ≤ H)
    (a : Nat → QRat) (offDiagVal : QRat)
    (hoff : QRat.abs offDiagVal ≤ dirichletOffDiagEnvelope N H a) :
    QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a ≤
      dirichletDiagEnergy N a + offDiagVal ∧
    dirichletDiagEnergy N a + offDiagVal ≤
      QRat.mk' 3 2 (by decide) * dirichletDiagEnergy N a := by
  have henv := dirichlet_offdiag_envelope_le_half_diag N H hH a
  have habs : QRat.abs offDiagVal ≤ QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a :=
    qrat_le_trans hoff henv
  have hup_off : offDiagVal ≤ QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a := by
    have h1 : offDiagVal ≤ QRat.abs offDiagVal := by
      dsimp [LE.le, QRat.le]
      simp only [qrat_abs_num, qrat_abs_den]
      have hd : (0 : Int) < (offDiagVal.den : Int) := qrat_den_pos_int offDiagVal
      have hn : offDiagVal.num ≤ (offDiagVal.num.natAbs : Int) := by
        if h0 : 0 ≤ offDiagVal.num then
          rw [Int.natAbs_of_nonneg h0]; exact Int.le_refl _
        else
          have ha : (offDiagVal.num.natAbs : Int) = -offDiagVal.num := by
            rcases Int.natAbs_eq offDiagVal.num with hp | hn <;> omega
          omega
      exact Int.mul_le_mul_of_nonneg_right hn (Int.le_of_lt hd)
    exact qrat_le_trans h1 habs
  have hlo_off : -(QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a) ≤ offDiagVal := by
    have h1 : -(QRat.abs offDiagVal) ≤ offDiagVal := by
      dsimp [LE.le, QRat.le]
      simp only [qrat_neg_num, qrat_neg_den, qrat_abs_num, qrat_abs_den]
      have hd : (0 : Int) < (offDiagVal.den : Int) := qrat_den_pos_int offDiagVal
      have hn : -(offDiagVal.num.natAbs : Int) ≤ offDiagVal.num := by
        if h0 : 0 ≤ offDiagVal.num then
          rw [Int.natAbs_of_nonneg h0]; omega
        else
          have ha : (offDiagVal.num.natAbs : Int) = -offDiagVal.num := by
            rcases Int.natAbs_eq offDiagVal.num with hp | hn <;> omega
          omega
      exact Int.mul_le_mul_of_nonneg_right hn (Int.le_of_lt hd)
    have h2 : -(QRat.mk' 1 2 (by decide) * dirichletDiagEnergy N a) ≤ -(QRat.abs offDiagVal) := by
      rw [qrat_le_iff] at habs ⊢
      simp only [qrat_neg_num, qrat_neg_den, Int.neg_mul]
      exact Int.neg_le_neg habs
    exact qrat_le_trans h2 h1
  have hlower_raw := qrat_add_le_add (qrat_le_refl (dirichletDiagEnergy N a)) hlo_off
  have hupper_raw := qrat_add_le_add (qrat_le_refl (dirichletDiagEnergy N a)) hup_off
  let E := dirichletDiagEnergy N a
  have hleft_eq : QRat.eqv (E + (-(QRat.mk' 1 2 (by decide) * E)))
      (QRat.mk' 1 2 (by decide) * E) := by
    dsimp [QRat.eqv]
    simp only [qrat_add_num, qrat_add_den, qrat_neg_num, qrat_neg_den,
      qrat_mul_num, qrat_mul_den, qrat_mk'_num, qrat_mk'_den,
      Int.one_mul, Int.natCast_mul, Int.neg_mul]
    rw [← Int.sub_eq_add_neg, ← Int.mul_sub]
    change E.num * ((((2 : Nat) : Int) * (E.den : Int)) - (E.den : Int)) *
        (((2 : Nat) : Int) * (E.den : Int)) =
      E.num * ((E.den : Int) * (((2 : Nat) : Int) * (E.den : Int)))
    rw [show ((2 : Nat) : Int) * (E.den : Int) - (E.den : Int) = (E.den : Int) by omega]
    ac_rfl
  have hright_eq : QRat.eqv (E + QRat.mk' 1 2 (by decide) * E)
      (QRat.mk' 3 2 (by decide) * E) := by
    dsimp [QRat.eqv]
    simp only [qrat_add_num, qrat_add_den, qrat_mul_num, qrat_mul_den,
      qrat_mk'_num, qrat_mk'_den, Int.one_mul, Int.natCast_mul]
    rw [← Int.mul_add]
    change E.num * ((((2 : Nat) : Int) * (E.den : Int)) + (E.den : Int)) *
        (((2 : Nat) : Int) * (E.den : Int)) =
      3 * E.num * ((E.den : Int) * (((2 : Nat) : Int) * (E.den : Int)))
    rw [show ((2 : Nat) : Int) * (E.den : Int) + (E.den : Int) = 3 * (E.den : Int) by omega]
    ac_rfl
  exact ⟨qrat_le_of_eqv_left hleft_eq hlower_raw, qrat_le_of_eqv_right hright_eq hupper_raw⟩

/-- Unweighted zeta Dirichlet polynomial coefficients `a_n = 1`. -/
def zetaDirichletCoeff (_ : Nat) : QRat :=
  QRat.ofInt 1

/-- Alternating Mobius-style mollifier coefficients `a_n ∈ {-1, 0, 1}`. -/
def altMobiusCoeff (n : Nat) : QRat :=
  match n with
  | 1 => QRat.ofInt 1
  | 2 => QRat.ofInt (-1)
  | 3 => QRat.ofInt (-1)
  | 4 => QRat.ofInt 0
  | 5 => QRat.ofInt (-1)
  | 6 => QRat.ofInt 1
  | _ => QRat.ofInt 0

/-- Certified explicit `L^2` diagonal-dominance instantiations for both the unweighted zeta
Dirichlet polynomial (`N=4`, `H=64`, diagonal energy `= 4`, sandwich `[2, 6]`) and the
alternating Mobius-style mollifier (`N=6`, `H=144`, diag energy `= 5`, sandwich `[5/2, 15/2]`). -/
theorem dirichlet_l2_zeta_and_mobius_certs :
    QRat.eqv (dirichletDiagEnergy 4 zetaDirichletCoeff) (QRat.ofInt 4) ∧
    QRat.eqv (dirichletDiagEnergy 6 altMobiusCoeff) (QRat.ofInt 5) ∧
    (∀ offZ : QRat, QRat.abs offZ ≤ dirichletOffDiagEnvelope 4 64 zetaDirichletCoeff →
      QRat.mk' 1 2 (by decide) * dirichletDiagEnergy 4 zetaDirichletCoeff ≤
        dirichletDiagEnergy 4 zetaDirichletCoeff + offZ ∧
      dirichletDiagEnergy 4 zetaDirichletCoeff + offZ ≤
        QRat.mk' 3 2 (by decide) * dirichletDiagEnergy 4 zetaDirichletCoeff) ∧
    (∀ offM : QRat, QRat.abs offM ≤ dirichletOffDiagEnvelope 6 144 altMobiusCoeff →
      QRat.mk' 1 2 (by decide) * dirichletDiagEnergy 6 altMobiusCoeff ≤
        dirichletDiagEnergy 6 altMobiusCoeff + offM ∧
      dirichletDiagEnergy 6 altMobiusCoeff + offM ≤
        QRat.mk' 3 2 (by decide) * dirichletDiagEnergy 6 altMobiusCoeff) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro offZ hoffZ
    exact dirichlet_l2_diagonal_dominance_sandwich 4 64 (by decide) zetaDirichletCoeff offZ hoffZ
  · intro offM hoffM
    exact dirichlet_l2_diagonal_dominance_sandwich 6 144 (by decide) altMobiusCoeff offM hoffM

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean
