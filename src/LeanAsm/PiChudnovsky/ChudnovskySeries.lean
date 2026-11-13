-- Path: leanasm/src/LeanAsm/PiChudnovsky/ChudnovskySeries.lean
-- Stage 3 checkpoint: Heegner-163 Chudnovsky series, binary splitting & tail bounds.
-- Max Column: 120 Columns

import LeanAsm.PiChudnovsky.CrtMulBridge

namespace PiChudnovsky

/-- Constructive factorial in core `Nat`. -/
def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

theorem natFact_pos (n : Nat) : 0 < natFact n := by
  induction n with
  | zero => decide
  | succ n' ih =>
      unfold natFact
      exact Nat.mul_pos (Nat.succ_pos n') ih

/-- Exact numerator of the `k`-th unsigned Chudnovsky series term. -/
def chudTermNum (k : Nat) : Nat :=
  natFact (6 * k) * (13591409 + 545140134 * k)

/-- Exact denominator of the `k`-th unsigned Chudnovsky series term. -/
def chudTermDen (k : Nat) : Nat :=
  natFact (3 * k) * (natFact k) ^ 3 * (640320 ^ (3 * k))

theorem chudTermNum_pos (k : Nat) : 0 < chudTermNum k := by
  unfold chudTermNum
  exact Nat.mul_pos (natFact_pos _) (by omega)

theorem chudTermDen_pos (k : Nat) : 0 < chudTermDen k := by
  unfold chudTermDen
  exact Nat.mul_pos
    (Nat.mul_pos (natFact_pos _) (Nat.pow_pos (natFact_pos _)))
    (Nat.pow_pos (by decide))

private theorem fact6_succ (k : Nat) :
    natFact (6 * (k + 1)) =
      (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
        natFact (6 * k) := by
  have h1 : 6 * (k + 1) = 6 * k + 6 := by omega
  rw [h1]
  dsimp only [natFact]
  simp only [Nat.mul_assoc]

private theorem fact3_succ (k : Nat) :
    natFact (3 * (k + 1)) =
      (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * natFact (3 * k) := by
  have h1 : 3 * (k + 1) = 3 * k + 3 := by omega
  rw [h1]
  dsimp only [natFact]
  simp only [Nat.mul_assoc]

private theorem even_factor_identity (k : Nat) :
    (6 * k + 6) * (6 * k + 4) * (6 * k + 2) =
      8 * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1)) := by
  have ha : 6 * k + 6 = 2 * (3 * k + 3) := by omega
  have hb : 6 * k + 4 = 2 * (3 * k + 2) := by omega
  have hc : 6 * k + 2 = 2 * (3 * k + 1) := by omega
  rw [ha, hb, hc]
  calc (2 * (3 * k + 3)) * (2 * (3 * k + 2)) * (2 * (3 * k + 1))
      = (2 * 2 * 2) * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ = 8 * ((3 * k + 3) * (3 * k + 2) * (3 * k + 1)) := rfl

private theorem odd_factor_bound (k : Nat) :
    8 * ((6 * k + 5) * (6 * k + 3) * (6 * k + 1)) ≤ 1728 * (k + 1) ^ 3 := by
  have h1 : 6 * k + 5 ≤ 6 * (k + 1) := by omega
  have h2 : 6 * k + 3 ≤ 6 * (k + 1) := by omega
  have h3 : 6 * k + 1 ≤ 6 * (k + 1) := by omega
  have hm : (6 * k + 5) * (6 * k + 3) * (6 * k + 1) ≤
      (6 * (k + 1)) * (6 * (k + 1)) * (6 * (k + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hcube : (6 * (k + 1)) * (6 * (k + 1)) * (6 * (k + 1)) = 216 * (k + 1) ^ 3 := by
    have hp : (6 * (k + 1)) ^ 3 = (6 * (k + 1)) * (6 * (k + 1)) * (6 * (k + 1)) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [← hp, Nat.mul_pow]
  calc 8 * ((6 * k + 5) * (6 * k + 3) * (6 * k + 1))
      ≤ 8 * (216 * (k + 1) ^ 3) := by
          rw [← hcube]; exact Nat.mul_le_mul_left 8 hm
    _ = 1728 * (k + 1) ^ 3 := by rw [← Nat.mul_assoc]

/-- Constructive Chudnovsky ratio decay for ALL `k ≥ 0`:
`a_{k+1} * (5 * 10^13) < a_k` (`a_{k+1} < a_k / (5 * 10^13) < 10^{-13} * a_k`). -/
theorem chudnovsky_alternating_decreasing (k : Nat) :
    chudTermNum (k + 1) * chudTermDen k * (5 * 10 ^ 13) < chudTermNum k * chudTermDen (k + 1) := by
  cases k with
  | zero => decide
  | succ m =>
      have hlin : 13591409 + 545140134 * (m + 1 + 1) ≤ 2 * (13591409 + 545140134 * (m + 1)) := by
        omega
      have h10 : 2 * (5 * 10 ^ 13) = 10 ^ 14 := by decide
      have hc : (13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13) ≤
          (13591409 + 545140134 * (m + 1)) * (10 ^ 14) := by
        calc (13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13)
            ≤ (2 * (13591409 + 545140134 * (m + 1))) * (5 * 10 ^ 13) :=
              Nat.mul_le_mul_right _ hlin
          _ = (13591409 + 545140134 * (m + 1)) * (2 * (5 * 10 ^ 13)) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm]
          _ = (13591409 + 545140134 * (m + 1)) * 10 ^ 14 := by rw [h10]
      have hnum : (6 * (m + 1) + 6) * (6 * (m + 1) + 5) * (6 * (m + 1) + 4) *
            (6 * (m + 1) + 3) * (6 * (m + 1) + 2) * (6 * (m + 1) + 1) =
          8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
            ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) := by
        have hev := even_factor_identity (m + 1)
        calc (6 * (m + 1) + 6) * (6 * (m + 1) + 5) * (6 * (m + 1) + 4) *
              (6 * (m + 1) + 3) * (6 * (m + 1) + 2) * (6 * (m + 1) + 1)
            = ((6 * (m + 1) + 6) * (6 * (m + 1) + 4) * (6 * (m + 1) + 2)) *
                ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm]
          _ = 8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) := by rw [hev]
      have hpoly :
          (6 * (m + 1) + 6) * (6 * (m + 1) + 5) * (6 * (m + 1) + 4) * (6 * (m + 1) + 3) *
            (6 * (m + 1) + 2) * (6 * (m + 1) + 1) *
            (13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13) <
          (13591409 + 545140134 * (m + 1)) *
            ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1) *
              (m + 1 + 1) ^ 3 * 640320 ^ 3) := by
        have hodd := odd_factor_bound (m + 1)
        have hbase_pos : 0 <
            ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
              (13591409 + 545140134 * (m + 1)) * (m + 1 + 1) ^ 3 :=
          Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (by omega)) (Nat.pow_pos (by omega))
        have hconst : 1728 * 10 ^ 14 < (640320 : Nat) ^ 3 := by decide
        have hstep1 :
            8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) *
                ((13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13)) ≤
            ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
              (13591409 + 545140134 * (m + 1)) * (m + 1 + 1) ^ 3 * (1728 * 10 ^ 14) := by
          calc 8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                  ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) *
                  ((13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13))
              ≤ 8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                  ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) *
                  ((13591409 + 545140134 * (m + 1)) * 10 ^ 14) := Nat.mul_le_mul_left _ hc
            _ = ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                  (13591409 + 545140134 * (m + 1)) *
                  (8 * ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1))) *
                  10 ^ 14 := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm]
            _ ≤ ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                  (13591409 + 545140134 * (m + 1)) * (1728 * (m + 1 + 1) ^ 3) * 10 ^ 14 :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hodd)
            _ = ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
                  (13591409 + 545140134 * (m + 1)) * (m + 1 + 1) ^ 3 * (1728 * 10 ^ 14) := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm]
        have hstep2 := Nat.mul_lt_mul_of_pos_left hconst hbase_pos
        have hrhs :
            ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
              (13591409 + 545140134 * (m + 1)) * (m + 1 + 1) ^ 3 * 640320 ^ 3 =
            (13591409 + 545140134 * (m + 1)) *
              ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1) *
                (m + 1 + 1) ^ 3 * 640320 ^ 3) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm]
        have hlhs :
            (6 * (m + 1) + 6) * (6 * (m + 1) + 5) * (6 * (m + 1) + 4) * (6 * (m + 1) + 3) *
              (6 * (m + 1) + 2) * (6 * (m + 1) + 1) *
              (13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13) =
            8 * ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1)) *
              ((6 * (m + 1) + 5) * (6 * (m + 1) + 3) * (6 * (m + 1) + 1)) *
              ((13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13)) := by
          rw [hnum]; simp only [Nat.mul_assoc]
        rw [hlhs, ← hrhs]
        exact Nat.lt_of_le_of_lt hstep1 hstep2
      have hshared_pos : 0 <
          natFact (6 * (m + 1)) * natFact (3 * (m + 1)) * (natFact (m + 1)) ^ 3 *
            640320 ^ (3 * (m + 1)) :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (natFact_pos _) (natFact_pos _))
          (Nat.pow_pos (natFact_pos _))) (Nat.pow_pos (by decide))
      have hscaled := Nat.mul_lt_mul_of_pos_left hpoly hshared_pos
      have hlhs_full :
          chudTermNum (m + 1 + 1) * chudTermDen (m + 1) * (5 * 10 ^ 13) =
          (natFact (6 * (m + 1)) * natFact (3 * (m + 1)) * (natFact (m + 1)) ^ 3 *
            640320 ^ (3 * (m + 1))) *
          ((6 * (m + 1) + 6) * (6 * (m + 1) + 5) * (6 * (m + 1) + 4) * (6 * (m + 1) + 3) *
            (6 * (m + 1) + 2) * (6 * (m + 1) + 1) *
            (13591409 + 545140134 * (m + 1 + 1)) * (5 * 10 ^ 13)) := by
        unfold chudTermNum chudTermDen
        rw [fact6_succ (m + 1)]
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
      have hrhs_full :
          chudTermNum (m + 1) * chudTermDen (m + 1 + 1) =
          (natFact (6 * (m + 1)) * natFact (3 * (m + 1)) * (natFact (m + 1)) ^ 3 *
            640320 ^ (3 * (m + 1))) *
          ((13591409 + 545140134 * (m + 1)) *
            ((3 * (m + 1) + 3) * (3 * (m + 1) + 2) * (3 * (m + 1) + 1) *
              (m + 1 + 1) ^ 3 * 640320 ^ 3)) := by
        unfold chudTermNum chudTermDen
        have hk3 : 3 * (m + 1 + 1) = 3 * (m + 1) + 3 := by omega
        have hpow : 640320 ^ (3 * (m + 1) + 3) = 640320 ^ 3 * 640320 ^ (3 * (m + 1)) := by
          rw [Nat.pow_add, Nat.mul_comm]
        have hkf : (natFact (m + 1 + 1)) ^ 3 = (m + 1 + 1) ^ 3 * (natFact (m + 1)) ^ 3 := by
          dsimp only [natFact]
          rw [Nat.mul_pow]
        rw [fact3_succ (m + 1), hkf, hk3, hpow]
        ac_rfl
      rw [hlhs_full, hrhs_full]
      exact hscaled

/-- Strict monotonicity of unsigned Chudnovsky terms for all `k : Nat`. -/
theorem chudnovsky_term_strict_mono (k : Nat) :
    chudTermNum (k + 1) * chudTermDen k < chudTermNum k * chudTermDen (k + 1) := by
  have h := chudnovsky_alternating_decreasing k
  have h1 : chudTermNum (k + 1) * chudTermDen k ≤
      chudTermNum (k + 1) * chudTermDen k * (5 * 10 ^ 13) :=
    Nat.le_mul_of_pos_right _ (by decide)
  exact Nat.lt_of_le_of_lt h1 h

/-- Certified tail bound at `k = 8`: `a_8 < 10^{-113} * a_0`. -/
theorem chudnovsky_k8_tail_bound :
    chudTermNum 8 * chudTermDen 0 * 10 ^ 113 < chudTermNum 0 * chudTermDen 8 := by
  decide

/-- Minimal constructive rational number for Chudnovsky series invariance. -/
structure CRat where
  num : Int
  den : Nat
  den_pos : 0 < den

/-- Constructive ordering `a.num * b.den ≤ b.num * a.den`. -/
def CRat.le (a b : CRat) : Prop :=
  a.num * (b.den : Int) ≤ b.num * (a.den : Int)

/-- Exact addition of constructive rationals. -/
def CRat.add (a b : CRat) : CRat where
  num := a.num * (b.den : Int) + b.num * (a.den : Int)
  den := a.den * b.den
  den_pos := Nat.mul_pos a.den_pos b.den_pos

/-- Exact signed `k`-th Chudnovsky term `(-1)^k * a_k`. -/
def chudSignedTerm (k : Nat) : CRat where
  num := if k % 2 = 0 then (chudTermNum k : Int) else -(chudTermNum k : Int)
  den := chudTermDen k
  den_pos := chudTermDen_pos k

/-- Partial sum `P(m) = ∑_{k=0}^{m-1} (-1)^k a_k`. -/
def chudPartialSum : Nat → CRat
  | 0 => ⟨0, 1, by decide⟩
  | m + 1 => CRat.add (chudPartialSum m) (chudSignedTerm m)

private theorem crat_le_refl (a : CRat) : CRat.le a a := Int.le_refl _

private theorem crat_le_trans {a b c : CRat} (hab : CRat.le a b) (hbc : CRat.le b c) :
    CRat.le a c := by
  unfold CRat.le at hab hbc ⊢
  have hb_pos : (0 : Int) < (b.den : Int) := Int.natCast_pos.mpr b.den_pos
  have ha_nonneg : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hc_nonneg : (0 : Int) ≤ (c.den : Int) := Int.natCast_nonneg _
  have h1 : a.num * (b.den : Int) * (c.den : Int) ≤ b.num * (a.den : Int) * (c.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hab hc_nonneg
  have h2 : b.num * (c.den : Int) * (a.den : Int) ≤ c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hbc ha_nonneg
  have hmid : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
    simp only [Int.mul_assoc, Int.mul_comm (a.den : Int) (c.den : Int)]
  have h3 : (a.num * (c.den : Int)) * (b.den : Int) ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    calc (a.num * (c.den : Int)) * (b.den : Int)
        = a.num * (b.den : Int) * (c.den : Int) := by
            simp only [Int.mul_assoc, Int.mul_comm (c.den : Int) (b.den : Int)]
      _ ≤ b.num * (a.den : Int) * (c.den : Int) := h1
      _ = b.num * (c.den : Int) * (a.den : Int) := hmid
      _ ≤ c.num * (b.den : Int) * (a.den : Int) := h2
      _ = (c.num * (a.den : Int)) * (b.den : Int) := by
            simp only [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
  exact Int.le_of_mul_le_mul_right h3 hb_pos

private theorem crat_le_add_right {a x : CRat} (hx : 0 ≤ x.num) :
    CRat.le a (CRat.add a x) := by
  unfold CRat.le CRat.add
  simp only [Int.natCast_mul]
  have ha : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hterm : 0 ≤ x.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_nonneg (Int.mul_nonneg hx ha) ha
  have hm : a.num * ((a.den : Int) * (x.den : Int)) = a.num * (x.den : Int) * (a.den : Int) := by
    simp only [Int.mul_assoc, Int.mul_comm (a.den : Int) (x.den : Int)]
  rw [Int.add_mul, hm, Int.mul_assoc x.num (a.den : Int) (a.den : Int)]
  exact Int.le_add_of_nonneg_right (by rw [← Int.mul_assoc]; exact hterm)

private theorem crat_add_right_le {a x : CRat} (hx : x.num ≤ 0) :
    CRat.le (CRat.add a x) a := by
  unfold CRat.le CRat.add
  simp only [Int.natCast_mul]
  have ha : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hterm : x.num * ((a.den : Int) * (a.den : Int)) ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hx (Int.mul_nonneg ha ha)
  have hm : a.num * ((a.den : Int) * (x.den : Int)) = a.num * (x.den : Int) * (a.den : Int) := by
    simp only [Int.mul_assoc, Int.mul_comm (a.den : Int) (x.den : Int)]
  rw [Int.add_mul, hm]
  rw [← Int.mul_assoc] at hterm
  omega

private theorem crat_add2_nonneg_diff (s a b : CRat)
    (hsum : 0 ≤ a.num * (b.den : Int) + b.num * (a.den : Int)) :
    CRat.le s (CRat.add (CRat.add s a) b) := by
  have h1 : CRat.le s (CRat.add s (CRat.add a b)) := by
    refine crat_le_add_right ?_
    exact hsum
  have hassoc : CRat.le (CRat.add s (CRat.add a b)) (CRat.add (CRat.add s a) b) := by
    unfold CRat.le CRat.add
    simp only [Int.natCast_mul]
    have hnum_eq :
        (s.num * ((a.den : Int) * (b.den : Int)) +
            (a.num * (b.den : Int) + b.num * (a.den : Int)) * (s.den : Int)) *
          ((s.den : Int) * (a.den : Int) * (b.den : Int)) =
        ((s.num * (a.den : Int) + a.num * (s.den : Int)) * (b.den : Int) +
            b.num * ((s.den : Int) * (a.den : Int))) *
          ((s.den : Int) * ((a.den : Int) * (b.den : Int))) := by
      simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm]
      omega
    exact Int.le_of_eq hnum_eq
  exact crat_le_trans h1 hassoc

private theorem crat_add2_nonpos_diff (s a b : CRat)
    (hsum : a.num * (b.den : Int) + b.num * (a.den : Int) ≤ 0) :
    CRat.le (CRat.add (CRat.add s a) b) s := by
  have h1 : CRat.le (CRat.add s (CRat.add a b)) s := by
    refine crat_add_right_le ?_
    exact hsum
  have hassoc : CRat.le (CRat.add (CRat.add s a) b) (CRat.add s (CRat.add a b)) := by
    unfold CRat.le CRat.add
    simp only [Int.natCast_mul]
    have hnum_eq :
        ((s.num * (a.den : Int) + a.num * (s.den : Int)) * (b.den : Int) +
            b.num * ((s.den : Int) * (a.den : Int))) *
          ((s.den : Int) * ((a.den : Int) * (b.den : Int))) =
        (s.num * ((a.den : Int) * (b.den : Int)) +
            (a.num * (b.den : Int) + b.num * (a.den : Int)) * (s.den : Int)) *
          ((s.den : Int) * (a.den : Int) * (b.den : Int)) := by
      simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm]
      omega
    exact Int.le_of_eq hnum_eq
  exact crat_le_trans hassoc h1

private theorem chud_even_pair_nonneg (r : Nat) :
    CRat.le (chudPartialSum (2 * r)) (chudPartialSum (2 * r + 2)) := by
  have hev : (2 * r) % 2 = 0 := by omega
  have hod : (2 * r + 1) % 2 = 1 := by omega
  have hmono := chudnovsky_term_strict_mono (2 * r)
  have hmonoInt :
      ((chudTermNum (2 * r + 1) : Int) * (chudTermDen (2 * r) : Int)) ≤
      ((chudTermNum (2 * r) : Int) * (chudTermDen (2 * r + 1) : Int)) := by
    have hle : chudTermNum (2 * r + 1) * chudTermDen (2 * r) ≤
        chudTermNum (2 * r) * chudTermDen (2 * r + 1) := Nat.le_of_lt hmono
    rw [← Int.natCast_mul, ← Int.natCast_mul]
    exact Int.ofNat_le.mpr hle
  have hsum :
      0 ≤ (chudSignedTerm (2 * r)).num * ((chudSignedTerm (2 * r + 1)).den : Int) +
          (chudSignedTerm (2 * r + 1)).num * ((chudSignedTerm (2 * r)).den : Int) := by
    unfold chudSignedTerm
    simp [hev, hod, Int.neg_mul]
    omega
  exact crat_add2_nonneg_diff (chudPartialSum (2 * r))
    (chudSignedTerm (2 * r)) (chudSignedTerm (2 * r + 1)) hsum

private theorem chud_odd_pair_nonpos (r : Nat) :
    CRat.le (chudPartialSum (2 * r + 3)) (chudPartialSum (2 * r + 1)) := by
  have hev : (2 * r + 2) % 2 = 0 := by omega
  have hod : (2 * r + 1) % 2 = 1 := by omega
  have hmono := chudnovsky_term_strict_mono (2 * r + 1)
  have hmonoInt :
      ((chudTermNum (2 * r + 2) : Int) * (chudTermDen (2 * r + 1) : Int)) ≤
      ((chudTermNum (2 * r + 1) : Int) * (chudTermDen (2 * r + 2) : Int)) := by
    have hle : chudTermNum (2 * r + 2) * chudTermDen (2 * r + 1) ≤
        chudTermNum (2 * r + 1) * chudTermDen (2 * r + 2) := Nat.le_of_lt hmono
    rw [← Int.natCast_mul, ← Int.natCast_mul]
    exact Int.ofNat_le.mpr hle
  have hsum :
      (chudSignedTerm (2 * r + 1)).num * ((chudSignedTerm (2 * r + 2)).den : Int) +
        (chudSignedTerm (2 * r + 2)).num * ((chudSignedTerm (2 * r + 1)).den : Int) ≤ 0 := by
    unfold chudSignedTerm
    simp [hev, hod, Int.neg_mul]
    omega
  exact crat_add2_nonpos_diff (chudPartialSum (2 * r + 1))
    (chudSignedTerm (2 * r + 1)) (chudSignedTerm (2 * r + 2)) hsum

private theorem chud_even_step (j : Nat) :
    CRat.le (chudPartialSum 8) (chudPartialSum (8 + 2 * j)) := by
  induction j with
  | zero => exact crat_le_refl _
  | succ j' ih =>
      have ha : 2 * (4 + j') = 8 + 2 * j' := by omega
      have hb : 2 * (4 + j') + 2 = 8 + 2 * (j' + 1) := by omega
      have hpair := chud_even_pair_nonneg (4 + j')
      rw [hb, ha] at hpair
      exact crat_le_trans ih hpair

private theorem chud_odd_step (j : Nat) :
    CRat.le (chudPartialSum (9 + 2 * j)) (chudPartialSum 9) := by
  induction j with
  | zero => exact crat_le_refl _
  | succ j' ih =>
      have hstep : 9 + 2 * (j' + 1) = 2 * (4 + j') + 3 := by omega
      have hprev : 2 * (4 + j') + 1 = 9 + 2 * j' := by omega
      rw [hstep]
      have hpair := chud_odd_pair_nonpos (4 + j')
      rw [hprev] at hpair
      exact crat_le_trans hpair ih

/-- Every partial sum `chudPartialSum m` (`m ≥ 8`) of the alternating Chudnovsky series is
constructively trapped between the 8-term lower bound (`S_8`) and 9-term upper bound (`S_9`). -/
theorem chudPartialSum_trapped (m : Nat) (hm : 8 ≤ m) :
    CRat.le (chudPartialSum 8) (chudPartialSum m) ∧
    CRat.le (chudPartialSum m) (chudPartialSum 9) := by
  have hev_step : ∀ r : Nat, CRat.le (chudPartialSum (2 * r)) (chudPartialSum (2 * r + 1)) := by
    intro r
    have hmod : (2 * r) % 2 = 0 := by omega
    refine crat_le_add_right ?_
    unfold chudSignedTerm
    simp [hmod]
  have hod_step : ∀ r : Nat,
      CRat.le (chudPartialSum (2 * r + 2)) (chudPartialSum (2 * r + 1)) := by
    intro r
    have hmod : (2 * r + 1) % 2 = 1 := by omega
    refine crat_add_right_le ?_
    unfold chudSignedTerm
    simp [hmod]
  by_cases hpar : (m - 8) % 2 = 0
  · obtain ⟨j, hj⟩ : ∃ j, m = 8 + 2 * j := ⟨(m - 8) / 2, by omega⟩
    rw [hj]
    refine ⟨chud_even_step j, ?_⟩
    cases j with
    | zero => exact hev_step 4
    | succ j' =>
        have hstep : 8 + 2 * (j' + 1) = 2 * (4 + j') + 2 := by omega
        have hodd : 2 * (4 + j') + 1 = 9 + 2 * j' := by omega
        rw [hstep]
        have hdown := hod_step (4 + j')
        rw [hodd] at hdown
        exact crat_le_trans hdown (chud_odd_step j')
  · obtain ⟨j, hj⟩ : ∃ j, m = 9 + 2 * j := ⟨(m - 8) / 2, by omega⟩
    rw [hj]
    have h1 : 2 * (4 + j) + 1 = 9 + 2 * j := by omega
    have h0 : 2 * (4 + j) = 8 + 2 * j := by omega
    have hup := hev_step (4 + j)
    rw [h1, h0] at hup
    exact ⟨crat_le_trans (chud_even_step j) hup, chud_odd_step j⟩

/-- `640320^3 / 24 = 10939058860032000`. -/
def c3Over24 : Nat := (640320 ^ 3) / 24

private def chudBinarySplitFuel (a b fuel : Nat) : Nat × Nat × Int :=
  match fuel with
  | 0 => (1, 1, 0)
  | fuel' + 1 =>
      if b ≤ a then (1, 1, 0)
      else if b - a = 1 then
        let k := a
        let P := if k = 0 then 1 else (6 * k - 5) * (2 * k - 1) * (6 * k - 1)
        let Q := if k = 0 then 1 else k ^ 3 * c3Over24
        let mag : Int := (natMulBigViaCrtNtt P (13591409 + 545140134 * k) : Int)
        let T : Int := if k % 2 = 0 then mag else -mag
        (P, Q, T)
      else
        let m := (a + b) / 2
        let left := chudBinarySplitFuel a m fuel'
        let right := chudBinarySplitFuel m b fuel'
        let P := natMulBigViaCrtNtt left.1 right.1
        let Q := natMulBigViaCrtNtt left.2.1 right.2.1
        let tLeft := intMulBigViaCrtNtt left.2.2 (right.2.1 : Int)
        let tRight := intMulBigViaCrtNtt (left.1 : Int) right.2.2
        (P, Q, tLeft + tRight)

/-- Constructive Chudnovsky binary splitting `(P, Q, T)` over `[a, b)` using
`natMulBigViaCrtNtt` / `intMulBigViaCrtNtt` (`karatsubaCrtNttMul192` on `< 10^96` limbs). -/
def chudnovskyBinarySplit (a b : Nat) : Nat × Nat × Int :=
  chudBinarySplitFuel a b (b - a)

private def chudBinarySplitExactFuel (a b fuel : Nat) : Nat × Nat × Int :=
  match fuel with
  | 0 => (1, 1, 0)
  | fuel' + 1 =>
      if b ≤ a then (1, 1, 0)
      else if b - a = 1 then
        let k := a
        let P := if k = 0 then 1 else (6 * k - 5) * (2 * k - 1) * (6 * k - 1)
        let Q := if k = 0 then 1 else k ^ 3 * c3Over24
        let mag : Int := ((P * (13591409 + 545140134 * k) : Nat) : Int)
        let T : Int := if k % 2 = 0 then mag else -mag
        (P, Q, T)
      else
        let m := (a + b) / 2
        let left := chudBinarySplitExactFuel a m fuel'
        let right := chudBinarySplitExactFuel m b fuel'
        let P := left.1 * right.1
        let Q := left.2.1 * right.2.1
        let tLeft := left.2.2 * (right.2.1 : Int)
        let tRight := (left.1 : Int) * right.2.2
        (P, Q, tLeft + tRight)

/-- Pure `Nat`/`Int` binary-splitting mirror used to keep `decide` kernel reduction lightweight. -/
def chudBinarySplitExact (a b : Nat) : Nat × Nat × Int :=
  chudBinarySplitExactFuel a b (b - a)

private theorem chudBinarySplitFuel_eq_exact (a b fuel : Nat) :
    chudBinarySplitFuel a b fuel = chudBinarySplitExactFuel a b fuel := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel' ih =>
      dsimp only [chudBinarySplitFuel, chudBinarySplitExactFuel]
      split
      · rfl
      · split
        · simp only [natMulBigViaCrtNtt_eq_mul]
        · rw [ih a ((a + b) / 2), ih ((a + b) / 2) b]
          simp only [natMulBigViaCrtNtt_eq_mul, intMulBigViaCrtNtt_eq_mul]

/-- Constructive equivalence allowing proofs to rewrite `chudnovskyBinarySplit` to
`chudBinarySplitExact`. -/
theorem chudBinarySplit_eq_exact (a b : Nat) :
    chudnovskyBinarySplit a b = chudBinarySplitExact a b :=
  chudBinarySplitFuel_eq_exact a b (b - a)

/-- Binary-split 8-term rational sum `S_8` (`k = 0..7`) numerator and denominator. -/
def chud8Split : Nat × Nat × Int := chudnovskyBinarySplit 0 8
def chud8Num : Nat := chud8Split.2.2.natAbs
def chud8Den : Nat := chud8Split.2.1

/-- Binary-split 9-term rational sum `S_9` (`k = 0..8`) numerator and denominator. -/
def chud9Split : Nat × Nat × Int := chudnovskyBinarySplit 0 9
def chud9Num : Nat := chud9Split.2.2.natAbs
def chud9Den : Nat := chud9Split.2.1

theorem chud8_eq_partialSum8 :
    (chud8Num : Int) * ((chudPartialSum 8).den : Int) =
      (chudPartialSum 8).num * (chud8Den : Int) ∧
    (0 : Int) < (chud8Num : Int) ∧
    (chud8Split.2.2 : Int) = (chud8Num : Int) := by
  dsimp only [chud8Num, chud8Den, chud8Split]
  rw [chudBinarySplit_eq_exact]
  decide

theorem chud9_eq_partialSum9 :
    (chud9Num : Int) * ((chudPartialSum 9).den : Int) =
      (chudPartialSum 9).num * (chud9Den : Int) ∧
    (0 : Int) < (chud9Num : Int) ∧
    (chud9Split.2.2 : Int) = (chud9Num : Int) := by
  dsimp only [chud9Num, chud9Den, chud9Split]
  rw [chudBinarySplit_eq_exact]
  decide

end PiChudnovsky

-- end of file: leanasm/src/LeanAsm/PiChudnovsky/ChudnovskySeries.lean
