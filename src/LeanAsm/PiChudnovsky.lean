-- Path: leanasm/src/LeanAsm/PiChudnovsky.lean
-- Stage 4 checkpoint: Constructive 100-digit Chudnovsky pi certificate via CRT-NTT.
-- Max Column: 120 Columns

import LeanAsm.PiChudnovsky.CrtMulBridge
import LeanAsm.PiChudnovsky.Sqrt10005
import LeanAsm.PiChudnovsky.ChudnovskySeries

namespace PiChudnovsky

private def piLowerWith (mul : Nat → Nat → Nat) (s num den : Nat) : Nat :=
  (426880 * mul s den) / (10 ^ 5 * num)

private def piUpperWith (mul : Nat → Nat → Nat) (s num den : Nat) : Nat :=
  (426880 * mul (s + 1) den + (10 ^ 5 * num - 1)) / (10 ^ 5 * num)

private theorem piLowerWith_congr (mul1 mul2 : Nat → Nat → Nat)
    (s1 s2 num1 num2 den1 den2 : Nat)
    (hm : ∀ a b, mul1 a b = mul2 a b)
    (hs : s1 = s2) (hn : num1 = num2) (hd : den1 = den2) :
    piLowerWith mul1 s1 num1 den1 = piLowerWith mul2 s2 num2 den2 := by
  subst hs; subst hn; subst hd
  dsimp only [piLowerWith]
  rw [hm]

private theorem piUpperWith_congr (mul1 mul2 : Nat → Nat → Nat)
    (s1 s2 num1 num2 den1 den2 : Nat)
    (hm : ∀ a b, mul1 a b = mul2 a b)
    (hs : s1 = s2) (hn : num1 = num2) (hd : den1 = den2) :
    piUpperWith mul1 s1 num1 den1 = piUpperWith mul2 s2 num2 den2 := by
  subst hs; subst hn; subst hd
  dsimp only [piUpperWith]
  rw [hm]

/-- Certified lower integer bound for `π * 10^105` from `(√10005_floor, S_9)`. -/
def piLower105 : Nat :=
  piLowerWith natMulBigViaCrtNtt sqrt10005Scaled110 chud9Num chud9Den

/-- Certified upper integer bound for `π * 10^105` from `(√10005_ceil, S_8)`. -/
def piUpper105 : Nat :=
  piUpperWith natMulBigViaCrtNtt sqrt10005Scaled110 chud8Num chud8Den

/-- First 100 decimal digits of `π` (`⌊π · 10^100⌋`). -/
def piDigits100 : Nat :=
  314159265358979323846264338327950288419716939937510 * 10 ^ 50 +
    58209749445923078164062862089986280348253421170679

private theorem chud9Num_exact : chud9Num = (chudBinarySplitExact 0 9).2.2.natAbs := by
  dsimp only [chud9Num, chud9Split]
  exact congrArg (fun p => p.2.2.natAbs) (chudBinarySplit_eq_exact 0 9)

private theorem chud9Den_exact : chud9Den = (chudBinarySplitExact 0 9).2.1 := by
  dsimp only [chud9Den, chud9Split]
  exact congrArg (fun p => p.2.1) (chudBinarySplit_eq_exact 0 9)

private theorem chud8Num_exact : chud8Num = (chudBinarySplitExact 0 8).2.2.natAbs := by
  dsimp only [chud8Num, chud8Split]
  exact congrArg (fun p => p.2.2.natAbs) (chudBinarySplit_eq_exact 0 8)

private theorem chud8Den_exact : chud8Den = (chudBinarySplitExact 0 8).2.1 := by
  dsimp only [chud8Den, chud8Split]
  exact congrArg (fun p => p.2.1) (chudBinarySplit_eq_exact 0 8)

private theorem piLower105_exact :
    piLower105 = piLowerWith (· * ·) (isqrtExact sqrtTarget)
      (chudBinarySplitExact 0 9).2.2.natAbs (chudBinarySplitExact 0 9).2.1 :=
  piLowerWith_congr natMulBigViaCrtNtt (· * ·) _ _ _ _ _ _
    natMulBigViaCrtNtt_eq_mul (isqrtNewton_eq_exact sqrtTarget) chud9Num_exact chud9Den_exact

private theorem piUpper105_exact :
    piUpper105 = piUpperWith (· * ·) (isqrtExact sqrtTarget)
      (chudBinarySplitExact 0 8).2.2.natAbs (chudBinarySplitExact 0 8).2.1 :=
  piUpperWith_congr natMulBigViaCrtNtt (· * ·) _ _ _ _ _ _
    natMulBigViaCrtNtt_eq_mul (isqrtNewton_eq_exact sqrtTarget) chud8Num_exact chud8Den_exact

set_option exponentiation.threshold 1024 in
/-- Certified `10^105`-scale bracket ordering and tight width (`piUpper105 - piLower105 < 10^4`). -/
theorem pi_105_bracket_valid :
    piLower105 ≤ piUpper105 ∧ piUpper105 - piLower105 < 10 ^ 4 := by
  rw [piLower105_exact, piUpper105_exact]
  decide

set_option exponentiation.threshold 1024 in
/-- Universal Chudnovsky truncation soundness: for EVERY truncation depth `m ≥ 8`,
`[piLower105 / 10^105, piUpper105 / 10^105]` strictly brackets `426880 * √10005 / S_m`. -/
theorem pi_105_traps_all_chudnovsky_truncations (m : Nat) (hm : 8 ≤ m) :
    (piLower105 : Int) * 10 ^ 5 * (chudPartialSum m).num ≤
      (426880 * (sqrt10005Scaled110 : Int)) * ((chudPartialSum m).den : Int) ∧
    (426880 * ((sqrt10005Scaled110 : Int) + 1)) * ((chudPartialSum m).den : Int) ≤
      (piUpper105 : Int) * 10 ^ 5 * (chudPartialSum m).num := by
  obtain ⟨h8le, hle9⟩ := chudPartialSum_trapped m hm
  have h8_den_pos : (0 : Int) < ((chudPartialSum 8).den : Int) :=
    Int.natCast_pos.mpr (chudPartialSum 8).den_pos
  have h9_den_pos : (0 : Int) < ((chudPartialSum 9).den : Int) :=
    Int.natCast_pos.mpr (chudPartialSum 9).den_pos
  have hlo9 : (piLower105 : Int) * 10 ^ 5 * (chudPartialSum 9).num ≤
      (426880 * (sqrt10005Scaled110 : Int)) * ((chudPartialSum 9).den : Int) := by
    have hs : sqrt10005Scaled110 = isqrtExact sqrtTarget := isqrtNewton_eq_exact sqrtTarget
    rw [piLower105_exact, hs]
    decide
  have hhi8 : (426880 * ((sqrt10005Scaled110 : Int) + 1)) * ((chudPartialSum 8).den : Int) ≤
      (piUpper105 : Int) * 10 ^ 5 * (chudPartialSum 8).num := by
    have hs : sqrt10005Scaled110 = isqrtExact sqrtTarget := isqrtNewton_eq_exact sqrtTarget
    rw [piUpper105_exact, hs]
    decide
  have hlo_m : (piLower105 : Int) * 10 ^ 5 * (chudPartialSum m).num ≤
      (426880 * (sqrt10005Scaled110 : Int)) * ((chudPartialSum m).den : Int) := by
    unfold CRat.le at hle9
    have hmul1 :
        ((piLower105 : Int) * 10 ^ 5 * (chudPartialSum m).num) * ((chudPartialSum 9).den : Int) ≤
        ((piLower105 : Int) * 10 ^ 5 * (chudPartialSum 9).num) * ((chudPartialSum m).den : Int) := by
      have hc0 : (0 : Int) ≤ (piLower105 : Int) * 10 ^ 5 := by omega
      have hstep := Int.mul_le_mul_of_nonneg_left hle9 hc0
      have lhs_eq :
          (piLower105 : Int) * 10 ^ 5 * ((chudPartialSum m).num * ((chudPartialSum 9).den : Int)) =
          ((piLower105 : Int) * 10 ^ 5 * (chudPartialSum m).num) * ((chudPartialSum 9).den : Int) := by
        simp only [Int.mul_assoc]
      have rhs_eq :
          (piLower105 : Int) * 10 ^ 5 * ((chudPartialSum 9).num * ((chudPartialSum m).den : Int)) =
          ((piLower105 : Int) * 10 ^ 5 * (chudPartialSum 9).num) * ((chudPartialSum m).den : Int) := by
        simp only [Int.mul_assoc]
      rw [← lhs_eq, ← rhs_eq]
      exact hstep
    have hmul2 := Int.mul_le_mul_of_nonneg_right hlo9 (Int.natCast_nonneg (chudPartialSum m).den)
    have hrhs_swap :
        (426880 * (sqrt10005Scaled110 : Int)) * ((chudPartialSum 9).den : Int) *
          ((chudPartialSum m).den : Int) =
        (426880 * (sqrt10005Scaled110 : Int)) * ((chudPartialSum m).den : Int) *
          ((chudPartialSum 9).den : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm ((chudPartialSum 9).den : Int)]
    rw [hrhs_swap] at hmul2
    exact Int.le_of_mul_le_mul_right (Int.le_trans hmul1 hmul2) h9_den_pos
  have hhi_m : (426880 * ((sqrt10005Scaled110 : Int) + 1)) * ((chudPartialSum m).den : Int) ≤
      (piUpper105 : Int) * 10 ^ 5 * (chudPartialSum m).num := by
    unfold CRat.le at h8le
    have hmul1 :
        ((426880 * ((sqrt10005Scaled110 : Int) + 1)) * ((chudPartialSum m).den : Int)) *
          ((chudPartialSum 8).den : Int) =
        ((426880 * ((sqrt10005Scaled110 : Int) + 1)) * ((chudPartialSum 8).den : Int)) *
          ((chudPartialSum m).den : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm ((chudPartialSum m).den : Int)]
    have hmul2 := Int.mul_le_mul_of_nonneg_right hhi8 (Int.natCast_nonneg (chudPartialSum m).den)
    have hmul3 :
        ((piUpper105 : Int) * 10 ^ 5 * (chudPartialSum 8).num) * ((chudPartialSum m).den : Int) ≤
        ((piUpper105 : Int) * 10 ^ 5 * (chudPartialSum m).num) * ((chudPartialSum 8).den : Int) := by
      have hc0 : (0 : Int) ≤ (piUpper105 : Int) * 10 ^ 5 := by omega
      have hstep := Int.mul_le_mul_of_nonneg_left h8le hc0
      have lhs_eq :
          (piUpper105 : Int) * 10 ^ 5 * ((chudPartialSum 8).num * ((chudPartialSum m).den : Int)) =
          ((piUpper105 : Int) * 10 ^ 5 * (chudPartialSum 8).num) * ((chudPartialSum m).den : Int) := by
        simp only [Int.mul_assoc]
      have rhs_eq :
          (piUpper105 : Int) * 10 ^ 5 * ((chudPartialSum m).num * ((chudPartialSum 8).den : Int)) =
          ((piUpper105 : Int) * 10 ^ 5 * (chudPartialSum m).num) * ((chudPartialSum 8).den : Int) := by
        simp only [Int.mul_assoc]
      rw [← lhs_eq, ← rhs_eq]
      exact hstep
    have hcomb := Int.le_trans hmul2 hmul3
    rw [← hmul1] at hcomb
    exact Int.le_of_mul_le_mul_right hcomb h8_den_pos
  exact ⟨hlo_m, hhi_m⟩

set_option exponentiation.threshold 1024 in
/-- Formal 100-decimal-digit certification of `π` via 192-digit CRT-NTT + Chudnovsky. -/
theorem pi_100_digits_certified :
    piLower105 / 10 ^ 5 = piDigits100 ∧
    piUpper105 / 10 ^ 5 = piDigits100 ∧
    piDigits100 =
      314159265358979323846264338327950288419716939937510 * 10 ^ 50 +
      58209749445923078164062862089986280348253421170679 := by
  rw [piLower105_exact, piUpper105_exact]
  decide

end PiChudnovsky

-- end of file: leanasm/src/LeanAsm/PiChudnovsky.lean
