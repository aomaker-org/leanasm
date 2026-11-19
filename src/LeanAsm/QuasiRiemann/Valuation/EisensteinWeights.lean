-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/EisensteinWeights.lean
-- Explicit rational Romik lacunary recurrence coefficients c_j and computed
-- Eisenstein basis weight polynomials w(a, k) from Chiriac & Jorza
-- (arXiv:2605.09738v2, Sections 2–3), over constructive QuasiRiemann.QRat.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic

namespace LeanAsm.QuasiRiemann.Valuation.EisensteinWeights

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic

/-! ## 1. Constructive Factorial and Romik Lacunary Coefficients `c_j` -/

/-- Standard factorial on `Nat`, strictly positive for all `n`. -/
def fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1) * fact k

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

/-- Unreduced rational Romik lacunary coefficient `c_j` for `k = 6n + 2` (`1 ≤ j ≤ n`):
    `c_j = ((4n + 1)! * (6n)!) / ((6n + 1) * (2n)! * (2n + 2j - 1)! * (4n - 2j + 1)!
                                  * (2j - 1)! * (2n - 2j + 1)!)`. -/
def romikCoeffRaw (n j : Nat) : QRat :=
  let num : Nat := fact (4 * n + 1) * fact (6 * n)
  let den : Nat := (6 * n + 1) * fact (2 * n) * fact (2 * n + 2 * j - 1) *
                   fact (4 * n - 2 * j + 1) * fact (2 * j - 1) * fact (2 * n - 2 * j + 1)
  have hden : 0 < den := by
    refine Nat.mul_pos ?_ (fact_pos _)
    refine Nat.mul_pos ?_ (fact_pos _)
    refine Nat.mul_pos ?_ (fact_pos _)
    refine Nat.mul_pos ?_ (fact_pos _)
    exact Nat.mul_pos (Nat.succ_pos _) (fact_pos _)
  ⟨(num : Int), den, hden⟩

/-- Reduced rational Romik coefficient `c_j` (`QRat.reduce (romikCoeffRaw n j)`). -/
def romikCoeff (n j : Nat) : QRat :=
  QRat.reduce (romikCoeffRaw n j)

/-- Index-reflection symmetry `c_j = c_{n - j + 1}` for `1 ≤ j ≤ n`. -/
theorem romikCoeffRaw_symm (n j : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    romikCoeffRaw n j = romikCoeffRaw n (n - j + 1) := by
  unfold romikCoeffRaw
  dsimp only
  congr 1
  have h1 : 2 * n + 2 * (n - j + 1) - 1 = 4 * n - 2 * j + 1 := by omega
  have h2 : 4 * n - 2 * (n - j + 1) + 1 = 2 * n + 2 * j - 1 := by omega
  have h3 : 2 * (n - j + 1) - 1 = 2 * n - 2 * j + 1 := by omega
  have h4 : 2 * n - 2 * (n - j + 1) + 1 = 2 * j - 1 := by omega
  rw [h1, h2, h3, h4]
  ac_rfl

theorem romikCoeff_symm (n j : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    romikCoeff n j = romikCoeff n (n - j + 1) := by
  unfold romikCoeff
  rw [romikCoeffRaw_symm n j hj1 hjn]

/-! ## 2. Exact 2-Adic Valuation Formula for `romikCoeffRaw n j` -/

private theorem mul_two_left (a k : Nat) : a * (2 * k) = 2 * (a * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]

theorem v2_mul_pos {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    v2 (a * b) = v2 a + v2 b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha_mod : a % 2 = 1
    · rw [v2_odd ha_mod]
      induction b using Nat.strongRecOn with
      | ind m ihm =>
        by_cases hm_mod : m % 2 = 1
        · rw [v2_odd hm_mod]
          have hprod_odd : (a * m) % 2 = 1 := by
            rw [Nat.mul_mod, ha_mod, hm_mod]
          rw [v2_odd hprod_odd]
        · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r := ⟨m / 2, by omega⟩
          have hr_pos : 0 < r := by omega
          rw [hr, v2_two_mul hr_pos, mul_two_left, v2_two_mul (Nat.mul_pos ha hr_pos),
              ihm r (by omega) hr_pos]
          omega
    · obtain ⟨k, hk⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
      have hk_pos : 0 < k := by omega
      rw [hk, v2_two_mul hk_pos]
      have hassoc : 2 * k * b = 2 * (k * b) := Nat.mul_assoc 2 k b
      rw [hassoc, v2_two_mul (Nat.mul_pos hk_pos hb), ih k (by omega) hk_pos hb]
      omega

private theorem hammingWeight_zero : hammingWeight 0 = 0 := by
  simp

private theorem hammingWeight_le (x : Nat) : hammingWeight x ≤ x := by
  induction x using Nat.strongRecOn with
  | ind n ihn =>
    cases n with
    | zero => simp
    | succ y =>
      have hrec : hammingWeight (y + 1) = (y + 1) % 2 + hammingWeight ((y + 1) / 2) := by
        simp [hammingWeight]
      have hsub : hammingWeight ((y + 1) / 2) ≤ (y + 1) / 2 := ihn ((y + 1) / 2) (by omega)
      omega

theorem v2_fact (n : Nat) :
    v2 (fact n) = n - hammingWeight n := by
  induction n with
  | zero =>
    have hv1 : v2 1 = 0 := v2_odd rfl
    change v2 1 = 0 - hammingWeight 0
    rw [hv1, hammingWeight_zero]
  | succ m ih =>
    change v2 ((m + 1) * fact m) = (m + 1) - hammingWeight (m + 1)
    rw [v2_mul_pos (Nat.succ_pos m) (fact_pos m), ih]
    have hstep : hammingWeight (m + 1) + v2 (m + 1) = hammingWeight m + 1 :=
      hammingWeight_step (Nat.succ_pos m)
    have hle := hammingWeight_le m
    have hle1 := hammingWeight_le (m + 1)
    simp only [Nat.succ_eq_add_one] at *
    omega

/-- Exact 2-adic valuation of the numerator of `romikCoeffRaw n j` via Legendre's formula. -/
theorem v2_romikCoeffRaw_num (n j : Nat) :
    v2 (romikCoeffRaw n j).num.natAbs =
      (4 * n + 1 - hammingWeight (4 * n + 1)) + (6 * n - hammingWeight (6 * n)) := by
  change v2 (fact (4 * n + 1) * fact (6 * n)) = _
  rw [v2_mul_pos (fact_pos _) (fact_pos _), v2_fact, v2_fact]

/-! ## 3. Classical Eisenstein Polynomial Basis Weights `w(a, k)` (Structural Recursion) -/

/-- Compute row `m` of `w(a, 2m)` given previously computed rows `0 .. m - 1`. -/
def computeWeightRow (m : Nat) (prev : List (Nat × List (Nat × QRat))) : List (Nat × QRat) :=
  match m with
  | 0 => []
  | 1 => []
  | 2 => [(1, QRat.ofInt 1)]
  | 3 => [(0, QRat.ofInt 1)]
  | n + 4 =>
    let total := n + 4
    let lookup (idx a : Nat) : QRat :=
      match prev.find? (fun p => p.1 == idx) with
      | none => QRat.ofInt 0
      | some (_, row) =>
        match row.find? (fun q => q.1 == a) with
        | none => QRat.ofInt 0
        | some (_, val) => val
    let scaleDen : Nat := (total - 3) * (2 * total - 1) * (2 * total + 1)
    have hden : 0 < scaleDen := by
      refine Nat.mul_pos (Nat.mul_pos ?_ ?_) ?_ <;> omega
    let scale : QRat := ⟨3, scaleDen, hden⟩
    let as : List Nat := (List.range (total / 2 + 1)).filter fun a => (total - 2 * a) % 3 == 0
    as.map fun a =>
      let acc := (List.range (total - 3)).foldl (fun (sum : QRat) offset =>
        let p := offset + 2
        let q := total - p
        let pqFactor := QRat.ofInt (((2 * p - 1) * (2 * q - 1) : Nat) : Int)
        let conv := (List.range (a + 1)).foldl (fun (s2 : QRat) a1 =>
          let a2 := a - a1
          let w1 := lookup p a1
          let w2 := lookup q a2
          QRat.add s2 (QRat.mul w1 w2)
        ) (QRat.ofInt 0)
        QRat.add sum (QRat.mul pqFactor conv)
      ) (QRat.ofInt 0)
      (a, QRat.reduce (QRat.mul scale acc))

/-- Structurally recursive bottom-up builder for rows `0 .. m` (kernel-reducible by `rfl`). -/
def weightTableAux : Nat → List (Nat × List (Nat × QRat))
  | 0 => [(0, [])]
  | m + 1 =>
    let prev := weightTableAux m
    (m + 1, computeWeightRow (m + 1) prev) :: prev

/-- Memoized table up to `m = 32` (`k = 64`). -/
private def weightTable32 : List (Nat × List (Nat × QRat)) :=
  weightTableAux 32

/-- Computed rational coefficient `w(a, k)` in `G_k = ∑_{4a + 6b = k} w(a, k) G_4^a G_6^b`. -/
def eisensteinWeight (a k : Nat) : QRat :=
  if k % 2 = 0 then
    let m := k / 2
    let tbl := if _h : m ≤ 32 then weightTable32 else weightTableAux m
    match tbl.find? (fun p => p.1 == m) with
    | none => QRat.ofInt 0
    | some (_, row) =>
      match row.find? (fun q => q.1 == a) with
      | none => QRat.ofInt 0
      | some (_, v) => v
  else
    QRat.ofInt 0

/-- 2-adic valuation of a reduced `QRat` (`v2(q.num.natAbs) - v2(q.den)` as `Int`). -/
def qratV2 (q : QRat) : Int :=
  (v2 q.num.natAbs : Int) - (v2 q.den : Int)

/-! ## 4. Kernel-Certified Evaluations & Proposition 4 Verification (`k = 4, 8, 16`) -/

theorem weight_4_1 : eisensteinWeight 1 4 = QRat.mk' 1 1 := rfl
theorem weight_6_0 : eisensteinWeight 0 6 = QRat.mk' 1 1 := rfl
theorem weight_8_2 : eisensteinWeight 2 8 = QRat.mk' 3 7 := rfl
theorem weight_10_1 : eisensteinWeight 1 10 = QRat.mk' 5 11 := rfl
theorem weight_12_3 : eisensteinWeight 3 12 = QRat.mk' 18 143 := rfl
theorem weight_12_0 : eisensteinWeight 0 12 = QRat.mk' 25 143 := rfl
theorem weight_14_2 : eisensteinWeight 2 14 = QRat.mk' 30 143 := rfl
theorem weight_16_4 : eisensteinWeight 4 16 = QRat.mk' 9 221 := by decide
theorem weight_16_1 : eisensteinWeight 1 16 = QRat.mk' 300 2431 := by decide

/-- Concrete verification of Proposition 4 on the computed `QRat` coefficients for
    `m = 0, 1, 2` (`k = 4, 8, 16`): `v2(w(2^m, 2^(m+2))) = 0`, while all other
    non-zero coefficients `w(a, 2^(m+2))` (`a ≠ 2^m`) have `v2 > 0`. -/
theorem prop4_computed_m0 :
    qratV2 (eisensteinWeight 1 4) = 0 := by
  rw [weight_4_1]
  change (v2 1 : Int) - (v2 1 : Int) = 0
  rw [v2_odd rfl]
  rfl

theorem prop4_computed_m1 :
    qratV2 (eisensteinWeight 2 8) = 0 := by
  rw [weight_8_2]
  change (v2 3 : Int) - (v2 7 : Int) = 0
  rw [v2_odd rfl, v2_odd rfl]
  rfl

theorem prop4_computed_m2 :
    qratV2 (eisensteinWeight 4 16) = 0 ∧ 0 < qratV2 (eisensteinWeight 1 16) := by
  rw [weight_16_4, weight_16_1]
  change (v2 9 : Int) - (v2 221 : Int) = 0 ∧ 0 < (v2 300 : Int) - (v2 2431 : Int)
  have hv300 : v2 300 = 2 := by
    have h300 : (300 : Nat) = 2 * 150 := rfl
    have h150 : (150 : Nat) = 2 * 75 := rfl
    rw [h300, v2_two_mul (by decide), h150, v2_two_mul (by decide), v2_odd rfl]
  rw [v2_odd rfl, v2_odd rfl, hv300, v2_odd rfl]
  exact ⟨rfl, by decide⟩

/-- Exact 2-adic valuation of the denominator of `romikCoeffRaw n j`. -/
theorem v2_romikCoeffRaw_den (n j : Nat) :
    v2 (romikCoeffRaw n j).den =
      (2 * n - hammingWeight (2 * n)) +
      (2 * n + 2 * j - 1 - hammingWeight (2 * n + 2 * j - 1)) +
      (4 * n - 2 * j + 1 - hammingWeight (4 * n - 2 * j + 1)) +
      (2 * j - 1 - hammingWeight (2 * j - 1)) +
      (2 * n - 2 * j + 1 - hammingWeight (2 * n - 2 * j + 1)) := by
  change v2 ((6 * n + 1) * fact (2 * n) * fact (2 * n + 2 * j - 1) *
             fact (4 * n - 2 * j + 1) * fact (2 * j - 1) * fact (2 * n - 2 * j + 1)) = _
  have hp1 : 0 < (6 * n + 1) * fact (2 * n) := Nat.mul_pos (Nat.succ_pos _) (fact_pos _)
  have hp2 : 0 < (6 * n + 1) * fact (2 * n) * fact (2 * n + 2 * j - 1) :=
    Nat.mul_pos hp1 (fact_pos _)
  have hp3 : 0 < (6 * n + 1) * fact (2 * n) * fact (2 * n + 2 * j - 1) *
                 fact (4 * n - 2 * j + 1) := Nat.mul_pos hp2 (fact_pos _)
  have hp4 : 0 < (6 * n + 1) * fact (2 * n) * fact (2 * n + 2 * j - 1) *
                 fact (4 * n - 2 * j + 1) * fact (2 * j - 1) := Nat.mul_pos hp3 (fact_pos _)
  rw [v2_mul_pos hp4 (fact_pos _), v2_mul_pos hp3 (fact_pos _), v2_mul_pos hp2 (fact_pos _),
      v2_mul_pos hp1 (fact_pos _), v2_mul_pos (Nat.succ_pos _) (fact_pos _)]
  have hodd : (6 * n + 1) % 2 = 1 := by omega
  rw [v2_odd hodd, v2_fact, v2_fact, v2_fact, v2_fact, v2_fact]
  omega

/-- Exact signed 2-adic valuation of `romikCoeffRaw n j` (Chiriac & Jorza, §3.1, p. 4):
    `v2(c_j) = s(6n) + s(2n) + s(2j-1) + s(2n-2j+1) - s(4n+1) - s(2n+2j-1) - s(4n-2j+1)`. -/
theorem qratV2_romikCoeffRaw (n j : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    qratV2 (romikCoeffRaw n j) =
      (hammingWeight (2 * n) : Int) + (hammingWeight (2 * n + 2 * j - 1) : Int) +
      (hammingWeight (4 * n - 2 * j + 1) : Int) + (hammingWeight (2 * j - 1) : Int) +
      (hammingWeight (2 * n - 2 * j + 1) : Int) -
      (hammingWeight (4 * n + 1) : Int) - (hammingWeight (6 * n) : Int) + 1 := by
  unfold qratV2
  rw [v2_romikCoeffRaw_num, v2_romikCoeffRaw_den]
  have h1 : hammingWeight (4 * n + 1) ≤ 4 * n + 1 := hammingWeight_le _
  have h2 : hammingWeight (6 * n) ≤ 6 * n := hammingWeight_le _
  have h3 : hammingWeight (2 * n) ≤ 2 * n := hammingWeight_le _
  have h4 : hammingWeight (2 * n + 2 * j - 1) ≤ 2 * n + 2 * j - 1 := hammingWeight_le _
  have h5 : hammingWeight (4 * n - 2 * j + 1) ≤ 4 * n - 2 * j + 1 := hammingWeight_le _
  have h6 : hammingWeight (2 * j - 1) ≤ 2 * j - 1 := hammingWeight_le _
  have h7 : hammingWeight (2 * n - 2 * j + 1) ≤ 2 * n - 2 * j + 1 := hammingWeight_le _
  have hb1 : 1 ≤ 2 * n + 2 * j := by omega
  have hb2 : 2 * j ≤ 4 * n := by omega
  have hb3 : 1 ≤ 2 * j := by omega
  have hb4 : 2 * j ≤ 2 * n := by omega
  simp only [Int.natCast_add, Int.ofNat_sub h1, Int.ofNat_sub h2, Int.ofNat_sub h3,
             Int.ofNat_sub h4, Int.ofNat_sub h5, Int.ofNat_sub h6, Int.ofNat_sub h7,
             Int.ofNat_sub hb1, Int.ofNat_sub hb2, Int.ofNat_sub hb3, Int.ofNat_sub hb4]
  omega

/-! ## 5. Romik Lacunary Convolution Operator & Kernel-Certified Checks (`n = 1, 2`) -/

/-- Unscaled Romik lacunary convolution for `(a, n)`:
    `∑_{j=1}^n c_j ∑_{a1 + a2 = a} w(a1, 2n + 2j) w(a2, 4n - 2j + 2)`. -/
def romikLacunaryRaw (a n : Nat) : QRat :=
  let acc := (List.range n).foldl (fun (sum : QRat) idx =>
    let j := idx + 1
    let cj := romikCoeff n j
    let k1 := 2 * n + 2 * j
    let k2 := 4 * n - 2 * j + 2
    let conv := (List.range (a + 1)).foldl (fun (s2 : QRat) a1 =>
      let a2 := a - a1
      QRat.add s2 (QRat.mul (eisensteinWeight a1 k1) (eisensteinWeight a2 k2))
    ) (QRat.ofInt 0)
    QRat.add sum (QRat.mul cj conv)
  ) (QRat.ofInt 0)
  QRat.reduce acc

theorem romik_n1_j1_val :
    romikCoeff 1 1 = QRat.mk' 1200 7 := by decide

theorem romik_lacunary_n1_matches_classical :
    QRat.reduce (QRat.mul (QRat.mk' 1 400) (romikLacunaryRaw 2 1)) = eisensteinWeight 2 8 := by
  decide

theorem romik_n2_symm_val :
    romikCoeff 2 1 = romikCoeff 2 2 :=
  romikCoeff_symm 2 1 (by decide) (by decide)

/-! ## 6. Extension to `m = 3` (`k = 32`) & Romik `n = 2` (`k = 14`) -/

set_option maxRecDepth 8192 in
theorem weight_32_8 :
    eisensteinWeight 8 32 = QRat.mk' 18063 43908059 := by decide

set_option maxRecDepth 8192 in
theorem weight_32_5 :
    eisensteinWeight 5 32 = QRat.mk' 16297669800 2321726435743 := by decide

set_option maxRecDepth 8192 in
theorem weight_32_2 :
    eisensteinWeight 2 32 = QRat.mk' 12157525500 2321726435743 := by decide

/-- Exact rational weights at `k = 32` (`m = 3`, `2^(m+2) = 32`):
    diagonal `a = 8` (`G_4^8`) has odd numerator and odd denominator (`v2 = 0`),
    while off-diagonal `a = 5` (`G_4^5 G_6^2`) and `a = 2` (`G_4^2 G_6^4`) have `v2 > 0`. -/
theorem prop4_computed_m3 :
    qratV2 (eisensteinWeight 8 32) = 0 ∧
    0 < qratV2 (eisensteinWeight 5 32) ∧
    0 < qratV2 (eisensteinWeight 2 32) := by
  rw [weight_32_8, weight_32_5, weight_32_2]
  dsimp only [qratV2, QRat.mk', Int.natAbs]
  constructor
  · have h1 : v2 18063 = 0 := v2_odd rfl
    have h2 : v2 43908059 = 0 := v2_odd rfl
    omega
  · constructor
    · have h1 : v2 2321726435743 = 0 := v2_odd rfl
      have h2 : 16297669800 = 2 * 8148834900 := rfl
      have h3 : v2 16297669800 = v2 8148834900 + 1 := by
        rw [h2, v2_two_mul (by decide)]; omega
      have h4 : v2 2321726435743 = 0 := h1
      omega
    · have h1 : v2 2321726435743 = 0 := v2_odd rfl
      have h2 : 12157525500 = 2 * 6078762750 := rfl
      have h3 : v2 12157525500 = v2 6078762750 + 1 := by
        rw [h2, v2_two_mul (by decide)]; omega
      have h4 : v2 2321726435743 = 0 := h1
      omega

/-- At `n = 2` (`k = 14`), `c_1 = c_2`, so the sparse Romik convolution reproduces
    the ratio `w(2, 14) / w(0, 14) = 30 / 25 = 6 / 5` across both monomials `G_4^2 G_6` and `G_6^2`. -/
theorem romik_lacunary_n2_ratio :
    QRat.reduce (QRat.mul (romikLacunaryRaw 2 2) (eisensteinWeight 0 14)) =
      QRat.reduce (QRat.mul (romikLacunaryRaw 0 2) (eisensteinWeight 2 14)) := by
  decide

/-! ## 7. Extension to `m = 4` (`k = 64`) -/

set_option maxRecDepth 8192 in
theorem weight_64_16 :
    eisensteinWeight 16 64 = QRat.mk' 2913885327735 68873858806309696867 := by decide

set_option maxRecDepth 8192 in
theorem weight_64_13 :
    eisensteinWeight 13 64 = QRat.mk' 600121535239657362071423070000 182366210209966086621041627701355557 := by decide

set_option maxRecDepth 8192 in
theorem weight_64_10 :
    eisensteinWeight 10 64 = QRat.mk' 3727457709186834823657216329000 147160378123100046732809653241634407 := by decide

set_option maxRecDepth 8192 in
theorem weight_64_7 :
    eisensteinWeight 7 64 =
      QRat.mk' 25836415074618238879673986008000000 658837012857118909222788817562797240139 := by decide

set_option maxRecDepth 8192 in
theorem weight_64_4 :
    eisensteinWeight 4 64 = QRat.mk' 64914423658947331536966724687500 5444933990554701729113957169940473059 := by decide

set_option maxRecDepth 8192 in
theorem weight_64_1 :
    eisensteinWeight 1 64 = QRat.mk' 4855259205271031250000 13732027066273772079835632049 := by decide

/-- Exact rational weights at `k = 64` (`m = 4`, `2^(m+2) = 64`):
    diagonal `a = 16` (`G_4^16`) has odd numerator and odd denominator (`v2 = 0`),
    while all off-diagonal weights (`a = 13, 10, 7, 4, 1`) have `v2 > 0`. -/
theorem prop4_computed_m4 :
    qratV2 (eisensteinWeight 16 64) = 0 ∧
    0 < qratV2 (eisensteinWeight 13 64) ∧
    0 < qratV2 (eisensteinWeight 10 64) ∧
    0 < qratV2 (eisensteinWeight 7 64) ∧
    0 < qratV2 (eisensteinWeight 4 64) ∧
    0 < qratV2 (eisensteinWeight 1 64) := by
  rw [weight_64_16, weight_64_13, weight_64_10, weight_64_7, weight_64_4, weight_64_1]
  dsimp only [qratV2, QRat.mk', Int.natAbs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : v2 2913885327735 = 0 := v2_odd rfl
    have h2 : v2 68873858806309696867 = 0 := v2_odd rfl
    omega
  · have h1 : v2 182366210209966086621041627701355557 = 0 := v2_odd rfl
    have h2 : (600121535239657362071423070000 : Nat) = 2 * 300060767619828681035711535000 := rfl
    have h3 : v2 600121535239657362071423070000 = v2 300060767619828681035711535000 + 1 := by
      rw [h2, v2_two_mul (by decide)]; omega
    omega
  · have h1 : v2 147160378123100046732809653241634407 = 0 := v2_odd rfl
    have h2 : (3727457709186834823657216329000 : Nat) = 2 * 1863728854593417411828608164500 := rfl
    have h3 : v2 3727457709186834823657216329000 = v2 1863728854593417411828608164500 + 1 := by
      rw [h2, v2_two_mul (by decide)]; omega
    omega
  · have h1 : v2 658837012857118909222788817562797240139 = 0 := v2_odd rfl
    have h2 : (25836415074618238879673986008000000 : Nat) = 2 * 12918207537309119439836993004000000 := rfl
    have h3 : v2 25836415074618238879673986008000000 = v2 12918207537309119439836993004000000 + 1 := by
      rw [h2, v2_two_mul (by decide)]; omega
    omega
  · have h1 : v2 5444933990554701729113957169940473059 = 0 := v2_odd rfl
    have h2 : (64914423658947331536966724687500 : Nat) = 2 * 32457211829473665768483362343750 := rfl
    have h3 : v2 64914423658947331536966724687500 = v2 32457211829473665768483362343750 + 1 := by
      rw [h2, v2_two_mul (by decide)]; omega
    omega
  · have h1 : v2 13732027066273772079835632049 = 0 := v2_odd rfl
    have h2 : (4855259205271031250000 : Nat) = 2 * 2427629602635515625000 := rfl
    have h3 : v2 4855259205271031250000 = v2 2427629602635515625000 + 1 := by
      rw [h2, v2_two_mul (by decide)]; omega
    omega

end LeanAsm.QuasiRiemann.Valuation.EisensteinWeights

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/EisensteinWeights.lean
