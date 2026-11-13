-- Path: leanasm/src/LeanAsm/PiChudnovsky/CrtMulBridge.lean
-- Stage 1 checkpoint: 192-digit two-tier Karatsuba-over-CRT-NTT arithmetic bridge.
-- Max Column: 120 Columns

import LeanAsm.CrtNttUniversal

namespace PiChudnovsky

/-- Base `10^96` (`1000^32`) boundary for direct 192-digit `karatsubaCrtNttMul192`. -/
def base96 : Nat := 1000 ^ 32

/-- Converts any `Nat` (`< 10^48`) into 16 base-1000 limbs (`CrtNtt.Vec16`). -/
def natToVec16 (n : Nat) : CrtNtt.Vec16 where
  x0  := CrtNtt.limb1000 n 0
  x1  := CrtNtt.limb1000 n 1
  x2  := CrtNtt.limb1000 n 2
  x3  := CrtNtt.limb1000 n 3
  x4  := CrtNtt.limb1000 n 4
  x5  := CrtNtt.limb1000 n 5
  x6  := CrtNtt.limb1000 n 6
  x7  := CrtNtt.limb1000 n 7
  x8  := CrtNtt.limb1000 n 8
  x9  := CrtNtt.limb1000 n 9
  x10 := CrtNtt.limb1000 n 10
  x11 := CrtNtt.limb1000 n 11
  x12 := CrtNtt.limb1000 n 12
  x13 := CrtNtt.limb1000 n 13
  x14 := CrtNtt.limb1000 n 14
  x15 := CrtNtt.limb1000 n 15

/-- Converts any `Nat` (`< 10^96`) into 32 base-1000 limbs (`CrtNtt.Vec32`). -/
def natToVec32 (n : Nat) : CrtNtt.Vec32 where
  lo := natToVec16 (n % 1000 ^ 16)
  hi := natToVec16 (n / 1000 ^ 16)

private theorem natToVec16_norm (n : Nat) : CrtNtt.isNormalizedVec16 (natToVec16 n) := by
  have h1000 : 0 < 1000 := by decide
  dsimp only [CrtNtt.isNormalizedVec16, natToVec16, CrtNtt.limb1000]
  exact ⟨Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000⟩

/-- Every `Vec32` built by `natToVec32` has all 32 limbs strictly `< 1000`. -/
theorem natToVec32_normalized (n : Nat) : CrtNtt.isNormalizedVec32 (natToVec32 n) :=
  ⟨natToVec16_norm _, natToVec16_norm _⟩

private theorem mod_mul_1000 (m M : Nat) (hM : 0 < M) :
    m % 1000 + 1000 * ((m / 1000) % M) = m % (1000 * M) := by
  have hdiv : m = 1000 * (m / 1000) + m % 1000 := (Nat.div_add_mod m 1000).symm
  have hq : m / 1000 = M * ((m / 1000) / M) + (m / 1000) % M :=
    (Nat.div_add_mod (m / 1000) M).symm
  have hlt_mod : m % 1000 < 1000 := Nat.mod_lt m (by decide)
  have hlt_q : (m / 1000) % M < M := Nat.mod_lt _ hM
  have hrem_lt : m % 1000 + 1000 * ((m / 1000) % M) < 1000 * M := by
    calc m % 1000 + 1000 * ((m / 1000) % M)
        < 1000 + 1000 * ((m / 1000) % M) := by omega
      _ = 1000 * (((m / 1000) % M) + 1) := by omega
      _ ≤ 1000 * M := Nat.mul_le_mul_left 1000 hlt_q
  have hm_eq :
      m % (1000 * M) =
        ((1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M))) % (1000 * M) := by
    congr 1
    calc m = 1000 * (m / 1000) + m % 1000 := hdiv
      _ = 1000 * (M * ((m / 1000) / M) + (m / 1000) % M) + m % 1000 :=
            congrArg (fun x => 1000 * x + m % 1000) hq
      _ = (1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M)) := by
            rw [Nat.mul_add, Nat.mul_assoc]; omega
  have hswapAdd :
      (1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M)) =
        (m % 1000 + 1000 * ((m / 1000) % M)) + (1000 * M) * ((m / 1000) / M) :=
    Nat.add_comm _ _
  rw [hm_eq, hswapAdd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

private theorem eval_limb_step (n i k : Nat) (hk : 0 < 1000 ^ k) :
    CrtNtt.limb1000 n i + 1000 * ((n / 1000 ^ (i + 1)) % 1000 ^ k) =
      (n / 1000 ^ i) % 1000 ^ (k + 1) := by
  have hpow : 1000 ^ (k + 1) = 1000 * 1000 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hdiv : (n / 1000 ^ i) / 1000 = n / 1000 ^ (i + 1) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [hpow, CrtNtt.limb1000, ← hdiv]
  exact mod_mul_1000 (n / 1000 ^ i) (1000 ^ k) hk

private theorem evalDigits1000Vec16_natToVec16 (n : Nat) (hn : n < 1000 ^ 16) :
    CrtNtt.evalDigits1000Vec16 (natToVec16 n) = n := by
  dsimp only [CrtNtt.evalDigits1000Vec16, natToVec16]
  have h15 : CrtNtt.limb1000 n 15 = (n / 1000 ^ 15) % 1000 ^ 1 := rfl
  rw [h15]
  rw [eval_limb_step n 14 1 (by decide)]
  rw [eval_limb_step n 13 2 (by decide)]
  rw [eval_limb_step n 12 3 (by decide)]
  rw [eval_limb_step n 11 4 (by decide)]
  rw [eval_limb_step n 10 5 (by decide)]
  rw [eval_limb_step n 9 6 (by decide)]
  rw [eval_limb_step n 8 7 (by decide)]
  rw [eval_limb_step n 7 8 (by decide)]
  rw [eval_limb_step n 6 9 (by decide)]
  rw [eval_limb_step n 5 10 (by decide)]
  rw [eval_limb_step n 4 11 (by decide)]
  rw [eval_limb_step n 3 12 (by decide)]
  rw [eval_limb_step n 2 13 (by decide)]
  rw [eval_limb_step n 1 14 (by decide)]
  rw [eval_limb_step n 0 15 (by decide)]
  simp [Nat.mod_eq_of_lt hn]

/-- Soundness of `natToVec32` roundtrip for all `n < 10^96` (`1000^32`). -/
theorem evalDigits1000Vec32_natToVec32 (n : Nat) (hn : n < 1000 ^ 32) :
    CrtNtt.evalDigits1000Vec32 (natToVec32 n) = n := by
  have hB16_pos : 0 < 1000 ^ 16 := by decide
  have hlo_lt : n % 1000 ^ 16 < 1000 ^ 16 := Nat.mod_lt _ hB16_pos
  have hpow32 : (1000 : Nat) ^ 32 = 1000 ^ 16 * 1000 ^ 16 := by decide
  have hhi_lt : n / 1000 ^ 16 < 1000 ^ 16 := by
    rw [hpow32] at hn
    have hdiv := Nat.div_add_mod n (1000 ^ 16)
    by_cases hlt : n / 1000 ^ 16 < 1000 ^ 16
    · exact hlt
    · have hge : 1000 ^ 16 ≤ n / 1000 ^ 16 := by omega
      have hmul : 1000 ^ 16 * 1000 ^ 16 ≤ 1000 ^ 16 * (n / 1000 ^ 16) :=
        Nat.mul_le_mul_left _ hge
      omega
  dsimp only [CrtNtt.evalDigits1000Vec32, natToVec32]
  rw [evalDigits1000Vec16_natToVec16 _ hlo_lt, evalDigits1000Vec16_natToVec16 _ hhi_lt]
  exact Nat.mod_add_div n (1000 ^ 16)

/-- Multiplies `a, b < 10^96` (`1000^32`) via verified 192-digit two-tier Karatsuba-over-CRT-NTT
(`karatsubaCrtNttMul192`), with a total `Nat.mul` fallback for `≥ 10^96`. -/
def natMul192ViaCrtNtt (a b : Nat) : Nat :=
  if a < 1000 ^ 32 ∧ b < 1000 ^ 32 then
    CrtNtt.evalDigits1000Vec64 (CrtNtt.karatsubaCrtNttMul192 (natToVec32 a) (natToVec32 b))
  else
    a * b

/-- For all `a, b < 10^96`, `natMul192ViaCrtNtt a b = a * b`, proved directly from
`CrtNtt.karatsubaCrtNttMul192_universal_sound` with zero non-standard axioms. -/
theorem natMul192ViaCrtNtt_eq_mul (a b : Nat) (ha : a < 1000 ^ 32) (hb : b < 1000 ^ 32) :
    natMul192ViaCrtNtt a b = a * b := by
  dsimp only [natMul192ViaCrtNtt]
  split
  · rw [CrtNtt.karatsubaCrtNttMul192_universal_sound _ _
        (natToVec32_normalized a) (natToVec32_normalized b),
      evalDigits1000Vec32_natToVec32 a ha, evalDigits1000Vec32_natToVec32 b hb]
  · exfalso
    rename_i hneg
    exact hneg ⟨ha, hb⟩

/-- Total equivalence `natMul192ViaCrtNtt a b = a * b` for all `a b : Nat`. -/
theorem natMul192ViaCrtNtt_total_eq_mul (a b : Nat) :
    natMul192ViaCrtNtt a b = a * b := by
  dsimp only [natMul192ViaCrtNtt]
  split
  · rename_i h
    rw [CrtNtt.karatsubaCrtNttMul192_universal_sound _ _
        (natToVec32_normalized a) (natToVec32_normalized b),
      evalDigits1000Vec32_natToVec32 a h.1, evalDigits1000Vec32_natToVec32 b h.2]
  · rfl

/-- Multiplies operands up to `10^192` (`base96^2`) by splitting into 96-digit base-`10^96` limbs and
invoking `natMul192ViaCrtNtt` on every limb pair (with `Nat.mul` fallback above `10^192`). -/
def natMulBigViaCrtNtt (a b : Nat) : Nat :=
  if a < base96 * base96 ∧ b < base96 * base96 then
    let a0 := a % base96
    let a1 := a / base96
    let b0 := b % base96
    let b1 := b / base96
    let z0 := natMul192ViaCrtNtt a0 b0
    let z1 := natMul192ViaCrtNtt a0 b1 + natMul192ViaCrtNtt a1 b0
    let z2 := natMul192ViaCrtNtt a1 b1
    z0 + base96 * (z1 + base96 * z2)
  else
    a * b

/-- Total equivalence `natMulBigViaCrtNtt a b = a * b` for all `a b : Nat`. -/
theorem natMulBigViaCrtNtt_eq_mul (a b : Nat) :
    natMulBigViaCrtNtt a b = a * b := by
  dsimp only [natMulBigViaCrtNtt]
  split
  · simp only [natMul192ViaCrtNtt_total_eq_mul]
    have ha := Nat.div_add_mod a base96
    have hb := Nat.div_add_mod b base96
    calc a % base96 * (b % base96) +
          base96 * (a % base96 * (b / base96) + a / base96 * (b % base96) +
            base96 * (a / base96 * (b / base96)))
        = a % base96 * (b % base96) + base96 * (a % base96 * (b / base96)) +
            (base96 * (a / base96 * (b % base96)) +
              base96 * (base96 * (a / base96 * (b / base96)))) := by
            simp only [Nat.mul_add, Nat.add_assoc]
      _ = a % base96 * (b % base96) + a % base96 * (base96 * (b / base96)) +
            (base96 * (a / base96) * (b % base96) +
              base96 * (a / base96) * (base96 * (b / base96))) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm]
      _ = (a % base96 + base96 * (a / base96)) * (b % base96 + base96 * (b / base96)) := by
            simp only [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
            rw [Nat.add_left_comm (a % base96 * (base96 * (b / base96)))]
      _ = a * b := by rw [Nat.add_comm (a % base96), ha, Nat.add_comm (b % base96), hb]
  · rfl

/-- Signed product over `Int` backed by `natMulBigViaCrtNtt`. -/
def intMulBigViaCrtNtt (x y : Int) : Int :=
  let p : Int := (natMulBigViaCrtNtt x.natAbs y.natAbs : Int)
  if (x < 0) == (y < 0) then p else -p

private theorem decide_natCast_lt_zero (n : Nat) : decide ((n : Int) < 0) = false := by
  rw [decide_eq_false_iff_not]
  omega

private theorem decide_negSucc_lt_zero (n : Nat) : decide (Int.negSucc n < 0) = true := by
  rw [decide_eq_true_eq]
  exact Int.negSucc_lt_zero n

/-- Total equivalence `intMulBigViaCrtNtt x y = x * y` for all `x y : Int`. -/
theorem intMulBigViaCrtNtt_eq_mul (x y : Int) :
    intMulBigViaCrtNtt x y = x * y := by
  dsimp only [intMulBigViaCrtNtt]
  rw [natMulBigViaCrtNtt_eq_mul]
  cases x with
  | ofNat a =>
      cases y with
      | ofNat b =>
          rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
          simp only [decide_natCast_lt_zero, beq_self_eq_true, ↓reduceIte,
            Int.natAbs_natCast, Int.natCast_mul]
      | negSucc b =>
          rw [Int.ofNat_eq_natCast]
          have hb_false : (false == true) = false := rfl
          simp only [decide_natCast_lt_zero, decide_negSucc_lt_zero, hb_false, Bool.false_eq_true,
            ↓reduceIte, Int.natAbs_natCast, Int.natAbs_negSucc]
          rw [Int.negSucc_eq, Int.mul_neg, Nat.succ_eq_add_one, Int.natCast_mul, Int.natCast_add,
            Int.natCast_one]
  | negSucc a =>
      cases y with
      | ofNat b =>
          rw [Int.ofNat_eq_natCast]
          have hb_false : (true == false) = false := rfl
          simp only [decide_natCast_lt_zero, decide_negSucc_lt_zero, hb_false, Bool.false_eq_true,
            ↓reduceIte, Int.natAbs_natCast, Int.natAbs_negSucc]
          rw [Int.negSucc_eq, Int.neg_mul, Nat.succ_eq_add_one, Int.natCast_mul, Int.natCast_add,
            Int.natCast_one]
      | negSucc b =>
          simp only [decide_negSucc_lt_zero, beq_self_eq_true, ↓reduceIte, Int.natAbs_negSucc]
          rw [Int.negSucc_eq, Int.negSucc_eq, Int.neg_mul, Int.mul_neg, Int.neg_neg,
            Nat.succ_eq_add_one, Nat.succ_eq_add_one, Int.natCast_mul, Int.natCast_add,
            Int.natCast_add, Int.natCast_one]

end PiChudnovsky

-- end of file: leanasm/src/LeanAsm/PiChudnovsky/CrtMulBridge.lean
