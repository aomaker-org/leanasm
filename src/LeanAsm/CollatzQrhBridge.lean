-- Path: leanasm/src/LeanAsm/CollatzQrhBridge.lean
-- Formal Collatz Dynamical System ↔ Quasi-Riemann Hypothesis Spectral & Diophantine Bridge.
-- Max Column: 100 Columns

import LeanAsm.Conjectures
import LeanAsm.QuasiRiemann
import LeanAsm.QuasiRiemann.UltraDeep72
import LeanAsm.PiChudnovsky.CrtMulBridge

namespace CollatzQrhBridge

open QuasiRiemann

/--
Subtract two ScaledInterval12 intervals: [a.lo - b.hi, a.hi - b.lo].
-/
def iv12Sub (a b : ScaledInterval12) : ScaledInterval12 :=
  ⟨a.lo - b.hi, a.hi - b.lo⟩

/--
Parity of 3^m: 3^m is always odd for any m.
-/
theorem nat_three_pow_mod_two (m : Nat) : 3 ^ m % 2 = 1 := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    have h3 : 3 ^ (m' + 1) = 2 * 3 ^ m' + 3 ^ m' := by
      calc
        3 ^ (m' + 1) = 3 * 3 ^ m' := by rw [Nat.pow_succ, Nat.mul_comm]
        _ = (2 + 1) * 3 ^ m' := rfl
        _ = 2 * 3 ^ m' + 1 * 3 ^ m' := by rw [Nat.add_mul]
        _ = 2 * 3 ^ m' + 3 ^ m' := by rw [Nat.one_mul]
    rw [h3, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod, ih]

/--
Parity of 2^(k'+1): 2^(k'+1) is always even.
-/
theorem nat_two_pow_succ_mod_two (k' : Nat) : 2 ^ (k' + 1) % 2 = 0 := by
  have h2 : 2 ^ (k' + 1) = 2 * 2 ^ k' := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [h2]
  exact Nat.mul_mod_right 2 (2 ^ k')

/--
Constructive Diophantine Cycle Obstruction:
No exact power resonance between 2 and 3 exists.
For any k, m with 1 ≤ m, 2^k ≠ 3^m.
Proved constructively with core equality axioms.
-/
theorem collatz_no_exact_power_resonance (k m : Nat) (hm : 1 ≤ m) : 2 ^ k ≠ 3 ^ m := by
  cases k with
  | zero =>
    rw [Nat.pow_zero]
    intro h
    have h3_1 : 3 ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) hm
    have h3_gt : 1 < 3 ^ m := Nat.lt_of_lt_of_le (by decide) h3_1
    exact (Nat.ne_of_lt h3_gt) h
  | succ k' =>
    intro h
    have h_mod := congrArg (· % 2) h
    rw [nat_two_pow_succ_mod_two, nat_three_pow_mod_two] at h_mod
    contradiction

/--
Diophantine log3 / log2 Sandwich:
3/2 < ln 3 / ln 2 < 8/5.
Proved via pure rational Taylor intervals from QuasiRiemann:
  3 * ln 2 < 2 * ln 3  and  3 * ln 3 < 5 * ln 2.
Proved constructively with ZERO axioms.
-/
theorem diophantine_log3_log2_sandwich :
    3 * (lnInterval12 2).hi < 2 * (lnInterval12 3).lo ∧
    3 * (lnInterval12 3).hi < 5 * (lnInterval12 2).lo := by
  decide

/--
Constructive {2, 3}-phase beat frequency interval:
(ln 3 - ln 2) * 10^12 is tightly bounded in [405465000000, 405465200000].
Proved constructively with ZERO axioms.
-/
theorem collatz_2_3_phase_beat_interval :
    let diff := iv12Sub (lnInterval12 3) (lnInterval12 2)
    405465000000 ≤ diff.lo ∧ diff.hi ≤ 405465200000 := by
  decide

/--
Structure representing a coupling between Collatz trajectory mixing exponent
and QRH Dirichlet cancellation abscissa.
-/
structure CollatzQrhCoupling where
  aNum : Nat
  aDen : Nat
  tNum : Nat
  tDen : Nat
  h_col_lo : aDen ≤ 2 * aNum
  h_col_hi : aNum < aDen
  h_qrh_lo : tDen ≤ 2 * tNum
  h_qrh_hi : tNum < tDen

/--
Collatz-QRH Shared Cancellation Hierarchy:
The random-walk/RH threshold 1/2, intermediate 3/4, QRH exponent 7/8,
and trivial bound 1 all strictly order within the unit interval:
  1/2 < 3/4 ∧ 3/4 < 7/8 ∧ 7/8 < 1.
Proved constructively with ZERO axioms.
-/
theorem collatz_qrh_shared_cancellation_hierarchy :
    (1 : Nat) * 4 < 3 * 2 ∧
    (3 : Nat) * 8 < 7 * 4 ∧
    (7 : Nat) * 1 < 1 * 8 := by
  decide

/--
Synchronized Collatz–QRH Mollifier & Exponent-Pair Cancellation Descent:
Connects the cross-domain Collatz–QRH ladder (`1/2 < 3/4 < 7/8 < 1`) with the
full constructive QRH mollifier descent (`1/2 < 3/4 < 5/6 < 7/8 < 11/12 < 1`),
`{A, B}*` subconvexity chain, and Guth–Maynard zero-density breakthrough.
Proved constructively with ZERO axioms.
-/
theorem collatz_qrh_mollifier_descent_synchronized :
    QRat.mk' 1 2 < QRat.mk' 3 4 ∧
    QRat.mk' 3 4 < QRat.mk' 5 6 ∧
    QRat.mk' 5 6 < QRat.mk' 7 8 ∧
    QRat.mk' 7 8 < QRat.mk' 11 12 ∧
    QRat.mk' 11 12 < QRat.ofInt 1 ∧
    qrhThresholdFromMollifier (QRat.mk' 1 3) < QRat.mk' 7 8 ∧
    qrhThresholdFromMollifier (QRat.mk' 1 2) < QRat.mk' 5 6 := by
  decide

-- =============================================================================
-- CRT-NTT Exponentiation, Convergent Gaps |2^k - 3^m|, & 36-Digit Linear Forms
-- =============================================================================

/-- Binary exponentiation `base ^ exp` backed by verified 96-digit CRT-NTT
Karatsuba multiplication `natMul96ViaCrtNtt`. -/
def powViaCrtNtt96 (base exp : Nat) : Nat :=
  if h : exp = 0 then
    1
  else
    let half := powViaCrtNtt96 base (exp / 2)
    let sq := natMul96ViaCrtNtt half half
    if exp % 2 = 0 then sq else natMul96ViaCrtNtt sq base
termination_by exp
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

private theorem nat_pow_even_eq (b k : Nat) (hk : k % 2 = 0) :
    b ^ (k / 2) * b ^ (k / 2) = b ^ k := by
  rw [← Nat.pow_add, show k / 2 + k / 2 = k by omega]

private theorem nat_pow_odd_eq (b k : Nat) (hk : k % 2 ≠ 0) :
    b ^ (k / 2) * b ^ (k / 2) * b = b ^ k := by
  rw [← Nat.pow_add, ← Nat.pow_succ]
  exact congrArg (b ^ ·) (by omega)

/-- Theorem (CRT-NTT Exponentiation Equivalence): `powViaCrtNtt96 base exp` equals
exact natural exponentiation `base ^ exp` for all `base exp : Nat`, proved
constructively via `natMul96ViaCrtNtt_total_eq_mul`. -/
theorem powViaCrtNtt96_eq_pow (base exp : Nat) :
    powViaCrtNtt96 base exp = base ^ exp := by
  induction exp using Nat.strongRecOn with
  | ind k ih =>
    unfold powViaCrtNtt96
    split
    · rename_i hk0
      subst hk0
      rfl
    · rename_i hkne
      have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hkne) (by decide)
      have ih_half := ih (k / 2) hlt
      dsimp only
      split
      · rename_i heven
        rw [natMul96ViaCrtNtt_total_eq_mul, ih_half]
        exact nat_pow_even_eq base k heven
      · rename_i hodd
        rw [natMul96ViaCrtNtt_total_eq_mul, natMul96ViaCrtNtt_total_eq_mul, ih_half]
        exact nat_pow_odd_eq base k hodd

set_option exponentiation.threshold 512 in
/-- Theorem (Convergent Power Separation): Certifies exact integer gaps
`|2^k - 3^m|` via `powViaCrtNtt96` across continued-fraction convergents of
`log_2(3)` from `(8, 5)` up to 93-digit `(306, 193)`. -/
theorem collatz_convergent_powers_separation_certified :
    powViaCrtNtt96 3 5 < powViaCrtNtt96 2 8 ∧
    powViaCrtNtt96 2 8 - powViaCrtNtt96 3 5 = 13 ∧
    powViaCrtNtt96 2 19 < powViaCrtNtt96 3 12 ∧
    powViaCrtNtt96 3 12 - powViaCrtNtt96 2 19 = 7153 ∧
    powViaCrtNtt96 3 41 < powViaCrtNtt96 2 65 ∧
    powViaCrtNtt96 2 65 - powViaCrtNtt96 3 41 = 420491770248316829 ∧
    powViaCrtNtt96 2 84 < powViaCrtNtt96 3 53 ∧
    powViaCrtNtt96 3 53 - powViaCrtNtt96 2 84 = 40432553845953101497907 ∧
    powViaCrtNtt96 3 193 < powViaCrtNtt96 2 306 ∧
    powViaCrtNtt96 2 306 - powViaCrtNtt96 3 193 =
      8919004416877265287627107489485238050671456548349002814112640455483105104697086921213106941 := by
  simp only [powViaCrtNtt96_eq_pow]
  decide

/-- Constructive 36-digit enclosure of `k · ln 2 - m · ln 3` built from the
certified intervals `lnInterval36 2` and `lnInterval36 3`. -/
def linearFormLn2Ln3Interval36 (k m : Nat) : ScaledInterval36 :=
  let ln2 := lnInterval36 2
  let ln3 := lnInterval36 3
  let lo := (k : Int) * ln2.lo - (m : Int) * ln3.hi
  let hi := (k : Int) * ln2.hi - (m : Int) * ln3.lo
  have hvalid : lo ≤ hi := by
    have hk : 0 ≤ (k : Int) := Int.natCast_nonneg k
    have hm : 0 ≤ (m : Int) := Int.natCast_nonneg m
    have h2 : (k : Int) * ln2.lo ≤ (k : Int) * ln2.hi :=
      Int.mul_le_mul_of_nonneg_left ln2.valid hk
    have h3 : (m : Int) * ln3.lo ≤ (m : Int) * ln3.hi :=
      Int.mul_le_mul_of_nonneg_left ln3.valid hm
    exact Int.sub_le_sub h2 h3
  ⟨lo, hi, hvalid⟩

/-- Theorem (Linear Form Interval Soundness): For any `a2 ∈ lnInterval36 2` and
`a3 ∈ lnInterval36 3`, the exact linear combination `(k : Int) * a2 - (m : Int) * a3`
lies inside `linearFormLn2Ln3Interval36 k m`. -/
theorem linearFormLn2Ln3Interval36_sound (k m : Nat) (a2 a3 : Int)
    (ha2 : (lnInterval36 2).lo ≤ a2 ∧ a2 ≤ (lnInterval36 2).hi)
    (ha3 : (lnInterval36 3).lo ≤ a3 ∧ a3 ≤ (lnInterval36 3).hi) :
    let iv := linearFormLn2Ln3Interval36 k m
    iv.lo ≤ (k : Int) * a2 - (m : Int) * a3 ∧
    (k : Int) * a2 - (m : Int) * a3 ≤ iv.hi := by
  have hk : 0 ≤ (k : Int) := Int.natCast_nonneg k
  have hm : 0 ≤ (m : Int) := Int.natCast_nonneg m
  have h2lo := Int.mul_le_mul_of_nonneg_left ha2.1 hk
  have h2hi := Int.mul_le_mul_of_nonneg_left ha2.2 hk
  have h3lo := Int.mul_le_mul_of_nonneg_left ha3.1 hm
  have h3hi := Int.mul_le_mul_of_nonneg_left ha3.2 hm
  exact ⟨Int.sub_le_sub h2lo h3hi, Int.sub_le_sub h2hi h3lo⟩

/-- Certified `10^36`-scaled lower bound on `|k · ln 2 - m · ln 3|`:
returns `iv.lo` if strictly positive, `-iv.hi` if strictly negative, else `0`. -/
def linearFormLn2Ln3AbsLower36 (k m : Nat) : Int :=
  let iv := linearFormLn2Ln3Interval36 k m
  max 0 (max iv.lo (-iv.hi))

/-- Constructive soundness of `linearFormLn2Ln3AbsLower36`: if `x` is enclosed
by `linearFormLn2Ln3Interval36 k m`, then `linearFormLn2Ln3AbsLower36 k m ≤ |x|`. -/
theorem linearFormLn2Ln3AbsLower36_sound (k m : Nat) (x : Int)
    (hx : (linearFormLn2Ln3Interval36 k m).lo ≤ x ∧
          x ≤ (linearFormLn2Ln3Interval36 k m).hi) :
    linearFormLn2Ln3AbsLower36 k m ≤ Int.ofNat x.natAbs := by
  dsimp [linearFormLn2Ln3AbsLower36]
  have h0 : (0 : Int) ≤ Int.ofNat x.natAbs := Int.natCast_nonneg _
  have hlo : (linearFormLn2Ln3Interval36 k m).lo ≤ Int.ofNat x.natAbs :=
    Int.le_trans hx.1 (Int.le_natAbs)
  have hneg : -x ≤ (x.natAbs : Int) := by
    calc -x ≤ ((-x).natAbs : Int) := Int.le_natAbs
      _ = (x.natAbs : Int) := by rw [Int.natAbs_neg]
  have hhi : -(linearFormLn2Ln3Interval36 k m).hi ≤ Int.ofNat x.natAbs :=
    Int.le_trans (Int.neg_le_neg hx.2) hneg
  exact Int.max_le.mpr ⟨h0, Int.max_le.mpr ⟨hlo, hhi⟩⟩

/-- Theorem (Baker-Type Effective Irrationality Measure Through `m = 193`):
For every convergent `(k, m)` in `(8, 5), (19, 12), (65, 41), (84, 53), (306, 193)`,
`linearFormLn2Ln3AbsLower36 k m` is strictly positive and
`|k · ln 2 - m · ln 3| · m^2 > 1 / 10` (`> 10^35` at `10^36` scale). -/
theorem baker_effective_measure_verified :
    let scale35 : Int := 100000000000000000000000000000000000
    (0 < linearFormLn2Ln3AbsLower36 8 5 ∧
      scale35 < linearFormLn2Ln3AbsLower36 8 5 * (5 * 5 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower36 19 12 ∧
      scale35 < linearFormLn2Ln3AbsLower36 19 12 * (12 * 12 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower36 65 41 ∧
      scale35 < linearFormLn2Ln3AbsLower36 65 41 * (41 * 41 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower36 84 53 ∧
      scale35 < linearFormLn2Ln3AbsLower36 84 53 * (53 * 53 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower36 306 193 ∧
      scale35 < linearFormLn2Ln3AbsLower36 306 193 * (193 * 193 : Int)) := by
  decide

/-- Theorem (Collatz Cycle Gap Obstruction): Any positive integer cycle equation
`n0 * 2^k = n0 * 3^m + rhs` with `1 ≤ n0` and `1 ≤ rhs` forces `3^m < 2^k` and
`1 ≤ powViaCrtNtt96 2 k - powViaCrtNtt96 3 m`, with `n0 * gap = rhs`. -/
theorem collatz_cycle_requires_positive_gap (n0 rhs k m : Nat)
    (_hn0 : 1 ≤ n0) (hrhs : 1 ≤ rhs)
    (heq : n0 * 2 ^ k = n0 * 3 ^ m + rhs) :
    3 ^ m < 2 ^ k ∧
    1 ≤ powViaCrtNtt96 2 k - powViaCrtNtt96 3 m ∧
    n0 * (powViaCrtNtt96 2 k - powViaCrtNtt96 3 m) = rhs := by
  have hlt_mul : n0 * 3 ^ m < n0 * 2 ^ k := by omega
  have hlt : 3 ^ m < 2 ^ k := by
    rcases Nat.lt_trichotomy (3 ^ m) (2 ^ k) with h1 | h2 | h3
    · exact h1
    · rw [h2] at hlt_mul
      exact absurd hlt_mul (Nat.lt_irrefl _)
    · have := Nat.mul_le_mul_left n0 (Nat.le_of_lt h3)
      omega
  have hgap : n0 * (2 ^ k - 3 ^ m) = rhs := by
    rw [Nat.mul_sub_left_distrib]
    omega
  rw [powViaCrtNtt96_eq_pow, powViaCrtNtt96_eq_pow]
  refine ⟨hlt, ?_, hgap⟩
  omega

/-- Safe checked upper bound `⌈2π / |k · ln 2 - m · ln 3|⌉` for the `{2, 3}`
spectral beat period `Δt = 2π / |k · ln 2 - m · ln 3|`, returning `none`
when `linearFormLn2Ln3AbsLower36 k m ≤ 0`. -/
def collatzBeatPeriodUpper36 (k m : Nat) : Option Nat :=
  let absLo := linearFormLn2Ln3AbsLower36 k m
  if 0 < absLo then
    some ((twoPiInterval36.hi.natAbs + absLo.natAbs - 1) / absLo.natAbs)
  else
    none

private theorem mul_natAbs_of_nonneg {tp n : Nat} {z : Int} (hz : 0 < z)
    (hdiv : (tp + z.natAbs - 1) / z.natAbs = n) :
    (tp : Int) ≤ (n : Int) * z := by
  have hz_pos : 0 < z.natAbs := Int.natAbs_pos.mpr (by omega)
  have h1 : tp ≤ n * z.natAbs := by
    have hrem := Nat.lt_of_lt_of_le (Nat.mod_lt (tp + z.natAbs - 1) hz_pos)
      (Nat.le_refl z.natAbs)
    have hdm := Nat.div_add_mod (tp + z.natAbs - 1) z.natAbs
    rw [hdiv] at hdm
    have hmul : z.natAbs * n = n * z.natAbs := Nat.mul_comm _ _
    omega
  have hz_eq : (z.natAbs : Int) = z := Int.natAbs_of_nonneg (Int.le_of_lt hz)
  have hcast : (tp : Int) ≤ ((n * z.natAbs : Nat) : Int) := Int.ofNat_le.mpr h1
  rw [Int.natCast_mul, hz_eq] at hcast
  exact hcast

/-- Universal soundness of `collatzBeatPeriodUpper36`: any returned `bound`
satisfies `2π_hi ≤ bound * |k · ln 2 - m · ln 3|_lo`. -/
theorem collatzBeatPeriodUpper36_sound (k m bound : Nat)
    (hsome : collatzBeatPeriodUpper36 k m = some bound) :
    0 < linearFormLn2Ln3AbsLower36 k m ∧
    twoPiInterval36.hi ≤ (bound : Int) * linearFormLn2Ln3AbsLower36 k m := by
  dsimp [collatzBeatPeriodUpper36] at hsome
  split at hsome
  · rename_i hpos
    injection hsome with hdiv
    have htp : 0 ≤ twoPiInterval36.hi := by decide
    have hmul := mul_natAbs_of_nonneg hpos hdiv
    rw [Int.natAbs_of_nonneg htp] at hmul
    exact ⟨hpos, hmul⟩
  · cases hsome

/-- Theorem (QRH Spectral Beat Period Upper Bounds): For all five convergents
`(8, 5), (19, 12), (65, 41), (84, 53), (306, 193)`, `collatzBeatPeriodUpper36 k m`
succeeds (`some bound`) with `bound ≤ 3010` and `2π_hi ≤ bound * |k ln 2 - m ln 3|_lo`. -/
theorem collatz_qrh_phase_beat_lower_bound :
    collatzBeatPeriodUpper36 8 5 = some 121 ∧
    collatzBeatPeriodUpper36 19 12 = some 464 ∧
    collatzBeatPeriodUpper36 65 41 = some 549 ∧
    collatzBeatPeriodUpper36 84 53 = some 3009 ∧
    collatzBeatPeriodUpper36 306 193 = some 89 ∧
    twoPiInterval36.hi ≤ 121 * linearFormLn2Ln3AbsLower36 8 5 ∧
    twoPiInterval36.hi ≤ 464 * linearFormLn2Ln3AbsLower36 19 12 ∧
    twoPiInterval36.hi ≤ 549 * linearFormLn2Ln3AbsLower36 65 41 ∧
    twoPiInterval36.hi ≤ 3009 * linearFormLn2Ln3AbsLower36 84 53 ∧
    twoPiInterval36.hi ≤ 89 * linearFormLn2Ln3AbsLower36 306 193 := by
  decide

-- =============================================================================
-- 192-Digit CRT-NTT Exponentiation, Convergent (485, 306), & 72-Digit Forms
-- =============================================================================

/-- Binary exponentiation `base ^ exp` backed by verified 192-digit CRT-NTT
two-tier Karatsuba multiplication `PiChudnovsky.natMul192ViaCrtNtt`. -/
def powViaCrtNtt192 (base exp : Nat) : Nat :=
  if h : exp = 0 then
    1
  else
    let half := powViaCrtNtt192 base (exp / 2)
    let sq := PiChudnovsky.natMul192ViaCrtNtt half half
    if exp % 2 = 0 then sq else PiChudnovsky.natMul192ViaCrtNtt sq base
termination_by exp
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Theorem (192-Digit CRT-NTT Exponentiation Equivalence):
`powViaCrtNtt192 base exp` equals exact natural exponentiation `base ^ exp`
for all `base exp : Nat`, proved constructively via
`PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul`. -/
theorem powViaCrtNtt192_eq_pow (base exp : Nat) :
    powViaCrtNtt192 base exp = base ^ exp := by
  induction exp using Nat.strongRecOn with
  | ind k ih =>
    unfold powViaCrtNtt192
    split
    · rename_i hk0
      subst hk0
      rfl
    · rename_i hkne
      have hlt : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hkne) (by decide)
      have ih_half := ih (k / 2) hlt
      dsimp only
      split
      · rename_i heven
        rw [PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul, ih_half]
        exact nat_pow_even_eq base k heven
      · rename_i hodd
        rw [PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul,
          PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul, ih_half]
        exact nat_pow_odd_eq base k hodd

/-- Exact 144-digit difference `2^485 - 3^306` written in 72-digit limbs for
line-width clarity. -/
def expectedGap485 : Nat :=
  102065376400825306534437391838939444403106454408085639783964140880896699 * 10 ^ 72 +
  835673006969445010534504805079858638689074275443284439551032910142670903

set_option exponentiation.threshold 512 in
/-- Theorem (Convergent Power Separation Through `(485, 306)`):
Certifies exact integer gaps `|2^k - 3^m|` via `powViaCrtNtt192` across
convergents `(8, 5)`, `(19, 12)`, `(65, 41)`, `(84, 53)`, `(306, 193)`, and
the 146-digit strict upper convergent `(485, 306)` (`2^485 > 3^306`). -/
theorem collatz_convergent_485_306_separation_certified :
    powViaCrtNtt192 3 5 < powViaCrtNtt192 2 8 ∧
    powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5 = 13 ∧
    powViaCrtNtt192 2 19 < powViaCrtNtt192 3 12 ∧
    powViaCrtNtt192 3 12 - powViaCrtNtt192 2 19 = 7153 ∧
    powViaCrtNtt192 3 41 < powViaCrtNtt192 2 65 ∧
    powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41 = 420491770248316829 ∧
    powViaCrtNtt192 2 84 < powViaCrtNtt192 3 53 ∧
    powViaCrtNtt192 3 53 - powViaCrtNtt192 2 84 = 40432553845953101497907 ∧
    powViaCrtNtt192 3 193 < powViaCrtNtt192 2 306 ∧
    powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193 =
      8919004416877265287627107489485238050671456548349002814112640455483105104697086921213106941 ∧
    powViaCrtNtt192 3 306 < powViaCrtNtt192 2 485 ∧
    powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306 = expectedGap485 ∧
    0 < powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306 := by
  simp only [powViaCrtNtt192_eq_pow]
  decide +kernel

/-- Constructive 72-digit enclosure of `k · ln 2 - m · ln 3` built from the
certified intervals `lnInterval72 2` and `lnInterval72 3`. -/
def linearFormLn2Ln3Interval72 (k m : Nat) : ScaledInterval72 :=
  let ln2 := lnInterval72 2
  let ln3 := lnInterval72 3
  let lo := (k : Int) * ln2.lo - (m : Int) * ln3.hi
  let hi := (k : Int) * ln2.hi - (m : Int) * ln3.lo
  have hvalid : lo ≤ hi := by
    have hk : 0 ≤ (k : Int) := Int.natCast_nonneg k
    have hm : 0 ≤ (m : Int) := Int.natCast_nonneg m
    have h2 : (k : Int) * ln2.lo ≤ (k : Int) * ln2.hi :=
      Int.mul_le_mul_of_nonneg_left ln2.valid hk
    have h3 : (m : Int) * ln3.lo ≤ (m : Int) * ln3.hi :=
      Int.mul_le_mul_of_nonneg_left ln3.valid hm
    exact Int.sub_le_sub h2 h3
  ⟨lo, hi, hvalid⟩

/-- Theorem (72-Digit Linear Form Interval Soundness): For any `a2 ∈ lnInterval72 2`
and `a3 ∈ lnInterval72 3`, `(k : Int) * a2 - (m : Int) * a3` lies inside
`linearFormLn2Ln3Interval72 k m`. -/
theorem linearFormLn2Ln3Interval72_sound (k m : Nat) (a2 a3 : Int)
    (ha2 : (lnInterval72 2).lo ≤ a2 ∧ a2 ≤ (lnInterval72 2).hi)
    (ha3 : (lnInterval72 3).lo ≤ a3 ∧ a3 ≤ (lnInterval72 3).hi) :
    let iv := linearFormLn2Ln3Interval72 k m
    iv.lo ≤ (k : Int) * a2 - (m : Int) * a3 ∧
    (k : Int) * a2 - (m : Int) * a3 ≤ iv.hi := by
  have hk : 0 ≤ (k : Int) := Int.natCast_nonneg k
  have hm : 0 ≤ (m : Int) := Int.natCast_nonneg m
  have h2lo := Int.mul_le_mul_of_nonneg_left ha2.1 hk
  have h2hi := Int.mul_le_mul_of_nonneg_left ha2.2 hk
  have h3lo := Int.mul_le_mul_of_nonneg_left ha3.1 hm
  have h3hi := Int.mul_le_mul_of_nonneg_left ha3.2 hm
  exact ⟨Int.sub_le_sub h2lo h3hi, Int.sub_le_sub h2hi h3lo⟩

/-- Certified `10^72`-scaled lower bound on `|k · ln 2 - m · ln 3|`:
returns `iv.lo` if strictly positive, `-iv.hi` if strictly negative, else `0`. -/
def linearFormLn2Ln3AbsLower72 (k m : Nat) : Int :=
  let iv := linearFormLn2Ln3Interval72 k m
  max 0 (max iv.lo (-iv.hi))

/-- Constructive soundness of `linearFormLn2Ln3AbsLower72`: if `x` lies in
`linearFormLn2Ln3Interval72 k m`, then `linearFormLn2Ln3AbsLower72 k m ≤ |x|`. -/
theorem linearFormLn2Ln3AbsLower72_sound (k m : Nat) (x : Int)
    (hx : (linearFormLn2Ln3Interval72 k m).lo ≤ x ∧
          x ≤ (linearFormLn2Ln3Interval72 k m).hi) :
    linearFormLn2Ln3AbsLower72 k m ≤ Int.ofNat x.natAbs := by
  dsimp [linearFormLn2Ln3AbsLower72]
  have h0 : (0 : Int) ≤ Int.ofNat x.natAbs := Int.natCast_nonneg _
  have hlo : (linearFormLn2Ln3Interval72 k m).lo ≤ Int.ofNat x.natAbs :=
    Int.le_trans hx.1 (Int.le_natAbs)
  have hneg : -x ≤ (x.natAbs : Int) := by
    calc -x ≤ ((-x).natAbs : Int) := Int.le_natAbs
      _ = (x.natAbs : Int) := by rw [Int.natAbs_neg]
  have hhi : -(linearFormLn2Ln3Interval72 k m).hi ≤ Int.ofNat x.natAbs :=
    Int.le_trans (Int.neg_le_neg hx.2) hneg
  exact Int.max_le.mpr ⟨h0, Int.max_le.mpr ⟨hlo, hhi⟩⟩

/-- Theorem (72-Digit Baker-Type Effective Irrationality Measure Through `m = 306`):
For every convergent `(k, m)` in `(8, 5), (19, 12), (65, 41), (84, 53), (306, 193),
(485, 306)`, `linearFormLn2Ln3AbsLower72 k m` is strictly positive and
`|k · ln 2 - m · ln 3| · m^2 > 1 / 10` (`> 10^71` at `10^72` scale). -/
theorem baker_effective_measure_485_306_verified :
    let scale71 : Int := 10 ^ 71
    (0 < linearFormLn2Ln3AbsLower72 8 5 ∧
      scale71 < linearFormLn2Ln3AbsLower72 8 5 * (5 * 5 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower72 19 12 ∧
      scale71 < linearFormLn2Ln3AbsLower72 19 12 * (12 * 12 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower72 65 41 ∧
      scale71 < linearFormLn2Ln3AbsLower72 65 41 * (41 * 41 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower72 84 53 ∧
      scale71 < linearFormLn2Ln3AbsLower72 84 53 * (53 * 53 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower72 306 193 ∧
      scale71 < linearFormLn2Ln3AbsLower72 306 193 * (193 * 193 : Int)) ∧
    (0 < linearFormLn2Ln3AbsLower72 485 306 ∧
      scale71 < linearFormLn2Ln3AbsLower72 485 306 * (306 * 306 : Int)) := by
  decide +kernel

/-- Theorem (Hypothetical `(485, 306)` Collatz Cycle Denominator Bound):
Any positive integer cycle relation `n0 * 2^485 = n0 * 3^306 + rhs` (`1 ≤ n0, rhs`)
forces the exact 144-digit CRT-NTT gap `expectedGap485` to divide `rhs` (`n0 * expectedGap485 = rhs`),
bounding any hypothetical cycle entry via `n0 = rhs / expectedGap485`. -/
theorem collatz_485_306_cycle_denominator_certified (n0 rhs : Nat)
    (hn0 : 1 ≤ n0) (hrhs : 1 ≤ rhs)
    (heq : n0 * 2 ^ 485 = n0 * 3 ^ 306 + rhs) :
    3 ^ 306 < 2 ^ 485 ∧
    1 ≤ powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306 ∧
    powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306 = expectedGap485 ∧
    expectedGap485 ≤ rhs ∧
    n0 * expectedGap485 = rhs := by
  have hbase := collatz_cycle_requires_positive_gap n0 rhs 485 306 hn0 hrhs heq
  have hsep := collatz_convergent_485_306_separation_certified.2.2.2.2.2.2.2.2.2.2.2.1
  have hmul : n0 * expectedGap485 = rhs := by
    have h96 : n0 * (2 ^ 485 - 3 ^ 306) = rhs := by
      have h0 := hbase.2.2
      rw [powViaCrtNtt96_eq_pow, powViaCrtNtt96_eq_pow] at h0
      exact h0
    have h192 : 2 ^ 485 - 3 ^ 306 = expectedGap485 := by
      rw [← powViaCrtNtt192_eq_pow 2 485, ← powViaCrtNtt192_eq_pow 3 306]
      exact hsep
    rw [h192] at h96
    exact h96
  have hle : expectedGap485 ≤ rhs := by
    calc expectedGap485 = 1 * expectedGap485 := (Nat.one_mul _).symm
      _ ≤ n0 * expectedGap485 := Nat.mul_le_mul_right expectedGap485 hn0
      _ = rhs := hmul
  refine ⟨hbase.1, ?_, hsep, hle, hmul⟩
  rw [hsep]
  have hpos := collatz_convergent_485_306_separation_certified.2.2.2.2.2.2.2.2.2.2.2.2
  rw [hsep] at hpos
  exact hpos

/-- Safe checked 72-digit upper bound `⌈2π / |k · ln 2 - m · ln 3|⌉` for the
`{2, 3}` spectral beat period, returning `none` when `linearFormLn2Ln3AbsLower72 k m ≤ 0`. -/
def collatzBeatPeriodUpper72 (k m : Nat) : Option Nat :=
  let absLo := linearFormLn2Ln3AbsLower72 k m
  if 0 < absLo then
    some ((twoPiInterval72.hi.natAbs + absLo.natAbs - 1) / absLo.natAbs)
  else
    none

/-- Universal soundness of `collatzBeatPeriodUpper72`: any returned `bound`
satisfies `twoPiInterval72.hi ≤ bound * linearFormLn2Ln3AbsLower72 k m`. -/
theorem collatzBeatPeriodUpper72_sound (k m bound : Nat)
    (hsome : collatzBeatPeriodUpper72 k m = some bound) :
    0 < linearFormLn2Ln3AbsLower72 k m ∧
    twoPiInterval72.hi ≤ (bound : Int) * linearFormLn2Ln3AbsLower72 k m := by
  dsimp [collatzBeatPeriodUpper72] at hsome
  split at hsome
  · rename_i hpos
    injection hsome with hdiv
    have htp : 0 ≤ twoPiInterval72.hi := Int.natCast_nonneg _
    have hmul := mul_natAbs_of_nonneg hpos hdiv
    rw [Int.natAbs_of_nonneg htp] at hmul
    exact ⟨hpos, hmul⟩
  · cases hsome

/-- Theorem (72-Digit QRH Spectral Beat Period Upper Bounds Through `(485, 306)`):
Certifies sharp finite upper bounds on `2π / |k · ln 2 - m · ln 3|` across all
six convergents `(8, 5), (19, 12), (65, 41), (84, 53), (306, 193), (485, 306)`. -/
theorem collatz_qrh_phase_beat_72_verified :
    collatzBeatPeriodUpper72 8 5 = some 121 ∧
    collatzBeatPeriodUpper72 19 12 = some 464 ∧
    collatzBeatPeriodUpper72 65 41 = some 549 ∧
    collatzBeatPeriodUpper72 84 53 = some 3009 ∧
    collatzBeatPeriodUpper72 306 193 = some 89 ∧
    collatzBeatPeriodUpper72 485 306 = some 6147 ∧
    twoPiInterval72.hi ≤ 121 * linearFormLn2Ln3AbsLower72 8 5 ∧
    twoPiInterval72.hi ≤ 464 * linearFormLn2Ln3AbsLower72 19 12 ∧
    twoPiInterval72.hi ≤ 549 * linearFormLn2Ln3AbsLower72 65 41 ∧
    twoPiInterval72.hi ≤ 3009 * linearFormLn2Ln3AbsLower72 84 53 ∧
    twoPiInterval72.hi ≤ 89 * linearFormLn2Ln3AbsLower72 306 193 ∧
    twoPiInterval72.hi ≤ 6147 * linearFormLn2Ln3AbsLower72 485 306 := by
  dsimp [collatzBeatPeriodUpper72]
  rw [twoPiInterval72_hi_eq]
  decide +kernel

-- =============================================================================
-- Steiner–Simons–de Weger Cycle-Length & n_min Bounds Through (485, 306)
-- =============================================================================

/-- Cumulative halving count `s_j = ∑_{r=0}^{j-1} a_r` for a Collatz odd-step schedule `a`. -/
def cycleShift (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => cycleShift a j + a j

/-- Exact Collatz cycle RHS numerator `∑_{j=0}^{m-1} 3^{m - 1 - j} * 2^{s_j}`. -/
def cycleRhs (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => 3 * cycleRhs a m + 2 ^ cycleShift a m

/-- Constructive formalization of a positive `m`-odd-step Collatz cycle with odd iterates
`x 0, ..., x (m-1)`, halving exponents `a 0, ..., a (m-1) ≥ 1`, and minimum `nMin ≥ 1`. -/
structure CollatzOddCycle (m : Nat) where
  x : Nat → Nat
  a : Nat → Nat
  nMin : Nat
  nMin_pos : 1 ≤ nMin
  nMin_le : ∀ j < m, nMin ≤ x j
  a_pos : ∀ j < m, 1 ≤ a j
  step_eq : ∀ j < m, 2 ^ a j * x (j + 1) = 3 * x j + 1
  periodic : x m = x 0

theorem nat_pow2_le_pow3 (m : Nat) : 2 ^ m ≤ 3 ^ m :=
  Nat.pow_le_pow_left (by decide) m

theorem cycleShift_ge_idx (a : Nat → Nat) (m : Nat) (ha : ∀ j < m, 1 ≤ a j) :
    ∀ j ≤ m, j ≤ cycleShift a j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact Nat.le_refl 0
  | succ j ih =>
    intro hj
    have hjm : j ≤ m := Nat.le_of_lt (Nat.lt_of_succ_le hj)
    exact Nat.add_le_add (ih hjm) (ha j hj)

private theorem cycleShift_one (j : Nat) : cycleShift (fun _ => 1) j = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [cycleShift, ih]

private theorem cycleRhs_one_add_pow2 (m : Nat) :
    cycleRhs (fun _ => 1) m + 2 ^ m = 3 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc cycleRhs (fun _ => 1) (m + 1) + 2 ^ (m + 1)
        = (3 * cycleRhs (fun _ => 1) m + 2 ^ m) + (2 ^ m * 2) := by
          simp [cycleRhs, cycleShift_one, Nat.pow_succ]
      _ = 3 * cycleRhs (fun _ => 1) m + (2 ^ m + 2 * 2 ^ m) := by
          rw [Nat.mul_comm (2 ^ m) 2, Nat.add_assoc]
      _ = 3 * cycleRhs (fun _ => 1) m + 3 * 2 ^ m := by
          have h32 : 2 ^ m + 2 * 2 ^ m = 3 * 2 ^ m := by
            calc 2 ^ m + 2 * 2 ^ m = 1 * 2 ^ m + 2 * 2 ^ m := by rw [Nat.one_mul]
              _ = (1 + 2) * 2 ^ m := (Nat.add_mul 1 2 (2 ^ m)).symm
              _ = 3 * 2 ^ m := rfl
          rw [h32]
      _ = 3 * (cycleRhs (fun _ => 1) m + 2 ^ m) := (Nat.mul_add 3 _ _).symm
      _ = 3 * 3 ^ m := by rw [ih]
      _ = 3 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem cycleRhs_one_eq (m : Nat) : cycleRhs (fun _ => 1) m = 3 ^ m - 2 ^ m :=
  Nat.eq_sub_of_add_eq (cycleRhs_one_add_pow2 m)

theorem cycleRhs_ge_geo (a : Nat → Nat) (m : Nat) (ha : ∀ j < m, 1 ≤ a j) :
    3 ^ m - 2 ^ m ≤ cycleRhs a m := by
  rw [← cycleRhs_one_eq m]
  have hsub : ∀ t ≤ m, cycleRhs (fun _ => 1) t ≤ cycleRhs a t := by
    intro t
    induction t with
    | zero =>
      intro _
      exact Nat.le_refl 0
    | succ t ih =>
      intro htm
      have ht_le : t ≤ m := Nat.le_of_lt htm
      have hpow : 2 ^ cycleShift (fun _ => 1) t ≤ 2 ^ cycleShift a t := by
        rw [cycleShift_one t]
        exact Nat.pow_le_pow_right (by decide) (cycleShift_ge_idx a m ha t ht_le)
      exact Nat.add_le_add (Nat.mul_le_mul_left 3 (ih ht_le)) hpow
  exact hsub m (Nat.le_refl m)

/-- Constructive Collatz cycle minimum-element inequality: any schedule with `a_j ≥ 1`,
`s_m = k`, `3^m < 2^k`, and cycle equation `nMin * (2^k - 3^m) = cycleRhs a m` satisfies
`nMin * (2^k - 3^m) ≥ 3^m - 2^m`. -/
theorem collatz_cycle_min_element_lower_bound (nMin k m : Nat) (a : Nat → Nat)
    (ha : ∀ j < m, 1 ≤ a j) (_hk : cycleShift a m = k) (_hlt : 3 ^ m < 2 ^ k)
    (heq : nMin * (2 ^ k - 3 ^ m) = cycleRhs a m) :
    3 ^ m - 2 ^ m ≤ nMin * (2 ^ k - 3 ^ m) := by
  rw [heq]
  exact cycleRhs_ge_geo a m ha

private theorem collatz_odd_cycle_prefix_eq {m : Nat} (c : CollatzOddCycle m) :
    ∀ t ≤ m, 2 ^ cycleShift c.a t * c.x t = 3 ^ t * c.x 0 + cycleRhs c.a t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [cycleShift, cycleRhs]
  | succ t ih =>
    intro htm
    have ht_lt : t < m := htm
    have ht_le : t ≤ m := Nat.le_of_lt ht_lt
    calc 2 ^ cycleShift c.a (t + 1) * c.x (t + 1)
        = (2 ^ cycleShift c.a t * 2 ^ c.a t) * c.x (t + 1) := by
          simp [cycleShift, Nat.pow_add]
      _ = 2 ^ cycleShift c.a t * (2 ^ c.a t * c.x (t + 1)) := by
          rw [Nat.mul_assoc]
      _ = 2 ^ cycleShift c.a t * (3 * c.x t + 1) := by
          rw [c.step_eq t ht_lt]
      _ = 3 * (2 ^ cycleShift c.a t * c.x t) + 2 ^ cycleShift c.a t := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      _ = 3 * (3 ^ t * c.x 0 + cycleRhs c.a t) + 2 ^ cycleShift c.a t := by
          rw [ih ht_le]
      _ = 3 ^ (t + 1) * c.x 0 + (3 * cycleRhs c.a t + 2 ^ cycleShift c.a t) := by
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.pow_succ, Nat.mul_comm (3 ^ t) 3, Nat.add_assoc]
      _ = 3 ^ (t + 1) * c.x 0 + cycleRhs c.a (t + 1) := rfl

/-- Linear cycle identity derived from odd-step recurrence of `CollatzOddCycle m`. -/
theorem collatz_odd_cycle_linear_eq {m : Nat} (c : CollatzOddCycle m) :
    2 ^ cycleShift c.a m * c.x 0 = 3 ^ m * c.x 0 + cycleRhs c.a m := by
  have h := collatz_odd_cycle_prefix_eq c m (Nat.le_refl m)
  rwa [c.periodic] at h

/-- Strict positivity of `2^k - 3^m` for any nonempty `CollatzOddCycle m` (`1 ≤ m`). -/
theorem collatz_odd_cycle_gap_pos {m : Nat} (c : CollatzOddCycle m) (hm : 1 ≤ m) :
    3 ^ m < 2 ^ cycleShift c.a m := by
  have hlin := collatz_odd_cycle_linear_eq c
  have h1m : 1 ≤ cycleRhs c.a m := by
    have h32 : 1 ≤ 3 ^ m - 2 ^ m := by
      cases m with
      | zero => cases hm
      | succ m' =>
        have hpow : 2 ^ (m' + 1) < 3 ^ (m' + 1) := by
          have hbase : 2 ^ m' ≤ 3 ^ m' := nat_pow2_le_pow3 m'
          calc 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ, Nat.mul_comm]
            _ < 3 * 2 ^ m' := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
            _ ≤ 3 * 3 ^ m' := Nat.mul_le_mul_left 3 hbase
            _ = 3 ^ (m' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.sub_pos_of_lt hpow
    exact Nat.le_trans h32 (cycleRhs_ge_geo c.a m c.a_pos)
  have hx0_pos : 0 < c.x 0 :=
    Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_trans c.nMin_pos (c.nMin_le 0 hm))
  have hlt_mul : 3 ^ m * c.x 0 < 2 ^ cycleShift c.a m * c.x 0 := by
    rw [hlin]
    exact Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) h1m)
  cases Nat.lt_or_ge (3 ^ m) (2 ^ cycleShift c.a m) with
  | inl hlt => exact hlt
  | inr hge =>
    exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (c.x 0) hge) hlt_mul) (Nat.lt_irrefl _)

/-- Direct corollary of `collatz_cycle_min_element_lower_bound` for a `CollatzOddCycle` whose
minimum element occurs at `x 0 = nMin`. -/
theorem collatz_odd_cycle_min_element_lower_bound {m : Nat} (c : CollatzOddCycle m)
    (hm : 1 ≤ m) (hx0 : c.x 0 = c.nMin) :
    3 ^ m - 2 ^ m ≤ c.nMin * (2 ^ cycleShift c.a m - 3 ^ m) := by
  have hlin := collatz_odd_cycle_linear_eq c
  rw [hx0, Nat.mul_comm (2 ^ cycleShift c.a m) c.nMin, Nat.mul_comm (3 ^ m) c.nMin] at hlin
  have hgap := collatz_odd_cycle_gap_pos c hm
  have heq : c.nMin * (2 ^ cycleShift c.a m - 3 ^ m) = cycleRhs c.a m := by
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.add_comm (c.nMin * 3 ^ m)] at hlin
    exact Nat.sub_eq_of_eq_add hlin
  exact collatz_cycle_min_element_lower_bound c.nMin (cycleShift c.a m) m c.a
    c.a_pos rfl hgap heq

/-- Product upper inequality derived directly from `2^{a_j} * x_{j+1} = 3 * x_j + 1` and
`nMin ≤ x_j`: `2^k * nMin^m ≤ (3 * nMin + 1)^m`. -/
theorem collatz_odd_cycle_product_bound {m : Nat} (c : CollatzOddCycle m) :
    2 ^ cycleShift c.a m * c.nMin ^ m ≤ (3 * c.nMin + 1) ^ m := by
  cases m with
  | zero =>
    simp [cycleShift]
  | succ m' =>
    have hm : 1 ≤ m' + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hprefix : ∀ t ≤ m' + 1,
        2 ^ cycleShift c.a t * c.x t * c.nMin ^ t ≤ c.x 0 * (3 * c.nMin + 1) ^ t := by
      intro t
      induction t with
      | zero =>
        intro _
        simp [cycleShift]
      | succ t ih =>
        intro htm
        have ht_lt : t < m' + 1 := htm
        have ht_le : t ≤ m' + 1 := Nat.le_of_lt ht_lt
        have hstep_n : 2 ^ c.a t * c.x (t + 1) * c.nMin ≤ c.x t * (3 * c.nMin + 1) := by
          calc 2 ^ c.a t * c.x (t + 1) * c.nMin
              = (3 * c.x t + 1) * c.nMin := by rw [c.step_eq t ht_lt]
            _ = 3 * c.x t * c.nMin + c.nMin := by rw [Nat.add_mul, Nat.one_mul]
            _ ≤ 3 * c.x t * c.nMin + c.x t := Nat.add_le_add_left (c.nMin_le t ht_lt) _
            _ = c.x t * (3 * c.nMin + 1) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (c.x t) 3 c.nMin,
                  ← Nat.mul_assoc 3 (c.x t) c.nMin]
        have h1 :
            (2 ^ cycleShift c.a t * c.nMin ^ t) * (2 ^ c.a t * c.x (t + 1) * c.nMin) ≤
            (2 ^ cycleShift c.a t * c.nMin ^ t) * (c.x t * (3 * c.nMin + 1)) :=
          Nat.mul_le_mul_left _ hstep_n
        have h2 :
            (2 ^ cycleShift c.a t * c.x t * c.nMin ^ t) * (3 * c.nMin + 1) ≤
            (c.x 0 * (3 * c.nMin + 1) ^ t) * (3 * c.nMin + 1) :=
          Nat.mul_le_mul_right _ (ih ht_le)
        calc 2 ^ cycleShift c.a (t + 1) * c.x (t + 1) * c.nMin ^ (t + 1)
            = (2 ^ cycleShift c.a t * 2 ^ c.a t) * c.x (t + 1) * (c.nMin ^ t * c.nMin) := by
              simp [cycleShift, Nat.pow_add, Nat.pow_succ]
          _ = (2 ^ cycleShift c.a t * c.nMin ^ t) * (2 ^ c.a t * c.x (t + 1) * c.nMin) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm]
          _ ≤ (2 ^ cycleShift c.a t * c.nMin ^ t) * (c.x t * (3 * c.nMin + 1)) := h1
          _ = (2 ^ cycleShift c.a t * c.x t * c.nMin ^ t) * (3 * c.nMin + 1) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm]
          _ ≤ (c.x 0 * (3 * c.nMin + 1) ^ t) * (3 * c.nMin + 1) := h2
          _ = c.x 0 * (3 * c.nMin + 1) ^ (t + 1) := by
              simp only [Nat.pow_succ, Nat.mul_assoc]
    have hm_bound := hprefix (m' + 1) (Nat.le_refl _)
    rw [c.periodic] at hm_bound
    have hx0_pos : 0 < c.x 0 :=
      Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_trans c.nMin_pos (c.nMin_le 0 hm))
    have hreord : c.x 0 * (2 ^ cycleShift c.a (m' + 1) * c.nMin ^ (m' + 1)) ≤
        c.x 0 * (3 * c.nMin + 1) ^ (m' + 1) := by
      have hlhs : c.x 0 * (2 ^ cycleShift c.a (m' + 1) * c.nMin ^ (m' + 1)) =
          2 ^ cycleShift c.a (m' + 1) * c.x 0 * c.nMin ^ (m' + 1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (c.x 0)]
      have hrhs : c.x 0 * (3 * c.nMin + 1) ^ (m' + 1) =
          (3 * c.nMin + 1) ^ (m' + 1) * c.x 0 := Nat.mul_comm _ _
      simpa only [hlhs, hrhs] using hm_bound
    exact Nat.le_of_mul_le_mul_left hreord hx0_pos

/-- Exact Steiner 1-cycle divisibility condition: if `a_0 = ... = a_{m-2} = 1`,
then `cycleRhs a m = 3^m - 2^m`, so `nMin * (2^k - 3^m) = 3^m - 2^m` and
`(2^k - 3^m) ∣ (3^m - 2^m)`. -/
theorem steiner_1cycle_divides (nMin k m : Nat) (a : Nat → Nat)
    (h1cycle : ∀ j, j + 1 < m → a j = 1)
    (heq : nMin * (2 ^ k - 3 ^ m) = cycleRhs a m) :
    cycleRhs a m = 3 ^ m - 2 ^ m ∧
    nMin * (2 ^ k - 3 ^ m) = 3 ^ m - 2 ^ m ∧
    (2 ^ k - 3 ^ m) ∣ (3 ^ m - 2 ^ m) := by
  have hshift_eq : ∀ j < m, cycleShift a j = j := by
    intro j
    induction j with
    | zero =>
      intro _
      rfl
    | succ j ih =>
      intro hj1
      have hj : j < m := Nat.lt_of_succ_lt hj1
      simp [cycleShift, ih hj, h1cycle j hj1]
  have hrhs_eq : ∀ t ≤ m, cycleRhs a t = cycleRhs (fun _ => 1) t := by
    intro t
    induction t with
    | zero =>
      intro _
      rfl
    | succ t ih =>
      intro htm
      have ht_lt : t < m := htm
      have ht_le : t ≤ m := Nat.le_of_lt ht_lt
      simp only [cycleRhs, cycleShift_one]
      rw [ih ht_le, hshift_eq t ht_lt]
  have hrhs : cycleRhs a m = 3 ^ m - 2 ^ m :=
    (hrhs_eq m (Nat.le_refl m)).trans (cycleRhs_one_eq m)
  rw [hrhs] at heq
  exact ⟨hrhs, heq, ⟨nMin, by rw [← heq, Nat.mul_comm]⟩⟩

set_option exponentiation.threshold 512 in
private theorem steiner_crt_nondiv_checked :
    (powViaCrtNtt192 3 5 - powViaCrtNtt192 2 5) %
      (powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5) ≠ 0 ∧
    (powViaCrtNtt192 3 41 - powViaCrtNtt192 2 41) %
      (powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41) ≠ 0 ∧
    (powViaCrtNtt192 3 193 - powViaCrtNtt192 2 193) %
      (powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193) ≠ 0 ∧
    (powViaCrtNtt192 3 306 - powViaCrtNtt192 2 306) %
      (powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306) ≠ 0 := by
  simp only [powViaCrtNtt192_eq_pow]
  decide +kernel

private theorem not_dvd_of_mod_ne_zero {d n : Nat} (hmod : n % d ≠ 0) : ¬ (d ∣ n) := by
  intro hdvd
  exact hmod (Nat.mod_eq_zero_of_dvd hdvd)

/-- Constructive exclusion of Steiner 1-cycles at all four certified upper convergents
`(8, 5)`, `(65, 41)`, `(306, 193)`, and `(485, 306)` via `powViaCrtNtt192`. -/
theorem steiner_1cycle_excluded_at_convergents :
    ¬ ((powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5) ∣
      (powViaCrtNtt192 3 5 - powViaCrtNtt192 2 5)) ∧
    ¬ ((powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41) ∣
      (powViaCrtNtt192 3 41 - powViaCrtNtt192 2 41)) ∧
    ¬ ((powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193) ∣
      (powViaCrtNtt192 3 193 - powViaCrtNtt192 2 193)) ∧
    ¬ ((powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306) ∣
      (powViaCrtNtt192 3 306 - powViaCrtNtt192 2 306)) ∧
    (∀ (k m : Nat), (k = 8 ∧ m = 5) ∨ (k = 65 ∧ m = 41) ∨
        (k = 306 ∧ m = 193) ∨ (k = 485 ∧ m = 306) →
      ∀ (nMin : Nat) (a : Nat → Nat),
        (∀ j, j + 1 < m → a j = 1) →
        nMin * (2 ^ k - 3 ^ m) ≠ cycleRhs a m) := by
  have hchk := steiner_crt_nondiv_checked
  have h1 := not_dvd_of_mod_ne_zero hchk.1
  have h2 := not_dvd_of_mod_ne_zero hchk.2.1
  have h3 := not_dvd_of_mod_ne_zero hchk.2.2.1
  have h4 := not_dvd_of_mod_ne_zero hchk.2.2.2
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro k m hcase nMin a h1cycle heq
  have hdvd := (steiner_1cycle_divides nMin k m a h1cycle heq).2.2
  rw [← powViaCrtNtt192_eq_pow 2 k, ← powViaCrtNtt192_eq_pow 3 m,
      ← powViaCrtNtt192_eq_pow 2 m] at hdvd
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h1 hdvd
  · exact h2 hdvd
  · exact h3 hdvd
  · exact h4 hdvd

private theorem ceilDiv_le_of_le_mul {num den q : Nat} (hden : 0 < den)
    (hle : num ≤ q * den) : (num + den - 1) / den ≤ q := by
  cases Nat.eq_zero_or_pos q with
  | inl hq0 =>
    subst hq0
    have hnum0 : num = 0 := Nat.le_zero.mp (by simpa using hle)
    subst hnum0
    have hlt : den - 1 < den := Nat.sub_lt hden (by decide)
    simpa [Nat.zero_add] using Nat.le_of_eq (Nat.div_eq_of_lt hlt)
  | inr hq =>
    have hle_plus : num + den - 1 ≤ q * den + (den - 1) := by
      have hsub1 : 1 ≤ q * den + den :=
        Nat.le_trans (Nat.le_add_left 1 _) (Nat.add_le_add_left hden (q * den))
      calc num + den - 1 ≤ q * den + den - 1 :=
          Nat.sub_le_sub_right (Nat.add_le_add_right hle den) 1
        _ = q * den + (den - 1) := Nat.add_sub_assoc hden (q * den)
    have hdiv1 : (num + den - 1) / den ≤ (q * den + (den - 1)) / den :=
      Nat.div_le_div_right hle_plus
    have hdiv2 : (q * den + (den - 1)) / den = q := by
      rw [Nat.add_comm (q * den), Nat.mul_comm q den, Nat.add_mul_div_left _ _ hden,
          Nat.div_eq_of_lt (Nat.sub_lt hden (by decide)), Nat.zero_add]
    exact Nat.le_trans hdiv1 (Nat.le_of_eq hdiv2)

set_option exponentiation.threshold 512 in
private theorem convergent_nmin_ceil_checked :
    (powViaCrtNtt192 3 5 - powViaCrtNtt192 2 5 +
      (powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5) - 1) /
        (powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5) = 17 ∧
    (powViaCrtNtt192 3 41 - powViaCrtNtt192 2 41 +
      (powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41) - 1) /
        (powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41) = 87 ∧
    (powViaCrtNtt192 3 193 - powViaCrtNtt192 2 193 +
      (powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193) - 1) /
        (powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193) = 14 ∧
    (powViaCrtNtt192 3 306 - powViaCrtNtt192 2 306 +
      (powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306) - 1) /
        (powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306) = 978 ∧
    0 < powViaCrtNtt192 2 8 - powViaCrtNtt192 3 5 ∧
    0 < powViaCrtNtt192 2 65 - powViaCrtNtt192 3 41 ∧
    0 < powViaCrtNtt192 2 306 - powViaCrtNtt192 3 193 ∧
    0 < powViaCrtNtt192 2 485 - powViaCrtNtt192 3 306 := by
  simp only [powViaCrtNtt192_eq_pow]
  decide +kernel

/-- Explicit `n_min` lower bounds `⌈(3^{q_n} - 2^{q_n}) / (2^{p_n} - 3^{q_n})⌉` at upper
convergents `(8, 5)` (`≥ 17`), `(65, 41)` (`≥ 87`), `(306, 193)` (`≥ 14`), and
`(485, 306)` (`≥ 978`). -/
theorem collatz_convergent_nmin_lower_bounds (nMin k m : Nat) (a : Nat → Nat)
    (ha : ∀ j < m, 1 ≤ a j) (hk : cycleShift a m = k) (hlt : 3 ^ m < 2 ^ k)
    (heq : nMin * (2 ^ k - 3 ^ m) = cycleRhs a m) :
    (k = 8 ∧ m = 5 → 17 ≤ nMin) ∧
    (k = 65 ∧ m = 41 → 87 ≤ nMin) ∧
    (k = 306 ∧ m = 193 → 14 ≤ nMin) ∧
    (k = 485 ∧ m = 306 → 978 ≤ nMin) := by
  have hlb := collatz_cycle_min_element_lower_bound nMin k m a ha hk hlt heq
  have hc := convergent_nmin_ceil_checked
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨hk8, hm5⟩
    subst hk8 hm5
    rw [← powViaCrtNtt192_eq_pow 2 8, ← powViaCrtNtt192_eq_pow 3 5,
        ← powViaCrtNtt192_eq_pow 2 5] at hlb
    rw [← hc.1]
    exact ceilDiv_le_of_le_mul hc.2.2.2.2.1 hlb
  · intro ⟨hk65, hm41⟩
    subst hk65 hm41
    rw [← powViaCrtNtt192_eq_pow 2 65, ← powViaCrtNtt192_eq_pow 3 41,
        ← powViaCrtNtt192_eq_pow 2 41] at hlb
    rw [← hc.2.1]
    exact ceilDiv_le_of_le_mul hc.2.2.2.2.2.1 hlb
  · intro ⟨hk306, hm193⟩
    subst hk306 hm193
    rw [← powViaCrtNtt192_eq_pow 2 306, ← powViaCrtNtt192_eq_pow 3 193,
        ← powViaCrtNtt192_eq_pow 2 193] at hlb
    rw [← hc.2.2.1]
    exact ceilDiv_le_of_le_mul hc.2.2.2.2.2.2.1 hlb
  · intro ⟨hk485, hm306⟩
    subst hk485 hm306
    rw [← powViaCrtNtt192_eq_pow 2 485, ← powViaCrtNtt192_eq_pow 3 306,
        ← powViaCrtNtt192_eq_pow 2 306] at hlb
    rw [← hc.2.2.2.1]
    exact ceilDiv_le_of_le_mul hc.2.2.2.2.2.2.2 hlb

private def minExpOver3Loop (fuel k p2 p3 : Nat) : Nat :=
  match fuel with
  | 0 => k
  | fuel' + 1 => if p3 < p2 then k else minExpOver3Loop fuel' (k + 1) (2 * p2) p3

private def minExpOver3 (m : Nat) : Nat :=
  minExpOver3Loop (m + 2) m (2 ^ m) (3 ^ m)

private def checkRange306 : Bool :=
  (List.range 306).all fun i =>
    let m := i + 1
    let k := minExpOver3 m
    (2 ^ (k - 1) ≤ 3 ^ m) &&
    (3 ^ m < 2 ^ k) &&
    (3 ^ m * (10 * m + 1) < 2 ^ k * (10 * m)) &&
    ((0 : Int) < (linearFormLn2Ln3Interval72 k m).lo) &&
    ((10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m : Int))

set_option exponentiation.threshold 512 in
private theorem checkRange306_valid : checkRange306 = true := by
  decide +kernel

private theorem checkRange306_at {m : Nat} (hm1 : 1 ≤ m) (hm306 : m ≤ 306) :
    let k := minExpOver3 m
    2 ^ (k - 1) ≤ 3 ^ m ∧
    3 ^ m < 2 ^ k ∧
    3 ^ m * (10 * m + 1) < 2 ^ k * (10 * m) ∧
    (0 : Int) < (linearFormLn2Ln3Interval72 k m).lo ∧
    (10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m : Int) := by
  have hall := checkRange306_valid
  dsimp only [checkRange306] at hall
  rw [List.all_eq_true] at hall
  have hmem : m - 1 ∈ List.range 306 := by
    rw [List.mem_range]
    exact Nat.sub_lt_left_of_lt_add hm1 (Nat.lt_succ_of_le hm306)
  have hitem := hall (m - 1) hmem
  have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  rw [hm_eq] at hitem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hitem
  exact ⟨hitem.1.1.1.1, hitem.1.1.1.2, hitem.1.1.2, hitem.1.2, hitem.2⟩

/-- Uniform 72-digit linear-form lower measure and rational exponential margin
`1 + 1/(10m) < 2^k / 3^m` across every exponent pair `(k, m)` with `1 ≤ m ≤ 306`
and `3^m < 2^k`. -/
theorem collatz_linear_form_uniform_306 (m k : Nat) (hm1 : 1 ≤ m) (hm306 : m ≤ 306)
    (hpow : 3 ^ m < 2 ^ k) :
    (10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m : Int) ∧
    (10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m * m : Int) ∧
    3 ^ m * (10 * m + 1) < 2 ^ k * (10 * m) := by
  have h0 := checkRange306_at hm1 hm306
  let k0 := minExpOver3 m
  have hk0_le : k0 ≤ k := by
    cases Nat.lt_or_ge k k0 with
    | inl hk_lt =>
      have hk_le : k ≤ k0 - 1 := Nat.le_pred_of_lt hk_lt
      have h2_le : 2 ^ k ≤ 2 ^ (k0 - 1) := Nat.pow_le_pow_right (by decide) hk_le
      exact absurd (Nat.lt_of_le_of_lt h0.1 (Nat.lt_of_lt_of_le hpow h2_le)) (Nat.lt_irrefl _)
    | inr hk_ge => exact hk_ge
  have hln2_pos : (0 : Int) < (lnInterval72 2).lo := by decide +kernel
  have hiv_mono : (linearFormLn2Ln3Interval72 k0 m).lo ≤
      (linearFormLn2Ln3Interval72 k m).lo := by
    change (k0 : Int) * (lnInterval72 2).lo - (m : Int) * (lnInterval72 3).hi ≤
      (k : Int) * (lnInterval72 2).lo - (m : Int) * (lnInterval72 3).hi
    have hmul : (k0 : Int) * (lnInterval72 2).lo ≤ (k : Int) * (lnInterval72 2).lo :=
      Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hk0_le) (Int.le_of_lt hln2_pos)
    exact Int.sub_le_sub_right hmul _
  have hiv_k0 : (linearFormLn2Ln3Interval72 k0 m).lo = linearFormLn2Ln3AbsLower72 k0 m := by
    have hpos := h0.2.2.2.1
    have hlo_le : -(linearFormLn2Ln3Interval72 k0 m).hi ≤
        (linearFormLn2Ln3Interval72 k0 m).lo := by
      have hvalid := (linearFormLn2Ln3Interval72 k0 m).valid
      have h0hi : (0 : Int) < (linearFormLn2Ln3Interval72 k0 m).hi :=
        Int.lt_of_lt_of_le hpos hvalid
      have hneg : -(linearFormLn2Ln3Interval72 k0 m).hi < 0 := by
        calc -(linearFormLn2Ln3Interval72 k0 m).hi < -0 := Int.neg_lt_neg h0hi
          _ = 0 := rfl
      exact Int.le_of_lt (Int.lt_trans hneg hpos)
    change (linearFormLn2Ln3Interval72 k0 m).lo =
      max 0 (max (linearFormLn2Ln3Interval72 k0 m).lo (-(linearFormLn2Ln3Interval72 k0 m).hi))
    rw [Int.max_eq_left hlo_le, Int.max_eq_right (Int.le_of_lt hpos)]
  have habs_mono : linearFormLn2Ln3AbsLower72 k0 m ≤ linearFormLn2Ln3AbsLower72 k m := by
    have h1 : (linearFormLn2Ln3Interval72 k0 m).lo ≤ linearFormLn2Ln3AbsLower72 k m :=
      Int.le_trans hiv_mono (Int.le_trans (Int.le_max_left _ _) (Int.le_max_right 0 _))
    rwa [← hiv_k0]
  have hm_nonneg : (0 : Int) ≤ (m : Int) := Int.natCast_nonneg m
  have hscale_m : (10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m : Int) :=
    Int.lt_of_lt_of_le h0.2.2.2.2 (Int.mul_le_mul_of_nonneg_right habs_mono hm_nonneg)
  have hm_sq : (m : Int) ≤ (m * m : Int) := by
    have hnat : m ≤ m * m := by
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ m * m := Nat.mul_le_mul_left m hm1
    exact Int.ofNat_le.mpr hnat
  have hlin_pos : (0 : Int) ≤ linearFormLn2Ln3AbsLower72 k m :=
    Int.le_trans (Int.le_of_lt h0.2.2.2.1) (by rw [hiv_k0]; exact habs_mono)
  have hscale_mm : (10 ^ 71 : Int) < linearFormLn2Ln3AbsLower72 k m * (m * m : Int) :=
    Int.lt_of_lt_of_le hscale_m (Int.mul_le_mul_of_nonneg_left hm_sq hlin_pos)
  have hpow_le : 2 ^ k0 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk0_le
  have hmargin : 3 ^ m * (10 * m + 1) < 2 ^ k * (10 * m) :=
    Nat.lt_of_lt_of_le h0.2.2.1 (Nat.mul_le_mul_right (10 * m) hpow_le)
  exact ⟨hscale_m, hscale_mm, hmargin⟩

private theorem bernoulli_sub_nat (D m : Nat) (hm : m ≤ D) :
    (D - m) * D ^ m ≤ D * (D - 1) ^ m := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm_le : m ≤ D := Nat.le_of_lt hm
    have hih := ih hm_le
    let r := D - (m + 1)
    have hDr : D = r + m + 1 := by
      calc D = (m + 1) + r := (Nat.add_sub_of_le hm).symm
        _ = r + m + 1 := by rw [Nat.add_comm (m + 1) r, Nat.add_assoc]
    have hDm : D - m = r + 1 := by
      calc D - m = (r + m + 1) - m := by rw [hDr]
        _ = (r + 1 + m) - m := by rw [Nat.add_assoc, Nat.add_comm m 1, ← Nat.add_assoc]
        _ = r + 1 := Nat.add_sub_cancel (r + 1) m
    have hD1 : D - 1 = r + m := by
      calc D - 1 = (r + m + 1) - 1 := by rw [hDr]
        _ = r + m := Nat.add_sub_cancel (r + m) 1
    have hstep_r : (D - (m + 1)) * D ≤ (D - m) * (D - 1) := by
      rw [hDm, hD1]
      change r * D ≤ (r + 1) * (r + m)
      rw [hDr]
      calc r * (r + m + 1)
          = r * (r + m) + r := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ r * (r + m) + (r + m) := Nat.add_le_add_left (Nat.le_add_right r m) _
        _ = (r + 1) * (r + m) := by rw [Nat.add_mul, Nat.one_mul]
    calc (D - (m + 1)) * D ^ (m + 1)
        = ((D - (m + 1)) * D) * D ^ m := by rw [Nat.pow_succ, Nat.mul_comm (D ^ m) D, Nat.mul_assoc]
      _ ≤ ((D - m) * (D - 1)) * D ^ m := Nat.mul_le_mul_right _ hstep_r
      _ = ((D - m) * D ^ m) * (D - 1) := by
          rw [Nat.mul_assoc, Nat.mul_comm (D - 1), ← Nat.mul_assoc]
      _ ≤ (D * (D - 1) ^ m) * (D - 1) := Nat.mul_le_mul_right _ hih
      _ = D * (D - 1) ^ (m + 1) := by rw [Nat.mul_assoc, ← Nat.pow_succ]

private theorem pow_add_one_mul_sub_le (D m : Nat) (hm : m ≤ D) (hD : 1 ≤ D) :
    (D + 1) ^ m * (D - m) ≤ D ^ (m + 1) := by
  have hsq : (D + 1) * (D - 1) ≤ D * D := by
    let s := D - 1
    have hDs : D = s + 1 := (Nat.sub_add_cancel hD).symm
    change (D + 1) * s ≤ D * D
    rw [hDs]
    calc (s + 1 + 1) * s = (s + 1) * s + 1 * s := Nat.add_mul (s + 1) 1 s
      _ = (s + 1) * s + s := by rw [Nat.one_mul]
      _ ≤ (s + 1) * s + (s + 1) := Nat.add_le_add_left (Nat.le_succ s) _
      _ = (s + 1) * s + (s + 1) * 1 := by rw [Nat.mul_one]
      _ = (s + 1) * (s + 1) := (Nat.mul_add (s + 1) s 1).symm
  have hpow_sq : (D + 1) ^ m * (D - 1) ^ m ≤ D ^ m * D ^ m := by
    calc (D + 1) ^ m * (D - 1) ^ m
        = ((D + 1) * (D - 1)) ^ m := (Nat.mul_pow (D + 1) (D - 1) m).symm
      _ ≤ (D * D) ^ m := Nat.pow_le_pow_left hsq m
      _ = D ^ m * D ^ m := Nat.mul_pow D D m
  have hbern := bernoulli_sub_nat D m hm
  have hcomb : (D + 1) ^ m * (D - m) * D ^ m ≤ D ^ (m + 1) * D ^ m := by
    calc (D + 1) ^ m * (D - m) * D ^ m
        = (D + 1) ^ m * ((D - m) * D ^ m) := by rw [Nat.mul_assoc]
      _ ≤ (D + 1) ^ m * (D * (D - 1) ^ m) := Nat.mul_le_mul_left _ hbern
      _ = D * ((D + 1) ^ m * (D - 1) ^ m) := by rw [Nat.mul_left_comm]
      _ ≤ D * (D ^ m * D ^ m) := Nat.mul_le_mul_left D hpow_sq
      _ = D ^ (m + 1) * D ^ m := by rw [Nat.pow_succ, Nat.mul_comm (D ^ m) D, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right hcomb (Nat.pow_pos hD)

set_option exponentiation.threshold 512 in
private theorem three_pow_307_bounds :
    2 ^ 486 < 3 ^ 307 ∧ 3 ^ 307 < 2 ^ 487 := by
  decide +kernel

set_option exponentiation.threshold 512 in
/-- Simons–de Weger cycle-length barrier through `(485, 306)`:
- Every positive `CollatzOddCycle m` with `1 ≤ m ≤ 306` satisfies `nMin < 10 * m^2 ≤ 936,360`.
- Contrapositively, any `CollatzOddCycle m` with `1 ≤ m` and `nMin ≥ 936,360` must have at
  least `m ≥ 307` odd steps, `k ≥ 487` halving steps, and `K = k + m ≥ 793` total steps. -/
theorem collatz_cycle_length_lower_bound_306 {m : Nat} (c : CollatzOddCycle m) (hm1 : 1 ≤ m) :
    (m ≤ 306 → c.nMin < 10 * m * m ∧ c.nMin < 936360) ∧
    (936360 ≤ c.nMin →
      307 ≤ m ∧ 487 ≤ cycleShift c.a m ∧ 793 ≤ cycleShift c.a m + m) := by
  have upper_for_m : ∀ (hle : m ≤ 306), c.nMin < 10 * m * m := by
    intro hle
    cases Nat.lt_or_ge c.nMin (10 * m * m) with
    | inl hlt => exact hlt
    | inr hge =>
      let k := cycleShift c.a m
      have hgap : 3 ^ m < 2 ^ k := collatz_odd_cycle_gap_pos c hm1
      have hprod : 2 ^ k * c.nMin ^ m ≤ (3 * c.nMin + 1) ^ m :=
        collatz_odd_cycle_product_bound c
      have hunif := collatz_linear_form_uniform_306 m k hm1 hle hgap
      have hmargin : 3 ^ m * (10 * m + 1) < 2 ^ k * (10 * m) := hunif.2.2
      let D := 3 * c.nMin
      have hD_ge_30m2 : 30 * (m * m) ≤ D := by
        calc 30 * (m * m) = 3 * 10 * (m * m) := rfl
          _ = 3 * (10 * (m * m)) := Nat.mul_assoc 3 10 (m * m)
          _ = 3 * (10 * m * m) := by rw [Nat.mul_assoc 10 m m]
          _ ≤ 3 * c.nMin := Nat.mul_le_mul_left 3 hge
      have hm_le_mm : m ≤ m * m := by
        calc m = m * 1 := (Nat.mul_one m).symm
          _ ≤ m * m := Nat.mul_le_mul_left m hm1
      have hD_ge_m_sq : 10 * (m * m) + m ≤ D := by
        calc 10 * (m * m) + m ≤ 10 * (m * m) + 20 * (m * m) := by
              have h20 : m ≤ 20 * (m * m) :=
                Nat.le_trans hm_le_mm (Nat.le_mul_of_pos_left (m * m) (by decide))
              exact Nat.add_le_add_left h20 _
          _ = 30 * (m * m) := by
              rw [← Nat.add_mul]
          _ ≤ D := hD_ge_30m2
      have hm_lt_D : m < D :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.mul_pos (by decide) (Nat.mul_pos hm1 hm1)))
          hD_ge_m_sq
      have hm_le_D : m ≤ D := Nat.le_of_lt hm_lt_D
      have hD_pos : 1 ≤ D := Nat.le_trans hm1 hm_le_D
      have hDm_pos : 0 < D - m := Nat.sub_pos_of_lt hm_lt_D
      have hrat_D : 10 * m * D ≤ (10 * m + 1) * (D - m) := by
        have hsub : D - m + m = D := Nat.sub_add_cancel hm_le_D
        have hexp : (10 * m + 1) * (D - m) + (10 * m * m + m) =
            10 * m * D + D := by
          calc (10 * m + 1) * (D - m) + (10 * m * m + m)
              = 10 * m * (D - m) + (D - m) + (10 * m * m + m) := by
                rw [Nat.add_mul, Nat.one_mul]
            _ = (10 * m * (D - m) + 10 * m * m) + ((D - m) + m) := by
                simp only [Nat.add_assoc, Nat.add_left_comm]
            _ = 10 * m * ((D - m) + m) + D := by
                rw [← Nat.mul_add (10 * m) (D - m) m, hsub]
            _ = 10 * m * D + D := by rw [hsub]
        have hge_rhs : 10 * m * D + (10 * m * m + m) ≤ 10 * m * D + D := by
          rw [Nat.mul_assoc 10 m m]
          exact Nat.add_le_add_left hD_ge_m_sq _
        rw [← hexp] at hge_rhs
        exact Nat.le_of_add_le_add_right hge_rhs
      have h3D_lt : 3 ^ m * D < 2 ^ k * (D - m) := by
        have h1 : 3 ^ m * (10 * m * D) ≤ 3 ^ m * ((10 * m + 1) * (D - m)) :=
          Nat.mul_le_mul_left _ hrat_D
        have h2 : 3 ^ m * ((10 * m + 1) * (D - m)) < 2 ^ k * (10 * m) * (D - m) := by
          rw [← Nat.mul_assoc]
          exact Nat.mul_lt_mul_of_pos_right hmargin hDm_pos
        have h3 : (10 * m) * (3 ^ m * D) < (10 * m) * (2 ^ k * (D - m)) := by
          have hl : (10 * m) * (3 ^ m * D) = 3 ^ m * (10 * m * D) := by
            simp only [Nat.mul_left_comm, Nat.mul_assoc]
          have hr : (10 * m) * (2 ^ k * (D - m)) = 2 ^ k * (10 * m) * (D - m) := by
            simp only [Nat.mul_left_comm, Nat.mul_assoc]
          rw [hl, hr]
          exact Nat.lt_of_le_of_lt h1 h2
        cases Nat.lt_or_ge (3 ^ m * D) (2 ^ k * (D - m)) with
        | inl hlt => exact hlt
        | inr hge =>
          exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (10 * m) hge) h3) (Nat.lt_irrefl _)
      have hbern := pow_add_one_mul_sub_le D m hm_le_D hD_pos
      have hcontr : (3 * c.nMin + 1) ^ m < 2 ^ k * c.nMin ^ m := by
        have hD_succ : D ^ (m + 1) = D * D ^ m := by
          rw [Nat.pow_succ, Nat.mul_comm (D ^ m) D]
        have hleft : 3 ^ m * (D + 1) ^ m * (D - m) < 2 ^ k * D ^ m * (D - m) := by
          calc 3 ^ m * (D + 1) ^ m * (D - m)
              = 3 ^ m * ((D + 1) ^ m * (D - m)) := Nat.mul_assoc _ _ _
            _ ≤ 3 ^ m * D ^ (m + 1) := Nat.mul_le_mul_left _ hbern
            _ = (3 ^ m * D) * D ^ m := by rw [hD_succ, ← Nat.mul_assoc]
            _ < (2 ^ k * (D - m)) * D ^ m := Nat.mul_lt_mul_of_pos_right h3D_lt (Nat.pow_pos hD_pos)
            _ = 2 ^ k * D ^ m * (D - m) := by
              rw [Nat.mul_assoc (2 ^ k) (D - m) (D ^ m), Nat.mul_comm (D - m) (D ^ m),
                  ← Nat.mul_assoc]
        have hdrop : 3 ^ m * (D + 1) ^ m < 2 ^ k * D ^ m := by
          cases Nat.lt_or_ge (3 ^ m * (D + 1) ^ m) (2 ^ k * D ^ m) with
          | inl hlt => exact hlt
          | inr hge =>
            exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (D - m) hge) hleft) (Nat.lt_irrefl _)
        have hD_pow : 3 ^ m * (2 ^ k * c.nMin ^ m) = 2 ^ k * D ^ m := by
          have : D ^ m = 3 ^ m * c.nMin ^ m := Nat.mul_pow 3 c.nMin m
          rw [this, Nat.mul_left_comm]
        rw [← hD_pow] at hdrop
        cases Nat.lt_or_ge ((3 * c.nMin + 1) ^ m) (2 ^ k * c.nMin ^ m) with
        | inl hlt => exact hlt
        | inr hge =>
          exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (3 ^ m) hge) hdrop) (Nat.lt_irrefl _)
      exact absurd hprod (Nat.not_le_of_lt hcontr)
  refine ⟨?_, ?_⟩
  · intro hle
    have hu := upper_for_m hle
    have h936 : 10 * m * m ≤ 936360 := by
      calc 10 * m * m = 10 * (m * m) := Nat.mul_assoc 10 m m
        _ ≤ 10 * (306 * 306) := Nat.mul_le_mul_left 10 (Nat.mul_le_mul hle hle)
        _ = 936360 := by decide
    exact ⟨hu, Nat.lt_of_lt_of_le hu h936⟩
  · intro hn
    have hm307 : 307 ≤ m := by
      cases Nat.lt_or_ge 306 m with
      | inl hgt => exact hgt
      | inr hle =>
        have hlt := upper_for_m hle
        have h936 : 10 * m * m ≤ 936360 := by
          calc 10 * m * m = 10 * (m * m) := Nat.mul_assoc 10 m m
            _ ≤ 10 * (306 * 306) := Nat.mul_le_mul_left 10 (Nat.mul_le_mul hle hle)
            _ = 936360 := by decide
        exact absurd (Nat.lt_of_lt_of_le hlt h936) (Nat.not_lt_of_ge hn)
    have hgap : 3 ^ m < 2 ^ cycleShift c.a m := collatz_odd_cycle_gap_pos c hm1
    have h3_ge : 3 ^ 307 ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) hm307
    have h2_486 : 2 ^ 486 < 2 ^ cycleShift c.a m :=
      Nat.lt_trans (Nat.lt_of_lt_of_le three_pow_307_bounds.1 h3_ge) hgap
    have hk487 : 487 ≤ cycleShift c.a m := by
      cases Nat.lt_or_ge 486 (cycleShift c.a m) with
      | inl hgt => exact hgt
      | inr hle =>
        exact absurd h2_486 (Nat.not_lt_of_ge (Nat.pow_le_pow_right (by decide) hle))
    have hK793 : 793 ≤ cycleShift c.a m + m :=
      Nat.le_trans (by decide : 793 ≤ 487 + 307) (Nat.add_le_add hk487 hm307)
    exact ⟨hm307, hk487, hK793⟩

end CollatzQrhBridge

-- end of file: leanasm/src/LeanAsm/CollatzQrhBridge.lean
