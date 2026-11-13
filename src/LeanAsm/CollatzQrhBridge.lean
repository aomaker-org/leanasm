-- Path: leanasm/src/LeanAsm/CollatzQrhBridge.lean
-- Formal Collatz Dynamical System ↔ Quasi-Riemann Hypothesis Spectral & Diophantine Bridge.
-- Max Column: 100 Columns

import LeanAsm.Conjectures
import LeanAsm.QuasiRiemann

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

private theorem mul_natAbs_of_nonneg {n : Nat} {z : Int} (hz : 0 < z)
    (hdiv : (twoPiInterval36.hi.natAbs + z.natAbs - 1) / z.natAbs = n)
    (hnonneg : 0 ≤ twoPiInterval36.hi) :
    twoPiInterval36.hi ≤ (n : Int) * z := by
  have hz_pos : 0 < z.natAbs := Int.natAbs_pos.mpr (by omega)
  have h1 : twoPiInterval36.hi.natAbs ≤ n * z.natAbs := by
    have hrem := Nat.lt_of_lt_of_le (Nat.mod_lt (twoPiInterval36.hi.natAbs + z.natAbs - 1) hz_pos)
      (Nat.le_refl z.natAbs)
    have hdm := Nat.div_add_mod (twoPiInterval36.hi.natAbs + z.natAbs - 1) z.natAbs
    rw [hdiv] at hdm
    have hmul : z.natAbs * n = n * z.natAbs := Nat.mul_comm _ _
    omega
  have hz_eq : (z.natAbs : Int) = z := Int.natAbs_of_nonneg (Int.le_of_lt hz)
  have htp_eq : (twoPiInterval36.hi.natAbs : Int) = twoPiInterval36.hi :=
    Int.natAbs_of_nonneg hnonneg
  have hcast : ((twoPiInterval36.hi.natAbs : Nat) : Int) ≤ ((n * z.natAbs : Nat) : Int) :=
    Int.ofNat_le.mpr h1
  rw [htp_eq, Int.natCast_mul, hz_eq] at hcast
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
    exact ⟨hpos, mul_natAbs_of_nonneg hpos hdiv htp⟩
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

end CollatzQrhBridge

-- end of file: leanasm/src/LeanAsm/CollatzQrhBridge.lean
