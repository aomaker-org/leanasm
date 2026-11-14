-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep72.lean
-- Dedicated 72-digit CRT-NTT interval engine, Chudnovsky-backed 2π enclosure,
-- and N = 128 ultra-deep 2D zero-free rectangle sweeper down to σ = 0.501.
-- Max Column: 100 Columns

import LeanAsm.PiChudnovsky
import LeanAsm.QuasiRiemann
import LeanAsm.QuasiRiemann.Rat

namespace QuasiRiemann

-- =============================================================================
-- Part 15: 72-Digit CRT-NTT Fixed-Point Intervals & N = 128 Deep 2D Sweeper
--          Down to σ = 0.501 (gemweb048)
-- =============================================================================

/-- Re-export 192-digit Karatsuba-over-CRT-NTT multiplier from `PiChudnovsky`. -/
abbrev natMul192ViaCrtNtt : Nat → Nat → Nat := PiChudnovsky.natMul192ViaCrtNtt

/-- Theorem: For all `a, b < 10^96` (`1000^32`), `natMul192ViaCrtNtt a b = a * b`,
proved constructively via `karatsubaCrtNttMul192_universal_sound` with zero non-standard axioms. -/
theorem natMul192ViaCrtNtt_eq_mul (a b : Nat) (ha : a < 1000 ^ 32) (hb : b < 1000 ^ 32) :
    natMul192ViaCrtNtt a b = a * b :=
  PiChudnovsky.natMul192ViaCrtNtt_eq_mul a b ha hb

/-- Total equivalence `natMul192ViaCrtNtt a b = a * b` for all `a b : Nat`. -/
theorem natMul192ViaCrtNtt_total_eq_mul (a b : Nat) :
    natMul192ViaCrtNtt a b = a * b :=
  PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul a b

/-- Signed integer product backed by `natMul192ViaCrtNtt` (`karatsubaCrtNttMul192`). -/
def intMul192ViaCrtNtt (x y : Int) : Int :=
  let prodAbs : Int := (natMul192ViaCrtNtt x.natAbs y.natAbs : Int)
  if (x < 0) == (y < 0) then prodAbs else -prodAbs

/-- Exact equality `intMul192ViaCrtNtt x y = x * y` for all `x y : Int`. -/
theorem intMul192ViaCrtNtt_eq_mul (x y : Int) :
    intMul192ViaCrtNtt x y = x * y := by
  dsimp [intMul192ViaCrtNtt]
  rw [natMul192ViaCrtNtt_total_eq_mul]
  exact int_mul_sign_cases x y

private theorem intMul192ViaCrtNtt_fn_eq : intMul192ViaCrtNtt = Int.mul :=
  funext fun x => funext fun y => intMul192ViaCrtNtt_eq_mul x y

/-- Scaling constant `10^66` converting `10^6` grid units into `10^72` scale. -/
def scale66 : Nat := 1000000000000000000000000000000000000000000000000000000000000000000

/-- Integer copy of `10^66` for projection from `ScaledInterval72` to `ScaledInterval`. -/
def scale66Int : Int := (scale66 : Int)

/-- Scaling constant `10^72` for 72-digit fixed-point intervals. -/
def scale72 : Nat := 1000000000000000000000000000000000000000000000000000000000000000000000000

/-- Integer copy of `10^72`. -/
def scale72Int : Int := (scale72 : Int)

private theorem scale72Int_pos : (0 : Int) < scale72Int := by decide

/-- Floor division `⌊n / 10^72⌋` via Euclidean division. -/
def floorDiv72 (n : Int) : Int := n.ediv scale72Int

/-- Ceiling division `⌈n / 10^72⌉` via negated Euclidean division. -/
def ceilDiv72 (n : Int) : Int := -((-n).ediv scale72Int)

private theorem floorDiv72_mul_le (n : Int) : floorDiv72 n * scale72Int ≤ n := by
  have h := ediv_mul_le_self n scale72Int scale72Int_pos
  rw [Int.mul_comm] at h
  exact h

private theorem le_ceilDiv72_mul (n : Int) : n ≤ ceilDiv72 n * scale72Int := by
  have h := ediv_mul_le_self (-n) scale72Int scale72Int_pos
  have heq : ceilDiv72 n * scale72Int = -(scale72Int * ((-n).ediv scale72Int)) := by
    dsimp [ceilDiv72]
    rw [Int.neg_mul, Int.mul_comm]
  rw [heq]
  omega

/-- Constructive 72-digit fixed-point closed interval `[lo / 10^72, hi / 10^72]` with `lo ≤ hi`. -/
structure ScaledInterval72 where
  lo : Int
  hi : Int
  valid : lo ≤ hi := by omega

instance : Repr ScaledInterval72 where
  reprPrec iv _ := s!"[{iv.lo}, {iv.hi}]"

instance : DecidableEq ScaledInterval72 := fun a b =>
  if h : a.lo = b.lo ∧ a.hi = b.hi then
    isTrue (by cases a; cases b; simp only at h; cases h.1; cases h.2; rfl)
  else
    isFalse (by intro heq; apply h; cases heq; exact ⟨rfl, rfl⟩)

/-- Zero interval `[0, 0]` at `10^72` scale. -/
def iv72Zero : ScaledInterval72 := ⟨0, 0, by decide⟩

/-- Unit interval `[1, 1]` at `10^72` scale. -/
def iv72One : ScaledInterval72 := ⟨scale72Int, scale72Int, by decide⟩

/-- Interval addition at `10^72` scale. -/
def iv72Add (a b : ScaledInterval72) : ScaledInterval72 :=
  ⟨a.lo + b.lo, a.hi + b.hi, Int.add_le_add a.valid b.valid⟩

/-- Interval subtraction at `10^72` scale. -/
def iv72Sub (a b : ScaledInterval72) : ScaledInterval72 :=
  ⟨a.lo - b.hi, a.hi - b.lo, Int.sub_le_sub a.valid b.valid⟩

/-- Interval negation at `10^72` scale. -/
def iv72Neg (a : ScaledInterval72) : ScaledInterval72 :=
  ⟨-a.hi, -a.lo, Int.neg_le_neg a.valid⟩

/-- Non-negative natural scalar multiplication of a `ScaledInterval72`. -/
def iv72ScaleNat (k : Nat) (a : ScaledInterval72) : ScaledInterval72 :=
  ⟨(k : Int) * a.lo, (k : Int) * a.hi,
    Int.mul_le_mul_of_nonneg_left a.valid (Int.natCast_nonneg k)⟩

/-- Outward interval division by positive natural `d` at `10^72` scale. -/
def iv72DivNat (a : ScaledInterval72) (d : Nat) (hd : 0 < d := by omega) :
    ScaledInterval72 :=
  ⟨a.lo.ediv (d : Int), -((-a.hi).ediv (d : Int)),
    floorDiv_le_ceilDiv_gen (Int.natCast_pos.mpr hd) a.valid⟩

/-- Projects `ScaledInterval72` (`10^72`) conservatively to `ScaledInterval` (`10^6`). -/
def toScaled6From72 (iv : ScaledInterval72) : ScaledInterval :=
  ⟨iv.lo.ediv scale66Int, -((-iv.hi).ediv scale66Int)⟩

/-- Outward 72-digit interval multiplication via 192-digit CRT-NTT Karatsuba (`intMul192ViaCrtNtt`). -/
def mulInterval72 (x y : ScaledInterval72) : ScaledInterval72 :=
  let p1 := intMul192ViaCrtNtt x.lo y.lo
  let p2 := intMul192ViaCrtNtt x.lo y.hi
  let p3 := intMul192ViaCrtNtt x.hi y.lo
  let p4 := intMul192ViaCrtNtt x.hi y.hi
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  ⟨floorDiv72 minP, ceilDiv72 maxP, floorDiv_le_ceilDiv_gen scale72Int_pos (by omega)⟩

/-- Direct integer-multiplication twin of `mulInterval72` for fast kernel `decide` reduction. -/
def mulInterval72Fast (x y : ScaledInterval72) : ScaledInterval72 :=
  let p1 := x.lo * y.lo
  let p2 := x.lo * y.hi
  let p3 := x.hi * y.lo
  let p4 := x.hi * y.hi
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  ⟨floorDiv72 minP, ceilDiv72 maxP, floorDiv_le_ceilDiv_gen scale72Int_pos (by omega)⟩

/-- Theorem: `mulInterval72` and `mulInterval72Fast` agree extensionally on all inputs,
backed by `karatsubaCrtNttMul192_universal_sound`. -/
theorem mulInterval72_eq_fast (x y : ScaledInterval72) :
    mulInterval72 x y = mulInterval72Fast x y := by
  dsimp [mulInterval72, mulInterval72Fast]
  simp only [intMul192ViaCrtNtt_eq_mul]

/-- Theorem: `mulInterval72` is sound for all real-scaled points `a ∈ x` and `b ∈ y`,
preserving both `lo ≤ hi` and scaled containment `prod.lo * 10^72 ≤ a * b ≤ prod.hi * 10^72`. -/
theorem mulInterval72_sound (x y : ScaledInterval72) (a b : Int)
    (ha : x.lo ≤ a ∧ a ≤ x.hi) (hb : y.lo ≤ b ∧ b ≤ y.hi) :
    let prod := mulInterval72 x y
    prod.lo ≤ prod.hi ∧ prod.lo * scale72Int ≤ a * b ∧ a * b ≤ prod.hi * scale72Int := by
  intro prod
  refine ⟨prod.valid, ?_⟩
  have hcb := corner_bounds x.lo x.hi y.lo y.hi a b ha hb
  have heq : prod = mulInterval72Fast x y := mulInterval72_eq_fast x y
  rw [heq]
  dsimp [mulInterval72Fast]
  have hlo : floorDiv72 (min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi))) *
      scale72Int ≤ a * b :=
    Int.le_trans (floorDiv72_mul_le _) hcb.1
  have hhi : a * b ≤
      ceilDiv72 (max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi))) *
        scale72Int :=
    Int.le_trans hcb.2 (le_ceilDiv72_mul _)
  exact ⟨hlo, hhi⟩

private abbrev RawIv72 := Int × Int

private def rawAdd72 (a b : RawIv72) : RawIv72 := (a.1 + b.1, a.2 + b.2)
private def rawSub72 (a b : RawIv72) : RawIv72 := (a.1 - b.2, a.2 - b.1)
private def rawScaleNat72 (k : Nat) (a : RawIv72) : RawIv72 := ((k : Int) * a.1, (k : Int) * a.2)
private def rawDivNat72 (a : RawIv72) (d : Int) : RawIv72 := (a.1.ediv d, -((-a.2).ediv d))

private def rawInvDen72 (den : Int) : RawIv72 :=
  (scale72Int.ediv den, -((-scale72Int).ediv den))

private def rawArtanh72 (d : Nat) : RawIv72 :=
  let (_, acc) :=
    foldNatStep 82 0 ((d : Int), (0, 0)) (fun k (p, acc) =>
      let den : Int := (2 * k + 1) * p
      (p * d * d, rawAdd72 acc (rawInvDen72 den)))
  (acc.1, acc.2 + 2)

private def rawToIv72 (r : RawIv72) : ScaledInterval72 :=
  if h : r.1 ≤ r.2 then ⟨r.1, r.2, h⟩ else iv72Zero

/-- 72-digit hyperbolic arctangent `artanh(1/d)` via 82 Taylor terms (`d ≥ 3`). -/
def artanhTaylor72 (d : Nat) : ScaledInterval72 :=
  rawToIv72 (rawArtanh72 d)

private def scale33Nat : Nat := 10 ^ 33

private theorem scale33Nat_pos : 0 < scale33Nat := by decide

private def twoPiRaw72 : RawIv72 :=
  (Int.ofNat (2 * PiChudnovsky.piLower105 / scale33Nat),
   Int.ofNat ((2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat))

private def twoPiLoLit72 : Nat :=
  6283185307179586476925286766559005768394338798750211641949889184615632812

private def twoPiHiLit72 : Nat :=
  6283185307179586476925286766559005768394338798750211641949889184615632813

private def twoPiRaw72Lit : RawIv72 :=
  (Int.ofNat twoPiLoLit72, Int.ofNat twoPiHiLit72)

private theorem nat_div_eq_of_bracket {n q d : Nat} (hd : 0 < d)
    (hlo : q * d ≤ n) (hhi : n < (q + 1) * d) : n / d = q := by
  have hdm := Nat.div_add_mod n d
  have hmod := Nat.mod_lt n hd
  if hlt : n / d < q then
    have hmul : (n / d + 1) * d ≤ q * d := Nat.mul_le_mul_right d hlt
    have hstep : d * (n / d) + d = (n / d + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  else if hgt : q < n / d then
    have hmul : (q + 1) * d ≤ d * (n / d) := by
      simpa [Nat.mul_comm (n / d) d] using Nat.mul_le_mul_right d hgt
    omega
  else
    exact Nat.le_antisymm (Nat.not_lt.mp hgt) (Nat.not_lt.mp hlt)

private theorem twoPi_div_eq_lits :
    2 * PiChudnovsky.piLower105 / scale33Nat = twoPiLoLit72 ∧
    (2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat = twoPiHiLit72 := by
  obtain ⟨hlo, hhi, hdigits⟩ := PiChudnovsky.pi_100_digits_certified
  have hdm_lo := Nat.div_add_mod PiChudnovsky.piLower105 (10 ^ 5)
  have hmod_lo := Nat.mod_lt PiChudnovsky.piLower105 (by decide : 0 < 10 ^ 5)
  rw [hlo] at hdm_lo
  have h_lo_1 : 10 ^ 5 * PiChudnovsky.piDigits100 ≤ PiChudnovsky.piLower105 :=
    Nat.le.intro hdm_lo
  have h_lo_2 : PiChudnovsky.piLower105 < 10 ^ 5 * PiChudnovsky.piDigits100 + 10 ^ 5 := by
    omega
  have h1_lo : twoPiLoLit72 * scale33Nat ≤ 2 * (10 ^ 5 * PiChudnovsky.piDigits100) := by
    rw [hdigits]; decide
  have h2_lo :
      2 * (10 ^ 5 * PiChudnovsky.piDigits100 + 10 ^ 5) ≤ (twoPiLoLit72 + 1) * scale33Nat := by
    rw [hdigits]; decide
  have hdm_hi := Nat.div_add_mod PiChudnovsky.piUpper105 (10 ^ 5)
  have hmod_hi := Nat.mod_lt PiChudnovsky.piUpper105 (by decide : 0 < 10 ^ 5)
  rw [hhi] at hdm_hi
  have h_hi_1 : 10 ^ 5 * PiChudnovsky.piDigits100 ≤ PiChudnovsky.piUpper105 :=
    Nat.le.intro hdm_hi
  have h_hi_2 : PiChudnovsky.piUpper105 < 10 ^ 5 * PiChudnovsky.piDigits100 + 10 ^ 5 := by
    omega
  have h1_hi :
      twoPiHiLit72 * scale33Nat ≤ 2 * (10 ^ 5 * PiChudnovsky.piDigits100) + scale33Nat - 1 := by
    rw [hdigits]; decide
  have h2_hi :
      2 * (10 ^ 5 * PiChudnovsky.piDigits100 + 10 ^ 5) + scale33Nat - 1 ≤
        (twoPiHiLit72 + 1) * scale33Nat := by
    rw [hdigits]; decide
  have hhi_lo_le :
      2 * (10 ^ 5 * PiChudnovsky.piDigits100) + scale33Nat - 1 ≤
        2 * PiChudnovsky.piUpper105 + scale33Nat - 1 :=
    Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h_hi_1) scale33Nat) 1
  have hhi_hi_lt :
      2 * PiChudnovsky.piUpper105 + scale33Nat - 1 <
        2 * (10 ^ 5 * PiChudnovsky.piDigits100 + 10 ^ 5) + scale33Nat - 1 :=
    Nat.sub_lt_sub_right
      (Nat.le_trans scale33Nat_pos (Nat.le_add_left scale33Nat (2 * PiChudnovsky.piUpper105)))
      (Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left h_hi_2 (by decide)) scale33Nat)
  exact ⟨
    nat_div_eq_of_bracket scale33Nat_pos
      (Nat.le_trans h1_lo (Nat.mul_le_mul_left 2 h_lo_1))
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left h_lo_2 (by decide)) h2_lo),
    nat_div_eq_of_bracket scale33Nat_pos
      (Nat.le_trans h1_hi hhi_lo_le)
      (Nat.lt_of_lt_of_le hhi_hi_lt h2_hi)⟩

private theorem twoPiRaw72_eq : twoPiRaw72 = twoPiRaw72Lit :=
  Prod.ext (congrArg Int.ofNat twoPi_div_eq_lits.1) (congrArg Int.ofNat twoPi_div_eq_lits.2)

private theorem nat_div_le_ceil_div (a b d : Nat) (hd : 0 < d) (hab : a ≤ b) :
    a / d ≤ (b + d - 1) / d :=
  Nat.div_le_div_right (by omega)

private theorem nat_le_ceil_div_mul (b d : Nat) (hd : 0 < d) :
    b ≤ ((b + d - 1) / d) * d := by
  have hdm := Nat.div_add_mod (b + d - 1) d
  have hmod := Nat.mod_lt (b + d - 1) hd
  rw [Nat.mul_comm] at hdm
  omega

/-- 72-digit enclosure of `2π` derived directly from `PiChudnovsky`'s certified
`10^105` bracket `[piLower105, piUpper105]` by conservative projection modulo `10^33`. -/
def twoPiInterval72 : ScaledInterval72 where
  lo := twoPiRaw72.1
  hi := twoPiRaw72.2
  valid :=
    Int.ofNat_le.mpr
      (nat_div_le_ceil_div (2 * PiChudnovsky.piLower105) (2 * PiChudnovsky.piUpper105)
        scale33Nat scale33Nat_pos (Nat.mul_le_mul_left 2 PiChudnovsky.pi_105_bracket_valid.1))

/-- Exact equality `twoPiInterval72.hi = twoPiRaw72Lit.2` derived from
`PiChudnovsky.pi_100_digits_certified` for fast downstream `decide +kernel` checks. -/
theorem twoPiInterval72_hi_eq : twoPiInterval72.hi = twoPiRaw72Lit.2 := by
  change twoPiRaw72.2 = twoPiRaw72Lit.2
  rw [twoPiRaw72_eq]

/-- Constructive order validity `twoPiInterval72.lo ≤ twoPiInterval72.hi`
derived directly from `PiChudnovsky.pi_105_bracket_valid`. -/
theorem twoPiInterval72_valid : twoPiInterval72.lo ≤ twoPiInterval72.hi :=
  twoPiInterval72.valid

/-- Exact integer bracketing linking `twoPiInterval72` at scale `10^72` directly to
`PiChudnovsky.pi_105_bracket_valid` at scale `10^105`. -/
theorem twoPiInterval72_from_chudnovsky_sound :
    twoPiInterval72.lo * 10 ^ 33 ≤ 2 * (PiChudnovsky.piLower105 : Int) ∧
    2 * (PiChudnovsky.piUpper105 : Int) ≤ twoPiInterval72.hi * 10 ^ 33 := by
  have _ := PiChudnovsky.pi_105_bracket_valid
  constructor
  · have hnat :
        (2 * PiChudnovsky.piLower105 / scale33Nat) * scale33Nat ≤
          2 * PiChudnovsky.piLower105 :=
      Nat.div_mul_le_self (2 * PiChudnovsky.piLower105) scale33Nat
    have hint :
        Int.ofNat ((2 * PiChudnovsky.piLower105 / scale33Nat) * scale33Nat) ≤
          Int.ofNat (2 * PiChudnovsky.piLower105) := Int.ofNat_le.mpr hnat
    have hmul1 :
        twoPiInterval72.lo * (10 ^ 33 : Int) =
          Int.ofNat ((2 * PiChudnovsky.piLower105 / scale33Nat) * scale33Nat) := by
      change Int.ofNat (2 * PiChudnovsky.piLower105 / scale33Nat) * Int.ofNat scale33Nat = _
      exact (Int.natCast_mul _ _).symm
    have hmul2 :
        2 * (PiChudnovsky.piLower105 : Int) = Int.ofNat (2 * PiChudnovsky.piLower105) :=
      (Int.natCast_mul 2 PiChudnovsky.piLower105).symm
    rw [hmul1, hmul2]
    exact hint
  · have hnat :
        2 * PiChudnovsky.piUpper105 ≤
          ((2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat) * scale33Nat :=
      nat_le_ceil_div_mul (2 * PiChudnovsky.piUpper105) scale33Nat scale33Nat_pos
    have hint :
        Int.ofNat (2 * PiChudnovsky.piUpper105) ≤
          Int.ofNat (((2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat) *
            scale33Nat) := Int.ofNat_le.mpr hnat
    have hmul1 :
        2 * (PiChudnovsky.piUpper105 : Int) = Int.ofNat (2 * PiChudnovsky.piUpper105) :=
      (Int.natCast_mul 2 PiChudnovsky.piUpper105).symm
    have hmul2 :
        twoPiInterval72.hi * (10 ^ 33 : Int) =
          Int.ofNat (((2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat) *
            scale33Nat) := by
      change
        Int.ofNat ((2 * PiChudnovsky.piUpper105 + scale33Nat - 1) / scale33Nat) *
          Int.ofNat scale33Nat = _
      exact (Int.natCast_mul _ _).symm
    rw [hmul1, hmul2]
    exact hint

private def reduceModTwoPiRaw72With (tp xIv : RawIv72) : RawIv72 :=
  let mid := (xIv.1 + xIv.2).ediv 2
  let twoPiMid := (tp.1 + tp.2).ediv 2
  let k := (mid + twoPiMid.ediv 2).ediv twoPiMid
  if 0 ≤ k then
    (xIv.1 - k * tp.2, xIv.2 - k * tp.1)
  else
    (xIv.1 - k * tp.1, xIv.2 - k * tp.2)

private def reduceModTwoPiRaw72 (xIv : RawIv72) : RawIv72 :=
  reduceModTwoPiRaw72With twoPiRaw72 xIv

/-- Argument reduction modulo `2π` at `10^72` scale centered near `[-π, π]`. -/
def reduceModTwoPiCentered72 (xIv : ScaledInterval72) : ScaledInterval72 :=
  rawToIv72 (reduceModTwoPiRaw72 (xIv.lo, xIv.hi))

private def ln2Raw72 : RawIv72 := rawScaleNat72 2 (rawArtanh72 3)
private def ln3Raw72 : RawIv72 := rawAdd72 ln2Raw72 (rawScaleNat72 2 (rawArtanh72 5))
private def ln5Raw72 : RawIv72 := rawAdd72 (rawScaleNat72 2 ln2Raw72)
  (rawScaleNat72 2 (rawArtanh72 9))
private def ln7Raw72 : RawIv72 := rawSub72 (rawScaleNat72 3 ln2Raw72)
  (rawScaleNat72 2 (rawArtanh72 15))
private def ln11Raw72 : RawIv72 := rawAdd72 (rawAdd72 ln2Raw72 ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 21))
private def ln13Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) ln3Raw72)
  (rawScaleNat72 2 (rawArtanh72 25))
private def ln17Raw72 : RawIv72 := rawAdd72 (rawScaleNat72 4 ln2Raw72)
  (rawScaleNat72 2 (rawArtanh72 33))
private def ln19Raw72 : RawIv72 := rawAdd72 (rawAdd72 ln2Raw72 (rawScaleNat72 2 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 37))
private def ln23Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 3 ln2Raw72) ln3Raw72)
  (rawScaleNat72 2 (rawArtanh72 47))
private def ln29Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) ln7Raw72)
  (rawScaleNat72 2 (rawArtanh72 57))
private def ln31Raw72 : RawIv72 := rawSub72 (rawScaleNat72 5 ln2Raw72)
  (rawScaleNat72 2 (rawArtanh72 63))
private def ln37Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) (rawScaleNat72 2 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 73))
private def ln41Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 3 ln2Raw72) ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 81))
private def ln43Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawAdd72 ln2Raw72 ln3Raw72) ln7Raw72)
  (rawScaleNat72 2 (rawArtanh72 85))
private def ln47Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 4 ln2Raw72) ln3Raw72)
  (rawScaleNat72 2 (rawArtanh72 95))
private def ln53Raw72 : RawIv72 := rawSub72 (rawAdd72 ln2Raw72 (rawScaleNat72 3 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 107))
private def ln59Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) ln3Raw72) ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 119))
private def ln61Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) ln3Raw72) ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 121))
private def ln67Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawAdd72 ln2Raw72 ln3Raw72) ln11Raw72)
  (rawScaleNat72 2 (rawArtanh72 133))
private def ln71Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 3 ln2Raw72) (rawScaleNat72 2 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 143))
private def ln73Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 3 ln2Raw72) (rawScaleNat72 2 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 145))
private def ln79Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 4 ln2Raw72) ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 159))
private def ln83Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) ln3Raw72) ln7Raw72)
  (rawScaleNat72 2 (rawArtanh72 167))
private def ln89Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawAdd72 ln2Raw72 (rawScaleNat72 2 ln3Raw72)) ln5Raw72)
  (rawScaleNat72 2 (rawArtanh72 179))
private def ln97Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 5 ln2Raw72) ln3Raw72)
  (rawScaleNat72 2 (rawArtanh72 193))
private def ln101Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) (rawScaleNat72 2 ln5Raw72))
  (rawScaleNat72 2 (rawArtanh72 201))
private def ln103Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 3 ln2Raw72) ln13Raw72)
  (rawScaleNat72 2 (rawArtanh72 207))
private def ln107Raw72 : RawIv72 := rawSub72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) (rawScaleNat72 3 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 215))
private def ln109Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 2 ln2Raw72) (rawScaleNat72 3 ln3Raw72))
  (rawScaleNat72 2 (rawArtanh72 217))
private def ln113Raw72 : RawIv72 := rawAdd72 (rawAdd72 (rawScaleNat72 4 ln2Raw72) ln7Raw72)
  (rawScaleNat72 2 (rawArtanh72 225))
private def ln127Raw72 : RawIv72 := rawSub72 (rawScaleNat72 7 ln2Raw72)
  (rawScaleNat72 2 (rawArtanh72 255))

private structure LnPrimeTable72 where
  p2 : RawIv72
  p3 : RawIv72
  p5 : RawIv72
  p7 : RawIv72
  p11 : RawIv72
  p13 : RawIv72
  p17 : RawIv72
  p19 : RawIv72
  p23 : RawIv72
  p29 : RawIv72
  p31 : RawIv72
  p37 : RawIv72
  p41 : RawIv72
  p43 : RawIv72
  p47 : RawIv72
  p53 : RawIv72
  p59 : RawIv72
  p61 : RawIv72
  p67 : RawIv72
  p71 : RawIv72
  p73 : RawIv72
  p79 : RawIv72
  p83 : RawIv72
  p89 : RawIv72
  p97 : RawIv72
  p101 : RawIv72
  p103 : RawIv72
  p107 : RawIv72
  p109 : RawIv72
  p113 : RawIv72
  p127 : RawIv72
  deriving DecidableEq

private def lnPrimeTable72Crt : LnPrimeTable72 :=
  ⟨ln2Raw72, ln3Raw72, ln5Raw72, ln7Raw72, ln11Raw72, ln13Raw72,
   ln17Raw72, ln19Raw72, ln23Raw72, ln29Raw72, ln31Raw72, ln37Raw72,
   ln41Raw72, ln43Raw72, ln47Raw72, ln53Raw72, ln59Raw72, ln61Raw72,
   ln67Raw72, ln71Raw72, ln73Raw72, ln79Raw72, ln83Raw72, ln89Raw72,
   ln97Raw72, ln101Raw72, ln103Raw72, ln107Raw72, ln109Raw72, ln113Raw72,
   ln127Raw72⟩

private def lnPrimeTable72Lit : LnPrimeTable72 :=
  ⟨(693147180559945309417232121458176568075500134360255254120680009493393552,
    693147180559945309417232121458176568075500134360255254120680009493393720),
   (1098612288668109691395245236922525704647490557822749451734694333637494172,
    1098612288668109691395245236922525704647490557822749451734694333637494502),
   (1609437912434100374600759333226187639525601354268517721912647891474178804,
    1609437912434100374600759333226187639525601354268517721912647891474179308),
   (1945910149055313305105352743443179729637084729581861188459390149937579516,
    1945910149055313305105352743443179729637084729581861188459390149937580188),
   (2397895272798370544061943577965129299821706853937417175218567709130573344,
    2397895272798370544061943577965129299821706853937417175218567709130574184),
   (2564949357461536736053487441565318604805267944760207116419045510663464384,
    2564949357461536736053487441565318604805267944760207116419045510663465212),
   (2833213344056216080249534617873126535588203012585744787297237737882292278,
    2833213344056216080249534617873126535588203012585744787297237737882293118),
   (2944438979166440460009027431887853537237379261299128818537960236409292364,
    2944438979166440460009027431887853537237379261299128818537960236409293360),
   (3135494215929149690806752831810196118442380314840435741998635377482992772,
    3135494215929149690806752831810196118442380314840435741998635377482993774),
   (3367295829986474027183272032361911605494512913922744078921670351642780276,
    3367295829986474027183272032361911605494512913922744078921670351642781452),
   (3433987204485146245929164324542357210449938930480591971756718072474980912,
    3433987204485146245929164324542357210449938930480591971756718072474981920),
   (3610917912644224444368095671031447163900077587167636163644912681192989344,
    3610917912644224444368095671031447163900077587167636163644912681192990508),
   (3713572066704307803866763373037407588376410469399301633619262910259978204,
    3713572066704307803866763373037407588376410469399301633619262910259979380),
   (3761200115693562423472842513345847035559136184881555415191685264922858620,
    3761200115693562423472842513345847035559136184881555415191685264922859958),
   (3850147601710058586820950669772173708896050502020224033200508346806817660,
    3850147601710058586820950669772173708896050502020224033200508346806818830),
   (3970291913552121834144469139029057770359977752911217603048129470018004052,
    3970291913552121834144469139029057770359977752911217603048129470018005378),
   (4077537443905719450616050373719697624063346789330454529512036697059199518,
    4077537443905719450616050373719697624063346789330454529512036697059200856),
   (4110873864173311248751389103425614746315681743081261062937383646419439346,
    4110873864173311248751389103425614746315681743081261062937383646419440684),
   (4204692619390966059670071996363722750566932903221895337137784130775268018,
    4204692619390966059670071996363722750566932903221895337137784130775269524),
   (4262679877041315421329454532513034096759576526710566108121425802027350900,
    4262679877041315421329454532513034096759576526710566108121425802027352232),
   (4290459441148391129092108857438542570904752844871597664595698857161789508,
    4290459441148391129092108857438542570904752844871597664595698857161790840),
   (4369447852467021494172945541481410922173541224422609625412171117559805446,
    4369447852467021494172945541481410922173541224422609625412171117559806790),
   (4418840607796597923475472223291370453029313056663236370187943462938578232,
    4418840607796597923475472223291370453029313056663236370187943462938579738),
   (4488636369732139838317815540669849219404660387132959364106697577287953244,
    4488636369732139838317815540669849219404660387132959364106697577287954744),
   (4574710978503382822116721621703961713808914902658781355976234368760176802,
    4574710978503382822116721621703961713808914902658781355976234368760178140),
   (4615120516841259450884198266912989156890882587197604749931265361702011360,
    4615120516841259450884198266912989156890882587197604749931265361702012872),
   (4634728988229635770768602315053440820628261108370803162611230959030530560,
    4634728988229635770768602315053440820628261108370803162611230959030532060),
   (4672828834461906173304398817023277001563146276131407553560116719246716714,
    4672828834461906173304398817023277001563146276131407553560116719246718208),
   (4691347882229143700377316452209201651060348883503231153074873554680902762,
    4691347882229143700377316452209201651060348883503231153074873554680904256),
   (4727387818712340568582131493616021672029330388702993794740348035343573264,
    4727387818712340568582131493616021672029330388702993794740348035343574776),
   (4844187086458591273047440807716292394873909123926085762907265207857184616,
    4844187086458591273047440807716292394873909123926085762907265207857185960)⟩

private theorem lnPrimeTable72_eq : lnPrimeTable72Crt = lnPrimeTable72Lit := by
  decide +kernel

private def lnRaw72_1_to_16 (t : LnPrimeTable72) : Nat → RawIv72
  | 1   => (0, 0)
  | 2   => t.p2
  | 3   => t.p3
  | 4   => rawScaleNat72 2 t.p2
  | 5   => t.p5
  | 6   => rawAdd72 t.p2 t.p3
  | 7   => t.p7
  | 8   => rawScaleNat72 3 t.p2
  | 9   => rawScaleNat72 2 t.p3
  | 10  => rawAdd72 t.p2 t.p5
  | 11  => t.p11
  | 12  => rawAdd72 (rawScaleNat72 2 t.p2) t.p3
  | 13  => t.p13
  | 14  => rawAdd72 t.p2 t.p7
  | 15  => rawAdd72 t.p3 t.p5
  | 16  => rawScaleNat72 4 t.p2
  | _   => (0, 0)

private def lnRaw72_17_to_32 (t : LnPrimeTable72) : Nat → RawIv72
  | 17  => t.p17
  | 18  => rawAdd72 t.p2 (rawScaleNat72 2 t.p3)
  | 19  => t.p19
  | 20  => rawAdd72 (rawScaleNat72 2 t.p2) t.p5
  | 21  => rawAdd72 t.p3 t.p7
  | 22  => rawAdd72 t.p2 t.p11
  | 23  => t.p23
  | 24  => rawAdd72 (rawScaleNat72 3 t.p2) t.p3
  | 25  => rawScaleNat72 2 t.p5
  | 26  => rawAdd72 t.p2 t.p13
  | 27  => rawScaleNat72 3 t.p3
  | 28  => rawAdd72 (rawScaleNat72 2 t.p2) t.p7
  | 29  => t.p29
  | 30  => rawAdd72 (rawAdd72 t.p2 t.p3) t.p5
  | 31  => t.p31
  | 32  => rawScaleNat72 5 t.p2
  | _   => (0, 0)

private def lnRaw72_33_to_48 (t : LnPrimeTable72) : Nat → RawIv72
  | 33  => rawAdd72 t.p3 t.p11
  | 34  => rawAdd72 t.p2 t.p17
  | 35  => rawAdd72 t.p5 t.p7
  | 36  => rawAdd72 (rawScaleNat72 2 t.p2) (rawScaleNat72 2 t.p3)
  | 37  => t.p37
  | 38  => rawAdd72 t.p2 t.p19
  | 39  => rawAdd72 t.p3 t.p13
  | 40  => rawAdd72 (rawScaleNat72 3 t.p2) t.p5
  | 41  => t.p41
  | 42  => rawAdd72 (rawAdd72 t.p2 t.p3) t.p7
  | 43  => t.p43
  | 44  => rawAdd72 (rawScaleNat72 2 t.p2) t.p11
  | 45  => rawAdd72 (rawScaleNat72 2 t.p3) t.p5
  | 46  => rawAdd72 t.p2 t.p23
  | 47  => t.p47
  | 48  => rawAdd72 (rawScaleNat72 4 t.p2) t.p3
  | _   => (0, 0)

private def lnRaw72_49_to_64 (t : LnPrimeTable72) : Nat → RawIv72
  | 49  => rawScaleNat72 2 t.p7
  | 50  => rawAdd72 t.p2 (rawScaleNat72 2 t.p5)
  | 51  => rawAdd72 t.p3 t.p17
  | 52  => rawAdd72 (rawScaleNat72 2 t.p2) t.p13
  | 53  => t.p53
  | 54  => rawAdd72 t.p2 (rawScaleNat72 3 t.p3)
  | 55  => rawAdd72 t.p5 t.p11
  | 56  => rawAdd72 (rawScaleNat72 3 t.p2) t.p7
  | 57  => rawAdd72 t.p3 t.p19
  | 58  => rawAdd72 t.p2 t.p29
  | 59  => t.p59
  | 60  => rawAdd72 (rawAdd72 (rawScaleNat72 2 t.p2) t.p3) t.p5
  | 61  => t.p61
  | 62  => rawAdd72 t.p2 t.p31
  | 63  => rawAdd72 (rawScaleNat72 2 t.p3) t.p7
  | 64  => rawScaleNat72 6 t.p2
  | _   => (0, 0)

private def lnRaw72_65_to_80 (t : LnPrimeTable72) : Nat → RawIv72
  | 65  => rawAdd72 t.p5 t.p13
  | 66  => rawAdd72 (rawAdd72 t.p2 t.p3) t.p11
  | 67  => t.p67
  | 68  => rawAdd72 (rawScaleNat72 2 t.p2) t.p17
  | 69  => rawAdd72 t.p3 t.p23
  | 70  => rawAdd72 (rawAdd72 t.p2 t.p5) t.p7
  | 71  => t.p71
  | 72  => rawAdd72 (rawScaleNat72 3 t.p2) (rawScaleNat72 2 t.p3)
  | 73  => t.p73
  | 74  => rawAdd72 t.p2 t.p37
  | 75  => rawAdd72 t.p3 (rawScaleNat72 2 t.p5)
  | 76  => rawAdd72 (rawScaleNat72 2 t.p2) t.p19
  | 77  => rawAdd72 t.p7 t.p11
  | 78  => rawAdd72 (rawAdd72 t.p2 t.p3) t.p13
  | 79  => t.p79
  | 80  => rawAdd72 (rawScaleNat72 4 t.p2) t.p5
  | _   => (0, 0)

private def lnRaw72_81_to_96 (t : LnPrimeTable72) : Nat → RawIv72
  | 81  => rawScaleNat72 4 t.p3
  | 82  => rawAdd72 t.p2 t.p41
  | 83  => t.p83
  | 84  => rawAdd72 (rawAdd72 (rawScaleNat72 2 t.p2) t.p3) t.p7
  | 85  => rawAdd72 t.p5 t.p17
  | 86  => rawAdd72 t.p2 t.p43
  | 87  => rawAdd72 t.p3 t.p29
  | 88  => rawAdd72 (rawScaleNat72 3 t.p2) t.p11
  | 89  => t.p89
  | 90  => rawAdd72 (rawAdd72 t.p2 (rawScaleNat72 2 t.p3)) t.p5
  | 91  => rawAdd72 t.p7 t.p13
  | 92  => rawAdd72 (rawScaleNat72 2 t.p2) t.p23
  | 93  => rawAdd72 t.p3 t.p31
  | 94  => rawAdd72 t.p2 t.p47
  | 95  => rawAdd72 t.p5 t.p19
  | 96  => rawAdd72 (rawScaleNat72 5 t.p2) t.p3
  | _   => (0, 0)

private def lnRaw72_97_to_112 (t : LnPrimeTable72) : Nat → RawIv72
  | 97  => t.p97
  | 98  => rawAdd72 t.p2 (rawScaleNat72 2 t.p7)
  | 99  => rawAdd72 (rawScaleNat72 2 t.p3) t.p11
  | 100 => rawAdd72 (rawScaleNat72 2 t.p2) (rawScaleNat72 2 t.p5)
  | 101 => t.p101
  | 102 => rawAdd72 (rawAdd72 t.p2 t.p3) t.p17
  | 103 => t.p103
  | 104 => rawAdd72 (rawScaleNat72 3 t.p2) t.p13
  | 105 => rawAdd72 (rawAdd72 t.p3 t.p5) t.p7
  | 106 => rawAdd72 t.p2 t.p53
  | 107 => t.p107
  | 108 => rawAdd72 (rawScaleNat72 2 t.p2) (rawScaleNat72 3 t.p3)
  | 109 => t.p109
  | 110 => rawAdd72 (rawAdd72 t.p2 t.p5) t.p11
  | 111 => rawAdd72 t.p3 t.p37
  | 112 => rawAdd72 (rawScaleNat72 4 t.p2) t.p7
  | _   => (0, 0)

private def lnRaw72_113_to_128 (t : LnPrimeTable72) : Nat → RawIv72
  | 113 => t.p113
  | 114 => rawAdd72 (rawAdd72 t.p2 t.p3) t.p19
  | 115 => rawAdd72 t.p5 t.p23
  | 116 => rawAdd72 (rawScaleNat72 2 t.p2) t.p29
  | 117 => rawAdd72 (rawScaleNat72 2 t.p3) t.p13
  | 118 => rawAdd72 t.p2 t.p59
  | 119 => rawAdd72 t.p7 t.p17
  | 120 => rawAdd72 (rawAdd72 (rawScaleNat72 3 t.p2) t.p3) t.p5
  | 121 => rawScaleNat72 2 t.p11
  | 122 => rawAdd72 t.p2 t.p61
  | 123 => rawAdd72 t.p3 t.p41
  | 124 => rawAdd72 (rawScaleNat72 2 t.p2) t.p31
  | 125 => rawScaleNat72 3 t.p5
  | 126 => rawAdd72 (rawAdd72 t.p2 (rawScaleNat72 2 t.p3)) t.p7
  | 127 => t.p127
  | 128 => rawScaleNat72 7 t.p2
  | _   => (0, 0)

private def lnRaw72With (t : LnPrimeTable72) (n : Nat) : RawIv72 :=
  if n ≤ 64 then
    if n ≤ 32 then
      if n ≤ 16 then lnRaw72_1_to_16 t n else lnRaw72_17_to_32 t n
    else
      if n ≤ 48 then lnRaw72_33_to_48 t n else lnRaw72_49_to_64 t n
  else
    if n ≤ 96 then
      if n ≤ 80 then lnRaw72_65_to_80 t n else lnRaw72_81_to_96 t n
    else
      if n ≤ 112 then lnRaw72_97_to_112 t n else lnRaw72_113_to_128 t n

private def lnRaw72 (n : Nat) : RawIv72 :=
  lnRaw72With lnPrimeTable72Crt n

private theorem lnRaw72_eq_lit : lnRaw72 = lnRaw72With lnPrimeTable72Lit := by
  funext n; dsimp [lnRaw72]; rw [lnPrimeTable72_eq]

/-- Pure rational 72-digit logarithm enclosures `ln(n)` for `1 ≤ n ≤ 128`
via all 31 primes up to 127 and exact additive prime factorizations. -/
def lnInterval72 (n : Nat) : ScaledInterval72 :=
  rawToIv72 (lnRaw72 n)

/-- Constructive validity predicate for `lnInterval72 n` across `1 ≤ n ≤ 128`. -/
def ValidLnBound72 (n : Nat) (iv : ScaledInterval72) : Prop :=
  iv.lo ≤ iv.hi ∧
  0 ≤ iv.lo ∧
  if n = 1 then
    iv.lo = 0 ∧ iv.hi = 0
  else
    693147180559945309417232121458176568075500134360255254120680009493393500 ≤ iv.lo ∧
    iv.hi ≤ 4852030263919617165920624850207235976528500940521786778844760066453760000 ∧
    iv.hi - iv.lo ≤ 5000

instance (n : Nat) (iv : ScaledInterval72) : Decidable (ValidLnBound72 n iv) := by
  dsimp [ValidLnBound72]
  infer_instance

private def checkLnRangeAux72 (fn : Nat → RawIv72) : Nat → Bool
  | 0 => true
  | k + 1 =>
    let iv := rawToIv72 (fn (k + 1))
    decide (0 ≤ iv.lo ∧ ValidLnBound72 (k + 1) iv) && checkLnRangeAux72 fn k

private theorem checkLnRangeAux72_sound (fn : Nat → RawIv72) (m : Nat)
    (h : checkLnRangeAux72 fn m = true) :
    ∀ n, 1 ≤ n → n ≤ m →
      (rawToIv72 (fn n)).lo ≥ 0 ∧ ValidLnBound72 n (rawToIv72 (fn n)) := by
  induction m with
  | zero =>
    intro n h1 h0; omega
  | succ k ih =>
    dsimp [checkLnRangeAux72] at h
    have hand : decide (0 ≤ (rawToIv72 (fn (k + 1))).lo ∧
        ValidLnBound72 (k + 1) (rawToIv72 (fn (k + 1)))) = true ∧
        checkLnRangeAux72 fn k = true := Bool.and_eq_true _ _ |>.mp h
    intro n h1 hle
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact ih hand.2 n h1 (Nat.lt_succ_iff.mp hlt)
    · exact of_decide_eq_true hand.1

/-- Theorem: For every `1 ≤ n ≤ 128`, `lnInterval72 n` is non-negative and satisfies `ValidLnBound72`.
Proved constructively with ZERO `Classical.choice` and ZERO `sorryAx`. -/
theorem ln_table_1_to_128_valid :
    ∀ n, 1 ≤ n → n ≤ 128 → (lnInterval72 n).lo ≥ 0 ∧ ValidLnBound72 n (lnInterval72 n) := by
  have hok : checkLnRangeAux72 (lnRaw72With lnPrimeTable72Lit) 128 = true := by decide
  have h := checkLnRangeAux72_sound (lnRaw72With lnPrimeTable72Lit) 128 hok
  simpa [lnInterval72, lnRaw72_eq_lit] using h

private def rawMul72Fast (a b : RawIv72) : RawIv72 :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  (floorDiv72 minP, ceilDiv72 maxP)

private def rawMul72Crt (a b : RawIv72) : RawIv72 :=
  let p1 := intMul192ViaCrtNtt a.1 b.1
  let p2 := intMul192ViaCrtNtt a.1 b.2
  let p3 := intMul192ViaCrtNtt a.2 b.1
  let p4 := intMul192ViaCrtNtt a.2 b.2
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  (floorDiv72 minP, ceilDiv72 maxP)

private theorem rawMul72_fn_eq : rawMul72Crt = rawMul72Fast := by
  funext a b
  dsimp [rawMul72Crt, rawMul72Fast]
  simp only [intMul192ViaCrtNtt_eq_mul]

private def rawToScaled6From72 (iv : RawIv72) : ScaledInterval :=
  ⟨iv.1.ediv scale66Int, -((-iv.2).ediv scale66Int)⟩

private def rawClampUnit72 (acc : RawIv72) (rem : Int) : RawIv72 :=
  let lo0 := max (-scale72Int) (acc.1 - rem)
  let hi0 := min scale72Int (acc.2 + rem)
  if lo0 ≤ hi0 then (lo0, hi0) else (acc.1 - rem, acc.2 + rem)

private def expSeries30 (mulS : Int → Int → Int) (yLo yHi : Int) :
    Nat → Int → Int → Int → Int → RawIv72
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m : Int := (30 - k : Nat)
    let ntLo := Int.ediv (floorDiv72 (mulS tLo yLo)) m
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv72 (mulS tHi yHi))) m)
    if (30 - k) % 2 == 1 then
      expSeries30 mulS yLo yHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      expSeries30 mulS yLo yHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def rawTaylorExpNeg72 (mulS : Int → Int → Int) (yIv : RawIv72) : RawIv72 :=
  let yLo := max 0 (Int.ediv yIv.1 256)
  let yHi := max 0 (Int.neg (Int.ediv (Int.neg yIv.2) 256))
  let acc := expSeries30 mulS yLo yHi 30 scale72Int scale72Int scale72Int scale72Int
  let s0Lo := max 0 (Int.sub acc.1 32)
  let s0Hi := max 0 (Int.add acc.2 32)
  let s1Lo := floorDiv72 (mulS s0Lo s0Lo); let s1Hi := ceilDiv72 (mulS s0Hi s0Hi)
  let s2Lo := floorDiv72 (mulS s1Lo s1Lo); let s2Hi := ceilDiv72 (mulS s1Hi s1Hi)
  let s3Lo := floorDiv72 (mulS s2Lo s2Lo); let s3Hi := ceilDiv72 (mulS s2Hi s2Hi)
  let s4Lo := floorDiv72 (mulS s3Lo s3Lo); let s4Hi := ceilDiv72 (mulS s3Hi s3Hi)
  let s5Lo := floorDiv72 (mulS s4Lo s4Lo); let s5Hi := ceilDiv72 (mulS s4Hi s4Hi)
  let s6Lo := floorDiv72 (mulS s5Lo s5Lo); let s6Hi := ceilDiv72 (mulS s5Hi s5Hi)
  let s7Lo := floorDiv72 (mulS s6Lo s6Lo); let s7Hi := ceilDiv72 (mulS s6Hi s6Hi)
  (floorDiv72 (mulS s7Lo s7Lo), ceilDiv72 (mulS s7Hi s7Hi))

private def doubleAngleCosSin72 (mul : RawIv72 → RawIv72 → RawIv72) (c s : RawIv72) :
    RawIv72 × RawIv72 :=
  let c2 := mul c c
  let s2 := mul s s
  let cs := mul c s
  (rawClampUnit72 (rawSub72 c2 s2) 0, rawClampUnit72 (rawScaleNat72 2 cs) 0)

private def cosSeries36 (mulS : Int → Int → Int) (rLo rHi : Int) :
    Nat → Int → Int → Int → Int → RawIv72
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m := 36 - k
    let den : Int := ((2 * m - 1) * (2 * m) : Nat)
    let ntLo := Int.ediv (floorDiv72 (mulS tLo rLo)) den
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv72 (mulS tHi rHi))) den)
    if m % 2 == 1 then
      cosSeries36 mulS rLo rHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      cosSeries36 mulS rLo rHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def sinSeries36 (mulS : Int → Int → Int) (rLo rHi : Int) :
    Nat → Int → Int → Int → Int → RawIv72
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m := 36 - k
    let den : Int := ((2 * m) * (2 * m + 1) : Nat)
    let ntLo := Int.ediv (floorDiv72 (mulS tLo rLo)) den
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv72 (mulS tHi rHi))) den)
    if m % 2 == 1 then
      sinSeries36 mulS rLo rHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      sinSeries36 mulS rLo rHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def rawTaylorCosSin72 (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (rIv : RawIv72) : RawIv72 × RawIv72 :=
  let th := rawDivNat72 rIv 2
  let r2r := mul th th
  let rLo := max 0 r2r.1
  let rHi := max 0 r2r.2
  let accC := cosSeries36 mulS rLo rHi 36 scale72Int scale72Int scale72Int scale72Int
  let accS := sinSeries36 mulS rLo rHi 36 scale72Int scale72Int scale72Int scale72Int
  let c0 : RawIv72 := (accC.1 - 40, accC.2 + 40)
  let s0 := mul th (accS.1 - 40, accS.2 + 40)
  doubleAngleCosSin72 mul c0 s0

private def rawTaylorCos72 (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (rIv : RawIv72) : RawIv72 :=
  (rawTaylorCosSin72 mulS mul rIv).1

private def rawTaylorSin72 (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (rIv : RawIv72) : RawIv72 :=
  (rawTaylorCosSin72 mulS mul rIv).2

/-- 72-digit alternating Taylor series for `exp(-y)` (`y ∈ [0, 5]`), backed by `intMul192ViaCrtNtt`. -/
def taylorExpNegInterval72 (yIv : ScaledInterval72) : ScaledInterval72 :=
  rawToIv72 (rawTaylorExpNeg72 intMul192ViaCrtNtt (yIv.lo, yIv.hi))

/-- 72-digit alternating Taylor series for `cos(r)` (`r ∈ [-π, π]`), backed by `intMul192ViaCrtNtt`. -/
def taylorCosInterval72 (rIv : ScaledInterval72) : ScaledInterval72 :=
  rawToIv72 (rawTaylorCos72 intMul192ViaCrtNtt rawMul72Crt (rIv.lo, rIv.hi))

/-- 72-digit alternating Taylor series for `sin(r)` (`r ∈ [-π, π]`), backed by `intMul192ViaCrtNtt`. -/
def taylorSinInterval72 (rIv : ScaledInterval72) : ScaledInterval72 :=
  rawToIv72 (rawTaylorSin72 intMul192ViaCrtNtt rawMul72Crt (rIv.lo, rIv.hi))

/-- Conservative dyadic rational upper bounds on `128^{-σ} = 2^{-7σ}` from `σ_lo * 10^72`. -/
def n128PowNegUpperFromSigma72 (sLo72 : Nat) : Nat × Nat :=
  if sLo72 ≥ 875000 * scale66 then (1, 69)
  else if sLo72 ≥ 750000 * scale66 then (1, 38)
  else if sLo72 ≥ 625000 * scale66 then (1, 20)
  else if sLo72 ≥ 562500 * scale66 then (1, 15)
  else if sLo72 ≥ 520000 * scale66 then (1, 12)
  else if sLo72 ≥ 501000 * scale66 then (1, 11)
  else if sLo72 ≥ 500000 * scale66 then (1, 11)
  else (1, 1)

/-- Theorem (Soundness of `128^{-σ} = 2^{-7σ}` Dyadic Bounds Down to `σ = 0.501`):
Proved constructively with ZERO axioms. -/
theorem n128_pow_neg_sigma72_sound :
    69 ^ 8 < 2 ^ 49 ∧
    38 ^ 4 < 2 ^ 21 ∧
    20 ^ 8 < 2 ^ 35 ∧
    15 ^ 16 < 2 ^ 63 ∧
    12 ^ 25 < 2 ^ 91 ∧
    11 ^ 2 < 2 ^ 7 ∧
    n128PowNegUpperFromSigma72 (501000 * scale66) = (1, 11) ∧
    n128PowNegUpperFromSigma72 (500000 * scale66) = (1, 11) ∧
    n128PowNegUpperFromSigma72 (875000 * scale66) = (1, 69) := by
  decide

/-- Monotonic second-order Euler–Maclaurin remainder bound for `N = 128` across 2D rectangle
`[sLo6, sHi6] × [tLo6, tHi6]`. -/
def eulerMaclaurinB2TailRect2D_N128 (sLo6 tLo6 tHi6 : Nat) : Nat :=
  let (pNum, pDen) := n128PowNegUpperFromSigma72 (sLo6 * scale66)
  let tLoInt := tLo6 / 1000000
  let tHiInt := (tHi6 + 999999) / 1000000
  let poleTerm := (10 * 1000000 + tLoInt - 1) / tLoInt
  let halfTerm := (pNum * 1000000 + 2 * pDen - 1) / (2 * pDen)
  let b2Term := ((tHiInt + 2) * pNum * 1000000 + 1536 * pDen - 1) / (1536 * pDen)
  let intDen := 3 * (sLo6 / 125000 + 8) * 128 * pDen
  let intTerm := (2 * (tHiInt + 2) * (tHiInt + 2) * pNum * 1000000 + intDen - 1) / intDen
  poleTerm + halfTerm + b2Term + intTerm

private def generateDirichletRectTermEntryN128Core
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sigmaIv72 tIv72 : RawIv72) (n : Nat) : DirichletTermEntry :=
  if n == 1 then
    ⟨1, ⟨1000000, 1000000⟩, ⟨1000000, 1000000⟩, ⟨0, 0⟩⟩
  else
    let lnIv := lnRaw72With tbl n
    let yIv := mul sigmaIv72 lnIv
    let ampIv := rawToScaled6From72 (rawTaylorExpNeg72 mulS yIv)
    let xIv := mul tIv72 lnIv
    let rIv := reduceModTwoPiRaw72With tp xIv
    let (cosRaw, sinRaw) := rawTaylorCosSin72 mulS mul rIv
    ⟨n, ampIv, rawToScaled6From72 cosRaw, rawToScaled6From72 sinRaw⟩

private def genEntriesTree72Pow2
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sigmaIv72 tIv72 : RawIv72) : Nat → Nat → Nat → EntriesTree
  | 0, base, _ =>
    .leaf (generateDirichletRectTermEntryN128Core tp tbl mulS mul sigmaIv72 tIv72 base)
  | d + 1, base, half =>
    .node
      (genEntriesTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 d base (half / 2))
      (genEntriesTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 d (base + half) (half / 2))

private def buildRect2DCertN128Core
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  if sLo6 ≤ sHi6 ∧ tLo6 ≤ tHi6 then
    let sigmaIv72 : RawIv72 := ((sLo6 : Int) * scale66Int, (sHi6 : Int) * scale66Int)
    let tIv72 : RawIv72 := ((tLo6 : Int) * scale66Int, (tHi6 : Int) * scale66Int)
    let tree := genEntriesTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 7 1 64
    let tail := eulerMaclaurinB2TailRect2D_N128 sLo6 tLo6 tHi6
    if isValidRectTreeN64 sLo6 sHi6 tLo6 tHi6 tail tree then
      some ⟨sLo6, sHi6, tLo6, tHi6, tree.toList, tail⟩
    else
      none
  else
    none

private def sweepRectangles2DN128Core
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72) :
    List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert
  | [] => []
  | (sLo6, sHi6, tLo6, tHi6) :: rest =>
    match buildRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
    | some r => r :: sweepRectangles2DN128Core tp tbl mulS mul rest
    | none => sweepRectangles2DN128Core tp tbl mulS mul rest

/-- Builds an `N = 128` 2D rectangle certificate evaluated at 72-digit (`rawMul72Crt`) precision
against `eulerMaclaurinB2TailRect2D_N128`; returns `none` if invalid. -/
def buildRect2DCertN128 (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  buildRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt sLo6 sHi6 tLo6 tHi6

/-- Sweeps candidate `N = 128` 2D rectangles at 72-digit precision, keeping only valid certificates. -/
def sweepRectangles2DN128 : List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert :=
  sweepRectangles2DN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt

/-- Candidate ultra-deep 2D rectangles stepping down to `σ = 0.501` for `N = 128`. -/
def ultraDeepStripRectGrid2D_N128 : List (Nat × Nat × Nat × Nat) :=
  [ (501000, 503000, 108900000, 108910000),
    (501000, 503000, 109000000, 109010000),
    (501000, 503000, 125900000, 125910000),
    (501000, 503000, 126000000, 126010000),
    (502000, 504000, 136400000, 136410000),
    (505000, 507000, 108900000, 108910000),
    (510000, 512000, 108900000, 108910000) ]

/-- Theorem: Any rectangle certificate constructed by `buildRect2DCertN128` is valid.
Proved constructively with ZERO axioms. -/
theorem buildRect2DCertN128_implies_valid (sLo6 sHi6 tLo6 tHi6 : Nat) (r : DirichletRect2DCert) :
    buildRect2DCertN128 sLo6 sHi6 tLo6 tHi6 = some r → IsValidRect2DCert r := by
  dsimp [buildRect2DCertN128, buildRect2DCertN128Core]
  split
  · split
    · rename_i hvalid
      intro h
      injection h with hreq
      subst hreq
      exact isValidRectTreeN64_sound _ _ _ _ _ _ hvalid
    · intro h
      contradiction
  · intro h
    contradiction

/-- Theorem (Universal Soundness of `N = 128` 2D Rectangle Sweeper):
EVERY rectangle returned by `sweepRectangles2DN128` satisfies `IsValidRect2DCert`.
Proved constructively with ZERO axioms. -/
theorem sweepRectangles2DN128_all_valid (rects : List (Nat × Nat × Nat × Nat))
    (r : DirichletRect2DCert) :
    r ∈ sweepRectangles2DN128 rects → IsValidRect2DCert r := by
  dsimp [sweepRectangles2DN128]
  induction rects with
  | nil =>
    intro h
    cases h
  | cons head tail ih =>
    rcases head with ⟨sLo6, sHi6, tLo6, tHi6⟩
    dsimp [sweepRectangles2DN128Core]
    have hopt : buildRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt
                  sLo6 sHi6 tLo6 tHi6 = none ∨
                ∃ b, buildRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt
                  sLo6 sHi6 tLo6 tHi6 = some b := by
      cases buildRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt
          sLo6 sHi6 tLo6 tHi6 with
      | none => left; rfl
      | some b => right; exact ⟨b, rfl⟩
    rcases hopt with hnone | ⟨b, hsome⟩
    · rw [hnone]
      intro hmem
      exact ih hmem
    · rw [hsome]
      intro hmem
      have hcases : r = b ∨
          r ∈ sweepRectangles2DN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt tail := by
        cases hmem with
        | head => left; rfl
        | tail _ hrest => right; exact hrest
      rcases hcases with rfl | hrest
      · exact buildRect2DCertN128_implies_valid sLo6 sHi6 tLo6 tHi6 r hsome
      · exact ih hrest

private theorem sweep_build_step_128 (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sLo6 sHi6 tLo6 tHi6 : Nat) (rest : List (Nat × Nat × Nat × Nat))
    (hsome : (buildRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6).isSome = true) :
    ∃ r, sweepRectangles2DN128Core tp tbl mulS mul ((sLo6, sHi6, tLo6, tHi6) :: rest) =
           r :: sweepRectangles2DN128Core tp tbl mulS mul rest ∧
         r.sLo6 = sLo6 ∧ r.sHi6 = sHi6 ∧ r.tLo6 = tLo6 ∧ r.tHi6 = tHi6 := by
  dsimp [sweepRectangles2DN128Core]
  cases hbuild : buildRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
  | none =>
    rw [hbuild] at hsome
    simp at hsome
  | some r =>
    dsimp [buildRect2DCertN128Core] at hbuild
    split at hbuild
    · split at hbuild
      · injection hbuild with hreq
        subst hreq
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      · cases hbuild
    · cases hbuild

private theorem rectN128_0_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 503000 108900000 108910000).isSome = true := by
  decide +kernel

private theorem rectN128_1_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 503000 109000000 109010000).isSome = true := by
  decide +kernel

private theorem rectN128_2_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 503000 125900000 125910000).isSome = true := by
  decide +kernel

private theorem rectN128_3_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 503000 126000000 126010000).isSome = true := by
  decide +kernel

private theorem rectN128_4_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      502000 504000 136400000 136410000).isSome = true := by
  decide +kernel

private theorem rectN128_5_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      505000 507000 108900000 108910000).isSome = true := by
  decide +kernel

private theorem rectN128_6_valid :
    (buildRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      510000 512000 108900000 108910000).isSome = true := by
  decide +kernel

/-- Theorem (Ultra-Deep 2D Rectangles Down to `σ = 0.501` Certified):
All 7 candidate `N = 128` 2D rectangles down to `σ = 0.501` pass against the rigorous
second-order Euler–Maclaurin bound `eulerMaclaurinB2TailRect2D_N128` with positive 2D area
`Δσ · Δt = 140000000 / 10^12`, proved constructively via `karatsubaCrtNttMul192_universal_sound`
with ZERO `Classical.choice` and ZERO `sorryAx`. -/
theorem ultra_deep_rects_down_to_0501_certified :
    let swept := sweepRectangles2DN128 ultraDeepStripRectGrid2D_N128
    0 < swept.length ∧
    swept.length = 7 ∧
    0 < totalCertifiedAreaScaled12 swept ∧
    totalCertifiedAreaScaled12 swept = 140000000 ∧
    (∃ r ∈ swept, r.sLo6 = 501000) := by
  have hswap : sweepRectangles2DN128 ultraDeepStripRectGrid2D_N128 =
      sweepRectangles2DN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
        ultraDeepStripRectGrid2D_N128 := by
    dsimp [sweepRectangles2DN128]
    rw [twoPiRaw72_eq, lnPrimeTable72_eq, intMul192ViaCrtNtt_fn_eq, rawMul72_fn_eq]
  rw [hswap]
  dsimp [ultraDeepStripRectGrid2D_N128]
  obtain ⟨r0, hs0, h0s, h0S, h0t, h0T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 501000 503000 108900000 108910000 _ rectN128_0_valid
  obtain ⟨r1, hs1, h1s, h1S, h1t, h1T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 501000 503000 109000000 109010000 _ rectN128_1_valid
  obtain ⟨r2, hs2, h2s, h2S, h2t, h2T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 501000 503000 125900000 125910000 _ rectN128_2_valid
  obtain ⟨r3, hs3, h3s, h3S, h3t, h3T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 501000 503000 126000000 126010000 _ rectN128_3_valid
  obtain ⟨r4, hs4, h4s, h4S, h4t, h4T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 502000 504000 136400000 136410000 _ rectN128_4_valid
  obtain ⟨r5, hs5, h5s, h5S, h5t, h5T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 505000 507000 108900000 108910000 _ rectN128_5_valid
  obtain ⟨r6, hs6, h6s, h6S, h6t, h6T⟩ := sweep_build_step_128 twoPiRaw72Lit lnPrimeTable72Lit
    Int.mul rawMul72Fast 510000 512000 108900000 108910000 [] rectN128_6_valid
  have hnil : sweepRectangles2DN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast [] = [] := rfl
  rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hnil]
  refine ⟨by simp, by rfl, ?_, ?_, ⟨r0, List.Mem.head _, h0s⟩⟩
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T, h5s, h5S, h5t, h5T, h6s, h6S, h6t, h6T]
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T, h5s, h5S, h5t, h5T, h6s, h6S, h6t, h6T]


end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep72.lean
