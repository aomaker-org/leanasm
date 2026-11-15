-- Path: leanasm/src/LeanAsm/QuasiRiemann/ParametricQrhLadder.lean
-- Parametric QRH binary ladder (θ ↓ 1/2, ϑ ↑ 1) coupled to Kim-Sarnak (7/64) and ShortIntervalPrimes.
-- Max Column: 120 Columns

import LeanAsm.QuasiRiemann.ZeroDensityBridge
import LeanAsm.QuasiRiemann.ShortIntervalPrimes
import LeanAsm.GSp4FunctorialityBridge

namespace QuasiRiemann

-- =============================================================================
-- 1. Parametric Short-Interval Descent & Dual Mollifier Ascent Exponents
-- =============================================================================

/-- Inductive binary-ladder QRH short-interval exponent `θ(k) = (2^k + 1) / 2^(k + 1)`,
descending strictly from `3/4` (`k = 1`), `5/8` (`k = 2`), `9/16` (`k = 3`),
`17/32` (`k = 4`), `33/64` (`k = 5`) toward the Riemann Hypothesis limit `1/2`. -/
def qrhShortExponent (k : Nat) : QRat :=
  QRat.mk' ((2 ^ k + 1 : Nat) : Int) (2 ^ (k + 1)) (Nat.pow_pos (by decide))

/-- Dual strip / mollifier fraction `ϑ(k) = (2^(k + 1) - 1) / 2^(k + 1)`,
ascending strictly from `3/4` (`k = 1`), `7/8` (`k = 2`), `15/16` (`k = 3`),
`31/32` (`k = 4`), `63/64` (`k = 5`) toward `1`. -/
def qrhDualFraction (k : Nat) : QRat :=
  QRat.mk' ((2 ^ (k + 1) - 1 : Nat) : Int) (2 ^ (k + 1)) (Nat.pow_pos (by decide))

private theorem two_pow_succ_eq (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

private theorem two_pow_int_succ (k : Nat) :
    ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) := by
  have hn : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ_eq k
  rw [hn, Int.natCast_mul]
  rfl

private theorem one_le_two_pow (k : Nat) : 1 ≤ 2 ^ k :=
  Nat.one_le_pow k 2 (by decide)

private theorem int_short_step_lt (p : Int) (hp : 1 ≤ p) :
    (2 * p + 1) * (2 * p) < (p + 1) * (4 * p) := by
  have hl : (2 * p + 1) * (2 * p) = 4 * (p * p) + 2 * p := by
    rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
    have ha : 2 * (p * (2 * p)) = 4 * (p * p) := by ac_rfl
    rw [ha]
  have hr : (p + 1) * (4 * p) = 4 * (p * p) + 4 * p := by
    rw [Int.add_mul, Int.one_mul]
    have ha : p * (4 * p) = 4 * (p * p) := by ac_rfl
    rw [ha]
  rw [hl, hr]
  omega

private theorem int_dual_step_lt (p : Int) (hp : 1 ≤ p) :
    (p - 1) * (2 * p) < (2 * p - 1) * p := by
  have hl : (p - 1) * (2 * p) = 2 * (p * p) - 2 * p := by
    rw [Int.sub_mul, Int.one_mul]
    have ha : p * (2 * p) = 2 * (p * p) := by ac_rfl
    rw [ha]
  have hr : (2 * p - 1) * p = 2 * (p * p) - p := by
    rw [Int.sub_mul, Int.one_mul, Int.mul_assoc]
  rw [hl, hr]
  omega

/-- Universal strict descent of `qrhShortExponent`: every step `k ↦ k + 1` stays strictly
above `1/2` while strictly shrinking the QRH exponent (`qrhShortExponent (k + 1) < qrhShortExponent k`),
plus the concrete beyond-`7/8` descending chain `7/8 > 3/4 > 5/8 > 9/16 > 17/32 > 33/64 > 1/2`. -/
theorem qrhShortExponent_strict_anti :
    (∀ k : Nat,
      QRat.mk' 1 2 (by decide) < qrhShortExponent (k + 1) ∧
      qrhShortExponent (k + 1) < qrhShortExponent k) ∧
    (∀ k : Nat, 2 ≤ k → qrhShortExponent k < qrhThresholdSevenEighths) ∧
    (QRat.mk' 1 2 (by decide) < qrhShortExponent 5 ∧
     qrhShortExponent 5 < qrhShortExponent 4 ∧
     qrhShortExponent 4 < qrhShortExponent 3 ∧
     qrhShortExponent 3 < qrhShortExponent 2 ∧
     qrhShortExponent 2 < qrhShortExponent 1 ∧
     qrhShortExponent 1 < qrhThresholdSevenEighths) := by
  have hstep : ∀ k : Nat,
      QRat.mk' 1 2 (by decide) < qrhShortExponent (k + 1) ∧
      qrhShortExponent (k + 1) < qrhShortExponent k := by
    intro k
    have hpow : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := Int.ofNat_le.mpr (one_le_two_pow k)
    have hp1 : ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) :=
      two_pow_int_succ k
    have hp2 : ((2 ^ (k + 2) : Nat) : Int) = 4 * ((2 ^ k : Nat) : Int) := by
      rw [two_pow_int_succ (k + 1), hp1, ← Int.mul_assoc]
      rfl
    change (1 : Int) * ((2 ^ (k + 2) : Nat) : Int) <
        ((2 ^ (k + 1) + 1 : Nat) : Int) * (2 : Int) ∧
      ((2 ^ (k + 1) + 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int) <
        ((2 ^ k + 1 : Nat) : Int) * ((2 ^ (k + 2) : Nat) : Int)
    rw [Int.natCast_add, Int.natCast_add, hp1, hp2]
    exact ⟨by omega, int_short_step_lt ((2 ^ k : Nat) : Int) hpow⟩
  refine ⟨hstep, ?_, by decide⟩
  intro k hk
  induction k with
  | zero => omega
  | succ k' ih =>
    cases Nat.decLe 2 k' with
    | isTrue hge =>
      have hk1 := (hstep k').2
      have h78 := ih hge
      change ((2 ^ (k' + 1) + 1 : Nat) : Int) * (8 : Int) <
        (7 : Int) * ((2 ^ (k' + 2) : Nat) : Int)
      change ((2 ^ (k' + 1) + 1 : Nat) : Int) * ((2 ^ (k' + 1) : Nat) : Int) <
        ((2 ^ k' + 1 : Nat) : Int) * ((2 ^ (k' + 2) : Nat) : Int) at hk1
      change ((2 ^ k' + 1 : Nat) : Int) * (8 : Int) <
        (7 : Int) * ((2 ^ (k' + 1) : Nat) : Int) at h78
      have hpos : (0 : Int) < ((2 ^ (k' + 1) : Nat) : Int) :=
        Int.natCast_pos.mpr (Nat.pow_pos (by decide))
      have hmul1 :
          (((2 ^ (k' + 1) + 1 : Nat) : Int) * ((2 ^ (k' + 1) : Nat) : Int)) * 8 <
            (((2 ^ k' + 1 : Nat) : Int) * ((2 ^ (k' + 2) : Nat) : Int)) * 8 :=
        Int.mul_lt_mul_of_pos_right hk1 (by decide)
      have hmul2 :
          (((2 ^ k' + 1 : Nat) : Int) * 8) * ((2 ^ (k' + 2) : Nat) : Int) <
            ((7 : Int) * ((2 ^ (k' + 1) : Nat) : Int)) * ((2 ^ (k' + 2) : Nat) : Int) :=
        Int.mul_lt_mul_of_pos_right h78 (Int.natCast_pos.mpr (Nat.pow_pos (by decide)))
      have ha : (((2 ^ (k' + 1) + 1 : Nat) : Int) * 8) * ((2 ^ (k' + 1) : Nat) : Int) =
          (((2 ^ (k' + 1) + 1 : Nat) : Int) * ((2 ^ (k' + 1) : Nat) : Int)) * 8 := by ac_rfl
      have hb : (((2 ^ k' + 1 : Nat) : Int) * ((2 ^ (k' + 2) : Nat) : Int)) * 8 =
          (((2 ^ k' + 1 : Nat) : Int) * 8) * ((2 ^ (k' + 2) : Nat) : Int) := by ac_rfl
      have hc : ((7 : Int) * ((2 ^ (k' + 1) : Nat) : Int)) * ((2 ^ (k' + 2) : Nat) : Int) =
          ((7 : Int) * ((2 ^ (k' + 2) : Nat) : Int)) * ((2 ^ (k' + 1) : Nat) : Int) := by ac_rfl
      have heqL :
          (((2 ^ (k' + 1) + 1 : Nat) : Int) * 8) * ((2 ^ (k' + 1) : Nat) : Int) <
            ((7 : Int) * ((2 ^ (k' + 2) : Nat) : Int)) * ((2 ^ (k' + 1) : Nat) : Int) := by
        omega
      exact Int.lt_of_mul_lt_mul_right heqL (Int.le_of_lt hpos)
    | isFalse _ =>
      have hk2 : k' + 1 = 2 := by omega
      rw [hk2]
      decide

/-- Explicit rational comparison of `qrhShortExponent` against `ZeroDensityBridge` and
`ShortIntervalPrimes` density benchmarks: Huxley `7/12`, Guth–Maynard `17/30`,
and `zdGuthMaynard` saving `1 - 15/26 = 11/26` (strictly overtaken between `k = 2` and `k = 3`). -/
theorem qrhShortExponent_density_benchmarks :
    let eHux := shortIntervalDensityExponent 12 5
    let eGM := shortIntervalDensityExponent 30 13
    let gmSav := QRat.ofInt 1 - zdGuthMaynard.exponent (QRat.mk' 3 4)
    QRat.eqv eHux (QRat.mk' 7 12) ∧
    QRat.eqv eGM (QRat.mk' 17 30) ∧
    QRat.eqv gmSav (QRat.mk' 11 26) ∧
    gmSav < QRat.mk' 1 2 ∧
    QRat.mk' 1 2 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 3 ∧
    qrhShortExponent 3 < eGM ∧
    eGM < eHux ∧
    eHux < qrhShortExponent 2 ∧
    qrhShortExponent 2 < qrhThresholdSevenEighths ∧
    chebyshevGap (qrhShortExponent 2) < gmSav ∧
    gmSav < chebyshevGap (qrhShortExponent 3) ∧
    chebyshevGap (qrhShortExponent 3) < chebyshevGap (qrhShortExponent 4) := by
  decide

private theorem qrat_sum_dual_int (p : Int) :
    ((p + 1) * (2 * p) + (2 * p - 1) * (2 * p)) * 2 = 3 * ((2 * p) * (2 * p)) := by
  have hl : (p + 1) * (2 * p) + (2 * p - 1) * (2 * p) = (3 * p) * (2 * p) := by
    rw [← Int.add_mul]
    have hm : (p + 1) + (2 * p - 1) = 3 * p := by omega
    rw [hm]
  rw [hl]
  ac_rfl

private theorem qrat_gap_dual_int (p : Int) :
    ((2 * p - 1) * 2 - 1 * (2 * p)) * (1 * (2 * p)) =
      (1 * (2 * p) - (p + 1) * 1) * ((2 * p) * 2) := by
  have hl : (2 * p - 1) * 2 - 1 * (2 * p) = 2 * (p - 1) := by omega
  have hr : 1 * (2 * p) - (p + 1) * 1 = p - 1 := by omega
  rw [hl, hr, Int.one_mul]
  ac_rfl

private theorem qrat_moll_dual_int (q : Int) :
    (1 * (q * 2) - (q - 1) * 1 * 1) * (2 * q) = (q + 1) * (1 * (q * 2)) := by
  have hl : 1 * (q * 2) - (q - 1) * 1 * 1 = q + 1 := by omega
  rw [hl, Int.one_mul]
  ac_rfl

/-- Universal strict ascent `7/8 < 15/16 < 31/32 < ... < 1` of `qrhDualFraction`,
together with exact dualities `qrhShortExponent k + qrhDualFraction k = 3/2`,
`qrhDualFraction k - 1/2 = 1 - qrhShortExponent k`, and
`qrhThresholdFromMollifier (qrhDualFraction k) = qrhShortExponent (k + 1)`. -/
theorem qrhDualFraction_strict_mono :
    (∀ k : Nat,
      qrhDualFraction k < qrhDualFraction (k + 1) ∧
      qrhDualFraction (k + 1) < QRat.ofInt 1) ∧
    (∀ k : Nat,
      QRat.eqv (qrhShortExponent k + qrhDualFraction k) (QRat.mk' 3 2 (by decide))) ∧
    (∀ k : Nat,
      QRat.eqv (qrhDualFraction k - QRat.mk' 1 2 (by decide))
        (QRat.ofInt 1 - qrhShortExponent k)) ∧
    (∀ k : Nat,
      QRat.eqv (qrhThresholdFromMollifier (qrhDualFraction k))
        (qrhShortExponent (k + 1))) ∧
    QRat.eqv qrhThresholdSevenEighths (qrhDualFraction 2) ∧
    (qrhDualFraction 2 < qrhDualFraction 3 ∧
     qrhDualFraction 3 < qrhDualFraction 4 ∧
     qrhDualFraction 4 < qrhDualFraction 5 ∧
     qrhDualFraction 5 < QRat.ofInt 1) := by
  have hmono : ∀ k : Nat,
      qrhDualFraction k < qrhDualFraction (k + 1) ∧
      qrhDualFraction (k + 1) < QRat.ofInt 1 := by
    intro k
    have hpow : 1 ≤ 2 ^ (k + 1) := one_le_two_pow (k + 1)
    have hsub1 : ((2 ^ (k + 1) - 1 : Nat) : Int) = ((2 ^ (k + 1) : Nat) : Int) - 1 :=
      Int.ofNat_sub hpow
    have hpow2 : 1 ≤ 2 ^ (k + 2) := one_le_two_pow (k + 2)
    have hsub2 : ((2 ^ (k + 2) - 1 : Nat) : Int) = ((2 ^ (k + 2) : Nat) : Int) - 1 :=
      Int.ofNat_sub hpow2
    have hp2 : ((2 ^ (k + 2) : Nat) : Int) = 2 * ((2 ^ (k + 1) : Nat) : Int) :=
      two_pow_int_succ (k + 1)
    change ((2 ^ (k + 1) - 1 : Nat) : Int) * ((2 ^ (k + 2) : Nat) : Int) <
        ((2 ^ (k + 2) - 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int) ∧
      ((2 ^ (k + 2) - 1 : Nat) : Int) * (1 : Int) <
        (1 : Int) * ((2 ^ (k + 2) : Nat) : Int)
    rw [hsub1, hsub2, hp2]
    have hpos : (1 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) := Int.ofNat_le.mpr hpow
    exact ⟨int_dual_step_lt ((2 ^ (k + 1) : Nat) : Int) hpos, by omega⟩
  have hsum : ∀ k : Nat,
      QRat.eqv (qrhShortExponent k + qrhDualFraction k) (QRat.mk' 3 2 (by decide)) := by
    intro k
    have hpow1 : 1 ≤ 2 ^ (k + 1) := one_le_two_pow (k + 1)
    have hsub1 : ((2 ^ (k + 1) - 1 : Nat) : Int) = ((2 ^ (k + 1) : Nat) : Int) - 1 :=
      Int.ofNat_sub hpow1
    have hp1 : ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) := two_pow_int_succ k
    change (((2 ^ k + 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int) +
        ((2 ^ (k + 1) - 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int)) * (2 : Int) =
      (3 : Int) * ((2 ^ (k + 1) * 2 ^ (k + 1) : Nat) : Int)
    rw [Int.natCast_add, hsub1, Int.natCast_mul, hp1]
    exact qrat_sum_dual_int ((2 ^ k : Nat) : Int)
  have hgap : ∀ k : Nat,
      QRat.eqv (qrhDualFraction k - QRat.mk' 1 2 (by decide))
        (QRat.ofInt 1 - qrhShortExponent k) := by
    intro k
    have hpow1 : 1 ≤ 2 ^ (k + 1) := one_le_two_pow (k + 1)
    have hsub1 : ((2 ^ (k + 1) - 1 : Nat) : Int) = ((2 ^ (k + 1) : Nat) : Int) - 1 :=
      Int.ofNat_sub hpow1
    have hp1 : ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) := two_pow_int_succ k
    change (((2 ^ (k + 1) - 1 : Nat) : Int) * (2 : Int) -
        (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)) * ((1 * 2 ^ (k + 1) : Nat) : Int) =
      ((1 : Int) * ((2 ^ (k + 1) : Nat) : Int) - ((2 ^ k + 1 : Nat) : Int) * (1 : Int)) *
        ((2 ^ (k + 1) * 2 : Nat) : Int)
    rw [hsub1, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, hp1]
    exact qrat_gap_dual_int ((2 ^ k : Nat) : Int)
  have hmoll : ∀ k : Nat,
      QRat.eqv (qrhThresholdFromMollifier (qrhDualFraction k)) (qrhShortExponent (k + 1)) := by
    intro k
    have hpow1 : 1 ≤ 2 ^ (k + 1) := one_le_two_pow (k + 1)
    have hsub1 : ((2 ^ (k + 1) - 1 : Nat) : Int) = ((2 ^ (k + 1) : Nat) : Int) - 1 :=
      Int.ofNat_sub hpow1
    have hp2 : ((2 ^ (k + 2) : Nat) : Int) = 2 * ((2 ^ (k + 1) : Nat) : Int) :=
      two_pow_int_succ (k + 1)
    rw [show qrhThresholdFromMollifier (qrhDualFraction k) =
        QRat.ofInt 1 - QRat.div (qrhDualFraction k) (QRat.ofInt 2) (by decide) from rfl]
    rw [show QRat.div (qrhDualFraction k) (QRat.ofInt 2) (by decide) =
        ⟨((2 ^ (k + 1) - 1 : Nat) : Int) * 1, 2 ^ (k + 1) * 2,
          Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)⟩ from rfl]
    change ((1 : Int) * ((2 ^ (k + 1) * 2 : Nat) : Int) -
        (((2 ^ (k + 1) - 1 : Nat) : Int) * (1 : Int)) * (1 : Int)) *
          ((2 ^ (k + 2) : Nat) : Int) =
      ((2 ^ (k + 1) + 1 : Nat) : Int) * ((1 * (2 ^ (k + 1) * 2) : Nat) : Int)
    rw [hsub1, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, hp2]
    exact qrat_moll_dual_int ((2 ^ (k + 1) : Nat) : Int)
  exact ⟨hmono, hsum, hgap, hmoll, by decide, by decide⟩

-- =============================================================================
-- 2. Automorphic Coupling & Kim-Sarnak (7/64) Amplified QRH Step
-- =============================================================================

private theorem pow_ten_factor_lt_pql
    (eBase coeff eCorr targetCoeff eTotal : Nat)
    (hCorrLe : eCorr ≤ eBase)
    (hCoeff : 2 * coeff + 1 < targetCoeff)
    (hScale : targetCoeff ≤ 10 ^ (eTotal - eBase))
    (hBaseLe : eBase ≤ eTotal) :
    2 * (coeff * 10 ^ eBase) + 10 ^ eCorr < 10 ^ eTotal := by
  have h1 : 10 ^ eCorr ≤ 10 ^ eBase := Nat.pow_le_pow_right (by decide) hCorrLe
  have h2 : 2 * (coeff * 10 ^ eBase) + 10 ^ eCorr ≤ (2 * coeff + 1) * 10 ^ eBase := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    omega
  have h3 : (2 * coeff + 1) * 10 ^ eBase < targetCoeff * 10 ^ eBase :=
    Nat.mul_lt_mul_of_pos_right hCoeff (Nat.pow_pos (by decide))
  have h4 : targetCoeff * 10 ^ eBase ≤ 10 ^ (eTotal - eBase) * 10 ^ eBase :=
    Nat.mul_le_mul_right _ hScale
  have h5 : 10 ^ (eTotal - eBase) * 10 ^ eBase = 10 ^ eTotal := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hBaseLe]
  omega

/-- Chebyshev spec at `x = 10^96` (`k = 8`) for the `k = 4` rung `θ = 17/32`. -/
def chebyshevSpec96_1732 : ChebyshevRemainderSpec :=
  ⟨8, by decide, 1, by decide, qrhShortExponent 4, by decide, by decide⟩

/-- Short-interval spec at `(x = 10^96, h = 10^57)` for `θ = 17/32` (`qrhShortExponent 4`).
Since `96 * 17 / 32 = 51` (`x^(17/32) = 10^51`), `2 * errUpper + 10^51 < 10^57`. -/
def shortIntervalQrh1732Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 17
    thetaDen := 32
    xScaleExp := 96
    hScaleExp := 57
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec96_1732
    primePowerCorr := 10 ^ 51
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Concrete `HasGuaranteedPrime` proof for `shortIntervalQrh1732Spec` (`10^96, +10^57`). -/
theorem shortIntervalQrh1732Spec_has_prime :
    shortIntervalQrh1732Spec.HasGuaranteedPrime := by
  dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh1732Spec,
    qrhRemainderBoundAtTwoTenPow, chebyshevSpec96_1732, qrhShortExponent]
  have hceil : tenPowThetaCeilExp 8 (QRat.mk' 17 32 (by decide)) = 51 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 8) * (29 * 8)) = 107648 := by decide
  have hEq : 2 * 1 * 10 ^ 51 * ((29 * 8) * (29 * 8)) = 107648 * 10 ^ 51 := by
    calc 2 * 1 * 10 ^ 51 * ((29 * 8) * (29 * 8))
        = (2 * 1 * ((29 * 8) * (29 * 8))) * 10 ^ 51 := by ac_rfl
      _ = 107648 * 10 ^ 51 := by rw [hmul]
  rw [hEq]
  exact pow_ten_factor_lt_pql 51 107648 51 1000000 57
    (by decide) (by decide) (by decide) (by decide)

/-- Admissible mollifier length amplified by an automorphic off-diagonal saving `θAuto`:
`ϑ(θAuto) = 1 - 2 * θAuto`, sending convexity (`1/2 ↦ 0`), Selberg (`1/4 ↦ 1/2`),
Kim-Shahidi `Sym^3` (`1/9 ↦ 7/9`), Kim-Sarnak `Sym^4` (`7/64 ↦ 25/32`), and
Ramanujan (`0 ↦ 1`). -/
def mollifierFromAutomorphic (θAuto : QRat) : QRat :=
  QRat.ofInt 1 - QRat.ofInt 2 * θAuto

/-- Resulting QRH threshold `1/2 + θAuto` (`= qrhThresholdFromMollifier (mollifierFromAutomorphic θAuto)`). -/
def qrhFromAutomorphic (θAuto : QRat) : QRat :=
  qrhThresholdFromMollifier (mollifierFromAutomorphic θAuto)

theorem qrhFromAutomorphic_eqv_half_add (θAuto : QRat) :
    QRat.eqv (qrhFromAutomorphic θAuto) (QRat.mk' 1 2 (by decide) + θAuto) := by
  rcases θAuto with ⟨n, d, hd⟩
  rw [show qrhFromAutomorphic ⟨n, d, hd⟩ =
      QRat.ofInt 1 - QRat.div (mollifierFromAutomorphic ⟨n, d, hd⟩) (QRat.ofInt 2) (by decide)
    from rfl]
  rw [show QRat.div (mollifierFromAutomorphic ⟨n, d, hd⟩) (QRat.ofInt 2) (by decide) =
      ⟨(mollifierFromAutomorphic ⟨n, d, hd⟩).num * 1,
        (mollifierFromAutomorphic ⟨n, d, hd⟩).den * 2,
        Nat.mul_pos (mollifierFromAutomorphic ⟨n, d, hd⟩).den_pos (by decide)⟩ from rfl]
  change ((1 : Int) * ((1 * (1 * d) * 2 : Nat) : Int) -
      ((1 * ((1 * d : Nat) : Int) - (2 * n) * 1) * 1) * 1) * ((2 * d : Nat) : Int) =
    ((1 : Int) * (d : Int) + n * 2) * ((1 * (1 * (1 * d) * 2) : Nat) : Int)
  repeat rw [Int.natCast_mul]
  rw [show ((1 : Nat) : Int) = 1 from rfl, show ((2 : Nat) : Int) = 2 from rfl]
  have ha : 1 * (1 * (1 * (d : Int)) * 2) - (1 * (1 * (d : Int)) - 2 * n * 1) * 1 * 1 =
      (d : Int) + 2 * n := by omega
  have hb : 1 * (1 * (1 * (d : Int)) * 2) = 2 * (d : Int) := by omega
  have hc : 1 * (d : Int) + n * 2 = (d : Int) + 2 * n := by omega
  rw [ha, hb, hc]

/-- Parametric QRH bridge coupling a `ZeroDensitySpec`, binary rung index `rungK ≥ 2`,
automorphic off-diagonal exponent `autoTheta < thetaSelberg`, admissible mollifier length,
and consecutive certified `ShortIntervalChebyshevSpec` steps (`rungK ↦ rungK + 1`). -/
structure ParametricQrhBridgeSpec where
  zdSpec : ZeroDensitySpec
  rungK : Nat
  rungK_ge_two : 2 ≤ rungK
  autoTheta : QRat
  autoTheta_nonneg : (0 : Int) ≤ autoTheta.num
  autoTheta_lt_selberg : autoTheta < GSp4FunctorialityBridge.thetaSelberg
  mollifierSpan : QRat
  mollifier_eq : QRat.eqv mollifierSpan (mollifierFromAutomorphic autoTheta)
  shortSpec : ShortIntervalChebyshevSpec
  nextShortSpec : ShortIntervalChebyshevSpec
  short_theta_eq : QRat.eqv shortSpec.thetaQRat (qrhShortExponent rungK)
  next_theta_eq : QRat.eqv nextShortSpec.thetaQRat (qrhShortExponent (rungK + 1))
  short_has_prime : shortSpec.HasGuaranteedPrime
  next_has_prime : nextShortSpec.HasGuaranteedPrime

/-- Concrete `ParametricQrhBridgeSpec` realizing `k = 3 ↦ 4` (`9/16 ↦ 17/32 < 17/30 < 7/8`)
coupled to `zdGuthMaynard` (`30/13`) and `GSp4FunctorialityBridge.thetaKimSarnakSym4` (`7/64`). -/
def kimSarnakBridgeSpec : ParametricQrhBridgeSpec where
  zdSpec := zdGuthMaynard
  rungK := 3
  rungK_ge_two := by decide
  autoTheta := GSp4FunctorialityBridge.thetaKimSarnakSym4
  autoTheta_nonneg := by decide
  autoTheta_lt_selberg := by decide
  mollifierSpan := QRat.mk' 25 32 (by decide)
  mollifier_eq := by decide
  shortSpec := shortIntervalQrh916Spec
  nextShortSpec := shortIntervalQrh1732Spec
  short_theta_eq := by decide
  next_theta_eq := by decide
  short_has_prime := sub_three_quarters_qrh_ladder_certs.2.2.2.2.2.1
  next_has_prime := shortIntervalQrh1732Spec_has_prime

private theorem qrat_eqv_symm {a b : QRat} (h : QRat.eqv a b) : QRat.eqv b a := by
  change a.num * (b.den : Int) = b.num * (a.den : Int) at h
  change b.num * (a.den : Int) = a.num * (b.den : Int)
  exact h.symm

private theorem qrat_eqv_lt_right {a b c : QRat} (heqv : QRat.eqv b c) (hlt : a < b) :
    a < c := by
  change a.num * (b.den : Int) < b.num * (a.den : Int) at hlt
  change b.num * (c.den : Int) = c.num * (b.den : Int) at heqv
  change a.num * (c.den : Int) < c.num * (a.den : Int)
  have hb : (0 : Int) < (b.den : Int) := Int.natCast_pos.mpr b.den_pos
  have hc : (0 : Int) < (c.den : Int) := Int.natCast_pos.mpr c.den_pos
  have h1 : (a.num * (b.den : Int)) * (c.den : Int) < (b.num * (a.den : Int)) * (c.den : Int) :=
    Int.mul_lt_mul_of_pos_right hlt hc
  have hl : (a.num * (b.den : Int)) * (c.den : Int) =
      (a.num * (c.den : Int)) * (b.den : Int) := by ac_rfl
  have hr : (b.num * (a.den : Int)) * (c.den : Int) =
      (b.num * (c.den : Int)) * (a.den : Int) := by ac_rfl
  have h2 : (c.num * (b.den : Int)) * (a.den : Int) =
      (c.num * (a.den : Int)) * (b.den : Int) := by ac_rfl
  rw [hl, hr, heqv, h2] at h1
  exact Int.lt_of_mul_lt_mul_right h1 (Int.le_of_lt hb)

private theorem qrat_eqv_lt_left {a b c : QRat} (heqv : QRat.eqv a b) (hlt : b < c) :
    a < c := by
  change b.num * (c.den : Int) < c.num * (b.den : Int) at hlt
  change a.num * (b.den : Int) = b.num * (a.den : Int) at heqv
  change a.num * (c.den : Int) < c.num * (a.den : Int)
  have hb : (0 : Int) < (b.den : Int) := Int.natCast_pos.mpr b.den_pos
  have ha : (0 : Int) < (a.den : Int) := Int.natCast_pos.mpr a.den_pos
  have h1 : (b.num * (c.den : Int)) * (a.den : Int) < (c.num * (b.den : Int)) * (a.den : Int) :=
    Int.mul_lt_mul_of_pos_right hlt ha
  have hl : (b.num * (c.den : Int)) * (a.den : Int) =
      (b.num * (a.den : Int)) * (c.den : Int) := by ac_rfl
  have hr : (c.num * (b.den : Int)) * (a.den : Int) =
      (c.num * (a.den : Int)) * (b.den : Int) := by ac_rfl
  have h2 : (a.num * (b.den : Int)) * (c.den : Int) =
      (a.num * (c.den : Int)) * (b.den : Int) := by ac_rfl
  rw [hl, ← heqv, h2, hr] at h1
  exact Int.lt_of_mul_lt_mul_right h1 (Int.le_of_lt hb)

private theorem qrat_sq_lt_of_nonneg_lt {a b : QRat} (ha : (0 : Int) ≤ a.num) (hlt : a < b) :
    a * a < b * b := by
  have hdb : (0 : Int) < (b.den : Int) := Int.natCast_pos.mpr b.den_pos
  change a.num * (b.den : Int) < b.num * (a.den : Int) at hlt
  change (a.num * a.num) * ((b.den * b.den : Nat) : Int) <
    (b.num * b.num) * ((a.den * a.den : Nat) : Int)
  rw [Int.natCast_mul, Int.natCast_mul]
  have h1 : (a.num * (b.den : Int)) * (a.num * (b.den : Int)) <
      (b.num * (a.den : Int)) * (b.num * (a.den : Int)) := by
    have hlo : 0 ≤ a.num * (b.den : Int) := Int.mul_nonneg ha (Int.le_of_lt hdb)
    have hpos : 0 < b.num * (a.den : Int) := Int.lt_of_le_of_lt hlo hlt
    have hm1 : (a.num * (b.den : Int)) * (a.num * (b.den : Int)) ≤
        (b.num * (a.den : Int)) * (a.num * (b.den : Int)) :=
      Int.mul_le_mul_of_nonneg_right (Int.le_of_lt hlt) hlo
    have hm2 : (b.num * (a.den : Int)) * (a.num * (b.den : Int)) <
        (b.num * (a.den : Int)) * (b.num * (a.den : Int)) :=
      Int.mul_lt_mul_of_pos_left hlt hpos
    exact Int.lt_of_le_of_lt hm1 hm2
  have hl : (a.num * (b.den : Int)) * (a.num * (b.den : Int)) =
      (a.num * a.num) * ((b.den : Int) * (b.den : Int)) := by ac_rfl
  have hr : (b.num * (a.den : Int)) * (b.num * (a.den : Int)) =
      (b.num * b.num) * ((a.den : Int) * (a.den : Int)) := by ac_rfl
  rw [← hl, ← hr]
  exact h1

private theorem qrat_sub_lt_of_left_lt {c x y : QRat} (hxy : x < y) :
    c - y < c - x := by
  change x.num * (y.den : Int) < y.num * (x.den : Int) at hxy
  change (c.num * (y.den : Int) - y.num * (c.den : Int)) * ((c.den * x.den : Nat) : Int) <
    (c.num * (x.den : Int) - x.num * (c.den : Int)) * ((c.den * y.den : Nat) : Int)
  rw [Int.natCast_mul, Int.natCast_mul]
  have hcc : (0 : Int) < (c.den : Int) * (c.den : Int) :=
    Int.mul_pos (Int.natCast_pos.mpr c.den_pos) (Int.natCast_pos.mpr c.den_pos)
  have hm : (x.num * (y.den : Int)) * ((c.den : Int) * (c.den : Int)) <
      (y.num * (x.den : Int)) * ((c.den : Int) * (c.den : Int)) :=
    Int.mul_lt_mul_of_pos_right hxy hcc
  have hl : (c.num * (y.den : Int) - y.num * (c.den : Int)) * ((c.den : Int) * (x.den : Int)) =
      c.num * (c.den : Int) * (x.den : Int) * (y.den : Int) -
        (y.num * (x.den : Int)) * ((c.den : Int) * (c.den : Int)) := by
    rw [Int.sub_mul]
    have ha : c.num * (y.den : Int) * ((c.den : Int) * (x.den : Int)) =
        c.num * (c.den : Int) * (x.den : Int) * (y.den : Int) := by ac_rfl
    have hb : y.num * (c.den : Int) * ((c.den : Int) * (x.den : Int)) =
        (y.num * (x.den : Int)) * ((c.den : Int) * (c.den : Int)) := by ac_rfl
    rw [ha, hb]
  have hr : (c.num * (x.den : Int) - x.num * (c.den : Int)) * ((c.den : Int) * (y.den : Int)) =
      c.num * (c.den : Int) * (x.den : Int) * (y.den : Int) -
        (x.num * (y.den : Int)) * ((c.den : Int) * (c.den : Int)) := by
    rw [Int.sub_mul]
    have ha : c.num * (x.den : Int) * ((c.den : Int) * (y.den : Int)) =
        c.num * (c.den : Int) * (x.den : Int) * (y.den : Int) := by ac_rfl
    have hb : x.num * (c.den : Int) * ((c.den : Int) * (y.den : Int)) =
        (x.num * (y.den : Int)) * ((c.den : Int) * (c.den : Int)) := by ac_rfl
    rw [ha, hb]
  rw [hl, hr]
  omega

/-- Theorem (Kim-Sarnak Amplified Parametric QRH Step):
For any valid `ParametricQrhBridgeSpec` and any strictly tighter automorphic off-diagonal
exponent `autoTheta' < spec.autoTheta` (`0 ≤ autoTheta'.num`):
1. The Selberg Laplacian spectral gap `selbergLambda1` strictly increases.
2. The admissible mollifier span `1 - 2 * θAuto` strictly increases and its associated
   QRH threshold `qrhFromAutomorphic` strictly decreases.
3. Both the dual ascent (`qrhDualFraction spec.rungK < qrhDualFraction (spec.rungK + 1)`) and
   short-interval descent (`nextShortSpec.thetaQRat < shortSpec.thetaQRat`) advance strictly,
   strictly enlarging `chebyshevGap` beyond `1/8 = 1 - 7/8`.
4. Any Chebyshev realization meeting `spec.nextShortSpec` envelopes guarantees positive prime
   count `(0 : Int) < thetaXH - thetaX` in `(x, x + h]`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem kim_sarnak_amplified_qrh_step
    (spec : ParametricQrhBridgeSpec)
    (autoTheta' : QRat)
    (hNonneg' : (0 : Int) ≤ autoTheta'.num)
    (hTight : autoTheta' < spec.autoTheta) :
    GSp4FunctorialityBridge.selbergLambda1 spec.autoTheta <
      GSp4FunctorialityBridge.selbergLambda1 autoTheta' ∧
    spec.mollifierSpan < mollifierFromAutomorphic autoTheta' ∧
    qrhFromAutomorphic autoTheta' < qrhFromAutomorphic spec.autoTheta ∧
    qrhDualFraction spec.rungK < qrhDualFraction (spec.rungK + 1) ∧
    spec.nextShortSpec.thetaQRat < spec.shortSpec.thetaQRat ∧
    spec.nextShortSpec.thetaQRat < qrhThresholdSevenEighths ∧
    chebyshevGap spec.shortSpec.thetaQRat < chebyshevGap spec.nextShortSpec.thetaQRat ∧
    chebyshevGap qrhThresholdSevenEighths < chebyshevGap spec.nextShortSpec.thetaQRat ∧
    (∀ (chebNext : ChebyshevRemainderSpec) (psiX psiXH thetaX thetaXH : Int),
      spec.nextShortSpec.hScaleExp ≤ spec.nextShortSpec.xScaleExp →
      qrhRemainderBoundAtTwoTenPow chebNext ≤ spec.nextShortSpec.errUpper →
      Int.natAbs (psiX - ((10 ^ spec.nextShortSpec.xScaleExp : Nat) : Int)) ≤
        spec.nextShortSpec.errUpper →
      Int.natAbs (psiXH -
          ((10 ^ spec.nextShortSpec.xScaleExp + 10 ^ spec.nextShortSpec.hScaleExp : Nat) : Int)) ≤
        spec.nextShortSpec.errUpper →
      (psiXH - psiX) - (thetaXH - thetaX) ≤ (spec.nextShortSpec.primePowerCorr : Int) →
      (0 : Int) < thetaXH - thetaX) := by
  have hSq : autoTheta' * autoTheta' < spec.autoTheta * spec.autoTheta :=
    qrat_sq_lt_of_nonneg_lt hNonneg' hTight
  have hLam :
      GSp4FunctorialityBridge.selbergLambda1 spec.autoTheta <
        GSp4FunctorialityBridge.selbergLambda1 autoTheta' := by
    dsimp [GSp4FunctorialityBridge.selbergLambda1]
    exact qrat_sub_lt_of_left_lt hSq
  have h2 : QRat.ofInt 2 * autoTheta' < QRat.ofInt 2 * spec.autoTheta := by
    change autoTheta'.num * (spec.autoTheta.den : Int) <
      spec.autoTheta.num * (autoTheta'.den : Int) at hTight
    change (2 * autoTheta'.num) * ((1 * spec.autoTheta.den : Nat) : Int) <
      (2 * spec.autoTheta.num) * ((1 * autoTheta'.den : Nat) : Int)
    simp only [Nat.one_mul]
    have hmul : 2 * (autoTheta'.num * (spec.autoTheta.den : Int)) <
        2 * (spec.autoTheta.num * (autoTheta'.den : Int)) := by omega
    have hl : (2 * autoTheta'.num) * (spec.autoTheta.den : Int) =
        2 * (autoTheta'.num * (spec.autoTheta.den : Int)) := by ac_rfl
    have hr : (2 * spec.autoTheta.num) * (autoTheta'.den : Int) =
        2 * (spec.autoTheta.num * (autoTheta'.den : Int)) := by ac_rfl
    rw [hl, hr]
    exact hmul
  have hMoll : mollifierFromAutomorphic spec.autoTheta < mollifierFromAutomorphic autoTheta' :=
    qrat_sub_lt_of_left_lt h2
  have hMollSpan : spec.mollifierSpan < mollifierFromAutomorphic autoTheta' :=
    qrat_eqv_lt_left spec.mollifier_eq hMoll
  have hQrh : qrhFromAutomorphic autoTheta' < qrhFromAutomorphic spec.autoTheta :=
    mollifier_descent_monotone _ _ hMoll
  have hDual : qrhDualFraction spec.rungK < qrhDualFraction (spec.rungK + 1) :=
    (qrhDualFraction_strict_mono.1 spec.rungK).1
  have hDesc : qrhShortExponent (spec.rungK + 1) < qrhShortExponent spec.rungK :=
    (qrhShortExponent_strict_anti.1 spec.rungK).2
  have hThetaStep : spec.nextShortSpec.thetaQRat < spec.shortSpec.thetaQRat :=
    qrat_eqv_lt_left spec.next_theta_eq (qrat_eqv_lt_right (qrat_eqv_symm spec.short_theta_eq) hDesc)
  have h78 : qrhShortExponent (spec.rungK + 1) < qrhThresholdSevenEighths :=
    qrhShortExponent_strict_anti.2.1 (spec.rungK + 1)
      (Nat.le_trans spec.rungK_ge_two (Nat.le_succ _))
  have hTheta78 : spec.nextShortSpec.thetaQRat < qrhThresholdSevenEighths :=
    qrat_eqv_lt_left spec.next_theta_eq h78
  have hGapStep : chebyshevGap spec.shortSpec.thetaQRat < chebyshevGap spec.nextShortSpec.thetaQRat :=
    qrat_sub_lt_of_left_lt hThetaStep
  have hGap78 : chebyshevGap qrhThresholdSevenEighths < chebyshevGap spec.nextShortSpec.thetaQRat :=
    qrat_sub_lt_of_left_lt hTheta78
  refine ⟨hLam, hMollSpan, hQrh, hDual, hThetaStep, hTheta78, hGapStep, hGap78, ?_⟩
  intro chebNext psiX psiXH thetaX thetaXH hH hE hBX hBXH hCorr
  exact short_interval_spec_guarantees_theta_pos chebNext spec.nextShortSpec hH hE
    psiX psiXH thetaX thetaXH hBX hBXH hCorr spec.next_has_prime

/-- Concrete certificate instantiating `kim_sarnak_amplified_qrh_step` on `kimSarnakBridgeSpec`
(`k = 3 ↦ 4`, `9/16 ↦ 17/32`) and certifying exact automorphic Kim-Sarnak `7/64` values
(`mollifierFromAutomorphic (7/64) = 25/32`, `qrhFromAutomorphic (7/64) = 39/64 < 5/8`,
and `selbergLambda1 (7/64) = 975/4096`). Zero `Classical.choice`, zero `sorryAx`. -/
theorem parametric_qrh_kim_sarnak_certs :
    QRat.eqv (mollifierFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QRat.mk' 25 32 (by decide)) ∧
    QRat.eqv (qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QRat.mk' 39 64 (by decide)) ∧
    qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4 < qrhShortExponent 2 ∧
    qrhShortExponent 4 < qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4 ∧
    QRat.eqv (GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QRat.mk' 975 4096 (by decide)) ∧
    (GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaKimShahidiSym3 <
      GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaKimSarnakSym4) ∧
    (mollifierFromAutomorphic GSp4FunctorialityBridge.thetaKimShahidiSym3 <
      mollifierFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4) ∧
    (qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimShahidiSym3) ∧
    kimSarnakBridgeSpec.nextShortSpec.thetaQRat < kimSarnakBridgeSpec.shortSpec.thetaQRat ∧
    chebyshevGap qrhThresholdSevenEighths < chebyshevGap kimSarnakBridgeSpec.nextShortSpec.thetaQRat ∧
    kimSarnakBridgeSpec.nextShortSpec.HasGuaranteedPrime := by
  have hStep := kim_sarnak_amplified_qrh_step kimSarnakBridgeSpec
    GSp4FunctorialityBridge.thetaRamanujan (by decide) (by decide)
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    hStep.2.2.2.2.1, hStep.2.2.2.2.2.2.2.1, kimSarnakBridgeSpec.next_has_prime⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ParametricQrhLadder.lean
