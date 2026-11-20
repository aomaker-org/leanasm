-- Path: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
-- Constructive cleared-denominator Euler contraction nonvanishing & reflection duality lemmas.
-- Bridges Euler-factor contraction nonvanishing and parametric QRH ladder reflection symmetry.
-- Zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.ParametricQrhLadder

namespace QuasiRiemann

private theorem two_pow_int_succ' (k : Nat) :
    ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) := by
  have hn : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hn, Int.natCast_mul]
  rfl

-- =============================================================================
-- 1. Cleared-Denominator Rational / Integer Contraction Nonvanishing
-- =============================================================================

/-- Cleared-denominator Euler factor contraction nonvanishing: `p^k - c ≠ 0` when `|c| < p^k`. -/
theorem qrh_contraction_nonvanishing_abs (p k : Nat) (c : Int)
    (hc : c.natAbs < p ^ k) :
    ((p ^ k : Nat) : Int) - c ≠ 0 := by
  have hc_lt : (c.natAbs : Int) < ((p ^ k : Nat) : Int) := Int.ofNat_lt.mpr hc
  have hc_le : c ≤ (c.natAbs : Int) := Int.le_natAbs
  omega

/-- Explicit distance-to-zero lower bound for contraction factor: `1 ≤ p^k - c` when `c < p^k`. -/
theorem qrh_contraction_distance_lower_bound (p k : Nat) (c : Int)
    (hc : c < ((p ^ k : Nat) : Int)) :
    1 ≤ ((p ^ k : Nat) : Int) - c := by
  omega

/-- Rational contraction factor nonvanishing as a `QRat`: `1 - c * p^(-k) ≠ 0`. -/
theorem qrh_contraction_qrat_ne_zero (p k : Nat) (hp : 0 < p) (c : Int)
    (hc : c.natAbs < p ^ k) :
    ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0) := by
  intro h
  change (1 * ((p ^ k : Nat) : Int) - c * 1) * 1 = 0 * ((1 * p ^ k : Nat) : Int) at h
  rw [Int.one_mul, Int.mul_one, Int.mul_one, Int.zero_mul] at h
  have hne := qrh_contraction_nonvanishing_abs p k c hc
  exact hne h

-- =============================================================================
-- 2. Dual Ladder Reflection Exponent & Duality Identities
-- =============================================================================

/-- Dual ladder reflection exponent `ϑ_refl(k) = (2^k - 1) / 2^(k + 1) = 1 - θ(k)`,
representing the reflected ladder parameter across the critical axis `1/2`. -/
def qrhReflectedExponent (k : Nat) : QRat :=
  QRat.mk' ((2 ^ k - 1 : Nat) : Int) (2 ^ (k + 1)) (Nat.pow_pos (by decide))

private theorem qrat_reflect_ident_int (p : Int) :
    (((p + 1) * (2 * p) + (p - 1) * (2 * p)) * 1) =
      1 * (2 * p * (2 * p)) := by
  have hl : (p + 1) * (2 * p) + (p - 1) * (2 * p) = 2 * p * (2 * p) := by
    have hm : (p + 1) + (p - 1) = 2 * p := by omega
    rw [← Int.add_mul, hm]
  rw [hl, Int.mul_one, Int.one_mul]

private theorem qrat_reflect_eqv_int (p : Int) :
    (p - 1) * (2 * p) =
      (1 * (2 * p) - (p + 1) * 1) * (2 * p) := by
  have hm : (p - 1) = (1 * (2 * p) - (p + 1) * 1) := by omega
  rw [hm]

private theorem qrat_short_add_half_int (p : Int) :
    ((p + 1) * 2 + 1 * (2 * p)) * (2 * p) =
      (1 * (2 * p) + 1 * 1) * (2 * p * 2) := by
  have hl : ((p + 1) * 2 + 1 * (2 * p)) = 4 * p + 2 := by omega
  have hr : (1 * (2 * p) + 1 * 1) * (2 * p * 2) = (2 * p + 1) * (4 * p) := by
    have h1 : 1 * (2 * p) + 1 * 1 = 2 * p + 1 := by omega
    have h2 : 2 * p * 2 = 4 * p := by omega
    rw [h1, h2]
  rw [hl, hr]
  have ha : (4 * p + 2) * (2 * p) = (2 * p + 1) * (4 * p) := by
    have hd : 4 * p + 2 = (2 * p + 1) * 2 := by omega
    rw [hd, Int.mul_assoc]
    have hc : 2 * (2 * p) = 4 * p := by omega
    rw [hc]
  exact ha

private theorem qrat_reflect_dist_int (p : Int) :
    (1 * (2 * p) - (1 * (2 * p) - (p + 1) * 1) * 2) * (2 * p) =
      1 * (2 * (2 * p)) := by
  have hl : 1 * (2 * p) - (1 * (2 * p) - (p + 1) * 1) * 2 = 2 := by omega
  rw [hl, Int.one_mul]

/-- Theorem: `qrhReflectedExponent k` is definitionally/cross-multiplication equivalent to
`1 - qrhShortExponent k`. -/
theorem qrhReflectedExponent_eqv_one_sub (k : Nat) :
    QRat.eqv (qrhReflectedExponent k) (QRat.ofInt 1 - qrhShortExponent k) := by
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hsub : ((2 ^ k - 1 : Nat) : Int) = ((2 ^ k : Nat) : Int) - 1 := Int.ofNat_sub hpow
  have hp1 := two_pow_int_succ' k
  change ((2 ^ k - 1 : Nat) : Int) * ((1 * 2 ^ (k + 1) : Nat) : Int) =
    ((1 : Int) * ((2 ^ (k + 1) : Nat) : Int) - ((2 ^ k + 1 : Nat) : Int) * (1 : Int)) *
      ((2 ^ (k + 1) : Nat) : Int)
  rw [Nat.one_mul]
  rw [hsub, Int.natCast_add, hp1]
  exact qrat_reflect_eqv_int ((2 ^ k : Nat) : Int)

/-- Theorem: `θ(k) + ϑ_refl(k) = 1` exact reflection sum across the critical line. -/
theorem qrh_ladder_reflection_identity (k : Nat) :
    QRat.eqv (qrhShortExponent k + qrhReflectedExponent k) (QRat.ofInt 1) := by
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hsub : ((2 ^ k - 1 : Nat) : Int) = ((2 ^ k : Nat) : Int) - 1 := Int.ofNat_sub hpow
  have hp1 := two_pow_int_succ' k
  change (((2 ^ k + 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int) +
      ((2 ^ k - 1 : Nat) : Int) * ((2 ^ (k + 1) : Nat) : Int)) * (1 : Int) =
    (1 : Int) * (((2 ^ (k + 1) * 2 ^ (k + 1) : Nat) : Int))
  rw [Int.natCast_add, hsub, Int.natCast_mul, hp1]
  exact qrat_reflect_ident_int ((2 ^ k : Nat) : Int)

/-- Dual ladder reflection identity linking ladder exponent to `1 + 1/2^(k+1)`:
`θ(k) + 1/2 = 1 + 1/2^(k+1)`. -/
theorem qrh_short_exponent_add_half_eq (k : Nat) :
    QRat.eqv (qrhShortExponent k + QRat.mk' 1 2 (by decide))
      (QRat.ofInt 1 + QRat.mk' 1 (2 ^ (k + 1)) (Nat.pow_pos (by decide))) := by
  have hp1 := two_pow_int_succ' k
  change (((2 ^ k + 1 : Nat) : Int) * (2 : Int) + (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)) *
      ((1 * 2 ^ (k + 1) : Nat) : Int) =
    ((1 : Int) * ((2 ^ (k + 1) : Nat) : Int) + (1 : Int) * (1 : Int)) *
      ((2 ^ (k + 1) * 2 : Nat) : Int)
  rw [Nat.one_mul]
  rw [Int.natCast_add, Int.natCast_mul, hp1]
  exact qrat_short_add_half_int ((2 ^ k : Nat) : Int)

/-- Dual ladder fraction sum identity: `θ(k) + ϑ(k) = 3/2`. -/
theorem qrh_ladder_dual_sum_eq_three_halves (k : Nat) :
    QRat.eqv (qrhShortExponent k + qrhDualFraction k) (QRat.mk' 3 2 (by decide)) :=
  (qrhDualFraction_strict_mono.2.1 k)

/-- Critical-axis distance identity: `θ(k) - 1/2 = 1/2^(k+1)`. -/
theorem qrh_short_exponent_distance_to_half (k : Nat) :
    QRat.eqv (qrhShortExponent k - QRat.mk' 1 2 (by decide))
      (QRat.mk' 1 (2 ^ (k + 1)) (Nat.pow_pos (by decide))) := by
  have hp1 := two_pow_int_succ' k
  change (((2 ^ k + 1 : Nat) : Int) * (2 : Int) - (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)) *
      ((2 ^ (k + 1) : Nat) : Int) =
    (1 : Int) * ((2 ^ (k + 1) * 2 : Nat) : Int)
  rw [Int.natCast_add, Int.natCast_mul, hp1]
  omega

/-- Reflected dual ladder fraction distance to critical axis: `1/2 - ϑ_refl(k) = 1/2^(k+1)`. -/
theorem qrh_reflected_exponent_distance_to_half (k : Nat) :
    QRat.eqv (QRat.mk' 1 2 (by decide) - (QRat.ofInt 1 - qrhShortExponent k))
      (QRat.mk' 1 (2 ^ (k + 1)) (Nat.pow_pos (by decide))) := by
  have hp1 := two_pow_int_succ' k
  change ((1 : Int) * ((1 * 2 ^ (k + 1) : Nat) : Int) -
      ((1 : Int) * ((2 ^ (k + 1) : Nat) : Int) -
        ((2 ^ k + 1 : Nat) : Int) * (1 : Int)) * (2 : Int)) *
        ((2 ^ (k + 1) : Nat) : Int) =
    (1 : Int) * ((2 * (1 * 2 ^ (k + 1) : Nat) : Nat) : Int)
  rw [Nat.one_mul]
  rw [Int.natCast_add, Int.natCast_mul, hp1]
  exact qrat_reflect_dist_int ((2 ^ k : Nat) : Int)

/-- Symmetric strip reflection nonvanishing bounds around the critical axis `1/2`:
`qrhReflectedExponent k < 1/2 < qrhShortExponent k`. -/
theorem qrh_symmetric_strip_reflection_bounds (k : Nat) :
    qrhReflectedExponent k < QRat.mk' 1 2 (by decide) ∧
    QRat.mk' 1 2 (by decide) < qrhShortExponent k := by
  have hp1 := two_pow_int_succ' k
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hsub : ((2 ^ k - 1 : Nat) : Int) = ((2 ^ k : Nat) : Int) - 1 := Int.ofNat_sub hpow
  constructor
  · change ((2 ^ k - 1 : Nat) : Int) * (2 : Int) <
      (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)
    rw [hsub, hp1]
    omega
  · change (1 : Int) * ((2 ^ (k + 1) : Nat) : Int) <
      ((2 ^ k + 1 : Nat) : Int) * (2 : Int)
    rw [Int.natCast_add, hp1]
    omega

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
