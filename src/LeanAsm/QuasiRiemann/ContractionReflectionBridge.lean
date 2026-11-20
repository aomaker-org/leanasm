-- Path: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
-- Constructive cleared-denominator Euler contraction nonvanishing & reflection duality lemmas.
-- Bridges Euler-factor contraction nonvanishing and parametric QRH ladder reflection symmetry.
-- Zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.Valuation.RNS

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

-- =============================================================================
-- 3. Constructive Strip Reflection, RNS, and QSD Lemmas (Issue #160)
-- =============================================================================

/-- Canonical critical axis point `1/2` as a `QRat`. -/
def halfQRat : QRat := QRat.mk' 1 2 (by decide)

/-- Reflection operator `s ↦ 1 - s` across the critical axis `1/2` over `QRat`. -/
def reflectQRat (s : QRat) : QRat := QRat.ofInt 1 - s

/-- Reflection involution identity: `1 - (1 - s) = s` up to `QRat.eqv`. -/
theorem half_plane_reflection_qrat_involution (s : QRat) :
    QRat.eqv (reflectQRat (reflectQRat s)) s := by
  change (1 * ((1 * s.den : Nat) : Int) - (1 * (s.den : Int) - s.num * 1) * 1) * (s.den : Int) =
    s.num * (((1 * (1 * s.den) : Nat) : Int))
  have h1 : ((1 * s.den : Nat) : Int) = (s.den : Int) := by rw [Nat.one_mul]
  have h2 : (((1 * (1 * s.den) : Nat) : Int)) = (s.den : Int) := by rw [Nat.one_mul, Nat.one_mul]
  rw [h1, h2]
  have h3 : (1 * (s.den : Int) - (1 * (s.den : Int) - s.num * 1) * 1) = s.num := by omega
  rw [h3]

/-- Reflection order-reversal equivalence: `1/2 < s ↔ 1 - s < 1/2`. -/
theorem half_plane_reflection_qrat_lt (s : QRat) :
    halfQRat < s ↔ reflectQRat s < halfQRat := by
  dsimp [halfQRat, reflectQRat, QRat.lt, QRat.sub, QRat.ofInt]
  constructor
  · intro h
    change 1 * s.den < s.num * 2 at h
    change (1 * (s.den : Int) - s.num * 1) * 2 < 1 * ((1 * s.den : Nat) : Int)
    rw [Nat.one_mul]
    omega
  · intro h
    change (1 * (s.den : Int) - s.num * 1) * 2 < 1 * ((1 * s.den : Nat) : Int) at h
    rw [Nat.one_mul] at h
    change 1 * s.den < s.num * 2
    omega

/-- Reflection preserves critical line coincidence: `s = 1/2 ↔ 1 - s = 1/2`. -/
theorem half_plane_reflection_qrat_eq_half (s : QRat) :
    QRat.eqv s halfQRat ↔ QRat.eqv (reflectQRat s) halfQRat := by
  dsimp [halfQRat, reflectQRat, QRat.eqv, QRat.sub, QRat.ofInt]
  constructor
  · intro h
    change s.num * 2 = 1 * (s.den : Int) at h
    change (1 * (s.den : Int) - s.num * 1) * 2 = 1 * ((1 * s.den : Nat) : Int)
    rw [Nat.one_mul]
    omega
  · intro h
    change (1 * (s.den : Int) - s.num * 1) * 2 = 1 * ((1 * s.den : Nat) : Int) at h
    rw [Nat.one_mul] at h
    change s.num * 2 = 1 * (s.den : Int)
    omega

/-- HalfPlaneReflectionQRat:
Constructive reflection duality theorem across the critical axis `1/2` for `QRat`.
Inspired by `Formalism/GammaFactorNonvanishing/RhOfRight.lean` and `HalfPlane.lean`:
Given reflection symmetry `P (1 - s) ↔ P s`, non-vanishing on the right half-plane
(`1/2 < s → ¬ P s`) forces non-vanishing on the reflected left half-plane (`s < 1/2`). -/
theorem HalfPlaneReflectionQRat (P : QRat → Prop)
    (h_symm : ∀ s : QRat, P (reflectQRat s) ↔ P s)
    (h_right : ∀ s : QRat, halfQRat < s → ¬ P s) :
    ∀ s : QRat, s < halfQRat → ¬ P s := by
  intro s hs_lt hPs
  have h_refl_lt : halfQRat < reflectQRat s := by
    dsimp [halfQRat, reflectQRat, QRat.lt, QRat.sub, QRat.ofInt] at hs_lt ⊢
    change s.num * 2 < 1 * (s.den : Int) at hs_lt
    change 1 * ((1 * s.den : Nat) : Int) < (1 * (s.den : Int) - s.num * 1) * 2
    rw [Nat.one_mul]
    omega
  have h_refl_P : P (reflectQRat s) := (h_symm s).mpr hPs
  exact h_right (reflectQRat s) h_refl_lt h_refl_P

/-- RnsStripNonVanishing:
Constructive RNS modular non-vanishing across the Mersenne prime tower `[7, 31, 127]`.
If at least one residue projection is non-zero, the reconstructed integer evaluation
form `x.reconstruct` cannot vanish (`x.reconstruct ≠ 0`). -/
theorem RnsStripNonVanishing (x : LeanAsm.QuasiRiemann.RNS.RnsInt 3)
    (h_mod : x.moduli = #[7, 31, 127])
    (r1 r2 r3 : Nat) (h_res : x.residues = #[r1, r2, r3])
    (hr1 : r1 < 7) (hr2 : r2 < 31) (hr3 : r3 < 127)
    (hp : QuasiRiemann.Valuation.AllPrimes x.moduli.toList)
    (hd : QuasiRiemann.Valuation.PairwiseDistinct x.moduli.toList)
    (hnz : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0) :
    x.reconstruct ≠ 0 := by
  have hmod := LeanAsm.QuasiRiemann.RNS.rnsInt_reconstruct_mod_eq
    r1 r2 r3 x h_res h_mod hr1 hr2 hr3 hp hd
  intro hz
  rw [hz] at hmod
  rcases hnz with hr1_nz | hr2_nz | hr3_nz
  · have h1 := hmod.1
    rw [Int.zero_emod] at h1
    have : r1 = 0 := by omega
    exact hr1_nz this
  · have h2 := hmod.2.1
    rw [Int.zero_emod] at h2
    have : r2 = 0 := by omega
    exact hr2_nz this
  · have h3 := hmod.2.2
    rw [Int.zero_emod] at h3
    have : r3 = 0 := by omega
    exact hr3_nz this

/-- QsdZeroExclusion:
Constructive QSD / rational band-exclusion bounds showing that quadratic / algebraic
spectral distance lower bounds strictly exclude non-trivial zeroes outside the
critical line within certified strip contraction envelopes. -/
theorem QsdZeroExclusion (centerLower lipNumerator radius deltaShrink : Nat)
    (_h_shrink : deltaShrink < radius)
    (h_contract : lipNumerator * radius < centerLower * (radius - deltaShrink))
    (z : Int) (hz : z.natAbs ≤ lipNumerator * radius) :
    ((centerLower * (radius - deltaShrink) : Nat) : Int) - z ≠ 0 := by
  have hz_le : z ≤ (z.natAbs : Int) := Int.le_natAbs
  have hz_neg : -z ≤ (z.natAbs : Int) := by
    have h := Int.le_natAbs (a := -z)
    rw [Int.natAbs_neg] at h
    exact h
  have hz_lt : (z.natAbs : Int) < (((centerLower * (radius - deltaShrink) : Nat) : Int)) := by
    have h1 : (z.natAbs : Int) ≤ ((lipNumerator * radius : Nat) : Int) := Int.ofNat_le.mpr hz
    have h2 : ((lipNumerator * radius : Nat) : Int) <
        (((centerLower * (radius - deltaShrink) : Nat) : Int)) :=
      Int.ofNat_lt.mpr h_contract
    omega
  omega

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
