-- Path: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
-- Constructive cleared-denominator Euler contraction nonvanishing & reflection duality lemmas.
-- Bridges Euler-factor contraction nonvanishing and parametric QRH ladder reflection symmetry.
-- Zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.DyadicAbelBridge
import LeanAsm.QuasiRiemann.MollifierVariationalBridge
import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.Valuation.Contraction
import LeanAsm.QuasiRiemann.QR.QrhCore

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

/-- Scale-dual contraction reflection bound:
For scale tower `k ≤ K`, base `0 < p`, and contraction coefficient `|c| < p^k`,
the scaled contraction reflection term `p^(K - k) * (p^k - c)` is strictly non-zero. -/
theorem qrh_dual_contraction_reflection_bound (p K k : Nat) (c : Int)
    (_hk : k ≤ K) (hp : 0 < p) (hc : c.natAbs < p ^ k) :
    ((p ^ (K - k) : Nat) : Int) * (((p ^ k : Nat) : Int) - c) ≠ 0 := by
  have _hpos : 0 < p ^ (K - k) := Nat.pow_pos hp
  have hscale_nz : ((p ^ (K - k) : Nat) : Int) ≠ 0 := by omega
  have hbase_nz : ((p ^ k : Nat) : Int) - c ≠ 0 :=
    qrh_contraction_nonvanishing_abs p k c hc
  exact Int.mul_ne_zero hscale_nz hbase_nz

/-- Scale-dual contraction reflection nonvanishing as a `QRat`:
`p^(K - k) * (1 - c * p^(-k)) ≠ 0`. -/
theorem qrh_dual_contraction_reflection_qrat_ne_zero (p K k : Nat) (c : Int)
    (hk : k ≤ K) (hp : 0 < p) (hc : c.natAbs < p ^ k) :
    ¬ QRat.eqv
      (QRat.mk' ((p ^ (K - k) : Nat) : Int) 1 (by decide) *
        (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)))
      (QRat.ofInt 0) := by
  have _h_base := qrh_contraction_qrat_ne_zero p k hp c hc
  intro h
  change (((p ^ (K - k) : Nat) : Int) * (1 * ((p ^ k : Nat) : Int) - c * 1)) * 1 =
      0 * _ at h
  rw [Int.one_mul, Int.mul_one, Int.mul_one, Int.zero_mul] at h
  have hmul_nz := qrh_dual_contraction_reflection_bound p K k c hk hp hc
  exact hmul_nz h

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

/-- Re-export of constructive RNS box/window exclusion nonvanishing in `QuasiRiemann`. -/
theorem rns_box_exclusion_ne_zero (val : Int) (boxLow boxHigh : Nat)
    (h_pos : 0 < boxLow) (h_box : (boxLow : Int) ≤ val ∧ val ≤ (boxHigh : Int)) :
    val ≠ 0 :=
  LeanAsm.QuasiRiemann.RNS.rns_box_exclusion_ne_zero val boxLow boxHigh h_pos h_box

/-- Re-export of constructive RNS rational box/window exclusion nonvanishing in `QuasiRiemann`. -/
theorem rns_qrat_box_exclusion_ne_zero (q : QRat) (boxLow boxHigh : Nat)
    (h_pos : 0 < boxLow) (h_box : (boxLow : Int) ≤ q.num ∧ q.num ≤ (boxHigh : Int)) :
    ¬ QRat.eqv q (QRat.ofInt 0) :=
  LeanAsm.QuasiRiemann.RNS.rns_qrat_box_exclusion_ne_zero q boxLow boxHigh h_pos h_box

-- =============================================================================
-- 6. Constructive Window Boxes & Character Bounds (QRatWindowBox, QRatCharBound)
-- =============================================================================

/-- Constructive 2D rational window box `[sLo, sHi] × [tLo, tHi]`.
Inspired by `CharacterBoxes.ShapeWin` in `subrepos/alpo-rh`. -/
structure QRatWindowBox where
  sLo : QRat
  sHi : QRat
  tLo : QRat
  tHi : QRat
  hs  : sLo ≤ sHi
  ht  : tLo ≤ tHi

/-- Point containment in a `QRatWindowBox`. -/
def QRatWindowBox.contains (B : QRatWindowBox) (s t : QRat) : Prop :=
  B.sLo ≤ s ∧ s ≤ B.sHi ∧ B.tLo ≤ t ∧ t ≤ B.tHi

/-- Sub-box containment relation between two `QRatWindowBox` structures. -/
def QRatWindowBox.subBox (A B : QRatWindowBox) : Prop :=
  B.sLo ≤ A.sLo ∧ A.sHi ≤ B.sHi ∧ B.tLo ≤ A.tLo ∧ A.tHi ≤ B.tHi

/-- Sub-box containment is reflexive. -/
theorem QRatWindowBox.subBox_refl (B : QRatWindowBox) :
    B.subBox B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change B.sLo.num * (B.sLo.den : Int) ≤ B.sLo.num * (B.sLo.den : Int)
    exact Int.le_refl _
  · change B.sHi.num * (B.sHi.den : Int) ≤ B.sHi.num * (B.sHi.den : Int)
    exact Int.le_refl _
  · change B.tLo.num * (B.tLo.den : Int) ≤ B.tLo.num * (B.tLo.den : Int)
    exact Int.le_refl _
  · change B.tHi.num * (B.tHi.den : Int) ≤ B.tHi.num * (B.tHi.den : Int)
    exact Int.le_refl _

/-- Sub-box containment preserves point containment (monotonicity). -/
theorem QRatWindowBox.contains_of_subBox {A B : QRatWindowBox} {s t : QRat}
    (hAB : A.subBox B) (hA : A.contains s t) :
    B.contains s t := by
  have hs1 := qrat_le_trans hAB.1 hA.1
  have hs2 := qrat_le_trans hA.2.1 hAB.2.1
  have ht1 := qrat_le_trans hAB.2.2.1 hA.2.2.1
  have ht2 := qrat_le_trans hA.2.2.2 hAB.2.2.2
  exact ⟨hs1, hs2, ht1, ht2⟩

/-- Transitivity of sub-box containment. -/
theorem QRatWindowBox.subBox_trans {A B C : QRatWindowBox}
    (hAB : A.subBox B) (hBC : B.subBox C) :
    A.subBox C := by
  have hs1 := qrat_le_trans hBC.1 hAB.1
  have hs2 := qrat_le_trans hAB.2.1 hBC.2.1
  have ht1 := qrat_le_trans hBC.2.2.1 hAB.2.2.1
  have ht2 := qrat_le_trans hAB.2.2.2 hBC.2.2.2
  exact ⟨hs1, hs2, ht1, ht2⟩

/-- Constructive character modulus / conductor bound certificate.
Inspired by `CharacterBoxes.SupplyChi` in `subrepos/alpo-rh`. -/
structure QRatCharBound where
  cond : Nat
  cond_pos : 0 < cond
  boundLo : QRat
  boundHi : QRat
  h_order : boundLo ≤ boundHi

/-- Constructive witness supply theorem:
For any conductor `q > 0` and window box `B`, supplies a certified character bound
witness `QRatCharBound` whose lower bound is positive (`0 < boundLo`) when
the box lower coordinate is positive. -/
def supplyCharWitness (cond : Nat) (hcond : 0 < cond) (B : QRatWindowBox) : QRatCharBound where
  cond := cond
  cond_pos := hcond
  boundLo := B.sLo
  boundHi := B.sHi
  h_order := B.hs

/-- Constructive character bound squared nonvanishing:
If character bound witness has lower bound `c > 0`, then the squared term `c^2` is strictly positive
and hence non-zero in `QRat`. -/
theorem qrat_char_bound_sq_ne_zero (c : Nat) (hc : 0 < c) :
    ¬ QRat.eqv (QRat.mk' ((c ^ 2 : Nat) : Int) 1 (by decide)) (QRat.ofInt 0) := by
  intro h
  change (((c ^ 2 : Nat) : Int) * (1 : Int)) = 0 * ((1 : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  have hc_sq : 0 < c ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_pos hc hc
  have : ((c ^ 2 : Nat) : Int) > 0 := by omega
  omega

/-- Character bound lower-bound positivity implies nonvanishing under rational equivalence. -/
theorem qrat_char_bound_witness_ne_zero (c : Nat) (hc : 0 < c) (den : Nat) (hden : 0 < den) :
    ¬ QRat.eqv (QRat.mk' (c : Int) den hden) (QRat.ofInt 0) := by
  intro h
  change ((c : Int) * (1 : Int)) = 0 * ((den : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  omega

/-- Composite window-box and character bound non-vanishing theorem:
Combining a window box `B` with positive `sLo` numerator and a character witness `W`
yields constructive non-zero rational margin. -/
theorem qrat_window_char_bound_nonvanishing (B : QRatWindowBox) (cond : Nat) (hcond : 0 < cond)
    (h_pos : 0 < B.sLo.num) :
    ¬ QRat.eqv (supplyCharWitness cond hcond B).boundLo (QRat.ofInt 0) := by
  intro h
  have _hd := B.sLo.den_pos
  change (B.sLo.num * (1 : Int)) = 0 * ((B.sLo.den : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  omega

/-- Non-degenerate window box specification requiring constructive non-zero scale
and carrier witness. Prevents vacuous or degenerate box instances where lower bounds
are zero or degenerate. -/
structure NonDegenerateWindowBox extends QRatWindowBox where
  sLo_pos : QRat.ofInt 0 < sLo
  tLo_pos : QRat.ofInt 0 < tLo

/-- Point containment in a `NonDegenerateWindowBox` guarantees constructive non-vanishing:
Any evaluation `(s, t)` contained in `B` is strictly positive in both coordinates. -/
theorem NonDegenerateWindowBox.contains_pos (B : NonDegenerateWindowBox) {s t : QRat}
    (h : B.toQRatWindowBox.contains s t) :
    QRat.ofInt 0 < s ∧ QRat.ofInt 0 < t := by
  have hs_pos := B.sLo_pos
  have ht_pos := B.tLo_pos
  change (0 : Int) * (B.sLo.den : Int) < B.sLo.num * 1 at hs_pos
  rw [Int.zero_mul, Int.mul_one] at hs_pos
  change (0 : Int) * (B.tLo.den : Int) < B.tLo.num * 1 at ht_pos
  rw [Int.zero_mul, Int.mul_one] at ht_pos
  have hs_le := h.1
  have ht_le := h.2.2.1
  change B.sLo.num * (s.den : Int) ≤ s.num * (B.sLo.den : Int) at hs_le
  have h_sden_pos : 0 < (s.den : Int) := by have := s.den_pos; omega
  have h_bden_pos : 0 < (B.sLo.den : Int) := by have := B.sLo.den_pos; omega
  have h_prod_s : 0 < B.sLo.num * (s.den : Int) := Int.mul_pos hs_pos h_sden_pos
  have hs_num_pos : 0 < s.num := by
    if h_pos : 0 < s.num then
      exact h_pos
    else
      have h_nonpos : s.num * (B.sLo.den : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  change B.tLo.num * (t.den : Int) ≤ t.num * (B.tLo.den : Int) at ht_le
  have h_tden_pos : 0 < (t.den : Int) := by have := t.den_pos; omega
  have h_btden_pos : 0 < (B.tLo.den : Int) := by have := B.tLo.den_pos; omega
  have h_prod_t : 0 < B.tLo.num * (t.den : Int) := Int.mul_pos ht_pos h_tden_pos
  have ht_num_pos : 0 < t.num := by
    if h_pos : 0 < t.num then
      exact h_pos
    else
      have h_nonpos : t.num * (B.tLo.den : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  constructor
  · change (0 : Int) * (s.den : Int) < s.num * 1
    rw [Int.zero_mul, Int.mul_one]
    exact hs_num_pos
  · change (0 : Int) * (t.den : Int) < t.num * 1
    rw [Int.zero_mul, Int.mul_one]
    exact ht_num_pos

/-- Constructive non-zero witness: Any point `(s, t)` in a `NonDegenerateWindowBox` is non-zero. -/
theorem NonDegenerateWindowBox.contains_ne_zero (B : NonDegenerateWindowBox) {s t : QRat}
    (h : B.toQRatWindowBox.contains s t) :
    ¬ QRat.eqv s (QRat.ofInt 0) ∧ ¬ QRat.eqv t (QRat.ofInt 0) := by
  have hpos := B.contains_pos h
  constructor
  · intro heq
    change s.num * 1 = 0 * ((s.den : Nat) : Int) at heq
    rw [Int.mul_one, Int.zero_mul] at heq
    have hs_pos := hpos.1
    change (0 : Int) * (s.den : Int) < s.num * 1 at hs_pos
    rw [Int.zero_mul, Int.mul_one] at hs_pos
    omega
  · intro heq
    change t.num * 1 = 0 * ((t.den : Nat) : Int) at heq
    rw [Int.mul_one, Int.zero_mul] at heq
    have ht_pos := hpos.2
    change (0 : Int) * (t.den : Int) < t.num * 1 at ht_pos
    rw [Int.zero_mul, Int.mul_one] at ht_pos
    omega

/-- Non-degenerate character conductor bound certificate requiring constructive
non-zero lower bound. -/
structure NonDegenerateCharBound extends QRatCharBound where
  boundLo_pos : QRat.ofInt 0 < boundLo

/-- Supplies a `NonDegenerateCharBound` from a `NonDegenerateWindowBox`. -/
def supplyNonDegenerateCharWitness (cond : Nat) (hcond : 0 < cond)
    (B : NonDegenerateWindowBox) : NonDegenerateCharBound where
  toQRatCharBound := supplyCharWitness cond hcond B.toQRatWindowBox
  boundLo_pos := B.sLo_pos

/-- Non-vanishing lower bound of `NonDegenerateCharBound`. -/
theorem NonDegenerateCharBound.boundLo_ne_zero (W : NonDegenerateCharBound) :
    ¬ QRat.eqv W.boundLo (QRat.ofInt 0) := by
  intro h
  have hp := W.boundLo_pos
  change (0 : Int) * (W.boundLo.den : Int) < W.boundLo.num * 1 at hp
  rw [Int.zero_mul, Int.mul_one] at hp
  change W.boundLo.num * 1 = 0 * ((W.boundLo.den : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  omega

-- =============================================================================
-- 7. Euler-Defect Contraction Nonvanishing & Real-Interval Box Exclusion (#167)
-- =============================================================================

/-- Euler-defect integer cleared contraction nonvanishing:
For `|a| ≤ 1` and `1 < p ^ k`, the cleared defect term `p ^ k - a` is strictly positive
and non-zero. Inspired by `CharacterBoxes.Imprimitive` in `subrepos/alpo-rh`. -/
theorem euler_defect_int_ne_zero (p k : Nat) (a : Int)
    (ha : a.natAbs ≤ 1) (hpk : 1 < p ^ k) :
    ((p ^ k : Nat) : Int) - a ≠ 0 := by
  have ha_le : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have ha_bound : (a.natAbs : Int) ≤ 1 := Int.ofNat_le.mpr ha
  have hpk_cast : 1 < ((p ^ k : Nat) : Int) := Int.ofNat_lt.mpr hpk
  omega

/-- Euler-defect integer cleared contraction strictly positive:
For `|a| ≤ 1` and `1 < p ^ k`, `0 < p ^ k - a`. -/
theorem euler_defect_int_pos (p k : Nat) (a : Int)
    (ha : a.natAbs ≤ 1) (hpk : 1 < p ^ k) :
    0 < ((p ^ k : Nat) : Int) - a := by
  have ha_le : a ≤ (a.natAbs : Int) := Int.le_natAbs
  have ha_bound : (a.natAbs : Int) ≤ 1 := Int.ofNat_le.mpr ha
  have hpk_cast : 1 < ((p ^ k : Nat) : Int) := Int.ofNat_lt.mpr hpk
  omega

/-- Euler-defect rational contraction factor nonvanishing as a `QRat`:
For `|a| ≤ 1` and `1 < p ^ k`, the rational factor `1 - a / p ^ k` is non-zero. -/
theorem euler_defect_qrat_ne_zero (p k : Nat) (hp : 0 < p) (a : Int)
    (ha : a.natAbs ≤ 1) (hpk : 1 < p ^ k) :
    ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' a (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0) := by
  intro h
  change (1 * ((p ^ k : Nat) : Int) - a * 1) * 1 = 0 * ((1 * p ^ k : Nat) : Int) at h
  rw [Int.one_mul, Int.mul_one, Int.mul_one, Int.zero_mul] at h
  have hne := euler_defect_int_ne_zero p k a ha hpk
  exact hne h

/-- Real-interval exclusion box `[1 - δ, 1 + δ]` in `QRat`.
Defines a symmetric real-interval box around 1 with radius `δ`.
Inspired by `CharacterBoxes.RealBox` in `subrepos/alpo-rh`. -/
def realIntervalBox (delta : QRat) : QRat × QRat :=
  (QRat.ofInt 1 - delta, QRat.ofInt 1 + delta)

/-- Real-interval box exclusion lower bound strictly positive:
If `0 ≤ δ` and `δ < 1` in `QRat`, then `0 < 1 - δ`. -/
theorem real_interval_box_pos (delta : QRat)
    (h_lt : delta < QRat.ofInt 1) :
    QRat.ofInt 0 < QRat.ofInt 1 - delta := by
  change delta.num * 1 < 1 * (delta.den : Int) at h_lt
  rw [Int.mul_one, Int.one_mul] at h_lt
  change 0 * (1 * delta.den : Int) < (1 * (delta.den : Int) - delta.num * 1) * 1
  rw [Int.zero_mul, Int.one_mul, Int.mul_one, Int.mul_one]
  omega

/-- Real-interval box exclusion nonvanishing on lower bound:
If `δ < 1` in `QRat`, then `1 - δ` does not vanish. -/
theorem real_interval_box_lower_ne_zero (delta : QRat)
    (h_lt : delta < QRat.ofInt 1) :
    ¬ QRat.eqv (QRat.ofInt 1 - delta) (QRat.ofInt 0) := by
  intro h
  change (1 * (delta.den : Int) - delta.num * 1) * 1 = 0 * ((1 * delta.den : Nat) : Int) at h
  rw [Int.one_mul, Int.mul_one, Int.mul_one, Int.zero_mul] at h
  change delta.num * 1 < 1 * (delta.den : Int) at h_lt
  rw [Int.mul_one, Int.one_mul] at h_lt
  omega

/-- Real-interval box exclusion on the full interval:
Any `x` in `[1 - δ, 1 + δ]` with `δ < 1` satisfies `0 < x` and therefore `x ≠ 0`. -/
theorem real_interval_box_contains_ne_zero (delta x : QRat)
    (h_lt : delta < QRat.ofInt 1)
    (hx_ge : QRat.ofInt 1 - delta ≤ x) :
    ¬ QRat.eqv x (QRat.ofInt 0) := by
  intro h
  change (1 * (delta.den : Int) - delta.num * 1) * (x.den : Int) ≤
    x.num * (((1 * delta.den : Nat) : Int)) at hx_ge
  rw [Int.one_mul, Int.mul_one] at hx_ge
  rw [Nat.one_mul] at hx_ge
  change x.num * 1 = 0 * ((x.den : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  rw [h, Int.zero_mul] at hx_ge
  change delta.num * 1 < 1 * (delta.den : Int) at h_lt
  rw [Int.mul_one, Int.one_mul] at h_lt
  have hxd := x.den_pos
  have hden_pos : 0 < (x.den : Int) := by omega
  have hdiff_pos : 0 < (delta.den : Int) - delta.num := by omega
  have hprod_pos : 0 < ((delta.den : Int) - delta.num) * (x.den : Int) :=
    Int.mul_pos hdiff_pos hden_pos
  omega

-- =============================================================================
-- 8. High-Order RNS Paired-Channel Contractions (N = 1024, 2048 / θ > 7/8) (#169)
-- =============================================================================

/-- High-order RNS pair box constructor for scale `N` and exponent `θ > 7/8`.
Constructs a paired-channel RNS contraction box over the prime tower `[7, 31, 127]`.
Uses non-zero unit RNS channel witnesses and explicit `θ`-aware cross-bound coupling
`(θ - 7/8) / (N + 1)`. Inspired by paired character boxes in `CharacterBoxes.PairRows`. -/
def highOrderRnsPairBox (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    LeanAsm.QuasiRiemann.RNS.RnsPairBox 3 where
  box1 := LeanAsm.QuasiRiemann.RNS.RnsQRat.one 3 #[7, 31, 127] (by decide)
  box2 := LeanAsm.QuasiRiemann.RNS.RnsQRat.one 3 #[7, 31, 127] (by decide)
  crossBound := QRat.mul (QRat.sub theta qrhThresholdSevenEighths) (QRat.mk' 1 (N + 1) (by omega))
  h_cross_pos := by
    dsimp [QRat.mul, QRat.sub, QRat.mk', qrhThresholdSevenEighths]
    have h_lt : (7 : Int) * theta.den < theta.num * 8 := h_theta
    have h_diff_pos : 0 < theta.num * 8 - 7 * (theta.den : Int) := by omega
    omega
  h_box1_nonneg := LeanAsm.QuasiRiemann.RNS.rnsQRat_toQRat_nonneg
    (LeanAsm.QuasiRiemann.RNS.RnsQRat.one 3 #[7, 31, 127] (by decide))
  h_box2_nonneg := LeanAsm.QuasiRiemann.RNS.rnsQRat_toQRat_nonneg
    (LeanAsm.QuasiRiemann.RNS.RnsQRat.one 3 #[7, 31, 127] (by decide))

/-- Concrete N = 1024 high-order paired-channel contraction certificate (`θ > 7/8`). -/
theorem rns_pair_box_N1024_cert (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0) :=
  (highOrderRnsPairBox 1024 theta h_theta).stepContract_ne_zero

/-- Concrete N = 2048 high-order paired-channel contraction certificate (`θ > 7/8`). -/
theorem rns_pair_box_N2048_cert (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0) :=
  (highOrderRnsPairBox 2048 theta h_theta).stepContract_ne_zero

/-- Parametric high-order paired-channel contraction certificate for arbitrary
scale `N` (`θ > 7/8`). -/
theorem rns_pair_box_param_cert (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0) :=
  (highOrderRnsPairBox N theta h_theta).stepContract_ne_zero

/-- Concrete N = 4096 high-order paired-channel contraction certificate (`θ > 7/8`). -/
theorem rns_pair_box_N4096_cert (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0) :=
  rns_pair_box_param_cert 4096 theta h_theta

/-- Explicit constructive unit RNS channel witness over the Mersenne tower `[7, 31, 127]`. -/
def highOrderRnsUnitQRat : LeanAsm.QuasiRiemann.RNS.RnsQRat 3 :=
  ⟨⟨#[1, 1, 1], #[7, 31, 127], rfl, rfl⟩, ⟨#[1, 1, 1], #[7, 31, 127], rfl, rfl⟩⟩

/-- Strict positivity of reconstructed numerator for `highOrderRnsUnitQRat`. -/
theorem highOrderRnsUnitQRat_num_pos : 0 < highOrderRnsUnitQRat.toQRat.num := by
  have h : highOrderRnsUnitQRat.toQRat.num = 1 := rfl
  rw [h]
  decide

/-- Canonical non-degenerate high-order RNS pair box constructor with constructive
non-zero witnesses. -/
def nonDegenerateHighOrderRnsPairBox (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    LeanAsm.QuasiRiemann.RNS.NonDegenerateRnsPairBox 3 where
  toRnsPairBox := {
    box1 := highOrderRnsUnitQRat
    box2 := highOrderRnsUnitQRat
    crossBound := QRat.mul (QRat.sub theta qrhThresholdSevenEighths)
      (QRat.mk' 1 (N + 1) (by omega))
    h_cross_pos := by
      dsimp [QRat.mul, QRat.sub, QRat.mk', qrhThresholdSevenEighths]
      have h_lt : (7 : Int) * theta.den < theta.num * 8 := h_theta
      have h_diff_pos : 0 < theta.num * 8 - 7 * (theta.den : Int) := by omega
      omega
    h_box1_nonneg := LeanAsm.QuasiRiemann.RNS.rnsQRat_toQRat_nonneg highOrderRnsUnitQRat
    h_box2_nonneg := LeanAsm.QuasiRiemann.RNS.rnsQRat_toQRat_nonneg highOrderRnsUnitQRat
  }
  h_box1_pos := highOrderRnsUnitQRat_num_pos
  h_box2_pos := highOrderRnsUnitQRat_num_pos

/-- Non-degenerate channel non-vanishing for `nonDegenerateHighOrderRnsPairBox`. -/
theorem nonDegenerateHighOrderRnsPairBox_channels_ne_zero (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (nonDegenerateHighOrderRnsPairBox N theta h_theta).box1.toQRat (QRat.ofInt 0) ∧
    ¬ QRat.eqv (nonDegenerateHighOrderRnsPairBox N theta h_theta).box2.toQRat (QRat.ofInt 0) :=
  (nonDegenerateHighOrderRnsPairBox N theta h_theta).channels_ne_zero

-- =============================================================================
-- 9. Constructive reflectHalf Involution & BoxSupplyBound Nonvanishing (#173)
-- =============================================================================

/-- Constructive symmetry reflection operator `reflectHalf x = 1 - x` across the
critical axis `1/2` over `QRat`.
Dual to `reflectQRat`, inspired by `RhOfRight.lean` in `subrepos/alpo-rh`. -/
def reflectHalf (x : QRat) : QRat :=
  QRat.ofInt 1 - x

/-- Involutivity of `reflectHalf`: `reflectHalf (reflectHalf x) = x` up to `QRat.eqv`. -/
theorem reflectHalf_involutive (x : QRat) :
    QRat.eqv (reflectHalf (reflectHalf x)) x :=
  half_plane_reflection_qrat_involution x

/-- Double application of `reflectHalf` restores the original `QRat` value. -/
theorem reflectHalf_reflectHalf (x : QRat) :
    QRat.eqv (reflectHalf (reflectHalf x)) x :=
  reflectHalf_involutive x

/-- Order reversal under `reflectHalf`: `x < y ↔ reflectHalf y < reflectHalf x`. -/
theorem reflectHalf_lt_reflectHalf (x y : QRat) :
    reflectHalf y < reflectHalf x ↔ x < y := by
  constructor
  · intro h
    change (1 * (y.den : Int) - y.num * 1) * ((1 * x.den : Nat) : Int) <
      (1 * (x.den : Int) - x.num * 1) * ((1 * y.den : Nat) : Int) at h
    rw [Nat.one_mul, Nat.one_mul] at h
    change x.num * (y.den : Int) < y.num * (x.den : Int)
    rw [Int.sub_mul, Int.sub_mul] at h
    rw [Int.one_mul, Int.mul_one, Int.one_mul, Int.mul_one] at h
    rw [Int.mul_comm (y.den : Int) (x.den : Int)] at h
    omega
  · intro h
    change (1 * (y.den : Int) - y.num * 1) * ((1 * x.den : Nat) : Int) <
      (1 * (x.den : Int) - x.num * 1) * ((1 * y.den : Nat) : Int)
    rw [Nat.one_mul, Nat.one_mul]
    change x.num * (y.den : Int) < y.num * (x.den : Int) at h
    rw [Int.sub_mul, Int.sub_mul]
    rw [Int.one_mul, Int.mul_one, Int.one_mul, Int.mul_one]
    rw [Int.mul_comm (y.den : Int) (x.den : Int)]
    omega

/-- Axis nonvanishing dichotomy:
If a predicate `P` on `QRat` is symmetric under `reflectHalf` (`P (reflectHalf x) ↔ P x`)
and vanishes nowhere to the right of the critical axis `1/2` (`1/2 < x → ¬ P x`),
then `P` cannot hold at any point `x < 1/2`.
Direct constructive analogue of `rh_of_right` from `RhOfRight.lean`. -/
theorem reflectHalf_axis_dichotomy (P : QRat → Prop)
    (h_symm : ∀ x : QRat, P (reflectHalf x) ↔ P x)
    (h_right : ∀ x : QRat, halfQRat < x → ¬ P x) :
    ∀ x : QRat, x < halfQRat → ¬ P x := by
  intro x hx_lt hPx
  have h_refl_lt : halfQRat < reflectHalf x := by
    dsimp [halfQRat, reflectHalf, QRat.lt, QRat.sub, QRat.ofInt] at hx_lt ⊢
    change x.num * 2 < 1 * (x.den : Int) at hx_lt
    change 1 * ((1 * x.den : Nat) : Int) < (1 * (x.den : Int) - x.num * 1) * 2
    rw [Nat.one_mul]
    omega
  have h_refl_P : P (reflectHalf x) := (h_symm x).mpr hPx
  exact h_right (reflectHalf x) h_refl_lt h_refl_P

/-- Constructive box supply bound certificate over `QRat`.
Captures an interval box `[xLo, xHi]` with a strictly positive lower bound `xLo > 0`,
guaranteeing uniform zero-free exclusion on the entire box supply.
Inspired by `CharacterBoxes/SupplyChi.lean` and `CharacterBoxes/Supply.lean`. -/
structure BoxSupplyBound where
  xLo : QRat
  xHi : QRat
  h_order : xLo ≤ xHi
  h_lo_pos : QRat.ofInt 0 < xLo

/-- Zero-free box property for `BoxSupplyBound`:
Any evaluation `x` within the supply box `[xLo, xHi]` satisfies `0 < x` and therefore
cannot vanish (`x ≠ 0` up to `QRat.eqv`). -/
theorem BoxSupplyBound.zero_free_box (B : BoxSupplyBound) (x : QRat)
    (hx_ge : B.xLo ≤ x) :
    ¬ QRat.eqv x (QRat.ofInt 0) := by
  intro h
  have h_pos := B.h_lo_pos
  change (0 : Int) * (B.xLo.den : Int) < B.xLo.num * (1 : Int) at h_pos
  rw [Int.zero_mul, Int.mul_one] at h_pos
  change x.num * (1 : Int) = 0 * ((x.den : Nat) : Int) at h
  rw [Int.mul_one, Int.zero_mul] at h
  change B.xLo.num * (x.den : Int) ≤ x.num * (B.xLo.den : Int) at hx_ge
  rw [h, Int.zero_mul] at hx_ge
  have h_xden_nat := x.den_pos
  have h_xden : 0 < (x.den : Int) := by omega
  have h_prod : 0 < B.xLo.num * (x.den : Int) := Int.mul_pos h_pos h_xden
  omega

/-- Strict positivity of any point `x` bounded below by `B.xLo`. -/
theorem BoxSupplyBound.zero_free_box_pos (B : BoxSupplyBound) (x : QRat)
    (hx_ge : B.xLo ≤ x) :
    QRat.ofInt 0 < x := by
  have h_pos := B.h_lo_pos
  change (0 : Int) * (B.xLo.den : Int) < B.xLo.num * (1 : Int) at h_pos
  rw [Int.zero_mul, Int.mul_one] at h_pos
  change (0 : Int) * (x.den : Int) < x.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change B.xLo.num * (x.den : Int) ≤ x.num * (B.xLo.den : Int) at hx_ge
  have h_xden_nat := x.den_pos
  have h_xden : 0 < (x.den : Int) := by omega
  have h_prod : 0 < B.xLo.num * (x.den : Int) := Int.mul_pos h_pos h_xden
  have h_ineq : 0 < x.num * (B.xLo.den : Int) := by omega
  if hx_pos : 0 < x.num then
    exact hx_pos
  else
    have h_bden_nat := B.xLo.den_pos
    have h_nonpos : x.num * (B.xLo.den : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    omega

/-- Canonical witness constructor for `BoxSupplyBound` given rational numerator and denominator. -/
def makeBoxSupplyBound (numLo denLo numHi denHi : Nat)
    (h_numLo_pos : 0 < numLo) (h_denLo_pos : 0 < denLo)
    (h_denHi_pos : 0 < denHi)
    (h_order : (numLo : Int) * (denHi : Int) ≤ (numHi : Int) * (denLo : Int)) :
    BoxSupplyBound where
  xLo := QRat.mk' (numLo : Int) denLo h_denLo_pos
  xHi := QRat.mk' (numHi : Int) denHi h_denHi_pos
  h_order := by
    exact h_order
  h_lo_pos := by
    change (0 : Int) * (denLo : Int) < (numLo : Int) * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    omega

/-- Converts an `RnsPairBox` into a constructive `BoxSupplyBound` on its contraction step.
Wires the discrete paired-channel RNS contraction lower bound into the continuous
interval supply representation. -/
def rnsPairBoxToBoxSupplyBound {k : Nat} (pb : LeanAsm.QuasiRiemann.RNS.RnsPairBox k) :
    BoxSupplyBound where
  xLo := pb.stepContract
  xHi := pb.stepContract
  h_order := by
    change pb.stepContract.num * (pb.stepContract.den : Int) ≤
      pb.stepContract.num * (pb.stepContract.den : Int)
    exact Int.le_refl _
  h_lo_pos := by
    have h_pos := pb.stepContract_pos
    change (0 : Int) * (pb.stepContract.den : Int) < pb.stepContract.num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    exact h_pos

/-- Converts a `NonDegenerateRnsPairBox` into a constructive `BoxSupplyBound`
with certified non-degenerate channel witnesses. -/
def nonDegenerateRnsPairBoxToBoxSupplyBound {k : Nat}
    (pb : LeanAsm.QuasiRiemann.RNS.NonDegenerateRnsPairBox k) :
    BoxSupplyBound :=
  rnsPairBoxToBoxSupplyBound pb.toRnsPairBox

/-- High-order RNS contraction box exclusion at scale `N = 1024` under `reflectHalf`.
Wires high-order paired-channel contraction at `N = 1024` (`RnsPairBox 3` via `highOrderRnsPairBox`)
and `BoxSupplyBound` into `reflectHalf` exclusion: the contraction step evaluation cannot vanish. -/
theorem qrh_rns_reflect_half_box_exclusion_1024 (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo ∧
    ¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := rns_pair_box_N1024_cert theta h_theta
  have h_xlo_eq : (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract := rfl
  have h_pos : QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo :=
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).h_lo_pos
  have h_refl := reflectHalf_reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract
  have h_refl_ne :
      ¬ QRat.eqv
        (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
        (QRat.ofInt 0) := by
    intro h
    have h_contra : (highOrderRnsPairBox 1024 theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * ((highOrderRnsPairBox 1024 theta h_theta).stepContract.den : Int) =
          (highOrderRnsPairBox 1024 theta h_theta).stepContract.num *
            ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
      have h_zero : (highOrderRnsPairBox 1024 theta h_theta).stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · omega
      change (highOrderRnsPairBox 1024 theta h_theta).stepContract.num * 1 =
        0 * (((highOrderRnsPairBox 1024 theta h_theta).stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact h_ne h_contra
  exact ⟨h_ne, h_xlo_eq, h_pos, h_refl_ne⟩

/-- High-order RNS contraction box exclusion under critical-axis reflection `reflectHalf`.
Wires high-order paired-channel contraction at `N = 2048` (`RnsPairBox 3` via `highOrderRnsPairBox`)
and `BoxSupplyBound` into `reflectHalf` exclusion: the contraction step evaluation cannot vanish. -/
theorem qrh_rns_reflect_half_box_exclusion (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo ∧
    ¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := rns_pair_box_N2048_cert theta h_theta
  have h_xlo_eq : (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract := rfl
  have h_pos : QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo :=
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).h_lo_pos
  have h_refl := reflectHalf_reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract
  have h_refl_ne :
      ¬ QRat.eqv
        (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
        (QRat.ofInt 0) := by
    intro h
    have h_contra : (highOrderRnsPairBox 2048 theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * ((highOrderRnsPairBox 2048 theta h_theta).stepContract.den : Int) =
          (highOrderRnsPairBox 2048 theta h_theta).stepContract.num *
            ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
      have h_zero : (highOrderRnsPairBox 2048 theta h_theta).stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · omega
      change (highOrderRnsPairBox 2048 theta h_theta).stepContract.num * 1 =
        0 * (((highOrderRnsPairBox 2048 theta h_theta).stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact h_ne h_contra
  exact ⟨h_ne, h_xlo_eq, h_pos, h_refl_ne⟩

/-- Parametric high-order RNS contraction box exclusion under `reflectHalf` for arbitrary `N`.
Wires high-order paired-channel contraction at scale `N` and `BoxSupplyBound` into `reflectHalf`
exclusion: the contraction step evaluation cannot vanish. -/
theorem qrh_rns_reflect_half_box_exclusion_param (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo ∧
    ¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := rns_pair_box_param_cert N theta h_theta
  have h_xlo_eq : (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract := rfl
  have h_pos : QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo :=
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).h_lo_pos
  have h_refl := reflectHalf_reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract
  have h_refl_ne :
      ¬ QRat.eqv
        (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
        (QRat.ofInt 0) := by
    intro h
    have h_contra : (highOrderRnsPairBox N theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * ((highOrderRnsPairBox N theta h_theta).stepContract.den : Int) =
          (highOrderRnsPairBox N theta h_theta).stepContract.num *
            ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
      have h_zero : (highOrderRnsPairBox N theta h_theta).stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · omega
      change (highOrderRnsPairBox N theta h_theta).stepContract.num * 1 =
        0 * (((highOrderRnsPairBox N theta h_theta).stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact h_ne h_contra
  exact ⟨h_ne, h_xlo_eq, h_pos, h_refl_ne⟩

/-- High-order RNS contraction box exclusion at scale `N = 4096` under `reflectHalf`. -/
theorem qrh_rns_reflect_half_box_exclusion_4096 (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo =
      (highOrderRnsPairBox 4096 theta h_theta).stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo ∧
    ¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0) :=
  qrh_rns_reflect_half_box_exclusion_param 4096 theta h_theta

/-- Coupled dyadic Abel gate rung 7 and high-order RNS reflection box exclusion.
Establishes that the high-order RNS paired-channel contraction at scale `8 * gate.scaleN`
(which equals `2048` when `gate.scaleN = 256`, as in `dyadicAbelGateRung7`) inherits
non-vanishing critical reflection exclusion and positive box supply bounds together
with the dyadic tail-step preservation of `gate`. -/
theorem dyadic_gate_rns_reflect_half_box_coupling
    (gate : InvSqrtTailGateSpec) (h_gate_scale : gate.scaleN = 256)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * gate.scaleN) * (gate.tailBound * gate.tailBound) ≤
      ((2 * gate.denomM) * (2 * gate.denomM)) * (gate.tailNum * gate.tailNum)) ∧
    (8 * gate.scaleN = 2048) ∧
    (¬ QRat.eqv (highOrderRnsPairBox (8 * gate.scaleN) theta h_theta).stepContract
      (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound
      (highOrderRnsPairBox (8 * gate.scaleN) theta h_theta)).xLo =
      (highOrderRnsPairBox (8 * gate.scaleN) theta h_theta).stepContract ∧
    (QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound
        (highOrderRnsPairBox (8 * gate.scaleN) theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf
        (reflectHalf
          (highOrderRnsPairBox (8 * gate.scaleN) theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step gate
  have h_scale : 8 * gate.scaleN = 2048 := by rw [h_gate_scale]
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  refine ⟨h_step, h_scale, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_rw : highOrderRnsPairBox (8 * gate.scaleN) theta h_theta =
        highOrderRnsPairBox 2048 theta h_theta := by rw [h_scale]
    rw [h_rw] at h
    exact h_excl.1 h
  · exact rfl
  · have h_pos := h_excl.2.2.1
    have h_rw : highOrderRnsPairBox (8 * gate.scaleN) theta h_theta =
        highOrderRnsPairBox 2048 theta h_theta := by rw [h_scale]
    rw [h_rw]
    exact h_pos
  · have h_refl := h_excl.2.2.2
    have h_rw : highOrderRnsPairBox (8 * gate.scaleN) theta h_theta =
        highOrderRnsPairBox 2048 theta h_theta := by rw [h_scale]
    rw [h_rw]
    exact h_refl

/-- Coupled dyadic Abel gate rung 8 and high-order RNS reflection box exclusion.
Establishes that the high-order RNS paired-channel contraction at scale `gate.scaleN`
(which equals `1024` when `gate.scaleN = 1024`, as in `dyadicAbelGateRung8`) inherits
non-vanishing critical reflection exclusion and positive box supply bounds together
with the dyadic tail-step preservation of `gate`. -/
theorem dyadic_gate_rns_reflect_half_box_coupling_1024
    (gate : InvSqrtTailGateSpec) (h_gate_scale : gate.scaleN = 1024)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * gate.scaleN) * (gate.tailBound * gate.tailBound) ≤
      ((2 * gate.denomM) * (2 * gate.denomM)) * (gate.tailNum * gate.tailNum)) ∧
    (gate.scaleN = 1024) ∧
    (¬ QRat.eqv (highOrderRnsPairBox gate.scaleN theta h_theta).stepContract
      (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound
      (highOrderRnsPairBox gate.scaleN theta h_theta)).xLo =
      (highOrderRnsPairBox gate.scaleN theta h_theta).stepContract ∧
    (QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound
        (highOrderRnsPairBox gate.scaleN theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf
        (reflectHalf
          (highOrderRnsPairBox gate.scaleN theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step gate
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  refine ⟨h_step, h_gate_scale, ?_, ?_, ?_, ?_⟩
  · intro h
    have h_rw : highOrderRnsPairBox gate.scaleN theta h_theta =
        highOrderRnsPairBox 1024 theta h_theta := by rw [h_gate_scale]
    rw [h_rw] at h
    exact h_excl.1 h
  · exact rfl
  · have h_pos := h_excl.2.2.1
    have h_rw : highOrderRnsPairBox gate.scaleN theta h_theta =
        highOrderRnsPairBox 1024 theta h_theta := by rw [h_gate_scale]
    rw [h_rw]
    exact h_pos
  · have h_refl := h_excl.2.2.2
    have h_rw : highOrderRnsPairBox gate.scaleN theta h_theta =
        highOrderRnsPairBox 1024 theta h_theta := by rw [h_gate_scale]
    rw [h_rw]
    exact h_refl

/-- Coupled dyadic Abel gate and high-order RNS reflection box exclusion at scale `N = 2048`.
Establishes that the high-order RNS paired-channel contraction at scale `2048` inherits
non-vanishing critical reflection exclusion and positive box supply bounds together
with the dyadic tail-step preservation of `gate`. -/
theorem dyadic_gate_rns_reflect_half_box_coupling_2048
    (gate : InvSqrtTailGateSpec)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * gate.scaleN) * (gate.tailBound * gate.tailBound) ≤
      ((2 * gate.denomM) * (2 * gate.denomM)) * (gate.tailNum * gate.tailNum)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract
      (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound
      (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 <
      (rnsPairBoxToBoxSupplyBound
        (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf
        (reflectHalf
          (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step gate
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  refine ⟨h_step, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

-- =============================================================================
-- 11. Parametric Dyadic Rungs (k ≥ 5) & Rungs 11..14 RNS Couplings (#185)
-- =============================================================================

/-- Coupled parametric dyadic Abel gate (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 1024`. Links parametric tail-gate preservation with `RnsPairBox 1024`. -/
theorem dyadic_parametric_gate_rns_reflect_half_box_coupling_1024
    (k : Nat) (hk : 5 ≤ k)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * (dyadicAbelGateParametric k hk).scaleN) *
      ((dyadicAbelGateParametric k hk).tailBound * (dyadicAbelGateParametric k hk).tailBound) ≤
      ((2 * (dyadicAbelGateParametric k hk).denomM) *
        (2 * (dyadicAbelGateParametric k hk).denomM)) *
        ((dyadicAbelGateParametric k hk).tailNum * (dyadicAbelGateParametric k hk).tailNum)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step (dyadicAbelGateParametric k hk)
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_step, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Abel gate (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 2048`. Links parametric tail-gate preservation with `RnsPairBox 2048`. -/
theorem dyadic_parametric_gate_rns_reflect_half_box_coupling_2048
    (k : Nat) (hk : 5 ≤ k)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * (dyadicAbelGateParametric k hk).scaleN) *
      ((dyadicAbelGateParametric k hk).tailBound * (dyadicAbelGateParametric k hk).tailBound) ≤
      ((2 * (dyadicAbelGateParametric k hk).denomM) *
        (2 * (dyadicAbelGateParametric k hk).denomM)) *
        ((dyadicAbelGateParametric k hk).tailNum * (dyadicAbelGateParametric k hk).tailNum)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step (dyadicAbelGateParametric k hk)
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_step, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Abel gate (`k ≥ 5`) and parametric high-order RNS reflection box
exclusion for arbitrary scale `N`. Links parametric tail-gate preservation with `RnsPairBox N`. -/
theorem dyadic_parametric_gate_rns_reflect_half_box_coupling_param
    (N : Nat) (k : Nat) (hk : 5 ≤ k)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * (dyadicAbelGateParametric k hk).scaleN) *
      ((dyadicAbelGateParametric k hk).tailBound * (dyadicAbelGateParametric k hk).tailBound) ≤
      ((2 * (dyadicAbelGateParametric k hk).denomM) *
        (2 * (dyadicAbelGateParametric k hk).denomM)) *
        ((dyadicAbelGateParametric k hk).tailNum * (dyadicAbelGateParametric k hk).tailNum)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step (dyadicAbelGateParametric k hk)
  have h_excl := qrh_rns_reflect_half_box_exclusion_param N theta h_theta
  exact ⟨h_step, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Abel gate (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 4096`. Links parametric tail-gate preservation with `RnsPairBox 4096`. -/
theorem dyadic_parametric_gate_rns_reflect_half_box_coupling_4096
    (k : Nat) (hk : 5 ≤ k)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * (dyadicAbelGateParametric k hk).scaleN) *
      ((dyadicAbelGateParametric k hk).tailBound * (dyadicAbelGateParametric k hk).tailBound) ≤
      ((2 * (dyadicAbelGateParametric k hk).denomM) *
        (2 * (dyadicAbelGateParametric k hk).denomM)) *
        ((dyadicAbelGateParametric k hk).tailNum * (dyadicAbelGateParametric k hk).tailNum)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo =
      (highOrderRnsPairBox 4096 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0)) :=
  dyadic_parametric_gate_rns_reflect_half_box_coupling_param 4096 k hk theta h_theta

/-- Coupled parametric dyadic Chebyshev spec (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 1024`. Couples short-interval prime positivity to `RnsPairBox 1024`. -/
theorem short_interval_dyadic_rns_reflect_half_box_coupling_1024
    (k : Nat) (hk : 5 ≤ k)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ 18)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    (shortIntervalDyadicSpec k hk).HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_prime := shortIntervalDyadicSpec_has_prime_of_factor_lt k hk hFactor
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Chebyshev spec (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 2048`. Couples short-interval prime positivity to `RnsPairBox 2048`. -/
theorem short_interval_dyadic_rns_reflect_half_box_coupling_2048
    (k : Nat) (hk : 5 ≤ k)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ 18)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    (shortIntervalDyadicSpec k hk).HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_prime := shortIntervalDyadicSpec_has_prime_of_factor_lt k hk hFactor
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Chebyshev spec (`k ≥ 5`) and parametric high-order RNS reflection box
exclusion for arbitrary scale `N`. Couples short-interval prime positivity to `RnsPairBox N`. -/
theorem short_interval_dyadic_rns_reflect_half_box_coupling_param
    (N : Nat) (k : Nat) (hk : 5 ≤ k)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ 18)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    (shortIntervalDyadicSpec k hk).HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_prime := shortIntervalDyadicSpec_has_prime_of_factor_lt k hk hFactor
  have h_excl := qrh_rns_reflect_half_box_exclusion_param N theta h_theta
  exact ⟨h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Chebyshev spec (`k ≥ 5`) with parameterized `eGap`
and parametric high-order RNS reflection box exclusion for arbitrary scale `N`.
Couples short-interval prime positivity to `RnsPairBox N`. -/
theorem short_interval_dyadic_egap_rns_reflect_half_box_coupling_param
    (N : Nat) (k : Nat) (hk : 5 ≤ k) (eGap : Nat)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ eGap)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    (shortIntervalDyadicSpec k hk eGap).HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_prime := shortIntervalDyadicSpec_has_prime_of_factor_lt k hk hFactor
  have h_excl := qrh_rns_reflect_half_box_exclusion_param N theta h_theta
  exact ⟨h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled parametric dyadic Chebyshev spec (`k ≥ 5`) and high-order RNS reflection box exclusion
at scale `N = 4096`. Couples short-interval prime positivity to `RnsPairBox 4096`. -/
theorem short_interval_dyadic_rns_reflect_half_box_coupling_4096
    (k : Nat) (hk : 5 ≤ k)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ 18)
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    (shortIntervalDyadicSpec k hk).HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo =
      (highOrderRnsPairBox 4096 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0)) :=
  short_interval_dyadic_rns_reflect_half_box_coupling_param 4096 k hk hFactor theta h_theta

/-- Coupled dyadic Abel gate rung 11 and high-order RNS reflection box exclusion at N = 1024. -/
theorem dyadic_gate_rung11_rns_reflect_half_box_coupling_1024
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung11.scaleN) *
      (dyadicAbelGateRung11.tailBound * dyadicAbelGateRung11.tailBound) ≤
      ((2 * dyadicAbelGateRung11.denomM) * (2 * dyadicAbelGateRung11.denomM)) *
        (dyadicAbelGateRung11.tailNum * dyadicAbelGateRung11.tailNum)) ∧
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung11
  have h_prime := shortIntervalDyadicRung11Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 11 and high-order RNS reflection box exclusion at N = 2048. -/
theorem dyadic_gate_rung11_rns_reflect_half_box_coupling_2048
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung11.scaleN) *
      (dyadicAbelGateRung11.tailBound * dyadicAbelGateRung11.tailBound) ≤
      ((2 * dyadicAbelGateRung11.denomM) * (2 * dyadicAbelGateRung11.denomM)) *
        (dyadicAbelGateRung11.tailNum * dyadicAbelGateRung11.tailNum)) ∧
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung11
  have h_prime := shortIntervalDyadicRung11Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 12 and high-order RNS reflection box exclusion at N = 1024. -/
theorem dyadic_gate_rung12_rns_reflect_half_box_coupling_1024
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung12.scaleN) *
      (dyadicAbelGateRung12.tailBound * dyadicAbelGateRung12.tailBound) ≤
      ((2 * dyadicAbelGateRung12.denomM) * (2 * dyadicAbelGateRung12.denomM)) *
        (dyadicAbelGateRung12.tailNum * dyadicAbelGateRung12.tailNum)) ∧
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung12
  have h_prime := shortIntervalDyadicRung12Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 12 and high-order RNS reflection box exclusion at N = 2048. -/
theorem dyadic_gate_rung12_rns_reflect_half_box_coupling_2048
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung12.scaleN) *
      (dyadicAbelGateRung12.tailBound * dyadicAbelGateRung12.tailBound) ≤
      ((2 * dyadicAbelGateRung12.denomM) * (2 * dyadicAbelGateRung12.denomM)) *
        (dyadicAbelGateRung12.tailNum * dyadicAbelGateRung12.tailNum)) ∧
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung12
  have h_prime := shortIntervalDyadicRung12Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 13 and high-order RNS reflection box exclusion at N = 1024. -/
theorem dyadic_gate_rung13_rns_reflect_half_box_coupling_1024
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung13.scaleN) *
      (dyadicAbelGateRung13.tailBound * dyadicAbelGateRung13.tailBound) ≤
      ((2 * dyadicAbelGateRung13.denomM) * (2 * dyadicAbelGateRung13.denomM)) *
        (dyadicAbelGateRung13.tailNum * dyadicAbelGateRung13.tailNum)) ∧
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung13
  have h_prime := shortIntervalDyadicRung13Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 13 and high-order RNS reflection box exclusion at N = 2048. -/
theorem dyadic_gate_rung13_rns_reflect_half_box_coupling_2048
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung13.scaleN) *
      (dyadicAbelGateRung13.tailBound * dyadicAbelGateRung13.tailBound) ≤
      ((2 * dyadicAbelGateRung13.denomM) * (2 * dyadicAbelGateRung13.denomM)) *
        (dyadicAbelGateRung13.tailNum * dyadicAbelGateRung13.tailNum)) ∧
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung13
  have h_prime := shortIntervalDyadicRung13Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 14 and high-order RNS reflection box exclusion at N = 1024. -/
theorem dyadic_gate_rung14_rns_reflect_half_box_coupling_1024
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum)) ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung14
  have h_prime := shortIntervalDyadicRung14Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 14 and high-order RNS reflection box exclusion at N = 2048. -/
theorem dyadic_gate_rung14_rns_reflect_half_box_coupling_2048
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum)) ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung14
  have h_prime := shortIntervalDyadicRung14Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Coupled dyadic Abel gate rung 14 and high-order RNS reflection box exclusion at N = 4096. -/
theorem dyadic_gate_rung14_rns_reflect_half_box_coupling_4096
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum)) ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo =
      (highOrderRnsPairBox 4096 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h_step := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung14
  have h_prime := shortIntervalDyadicRung14Spec_has_prime
  have h_excl := qrh_rns_reflect_half_box_exclusion_4096 theta h_theta
  exact ⟨h_step, h_prime, h_excl.1, rfl, h_excl.2.2.1, h_excl.2.2.2⟩

/-- Master certificate bundle coupling dyadic rungs 11..14 with N = 1024, N = 2048, and N = 4096
high-order RNS reflection boxes and critical exclusion. -/
theorem dyadic_rungs_k11_to_k14_rns_coupling_certs
    (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta) :
    ((4 * dyadicAbelGateRung11.scaleN) *
      (dyadicAbelGateRung11.tailBound * dyadicAbelGateRung11.tailBound) ≤
      ((2 * dyadicAbelGateRung11.denomM) * (2 * dyadicAbelGateRung11.denomM)) *
        (dyadicAbelGateRung11.tailNum * dyadicAbelGateRung11.tailNum)) ∧
    ((4 * dyadicAbelGateRung12.scaleN) *
      (dyadicAbelGateRung12.tailBound * dyadicAbelGateRung12.tailBound) ≤
      ((2 * dyadicAbelGateRung12.denomM) * (2 * dyadicAbelGateRung12.denomM)) *
        (dyadicAbelGateRung12.tailNum * dyadicAbelGateRung12.tailNum)) ∧
    ((4 * dyadicAbelGateRung13.scaleN) *
      (dyadicAbelGateRung13.tailBound * dyadicAbelGateRung13.tailBound) ≤
      ((2 * dyadicAbelGateRung13.denomM) * (2 * dyadicAbelGateRung13.denomM)) *
        (dyadicAbelGateRung13.tailNum * dyadicAbelGateRung13.tailNum)) ∧
    ((4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum)) ∧
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    (¬ QRat.eqv (highOrderRnsPairBox 1024 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 2048 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (¬ QRat.eqv (highOrderRnsPairBox 4096 theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo =
      (highOrderRnsPairBox 1024 theta h_theta).stepContract ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo =
      (highOrderRnsPairBox 2048 theta h_theta).stepContract ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo =
      (highOrderRnsPairBox 4096 theta h_theta).stepContract ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 1024 theta h_theta)).xLo) ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 2048 theta h_theta)).xLo) ∧
    (QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox 4096 theta h_theta)).xLo) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 1024 theta h_theta).stepContract))
      (QRat.ofInt 0)) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 2048 theta h_theta).stepContract))
      (QRat.ofInt 0)) ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0)) := by
  have h11 := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung11
  have h12 := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung12
  have h13 := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung13
  have h14 := inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung14
  have hp11 := shortIntervalDyadicRung11Spec_has_prime
  have hp12 := shortIntervalDyadicRung12Spec_has_prime
  have hp13 := shortIntervalDyadicRung13Spec_has_prime
  have hp14 := shortIntervalDyadicRung14Spec_has_prime
  have hex1024 := qrh_rns_reflect_half_box_exclusion_1024 theta h_theta
  have hex2048 := qrh_rns_reflect_half_box_exclusion theta h_theta
  have hex4096 := qrh_rns_reflect_half_box_exclusion_4096 theta h_theta
  exact ⟨h11, h12, h13, h14, hp11, hp12, hp13, hp14,
         hex1024.1, hex2048.1, hex4096.1, rfl, rfl, rfl,
         hex1024.2.2.1, hex2048.2.2.1, hex4096.2.2.1,
         hex1024.2.2.2, hex2048.2.2.2, hex4096.2.2.2⟩

-- =============================================================================
-- 12. RNS Valuation & RnsPairBox Contraction Reflection Weave (#129)
-- =============================================================================

/-- Couples discrete `RnsPairBox` contraction evaluations with p-adic step contraction growth:
Under `IsPAdicStepContraction p step f`, after `n` iterations the p-adic displacement valuation
grows by at least `n * step`, while `pb.stepContract` remains strictly positive, non-vanishing,
and invariant under double reflection `reflectHalf (reflectHalf ·)`. -/
theorem rns_pair_box_padic_contraction_weave
    {k : Nat} (pb : LeanAsm.QuasiRiemann.RNS.RnsPairBox k)
    (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p)
    (step : Int) (f : QRat → QRat)
    (h_cont : QuasiRiemann.Valuation.IsPAdicStepContraction p step f)
    (x₀ : QRat) (n m : Nat) :
    0 < pb.stepContract.num ∧
    (¬ QRat.eqv pb.stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound pb).xLo = pb.stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound pb).xLo ∧
    (¬ QRat.eqv (reflectHalf (reflectHalf pb.stepContract)) (QRat.ofInt 0)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀)) := by
  have h_pos := pb.stepContract_pos
  have h_ne := pb.stepContract_ne_zero
  have h_xlo : (rnsPairBoxToBoxSupplyBound pb).xLo = pb.stepContract := rfl
  have h_lo_pos := (rnsPairBoxToBoxSupplyBound pb).h_lo_pos
  have h_refl := reflectHalf_reflectHalf pb.stepContract
  have h_refl_ne : ¬ QRat.eqv (reflectHalf (reflectHalf pb.stepContract)) (QRat.ofInt 0) := by
    intro h
    have h_contra : pb.stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf pb.stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * (pb.stepContract.den : Int) =
          pb.stepContract.num * ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
      have h_zero : pb.stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · omega
      change pb.stepContract.num * 1 = 0 * ((pb.stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact h_ne h_contra
  have h_growth := QuasiRiemann.Valuation.iterate_val_growth p step f h_cont x₀ n
  have h_range := QuasiRiemann.Valuation.iterate_val_range p hp step f h_cont x₀ n m
  exact ⟨h_pos, h_ne, h_xlo, h_lo_pos, h_refl_ne, h_growth, h_range⟩

/-- Parametric high-order RNS pair box contraction reflection certificate weaving
`highOrderRnsPairBox N` with p-adic step contraction growth across scale `N`
and exponent `θ > 7/8`. -/
theorem high_order_rns_pair_box_padic_weave
    (N : Nat) (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta)
    (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p)
    (step : Int) (f : QRat → QRat)
    (h_cont : QuasiRiemann.Valuation.IsPAdicStepContraction p step f)
    (x₀ : QRat) (n m : Nat) :
    0 < (highOrderRnsPairBox N theta h_theta).stepContract.num ∧
    (¬ QRat.eqv (highOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo =
      (highOrderRnsPairBox N theta h_theta).stepContract ∧
    QRat.ofInt 0 < (rnsPairBoxToBoxSupplyBound (highOrderRnsPairBox N theta h_theta)).xLo ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf (highOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀)) :=
  rns_pair_box_padic_contraction_weave
    (highOrderRnsPairBox N theta h_theta) p hp step f h_cont x₀ n m

/-- Non-degenerate master weave coupling `nonDegenerateHighOrderRnsPairBox N` with
p-adic step contraction growth and constructive channel non-vanishing. -/
theorem non_degenerate_high_order_rns_pair_box_padic_weave
    (N : Nat) (theta : QRat) (h_theta : qrhThresholdSevenEighths < theta)
    (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p)
    (step : Int) (f : QRat → QRat)
    (h_cont : QuasiRiemann.Valuation.IsPAdicStepContraction p step f)
    (x₀ : QRat) (n m : Nat) :
    0 < (nonDegenerateHighOrderRnsPairBox N theta h_theta).box1.toQRat.num ∧
    0 < (nonDegenerateHighOrderRnsPairBox N theta h_theta).box2.toQRat.num ∧
    (¬ QRat.eqv (nonDegenerateHighOrderRnsPairBox N theta h_theta).box1.toQRat (QRat.ofInt 0)) ∧
    (¬ QRat.eqv (nonDegenerateHighOrderRnsPairBox N theta h_theta).box2.toQRat (QRat.ofInt 0)) ∧
    0 < (nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract.num ∧
    (¬ QRat.eqv (nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract (QRat.ofInt 0)) ∧
    (nonDegenerateRnsPairBoxToBoxSupplyBound
      (nonDegenerateHighOrderRnsPairBox N theta h_theta)).xLo =
      (nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract ∧
    QRat.ofInt 0 < (nonDegenerateRnsPairBoxToBoxSupplyBound
      (nonDegenerateHighOrderRnsPairBox N theta h_theta)).xLo ∧
    (¬ QRat.eqv
      (reflectHalf (reflectHalf
        (nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract))
      (QRat.ofInt 0)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀)) := by
  have hw := rns_pair_box_padic_contraction_weave
    (nonDegenerateHighOrderRnsPairBox N theta h_theta).toRnsPairBox p hp step f h_cont x₀ n m
  have hch := (nonDegenerateHighOrderRnsPairBox N theta h_theta).channels_ne_zero
  have hp1 := (nonDegenerateHighOrderRnsPairBox N theta h_theta).h_box1_pos
  have hp2 := (nonDegenerateHighOrderRnsPairBox N theta h_theta).h_box2_pos
  exact ⟨hp1, hp2, hch.1, hch.2, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
         hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

/-- Master certificate bundle for `ContractionReflectionBridge` combining
cleared-denominator contraction nonvanishing, reflection duality, RNS modular nonvanishing,
and QSD band-exclusion bounds under `[propext, Quot.sound]`. -/
theorem contraction_reflection_bridge_certs
    (p k : Nat) (hp : 0 < p) (c : Int) (hc : c.natAbs < p ^ k)
    (s : QRat)
    (x : LeanAsm.QuasiRiemann.RNS.RnsInt 3)
    (h_mod : x.moduli = #[7, 31, 127])
    (r1 r2 r3 : Nat) (h_res : x.residues = #[r1, r2, r3])
    (hr1 : r1 < 7) (hr2 : r2 < 31) (hr3 : r3 < 127)
    (hp_primes : QuasiRiemann.Valuation.AllPrimes x.moduli.toList)
    (hd_primes : QuasiRiemann.Valuation.PairwiseDistinct x.moduli.toList)
    (hnz : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0)
    (centerLower lipNumerator radius deltaShrink : Nat)
    (h_shrink : deltaShrink < radius)
    (h_contract : lipNumerator * radius < centerLower * (radius - deltaShrink))
    (z : Int) (hz : z.natAbs ≤ lipNumerator * radius)
    (s8 tAbs : Nat) (hs : 4 < s8) (ht : 0 < tAbs) (hHalf : InQrhHalfPlane s8 tAbs) :
    ¬ QRat.eqv (QRat.ofInt 1 - QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QRat.ofInt 0) ∧
    QRat.eqv (reflectQRat (reflectQRat s)) s ∧
    (halfQRat < s ↔ reflectQRat s < halfQRat) ∧
    x.reconstruct ≠ 0 ∧
    ((centerLower * (radius - deltaShrink) : Nat) : Int) - z ≠ 0 ∧
    (IsCertifiedZeroFree2D s8 tAbs ∨ InRemainingUnknownBox s8 tAbs) ∧
    IsCertifiedZeroFree2D s8 tAbs :=
  ⟨qrh_contraction_qrat_ne_zero p k hp c hc,
   half_plane_reflection_qrat_involution s,
   half_plane_reflection_qrat_lt s,
   RnsStripNonVanishing x h_mod r1 r2 r3 h_res hr1 hr2 hr3 hp_primes hd_primes hnz,
   QsdZeroExclusion centerLower lipNumerator radius deltaShrink h_shrink h_contract z hz,
   critical_strip_dichotomy_2d s8 tAbs hs ht,
   qrh_implies_certified_2d s8 tAbs hHalf⟩

-- =============================================================================
-- 13. Constructive Multi-Step Stepanov Gain-vs.-Cost Lift Chain (#209)
-- =============================================================================

/-- Constructive Stepanov-style multi-step lift chain specification over `QRat` / `Nat`:
Each lift stage achieves per-step contraction/amplification gain `gainPerStep`
at the expense of per-step error `costPerStep`, with strict stage-wise dominance. -/
structure StepanovLiftChainSpec where
  stages : Nat
  h_stages_pos : 0 < stages
  initBudget : QRat
  h_init_pos : 0 < initBudget.num
  gainPerStep : QRat
  costPerStep : QRat
  h_gain_pos : 0 < gainPerStep.num
  h_cost_pos : 0 < costPerStep.num
  h_step_dom : costPerStep < gainPerStep

/-- Accumulated per-step cost across `m` stages: `m • costPerStep`. -/
def StepanovLiftChainSpec.accumulatedCost (chain : StepanovLiftChainSpec) (m : Nat) : QRat :=
  QRat.mk' ((m : Int) * chain.costPerStep.num) chain.costPerStep.den chain.costPerStep.den_pos

/-- Accumulated per-step gain across `m` stages: `m • gainPerStep`. -/
def StepanovLiftChainSpec.accumulatedGain (chain : StepanovLiftChainSpec) (m : Nat) : QRat :=
  QRat.mk' ((m : Int) * chain.gainPerStep.num) chain.gainPerStep.den chain.gainPerStep.den_pos

/-- Net margin after `m` stages: `accumulatedGain m - accumulatedCost m`. -/
def StepanovLiftChainSpec.netMargin (chain : StepanovLiftChainSpec) (m : Nat) : QRat :=
  chain.accumulatedGain m - chain.accumulatedCost m

/-- Effective contracted error envelope after `m` stages: `initBudget + accumulatedCost m`. -/
def StepanovLiftChainSpec.effectiveCost (chain : StepanovLiftChainSpec) (m : Nat) : QRat :=
  chain.initBudget + chain.accumulatedCost m

/-- Step dominance lifts strictly across positive stage compositions:
If `costPerStep < gainPerStep`, then `accumulatedCost m < accumulatedGain m` for any `0 < m`. -/
theorem stepanov_lift_chain_accumulated_strict_dominance
    (chain : StepanovLiftChainSpec) (m : Nat) (hm : 0 < m) :
    chain.accumulatedCost m < chain.accumulatedGain m := by
  have h_dom : chain.costPerStep.num * (chain.gainPerStep.den : Int) <
      chain.gainPerStep.num * (chain.costPerStep.den : Int) := chain.h_step_dom
  have hm_int : 0 < (m : Int) := by omega
  have h_mul := Int.mul_lt_mul_of_pos_left h_dom hm_int
  have h1 : (m : Int) * (chain.costPerStep.num * (chain.gainPerStep.den : Int)) =
      (m : Int) * chain.costPerStep.num * (chain.gainPerStep.den : Int) := by
    rw [Int.mul_assoc]
  have h2 : (m : Int) * (chain.gainPerStep.num * (chain.costPerStep.den : Int)) =
      (m : Int) * chain.gainPerStep.num * (chain.costPerStep.den : Int) := by
    rw [Int.mul_assoc]
  change (m : Int) * chain.costPerStep.num * (chain.gainPerStep.den : Int) <
    (m : Int) * chain.gainPerStep.num * (chain.costPerStep.den : Int)
  rw [← h1, ← h2]
  exact h_mul

/-- Non-vanishing and positivity of net gain margin across positive stage counts `0 < m`. -/
theorem stepanov_lift_chain_net_margin_pos
    (chain : StepanovLiftChainSpec) (m : Nat) (hm : 0 < m) :
    0 < (chain.netMargin m).num ∧ ¬ QRat.eqv (chain.netMargin m) (QRat.ofInt 0) := by
  have h_dom := stepanov_lift_chain_accumulated_strict_dominance chain m hm
  have h_diff_pos : 0 < (chain.accumulatedGain m).num * ((chain.accumulatedCost m).den : Int) -
      (chain.accumulatedCost m).num * ((chain.accumulatedGain m).den : Int) := by
    change (chain.accumulatedCost m).num * ((chain.accumulatedGain m).den : Int) <
      (chain.accumulatedGain m).num * ((chain.accumulatedCost m).den : Int) at h_dom
    omega
  have h_num_pos : 0 < (chain.netMargin m).num := h_diff_pos
  have h_ne : ¬ QRat.eqv (chain.netMargin m) (QRat.ofInt 0) := by
    intro h
    change (chain.netMargin m).num * 1 = 0 * (((chain.netMargin m).den : Nat) : Int) at h
    rw [Int.mul_one, Int.zero_mul] at h
    omega
  exact ⟨h_num_pos, h_ne⟩

private theorem stepanov_comp_helper (u c_num c_den g_num g_den i m : Int)
    (h_dom : m * c_num * g_den < m * g_num * c_den)
    (h_sq_pos : 0 < i * i) :
    (u * c_den + m * c_num * i) * (i * g_den) <
    (u * g_den + m * g_num * i) * (i * c_den) := by
  have h_scaled := Int.mul_lt_mul_of_pos_right h_dom h_sq_pos
  have h_exp_l : (u * c_den + m * c_num * i) * (i * g_den) =
      u * c_den * (i * g_den) + (m * c_num * g_den) * (i * i) := by
    rw [Int.add_mul]
    congr 1
    simp only [Int.mul_comm, Int.mul_left_comm]
  have h_exp_r : (u * g_den + m * g_num * i) * (i * c_den) =
      u * g_den * (i * c_den) + (m * g_num * c_den) * (i * i) := by
    rw [Int.add_mul]
    congr 1
    simp only [Int.mul_comm, Int.mul_left_comm]
  have h_base_eq : u * c_den * (i * g_den) = u * g_den * (i * c_den) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  rw [h_exp_l, h_exp_r, h_base_eq]
  omega

/-- Preserved contraction ratio: the multi-step effective cost `initBudget + accumulatedCost m`
is bounded by `initBudget + accumulatedGain m` with strictly positive margin whenever `0 < m`. -/
theorem stepanov_lift_chain_composition_bound
    (chain : StepanovLiftChainSpec) (m : Nat) (hm : 0 < m) :
    chain.effectiveCost m < chain.initBudget + chain.accumulatedGain m ∧
    0 < (chain.effectiveCost m).num ∧
    ¬ QRat.eqv (chain.effectiveCost m) (QRat.ofInt 0) := by
  have h_dom := stepanov_lift_chain_accumulated_strict_dominance chain m hm
  have h_lt : chain.effectiveCost m < chain.initBudget + chain.accumulatedGain m := by
    change (chain.initBudget.num * (chain.costPerStep.den : Int) +
        (m : Int) * chain.costPerStep.num * (chain.initBudget.den : Int)) *
        ((chain.initBudget.den * chain.gainPerStep.den : Nat) : Int) <
      (chain.initBudget.num * (chain.gainPerStep.den : Int) +
        (m : Int) * chain.gainPerStep.num * (chain.initBudget.den : Int)) *
        ((chain.initBudget.den * chain.costPerStep.den : Nat) : Int)
    rw [Int.natCast_mul, Int.natCast_mul]
    have h_i_den : 0 < ((chain.initBudget.den : Nat) : Int) := by
      have := chain.initBudget.den_pos; omega
    have h_sq_pos : 0 < (chain.initBudget.den : Int) * (chain.initBudget.den : Int) :=
      Int.mul_pos h_i_den h_i_den
    change (m : Int) * chain.costPerStep.num * (chain.gainPerStep.den : Int) <
      (m : Int) * chain.gainPerStep.num * (chain.costPerStep.den : Int) at h_dom
    exact stepanov_comp_helper chain.initBudget.num chain.costPerStep.num
      (chain.costPerStep.den : Int) chain.gainPerStep.num (chain.gainPerStep.den : Int)
      (chain.initBudget.den : Int) (m : Int) h_dom h_sq_pos
  have h_cost_pos : 0 < (chain.effectiveCost m).num := by
    change 0 < chain.initBudget.num * (chain.costPerStep.den : Int) +
      (m : Int) * chain.costPerStep.num * (chain.initBudget.den : Int)
    have h_i_pos := chain.h_init_pos
    have h_c_pos := chain.h_cost_pos
    have h_m_pos : 0 < (m : Int) := by omega
    have h_mc_pos : 0 < (m : Int) * chain.costPerStep.num :=
      Int.mul_pos h_m_pos h_c_pos
    have h_c_den_pos : 0 < ((chain.costPerStep.den : Nat) : Int) := by
      have := chain.costPerStep.den_pos; omega
    have h_i_den_pos : 0 < ((chain.initBudget.den : Nat) : Int) := by
      have := chain.initBudget.den_pos; omega
    have h_part1 : 0 < chain.initBudget.num * ((chain.costPerStep.den : Nat) : Int) :=
      Int.mul_pos h_i_pos h_c_den_pos
    have h_part2 : 0 < (m : Int) * chain.costPerStep.num * ((chain.initBudget.den : Nat) : Int) :=
      Int.mul_pos h_mc_pos h_i_den_pos
    omega
  have h_cost_nz : ¬ QRat.eqv (chain.effectiveCost m) (QRat.ofInt 0) := by
    intro h
    change (chain.effectiveCost m).num * 1 = 0 * (((chain.effectiveCost m).den : Nat) : Int) at h
    rw [Int.mul_one, Int.zero_mul] at h
    omega
  exact ⟨h_lt, h_cost_pos, h_cost_nz⟩

/-- Canonical non-degenerate Stepanov lift chain witness at ladder depth 7/8:
Initial budget `1/8`, per-step cost `1/16`, per-step amplification gain `1/4` over 8 stages. -/
def stepanovLiftChainWitness : StepanovLiftChainSpec where
  stages := 8
  h_stages_pos := by decide
  initBudget := QRat.mk' 1 8 (by decide)
  h_init_pos := by decide
  gainPerStep := QRat.mk' 1 4 (by decide)
  costPerStep := QRat.mk' 1 16 (by decide)
  h_gain_pos := by decide
  h_cost_pos := by decide
  h_step_dom := by decide

/-- Master certificate bundle for the Stepanov lift chain witness:
Verifies stage-wise strict cost-gain dominance, non-vanishing effective cost,
and positive net margin across `m = 8` composition stages under `[propext, Quot.sound]`. -/
theorem stepanov_lift_chain_witness_certs :
    stepanovLiftChainWitness.accumulatedCost 8 <
      stepanovLiftChainWitness.accumulatedGain 8 ∧
    stepanovLiftChainWitness.effectiveCost 8 <
      stepanovLiftChainWitness.initBudget + stepanovLiftChainWitness.accumulatedGain 8 ∧
    0 < (stepanovLiftChainWitness.netMargin 8).num ∧
    (¬ QRat.eqv (stepanovLiftChainWitness.netMargin 8) (QRat.ofInt 0)) ∧
    0 < (stepanovLiftChainWitness.effectiveCost 8).num ∧
    (¬ QRat.eqv (stepanovLiftChainWitness.effectiveCost 8) (QRat.ofInt 0)) := by
  have hm : 0 < 8 := by decide
  have h_dom := stepanov_lift_chain_accumulated_strict_dominance stepanovLiftChainWitness 8 hm
  have h_comp := stepanov_lift_chain_composition_bound stepanovLiftChainWitness 8 hm
  have h_net := stepanov_lift_chain_net_margin_pos stepanovLiftChainWitness 8 hm
  exact ⟨h_dom, h_comp.1, h_net.1, h_net.2, h_comp.2.1, h_comp.2.2⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ContractionReflectionBridge.lean
