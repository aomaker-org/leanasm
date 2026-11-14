-- Path: leanasm/src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean
-- Constructive rational zero-density-to-QRH descent bridge linking A(σ), μ(σ),
-- QRH thresholds θ ∈ {3/4, 7/8, 11/12, 47/48}, Chebyshev gaps, and AsymptoticZfr.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann
import LeanAsm.QuasiRiemann.AsymptoticZfr

namespace QuasiRiemann

-- =============================================================================
-- 1. Constructive Rational Models: ZeroDensitySpec & SubconvexitySpec
-- =============================================================================

/-- Constructive rational zero-density slope model `N(σ, T) ≪ T^(A(σ)(1 - σ) + ε)`
backed by `QRat` arithmetic with strictly positive slope `A = p/q > 0`. -/
structure ZeroDensitySpec where
  name : String
  slope : QRat
  slope_pos : (0 : Int) < slope.num

/-- Constructive critical-line subconvexity model `μ(1/2) = p/q ≥ 0` over `QRat`
with Phragmén–Lindelöf linear interpolation `μ(σ) = 2 · μ(1/2) · (1 - σ)`. -/
structure SubconvexitySpec where
  name : String
  muHalf : QRat
  muHalf_nonneg : (0 : Int) ≤ muHalf.num

/-- Zero-density growth exponent `A(σ)(1 - σ)` at `sigma` via `QRat`. -/
def ZeroDensitySpec.exponent (spec : ZeroDensitySpec) (sigma : QRat) : QRat :=
  zeroDensityExponentAt spec.slope sigma

/-- Cleared-denominator sublinear zero-density condition `A(σ)(1 - σ) < 1`:
`slope.num * (sigma.den - sigma.num) < slope.den * sigma.den`. -/
def ZeroDensitySpec.sublinearAt (spec : ZeroDensitySpec) (sigma : QRat) : Prop :=
  spec.slope.num * ((sigma.den : Int) - sigma.num) <
    (spec.slope.den : Int) * (sigma.den : Int)

instance (spec : ZeroDensitySpec) (sigma : QRat) : Decidable (spec.sublinearAt sigma) :=
  inferInstanceAs (Decidable
    (spec.slope.num * ((sigma.den : Int) - sigma.num) <
      (spec.slope.den : Int) * (sigma.den : Int)))

/-- Linear Phragmén–Lindelöf convexity interpolation `μ(σ) = 2 · μ(1/2) · (1 - σ)`. -/
def SubconvexitySpec.muAt (s : SubconvexitySpec) (sigma : QRat) : QRat :=
  QRat.ofInt 2 * s.muHalf * (QRat.ofInt 1 - sigma)

/-- Chebyshev prime-counting remainder saving exponent `1 - θ` in
`ψ(x) - x = O(x^θ log² x) = O(x^(1 - gap) log² x)`. -/
def chebyshevGap (θ : QRat) : QRat :=
  QRat.ofInt 1 - θ

-- =============================================================================
-- 2. Cleared-Denominator Algebraic & Monotonicity Lemmas
-- =============================================================================

/-- Cleared-denominator equivalence: `spec.sublinearAt σ` holds iff
`spec.exponent σ < 1` in `QRat`. -/
theorem sublinearAt_iff_exponent_lt_one (spec : ZeroDensitySpec) (sigma : QRat) :
    spec.sublinearAt sigma ↔ spec.exponent sigma < QRat.ofInt 1 := by
  dsimp [ZeroDensitySpec.sublinearAt, ZeroDensitySpec.exponent, zeroDensityExponentAt]
  change spec.slope.num * ((sigma.den : Int) - sigma.num) <
      (spec.slope.den : Int) * (sigma.den : Int) ↔
    (spec.slope.num * (1 * (sigma.den : Int) - sigma.num * 1)) * 1 <
      1 * ((spec.slope.den * (1 * sigma.den) : Nat) : Int)
  simp only [Int.one_mul, Int.mul_one, Nat.one_mul]
  rfl

/-- Increasing `σ` never increases the zero-density exponent `A · (1 - σ)`. -/
theorem exponent_mono_sigma (spec : ZeroDensitySpec) {σ₁ σ₂ : QRat} (hσ : σ₁ ≤ σ₂) :
    spec.exponent σ₂ ≤ spec.exponent σ₁ := by
  dsimp [ZeroDensitySpec.exponent, zeroDensityExponentAt]
  have hsub : QRat.ofInt 1 - σ₂ ≤ QRat.ofInt 1 - σ₁ :=
    qrat_sub_le_sub (qrat_le_refl (QRat.ofInt 1)) hσ
  have hs : QRat.ofInt 0 ≤ spec.slope :=
    (qrat_nonneg_iff spec.slope).mpr (Int.le_of_lt spec.slope_pos)
  exact qrat_mul_le_mul_of_nonneg_left hsub hs

/-- Decreasing the zero-density slope never increases `A · (1 - σ)` for `σ ≤ 1`. -/
theorem exponent_mono_slope {s₁ s₂ : ZeroDensitySpec} {σ : QRat}
    (hs : s₁.slope ≤ s₂.slope) (hσ : σ ≤ QRat.ofInt 1) :
    s₁.exponent σ ≤ s₂.exponent σ := by
  dsimp [ZeroDensitySpec.exponent, zeroDensityExponentAt]
  have hnonneg : QRat.ofInt 0 ≤ QRat.ofInt 1 - σ := by
    have h := qrat_sub_le_sub (qrat_le_refl (QRat.ofInt 1)) hσ
    exact qrat_le_of_eqv_left (by decide) h
  exact qrat_mul_le_mul_of_nonneg_right hs hnonneg

/-- Rightward monotonicity of sublinear zero-density: if `A(1 - σ₁) < 1` and
`σ₁ ≤ σ₂`, then `A(1 - σ₂) < 1`. -/
theorem sublinearAt_mono_right (spec : ZeroDensitySpec) {σ₁ σ₂ : QRat}
    (hsub : spec.sublinearAt σ₁) (hle : σ₁ ≤ σ₂) :
    spec.sublinearAt σ₂ := by
  rw [sublinearAt_iff_exponent_lt_one] at hsub ⊢
  exact qrat_lt_of_le_of_lt (exponent_mono_sigma spec hle) hsub

/-- Endpoint identities for `SubconvexitySpec.muAt`: `μ(1/2) = muHalf` and `μ(1) = 0`. -/
theorem muAt_endpoints (s : SubconvexitySpec) :
    QRat.eqv (s.muAt (QRat.mk' 1 2)) s.muHalf ∧
    QRat.eqv (s.muAt (QRat.ofInt 1)) (QRat.ofInt 0) := by
  dsimp [SubconvexitySpec.muAt, QRat.eqv, QRat.ofInt, QRat.mk', QRat.mul, QRat.sub]
  constructor
  · change (2 * s.muHalf.num * (1 * (2 : Nat) - 1 * 1)) * (s.muHalf.den : Int) =
      s.muHalf.num * ((1 * s.muHalf.den * (1 * 2) : Nat) : Int)
    simp only [Int.natCast_mul]
    ac_rfl
  · change 2 * s.muHalf.num * (1 * 1 - 1 * 1) * 1 =
      0 * ((1 * s.muHalf.den * (1 * 1) : Nat) : Int)
    omega

/-- Phragmén–Lindelöf interpolation `μ(σ)` decreases as `σ` moves toward `1`. -/
theorem muAt_antitone (s : SubconvexitySpec) {σ₁ σ₂ : QRat} (hσ : σ₁ ≤ σ₂) :
    s.muAt σ₂ ≤ s.muAt σ₁ := by
  dsimp [SubconvexitySpec.muAt]
  have hsub : QRat.ofInt 1 - σ₂ ≤ QRat.ofInt 1 - σ₁ :=
    qrat_sub_le_sub (qrat_le_refl (QRat.ofInt 1)) hσ
  have hm : QRat.ofInt 0 ≤ QRat.ofInt 2 * s.muHalf := by
    have hμ : QRat.ofInt 0 ≤ s.muHalf := (qrat_nonneg_iff s.muHalf).mpr s.muHalf_nonneg
    exact qrat_mul_nonneg (by decide) hμ
  exact qrat_mul_le_mul_of_nonneg_left hsub hm

/-- A QRH threshold strictly below `1` leaves a strictly positive Chebyshev remainder gap. -/
theorem chebyshevGap_pos_of_lt_one {θ : QRat} (h : θ < QRat.ofInt 1) :
    QRat.ofInt 0 < chebyshevGap θ := by
  change 0 * ((1 * θ.den : Nat) : Int) < (1 * (θ.den : Int) - θ.num * 1) * 1
  change θ.num * 1 < 1 * (θ.den : Int) at h
  omega

/-- Lowering `θ` strictly widens the Chebyshev prime-counting remainder saving `1 - θ`. -/
theorem chebyshevGap_antitone {θ₁ θ₂ : QRat} (h : θ₁ < θ₂) :
    chebyshevGap θ₂ < chebyshevGap θ₁ := by
  change (1 * (θ₂.den : Int) - θ₂.num * 1) * ((1 * θ₁.den : Nat) : Int) <
    (1 * (θ₁.den : Int) - θ₁.num * 1) * ((1 * θ₂.den : Nat) : Int)
  change θ₁.num * (θ₂.den : Int) < θ₂.num * (θ₁.den : Int) at h
  simp only [Nat.one_mul, Int.one_mul, Int.mul_one, Int.sub_mul]
  rw [Int.mul_comm (θ₁.den : Int) (θ₂.den : Int)]
  omega

-- =============================================================================
-- 3. Benchmark Zero-Density & Subconvexity Specifications
-- =============================================================================

/-- Ingham benchmark zero-density slope `A(3/4) = 8/3` giving `A(3/4)(1 - 3/4) = 2/3`. -/
def zdIngham34 : ZeroDensitySpec :=
  ⟨"Ingham-3/4", QRat.mk' 8 3, by decide⟩

/-- Classical Ingham slope `A = 3` (reusing `QuasiRiemann.zeroDensityIngham`). -/
def zdInghamClassical : ZeroDensitySpec :=
  ⟨"Ingham-3", zeroDensityIngham, by decide⟩

/-- Huxley (1972) zero-density slope `A = 12/5` (reusing `QuasiRiemann.zeroDensityHuxley`). -/
def zdHuxley : ZeroDensitySpec :=
  ⟨"Huxley", zeroDensityHuxley, by decide⟩

/-- Guth–Maynard (2024) slope `A = 30/13` (reusing `QuasiRiemann.zeroDensityGuthMaynard`). -/
def zdGuthMaynard : ZeroDensitySpec :=
  ⟨"Guth-Maynard", zeroDensityGuthMaynard, by decide⟩

/-- Density Hypothesis limiting slope `A = 2` (reusing `QuasiRiemann.zeroDensityHypothesis`). -/
def zdDensityHypothesis : ZeroDensitySpec :=
  ⟨"Density-Hypothesis", zeroDensityHypothesis, by decide⟩

/-- Classical convexity bound `μ(1/2) = 1/4`. -/
def subconvConvexity : SubconvexitySpec :=
  ⟨"Convexity", QRat.mk' 1 4, by decide⟩

/-- Weyl–Hardy–Littlewood bound `μ(1/2) = 1/6`. -/
def subconvWeyl : SubconvexitySpec :=
  ⟨"Weyl", QRat.mk' 1 6, by decide⟩

/-- Bourgain (2017) decouplings subconvexity bound `μ(1/2) = 13/84`. -/
def subconvBourgain : SubconvexitySpec :=
  ⟨"Bourgain", QRat.mk' 13 84, by decide⟩

/-- Lindelöf hypothesis critical-line target `μ(1/2) = 0`. -/
def subconvLindelof : SubconvexitySpec :=
  ⟨"Lindelof", QRat.ofInt 0, by decide⟩

/-- QRH threshold rung `θ = 3/4`. -/
def qrhThresholdThreeQuarters : QRat := QRat.mk' 3 4

/-- QRH threshold rung `θ = 7/8`. -/
def qrhThresholdSevenEighths : QRat := QRat.mk' 7 8

/-- QRH threshold rung `θ = 11/12`. -/
def qrhThresholdElevenTwelfths : QRat := QRat.mk' 11 12

/-- QRH threshold rung `θ = 47/48`. -/
def qrhThresholdFortySevenFortyEighths : QRat := QRat.mk' 47 48

-- =============================================================================
-- 4. Benchmark Certificates (Ingham 2/3, Huxley 3/5, Guth-Maynard 15/26)
-- =============================================================================

/-- Theorem (Constructive Zero-Density & Subconvexity Benchmark Certificates):
At `σ = 3/4`, verifies the exact rational products `A(3/4)(1 - 3/4)` for Ingham (`2/3`),
Huxley (`3/5`), Guth–Maynard (`15/26`), and Density Hypothesis (`1/2`), proves the strict
improvement chain `1/2 < 15/26 < 3/5 < 2/3 < 3/4` with explicit savings `3/130`, and
certifies the critical-line subconvexity exponents `μ(1/2) ∈ {0, 13/84, 1/6, 1/4}`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_zero_density_benchmark_certs :
    let σ := QRat.mk' 3 4
    QRat.eqv (zdIngham34.exponent σ) (QRat.mk' 2 3) ∧
    QRat.eqv (zdHuxley.exponent σ) (QRat.mk' 3 5) ∧
    QRat.eqv (zdGuthMaynard.exponent σ) (QRat.mk' 15 26) ∧
    QRat.eqv (zdDensityHypothesis.exponent σ) (QRat.mk' 1 2) ∧
    zdDensityHypothesis.exponent σ < zdGuthMaynard.exponent σ ∧
    zdGuthMaynard.exponent σ < zdHuxley.exponent σ ∧
    zdHuxley.exponent σ < zdIngham34.exponent σ ∧
    zdIngham34.exponent σ < zdInghamClassical.exponent σ ∧
    zdGuthMaynard.sublinearAt σ ∧
    zdHuxley.sublinearAt σ ∧
    zdIngham34.sublinearAt σ ∧
    QRat.eqv (zdHuxley.exponent σ - zdGuthMaynard.exponent σ) (QRat.mk' 3 130) ∧
    QRat.eqv (subconvLindelof.muAt (QRat.mk' 1 2)) (QRat.ofInt 0) ∧
    QRat.eqv (subconvBourgain.muAt (QRat.mk' 1 2)) (QRat.mk' 13 84) ∧
    QRat.eqv (subconvWeyl.muAt (QRat.mk' 1 2)) (QRat.mk' 1 6) ∧
    QRat.eqv (subconvConvexity.muAt (QRat.mk' 1 2)) (QRat.mk' 1 4) ∧
    subconvLindelof.muHalf < subconvBourgain.muHalf ∧
    subconvBourgain.muHalf < subconvWeyl.muHalf ∧
    subconvWeyl.muHalf < subconvConvexity.muHalf := by
  decide

-- =============================================================================
-- 5. Zero-Density-to-QRH Threshold Descent & AsymptoticZfr Compatibility
-- =============================================================================

/-- Constructive QRH threshold theorem from zero-density slopes:
1. If `spec.exponent θ ≤ 1`, then `spec.sublinearAt σ` (`A(σ)(1 - σ) < 1`) holds
   unconditionally for all `σ > θ`.
2. If `spec.sublinearAt σ` holds for every admissible `σ ∈ (θ, 1]`, then any candidate
   nontrivial zero real part `β ≤ 1` satisfying zero-density saturation `1 ≤ spec.exponent β`
   must lie at or left of `θ` (`β ≤ θ`), preserving Chebyshev saving `1 - θ ≤ 1 - β`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem zero_density_implies_qrh_threshold (spec : ZeroDensitySpec) (θ : QRat) :
    ((spec.exponent θ ≤ QRat.ofInt 1) →
      ∀ σ : QRat, θ < σ → spec.sublinearAt σ) ∧
    ((∀ σ : QRat, θ < σ → σ ≤ QRat.ofInt 1 → spec.sublinearAt σ) →
      ∀ β : QRat, β ≤ QRat.ofInt 1 → QRat.ofInt 1 ≤ spec.exponent β →
        β ≤ θ ∧ chebyshevGap θ ≤ chebyshevGap β) := by
  constructor
  · intro hθ σ hσ
    rw [sublinearAt_iff_exponent_lt_one]
    have hstrict : spec.exponent σ < spec.exponent θ := by
      dsimp [ZeroDensitySpec.exponent, zeroDensityExponentAt]
      have hsub : QRat.ofInt 1 - σ < QRat.ofInt 1 - θ := by
        change (1 * (σ.den : Int) - σ.num * 1) * ((1 * θ.den : Nat) : Int) <
          (1 * (θ.den : Int) - θ.num * 1) * ((1 * σ.den : Nat) : Int)
        change θ.num * (σ.den : Int) < σ.num * (θ.den : Int) at hσ
        simp only [Nat.one_mul, Int.one_mul, Int.mul_one, Int.sub_mul]
        rw [Int.mul_comm (σ.den : Int) (θ.den : Int)]
        omega
      change (spec.slope.num * (QRat.ofInt 1 - σ).num) *
          ((spec.slope.den * (QRat.ofInt 1 - θ).den : Nat) : Int) <
        (spec.slope.num * (QRat.ofInt 1 - θ).num) *
          ((spec.slope.den * (QRat.ofInt 1 - σ).den : Nat) : Int)
      change (QRat.ofInt 1 - σ).num * ((QRat.ofInt 1 - θ).den : Int) <
        (QRat.ofInt 1 - θ).num * ((QRat.ofInt 1 - σ).den : Int) at hsub
      simp only [Int.natCast_mul]
      have hd : (0 : Int) < (spec.slope.den : Int) := Int.natCast_pos.mpr spec.slope.den_pos
      have hs : (0 : Int) < spec.slope.num := spec.slope_pos
      calc spec.slope.num * (QRat.ofInt 1 - σ).num *
              ((spec.slope.den : Int) * ((QRat.ofInt 1 - θ).den : Int))
          = (spec.slope.num * (spec.slope.den : Int)) *
              ((QRat.ofInt 1 - σ).num * ((QRat.ofInt 1 - θ).den : Int)) := by ac_rfl
        _ < (spec.slope.num * (spec.slope.den : Int)) *
              ((QRat.ofInt 1 - θ).num * ((QRat.ofInt 1 - σ).den : Int)) :=
            Int.mul_lt_mul_of_pos_left hsub (Int.mul_pos hs hd)
        _ = spec.slope.num * (QRat.ofInt 1 - θ).num *
              ((spec.slope.den : Int) * ((QRat.ofInt 1 - σ).den : Int)) := by ac_rfl
    exact qrat_lt_of_lt_of_le hstrict hθ
  · intro hdens β hβ1 hviol
    have hnot : ¬ θ < β := by
      intro hlt
      have hsub := hdens β hlt hβ1
      rw [sublinearAt_iff_exponent_lt_one] at hsub
      have hcontra : spec.exponent β < spec.exponent β :=
        qrat_lt_of_lt_of_le hsub hviol
      exact (Int.lt_irrefl _) hcontra
    have hβθ : β ≤ θ := by
      change β.num * (θ.den : Int) ≤ θ.num * (β.den : Int)
      change ¬ θ.num * (β.den : Int) < β.num * (θ.den : Int) at hnot
      exact Int.not_lt.mp hnot
    exact ⟨hβθ, qrat_sub_le_sub (qrat_le_refl (QRat.ofInt 1)) hβθ⟩

private theorem inv168_nonneg : QRat.ofInt 0 ≤ QRat.mk' 1 168 := by decide

private theorem cDvp_eqv_inv168_mul3 :
    QRat.eqv (QRat.mk' 1 168 * QRat.ofInt 3) cDvp := by
  decide

private theorem one_sub_inv168_eqv :
    QRat.eqv (QRat.mk' 167 168) (QRat.ofInt 1 - QRat.mk' 1 168) := by
  decide

private theorem theta47_lt_167_168 :
    qrhThresholdFortySevenFortyEighths < QRat.mk' 167 168 := by
  decide

private theorem qrh_ladder_order :
    qrhThresholdThreeQuarters < qrhThresholdSevenEighths ∧
    qrhThresholdSevenEighths < qrhThresholdElevenTwelfths ∧
    qrhThresholdElevenTwelfths < qrhThresholdFortySevenFortyEighths ∧
    qrhThresholdFortySevenFortyEighths < QRat.ofInt 1 := by
  decide

private theorem qrh_ladder_gaps :
    QRat.eqv (chebyshevGap qrhThresholdThreeQuarters) (QRat.mk' 1 4) ∧
    QRat.eqv (chebyshevGap qrhThresholdSevenEighths) (QRat.mk' 1 8) ∧
    QRat.eqv (chebyshevGap qrhThresholdElevenTwelfths) (QRat.mk' 1 12) ∧
    QRat.eqv (chebyshevGap qrhThresholdFortySevenFortyEighths) (QRat.mk' 1 48) ∧
    QRat.ofInt 0 < chebyshevGap qrhThresholdFortySevenFortyEighths ∧
    chebyshevGap qrhThresholdFortySevenFortyEighths < chebyshevGap qrhThresholdElevenTwelfths ∧
    chebyshevGap qrhThresholdElevenTwelfths < chebyshevGap qrhThresholdSevenEighths ∧
    chebyshevGap qrhThresholdSevenEighths < chebyshevGap qrhThresholdThreeQuarters := by
  decide

private theorem dvpDelta_pos_local (t : Nat) : QRat.ofInt 0 < dvpDelta t := by
  rw [qrat_pos_iff]
  dsimp [dvpDelta, QRat.mk']
  decide

/-- Auxiliary lower bound: for every `t ≥ dvpThresholdT0` (`16`), the dyadic-octave
log envelope satisfies `3 ≤ octaveLnUpper36QRat t`, bounding `c_dvp / L(t) ≤ 1/168`. -/
theorem cDvp_div_octaveLnUpper36_le_inv168 (t : Nat) (ht : dvpThresholdT0 ≤ t) :
    QRat.div cDvp (octaveLnUpper36QRat t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (octaveLnUpper36_pos t).2.1)) ≤ QRat.mk' 1 168 := by
  have h16 : QRat.ofInt 3 ≤ octaveLnUpper36QRat 16 := by
    have he := ln2Upper36_envelope_certs.2
    change 3 * ((10 ^ 36 : Nat) : Int) ≤ octaveLnUpper36 16 * 1
    rw [he]
    decide
  have hL3 : QRat.ofInt 3 ≤ octaveLnUpper36QRat t :=
    qrat_le_trans h16 (octaveLnUpper36_mono 16 t ht).2
  have hmul : cDvp ≤ QRat.mk' 1 168 * octaveLnUpper36QRat t := by
    have hstep : QRat.mk' 1 168 * QRat.ofInt 3 ≤ QRat.mk' 1 168 * octaveLnUpper36QRat t :=
      qrat_mul_le_mul_of_nonneg_left hL3 inv168_nonneg
    exact qrat_le_of_eqv_left cDvp_eqv_inv168_mul3 hstep
  exact qrat_div_le_of_le_mul (octaveLnUpper36_pos t).2.1 hmul

/-- Theorem (QRH Threshold Ladder & Chebyshev Remainder Gaps with DVP Compatibility):
1. Certifies `3/4 < 7/8 < 11/12 < 47/48 < 1`.
2. Certifies exact Chebyshev remainder exponent gaps `1 - θ ∈ {1/4, 1/8, 1/12, 1/48}`
   with strict ordering `0 < 1/48 < 1/12 < 1/8 < 1/4`.
3. For every height `t ≥ dvpThresholdT0` (`16`), proves every QRH ladder threshold `θ`
   lies strictly to the left of the asymptotic de la Vallée Poussin boundary
   `1 - c_dvp / octaveLnUpper36QRat t`, matching `dvp_asymptotic_zero_free_region`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_theta_ladder_certs (t : Nat) (ht : dvpThresholdT0 ≤ t) :
    let θ₁ := qrhThresholdThreeQuarters
    let θ₂ := qrhThresholdSevenEighths
    let θ₃ := qrhThresholdElevenTwelfths
    let θ₄ := qrhThresholdFortySevenFortyEighths
    let zfr := QRat.ofInt 1 - QRat.div cDvp (octaveLnUpper36QRat t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (octaveLnUpper36_pos t).2.1))
    (θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < QRat.ofInt 1) ∧
    (QRat.eqv (chebyshevGap θ₁) (QRat.mk' 1 4) ∧
     QRat.eqv (chebyshevGap θ₂) (QRat.mk' 1 8) ∧
     QRat.eqv (chebyshevGap θ₃) (QRat.mk' 1 12) ∧
     QRat.eqv (chebyshevGap θ₄) (QRat.mk' 1 48) ∧
     QRat.ofInt 0 < chebyshevGap θ₄ ∧
     chebyshevGap θ₄ < chebyshevGap θ₃ ∧
     chebyshevGap θ₃ < chebyshevGap θ₂ ∧
     chebyshevGap θ₂ < chebyshevGap θ₁) ∧
    (θ₁ < zfr ∧ θ₂ < zfr ∧ θ₃ < zfr ∧ θ₄ < zfr) := by
  have h1 := qrh_ladder_order
  have h2 := qrh_ladder_gaps
  have hdiv := cDvp_div_octaveLnUpper36_le_inv168 t ht
  have hzfr : QRat.mk' 167 168 ≤
      QRat.ofInt 1 - QRat.div cDvp (octaveLnUpper36QRat t)
        (Int.ne_of_gt ((qrat_pos_iff _).mp (octaveLnUpper36_pos t).2.1)) :=
    qrat_le_of_eqv_left one_sub_inv168_eqv
      (qrat_sub_le_sub (qrat_le_refl (QRat.ofInt 1)) hdiv)
  have hlt4 := qrat_lt_of_lt_of_le theta47_lt_167_168 hzfr
  have hlt3 := qrat_lt_of_le_of_lt (qrat_le_of_lt h1.2.2.1) hlt4
  have hlt2 := qrat_lt_of_le_of_lt (qrat_le_of_lt h1.2.1) hlt3
  have hlt1 := qrat_lt_of_le_of_lt (qrat_le_of_lt h1.1) hlt2
  exact ⟨h1, h2, hlt1, hlt2, hlt3, hlt4⟩

/-- Combined QRH Zero-Density + DVP Asymptotic Bridge Theorem:
For any height `t ≥ dvpThresholdT0` (`16`), combining `dvp_asymptotic_zero_free_region`
and `zero_density_implies_qrh_threshold` guarantees that any zero satisfying the 3-4-1
Hadamard bounds and zero-density saturation satisfies BOTH `β ≤ θ` and the uniform
asymptotic strip bound `β ≤ 1 - c_dvp / octaveLnUpper36QRat t < 1`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem zero_density_and_dvp_combined_region (spec : ZeroDensitySpec) (θ : QRat)
    (hdens : ∀ σ : QRat, θ < σ → σ ≤ QRat.ofInt 1 → spec.sublinearAt σ)
    (t : Nat) (ht : dvpThresholdT0 ≤ t) (β S0 S1 S2 : QRat)
    (hviol : QRat.ofInt 1 ≤ spec.exponent β)
    (hgap : QRat.ofInt 0 < QRat.ofInt 1 + dvpDelta t - β)
    (hpos341 : QRat.ofInt 0 ≤ QRat.ofInt 3 * S0 + QRat.ofInt 4 * S1 + S2)
    (hS0 : S0 ≤ QRat.div (QRat.ofInt 1) (dvpDelta t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (dvpDelta_pos_local t))) + QRat.ofInt 1)
    (hS1 : S1 ≤ -(QRat.div (QRat.ofInt 1) (QRat.ofInt 1 + dvpDelta t - β)
      (Int.ne_of_gt ((qrat_pos_iff _).mp hgap))) + QRat.mk' 1 2 * octaveLnUpper36QRat t)
    (hS2 : S2 ≤ QRat.mk' 3 4 * (octaveLnUpper36QRat t + ln2Upper36QRat)) :
    β ≤ θ ∧
    β ≤ QRat.ofInt 1 - QRat.div cDvp (octaveLnUpper36QRat t)
      (Int.ne_of_gt ((qrat_pos_iff _).mp (octaveLnUpper36_pos t).2.1)) ∧
    β < QRat.ofInt 1 ∧
    chebyshevGap θ ≤ chebyshevGap β := by
  have hdvp := dvp_asymptotic_zero_free_region t ht β S0 S1 S2 hgap hpos341 hS0 hS1 hS2
  have hβ1 : β ≤ QRat.ofInt 1 := qrat_le_of_lt hdvp.2.2
  have hqrh := (zero_density_implies_qrh_threshold spec θ).2 hdens β hβ1 hviol
  exact ⟨hqrh.1, hdvp.2.1, hdvp.2.2, hqrh.2⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean