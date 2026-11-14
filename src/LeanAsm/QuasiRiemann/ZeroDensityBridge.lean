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

-- =============================================================================
-- 6. Constructive Chebyshev Remainder Envelopes Across Benchmark Scales
-- =============================================================================

/-- Conservative integer log envelope `ln(10^(12k)) < 28k` (since `ln 10 < 7/3`
gives `12 * ln 10 < 28`). -/
def chebyshevLogEnv (k : Nat) : Nat :=
  28 * k

/-- Conservative integer log-squared envelope `(ln 10^(12k))^2 ≤ (28k)^2`. -/
def chebyshevLogSqEnv (k : Nat) : Nat :=
  chebyshevLogEnv k * chebyshevLogEnv k

/-- Exact integer exponent `(12 * k * θ.num.natAbs) / θ.den` when `θ.den ∣ 12 * k`,
so `(10^(12k))^θ = 10^e` is an exact power of `10`. -/
def tenPowThetaExactExp (k : Nat) (θ : QRat) : Nat :=
  (12 * k * θ.num.natAbs) / θ.den

/-- Ceiling integer exponent `⌈(12 * k * θ.num.natAbs) / θ.den⌉` for general
positive `θ`, agreeing with `tenPowThetaExactExp` whenever `θ.den ∣ 12 * k`. -/
def tenPowThetaCeilExp (k : Nat) (θ : QRat) : Nat :=
  (12 * k * θ.num.natAbs + θ.den - 1) / θ.den

/-- Saving exponent `12 * k - e` in `x / 10^e = 10^(12k - e)`. -/
def tenPowGapExp (k : Nat) (θ : QRat) : Nat :=
  12 * k - tenPowThetaCeilExp k θ

/-- Constructive Chebyshev remainder model `|ψ(x) - x| ≤ C · x^θ · (ln x)^2`
at `x = 10^(12k)` (`k ≥ 1`) with rational QRH exponent `0 < θ < 1`. -/
structure ChebyshevRemainderSpec where
  scaleK : Nat
  scaleK_pos : 1 ≤ scaleK
  prefactor : Nat
  prefactor_pos : 1 ≤ prefactor
  theta : QRat
  theta_pos : (0 : Int) < theta.num
  theta_lt_one : theta < QRat.ofInt 1

/-- Explicit integer remainder envelope `C · 10^(tenPowThetaCeilExp k θ) · (28k)^2`
bounding `|ψ(10^(12k)) - 10^(12k)|`. -/
def qrhRemainderBoundAtTenPow (spec : ChebyshevRemainderSpec) : Nat :=
  spec.prefactor * 10 ^ (tenPowThetaCeilExp spec.scaleK spec.theta) *
    chebyshevLogSqEnv spec.scaleK

theorem tenPowThetaCeilExp_eq_exact {k : Nat} {θ : QRat} (hdvd : θ.den ∣ 12 * k) :
    tenPowThetaCeilExp k θ = tenPowThetaExactExp k θ := by
  dsimp [tenPowThetaCeilExp, tenPowThetaExactExp]
  have hd : 0 < θ.den := θ.den_pos
  have hdvdMul : θ.den ∣ 12 * k * θ.num.natAbs :=
    Nat.dvd_trans hdvd (Nat.dvd_mul_right _ _)
  obtain ⟨q, hq⟩ := hdvdMul
  rw [hq]
  have hrew : θ.den * q + θ.den - 1 = θ.den * q + (θ.den - 1) := by omega
  rw [hrew, Nat.mul_add_div hd, Nat.mul_div_right q hd,
    Nat.div_eq_of_lt (by omega : θ.den - 1 < θ.den), Nat.add_zero]

theorem tenPowThetaExactExp_lt_scale {k : Nat} (hk : 1 ≤ k) {θ : QRat}
    (hpos : (0 : Int) < θ.num) (hlt : θ < QRat.ofInt 1) :
    tenPowThetaExactExp k θ < 12 * k := by
  dsimp [tenPowThetaExactExp]
  have hd : 0 < θ.den := θ.den_pos
  have hnum_lt : θ.num.natAbs < θ.den := by
    change θ.num * 1 < 1 * (θ.den : Int) at hlt
    omega
  have hmul : 12 * k * θ.num.natAbs < 12 * k * θ.den :=
    Nat.mul_lt_mul_of_pos_left hnum_lt (by omega)
  exact (Nat.div_lt_iff_lt_mul hd).mpr hmul

private theorem tenPowThetaExactExp_le_of_le {k : Nat} {θ₁ θ₂ : QRat}
    (hpos1 : (0 : Int) < θ₁.num) (hpos2 : (0 : Int) < θ₂.num)
    (hdvd1 : θ₁.den ∣ 12 * k) (hdvd2 : θ₂.den ∣ 12 * k) (hle : θ₁ ≤ θ₂) :
    tenPowThetaExactExp k θ₁ ≤ tenPowThetaExactExp k θ₂ := by
  dsimp [tenPowThetaExactExp]
  obtain ⟨q1, hq1⟩ := hdvd1
  obtain ⟨q2, hq2⟩ := hdvd2
  have hd1 : 0 < θ₁.den := θ₁.den_pos
  have hd2 : 0 < θ₂.den := θ₂.den_pos
  have hden_eq : θ₁.den * q1 = θ₂.den * q2 := by rw [← hq1, ← hq2]
  have he1 : (12 * k * θ₁.num.natAbs) / θ₁.den = q1 * θ₁.num.natAbs := by
    rw [hq1, Nat.mul_assoc, Nat.mul_div_right _ hd1]
  have he2 : (12 * k * θ₂.num.natAbs) / θ₂.den = q2 * θ₂.num.natAbs := by
    rw [hq2, Nat.mul_assoc, Nat.mul_div_right _ hd2]
  rw [he1, he2]
  have hnum : θ₁.num.natAbs * θ₂.den ≤ θ₂.num.natAbs * θ₁.den := by
    change θ₁.num * (θ₂.den : Int) ≤ θ₂.num * (θ₁.den : Int) at hle
    have h1 : (θ₁.num.natAbs : Int) = θ₁.num := Int.natAbs_of_nonneg (Int.le_of_lt hpos1)
    have h2 : (θ₂.num.natAbs : Int) = θ₂.num := Int.natAbs_of_nonneg (Int.le_of_lt hpos2)
    have hz : ((θ₁.num.natAbs * θ₂.den : Nat) : Int) ≤
        ((θ₂.num.natAbs * θ₁.den : Nat) : Int) := by
      rw [Int.natCast_mul, Int.natCast_mul, h1, h2]
      exact hle
    exact Int.ofNat_le.mp hz
  have hmul_le : (q1 * θ₁.num.natAbs) * (θ₁.den * θ₂.den) ≤
      (q2 * θ₂.num.natAbs) * (θ₁.den * θ₂.den) := by
    have lhs_eq : (q1 * θ₁.num.natAbs) * (θ₁.den * θ₂.den) =
        (θ₁.den * q1) * (θ₁.num.natAbs * θ₂.den) := by ac_rfl
    have rhs_eq : (q2 * θ₂.num.natAbs) * (θ₁.den * θ₂.den) =
        (θ₂.den * q2) * (θ₂.num.natAbs * θ₁.den) := by ac_rfl
    rw [lhs_eq, rhs_eq, hden_eq]
    exact Nat.mul_le_mul_left _ hnum
  exact Nat.le_of_mul_le_mul_right hmul_le (Nat.mul_pos hd1 hd2)

/-- Constructive monotonicity & exact power-of-ten relative savings across the QRH ladder:
for any `1 ≤ k`, `1 ≤ C`, and divisible rational exponents `θ₁ ≤ θ₂ < 1`,
`spec₁`'s remainder bound is bounded by `spec₂`'s, with exact savings factor
`10 ^ (e₂ - e₁)` where `eᵢ = tenPowThetaExactExp k θᵢ`. Zero `Classical.choice`, zero `sorryAx`. -/
theorem chebyshev_remainder_mono_theta (k C : Nat) (hk : 1 ≤ k) (hC : 1 ≤ C)
    (θ₁ θ₂ : QRat) (hpos1 : (0 : Int) < θ₁.num) (hpos2 : (0 : Int) < θ₂.num)
    (hlt2 : θ₂ < QRat.ofInt 1) (hdvd1 : θ₁.den ∣ 12 * k) (hdvd2 : θ₂.den ∣ 12 * k)
    (hle : θ₁ ≤ θ₂) :
    let hlt1 : θ₁ < QRat.ofInt 1 := qrat_lt_of_le_of_lt hle hlt2
    let e₁ := tenPowThetaExactExp k θ₁
    let e₂ := tenPowThetaExactExp k θ₂
    let s₁ : ChebyshevRemainderSpec := ⟨k, hk, C, hC, θ₁, hpos1, hlt1⟩
    let s₂ : ChebyshevRemainderSpec := ⟨k, hk, C, hC, θ₂, hpos2, hlt2⟩
    e₁ ≤ e₂ ∧
    e₂ < 12 * k ∧
    (10 : Nat) ^ e₂ = 10 ^ e₁ * 10 ^ (e₂ - e₁) ∧
    qrhRemainderBoundAtTenPow s₂ = qrhRemainderBoundAtTenPow s₁ * 10 ^ (e₂ - e₁) ∧
    qrhRemainderBoundAtTenPow s₁ ≤ qrhRemainderBoundAtTenPow s₂ := by
  intro hlt1 e₁ e₂ s₁ s₂
  have he : e₁ ≤ e₂ := tenPowThetaExactExp_le_of_le hpos1 hpos2 hdvd1 hdvd2 hle
  have hlt_k : e₂ < 12 * k := tenPowThetaExactExp_lt_scale hk hpos2 hlt2
  have hpow : (10 : Nat) ^ e₂ = 10 ^ e₁ * 10 ^ (e₂ - e₁) := by
    have hadd : e₁ + (e₂ - e₁) = e₂ := Nat.add_sub_cancel' he
    calc (10 : Nat) ^ e₂ = 10 ^ (e₁ + (e₂ - e₁)) := by rw [hadd]
      _ = 10 ^ e₁ * 10 ^ (e₂ - e₁) := Nat.pow_add _ _ _
  have hc1 : tenPowThetaCeilExp k θ₁ = e₁ := tenPowThetaCeilExp_eq_exact hdvd1
  have hc2 : tenPowThetaCeilExp k θ₂ = e₂ := tenPowThetaCeilExp_eq_exact hdvd2
  have hbeq : qrhRemainderBoundAtTenPow s₂ =
      qrhRemainderBoundAtTenPow s₁ * 10 ^ (e₂ - e₁) := by
    dsimp [qrhRemainderBoundAtTenPow, s₁, s₂]
    rw [hc1, hc2, hpow]
    ac_rfl
  have hble : qrhRemainderBoundAtTenPow s₁ ≤ qrhRemainderBoundAtTenPow s₂ := by
    rw [hbeq]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  exact ⟨he, hlt_k, hpow, hbeq, hble⟩

/-- Helper: symbolic relative-error certificate `10 * qrhRemainderBoundAtTenPow spec < 10^(12k)`
from the reduced saving inequality `10 * C * (28k)^2 < 10^(12k - e)` (no large power unfolding). -/
theorem tenPow_rel_err_lt_inv10 (k m : Nat) (hk : 1 ≤ k) (hm : 12 * k = m) (C : Nat)
    (hC : 1 ≤ C) (θ : QRat) (hpos : (0 : Int) < θ.num) (hlt : θ < QRat.ofInt 1)
    (hdvd : θ.den ∣ 12 * k)
    (hdom : 10 * (C * chebyshevLogSqEnv k) < 10 ^ (12 * k - tenPowThetaExactExp k θ)) :
    10 * qrhRemainderBoundAtTenPow ⟨k, hk, C, hC, θ, hpos, hlt⟩ < 10 ^ m := by
  have he_lt : tenPowThetaExactExp k θ < 12 * k :=
    tenPowThetaExactExp_lt_scale hk hpos hlt
  have he_le : tenPowThetaExactExp k θ ≤ 12 * k := Nat.le_of_lt he_lt
  have hceil : tenPowThetaCeilExp k θ = tenPowThetaExactExp k θ :=
    tenPowThetaCeilExp_eq_exact hdvd
  have hx : 10 ^ (tenPowThetaExactExp k θ) * 10 ^ (12 * k - tenPowThetaExactExp k θ) =
      (10 : Nat) ^ m := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' he_le, hm]
  have hmul := Nat.mul_lt_mul_of_pos_left hdom
    (Nat.pow_pos (by decide) : 0 < (10 : Nat) ^ (tenPowThetaExactExp k θ))
  rw [hx] at hmul
  have hlhs : 10 * qrhRemainderBoundAtTenPow ⟨k, hk, C, hC, θ, hpos, hlt⟩ =
      10 ^ (tenPowThetaExactExp k θ) * (10 * (C * chebyshevLogSqEnv k)) := by
    dsimp [qrhRemainderBoundAtTenPow]
    rw [hceil]
    ac_rfl
  rw [hlhs]
  exact hmul

/-- Relative Savings Certificates across Benchmark Scales (`x = 10^24` and `x = 10^48`):
1. At `x = 10^24` (`k = 2`), `θ = 3/4` reduces the Chebyshev remainder envelope by `10^3 = 1000`
   relative to `θ = 7/8` and by `10^4 = 10000` relative to `θ = 11/12`.
2. At `x = 10^48` (`k = 4`), `θ = 3/4` reduces the envelope by `10^11 = 100000000000`
   relative to `θ = 47/48`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_chebyshev_savings_certs :
    let θ₁ := qrhThresholdThreeQuarters
    let θ₂ := qrhThresholdSevenEighths
    let θ₃ := qrhThresholdElevenTwelfths
    let θ₄ := qrhThresholdFortySevenFortyEighths
    let s24_1 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s24_2 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s24_3 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s48_1 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s48_4 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₄, by decide, by decide⟩
    (tenPowThetaExactExp 2 θ₁ = 18 ∧ tenPowThetaExactExp 2 θ₂ = 21 ∧
      qrhRemainderBoundAtTenPow s24_2 = qrhRemainderBoundAtTenPow s24_1 * 1000 ∧
      qrhRemainderBoundAtTenPow s24_1 ≤ qrhRemainderBoundAtTenPow s24_2) ∧
    (tenPowThetaExactExp 2 θ₃ = 22 ∧
      qrhRemainderBoundAtTenPow s24_3 = qrhRemainderBoundAtTenPow s24_1 * 10000 ∧
      qrhRemainderBoundAtTenPow s24_1 ≤ qrhRemainderBoundAtTenPow s24_3) ∧
    (tenPowThetaExactExp 4 θ₁ = 36 ∧ tenPowThetaExactExp 4 θ₄ = 47 ∧
      qrhRemainderBoundAtTenPow s48_4 = qrhRemainderBoundAtTenPow s48_1 * 10 ^ 11 ∧
      qrhRemainderBoundAtTenPow s48_1 ≤ qrhRemainderBoundAtTenPow s48_4) := by
  have h1 := chebyshev_remainder_mono_theta 2 1 (by decide) (by decide)
    qrhThresholdThreeQuarters qrhThresholdSevenEighths
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h2 := chebyshev_remainder_mono_theta 2 1 (by decide) (by decide)
    qrhThresholdThreeQuarters qrhThresholdElevenTwelfths
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h3 := chebyshev_remainder_mono_theta 4 1 (by decide) (by decide)
    qrhThresholdThreeQuarters qrhThresholdFortySevenFortyEighths
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have he18 : tenPowThetaExactExp 2 qrhThresholdThreeQuarters = 18 := by decide
  have he21 : tenPowThetaExactExp 2 qrhThresholdSevenEighths = 21 := by decide
  have he22 : tenPowThetaExactExp 2 qrhThresholdElevenTwelfths = 22 := by decide
  have he36 : tenPowThetaExactExp 4 qrhThresholdThreeQuarters = 36 := by decide
  have he47 : tenPowThetaExactExp 4 qrhThresholdFortySevenFortyEighths = 47 := by decide
  have hp3 : (10 : Nat) ^ (21 - 18) = 1000 := by decide
  have hp4 : (10 : Nat) ^ (22 - 18) = 10000 := by decide
  have hp11 : (10 : Nat) ^ (47 - 36) = 10 ^ 11 := by decide
  refine ⟨⟨he18, he21, ?_, h1.2.2.2.2⟩, ⟨he22, ?_, h2.2.2.2.2⟩, ⟨he36, he47, ?_, h3.2.2.2.2⟩⟩
  · have hb := h1.2.2.2.1
    rw [he18, he21, hp3] at hb
    exact hb
  · have hb := h2.2.2.2.1
    rw [he18, he22, hp4] at hb
    exact hb
  · have hb := h3.2.2.2.1
    rw [he36, he47, hp11] at hb
    exact hb

/-- Constructive Benchmark Numerical Remainder Certificates (`C = 1`, `(ln x)^2 ≤ (28k)^2`):
1. Exact symbolic envelopes `10^e * (28k)^2` at `x ∈ {10^12, 10^24, 10^36, 10^48}` (using exact
   `10^e` when `θ.den ∣ 12k`, and integer ceiling `e_ceil` for `θ = 7/8` at `k = 1, 3`).
2. Strict sub-linear relative error: `< 1` at `(10^12, 3/4)` (`784 < 1000`), and `< 10^-1`
   at `(10^24, 3/4)`, `(10^36, 3/4)`, `(10^48, 3/4)`, and `(10^48, 7/8)`.
3. Minimal all-rung `< 10^-1` crossover at `x = 10^336` (`k = 28`): certifies
   `10 * bound < 10^336` simultaneously across ALL four rungs `θ ∈ {3/4, 7/8, 11/12, 47/48}`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_chebyshev_benchmark_certs :
    let θ₁ := qrhThresholdThreeQuarters
    let θ₂ := qrhThresholdSevenEighths
    let θ₃ := qrhThresholdElevenTwelfths
    let θ₄ := qrhThresholdFortySevenFortyEighths
    let s12_1 : ChebyshevRemainderSpec := ⟨1, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s12_2 : ChebyshevRemainderSpec := ⟨1, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s12_3 : ChebyshevRemainderSpec := ⟨1, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s24_1 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s24_2 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s24_3 : ChebyshevRemainderSpec := ⟨2, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s36_1 : ChebyshevRemainderSpec := ⟨3, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s36_2 : ChebyshevRemainderSpec := ⟨3, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s36_3 : ChebyshevRemainderSpec := ⟨3, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s48_1 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s48_2 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s48_3 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s48_4 : ChebyshevRemainderSpec := ⟨4, by decide, 1, by decide, θ₄, by decide, by decide⟩
    let s336_1 : ChebyshevRemainderSpec := ⟨28, by decide, 1, by decide, θ₁, by decide, by decide⟩
    let s336_2 : ChebyshevRemainderSpec := ⟨28, by decide, 1, by decide, θ₂, by decide, by decide⟩
    let s336_3 : ChebyshevRemainderSpec := ⟨28, by decide, 1, by decide, θ₃, by decide, by decide⟩
    let s336_4 : ChebyshevRemainderSpec := ⟨28, by decide, 1, by decide, θ₄, by decide, by decide⟩
    (qrhRemainderBoundAtTenPow s12_1 = 10 ^ 9 * 784 ∧
      qrhRemainderBoundAtTenPow s12_1 < 10 ^ 12 ∧
      qrhRemainderBoundAtTenPow s12_2 = 10 ^ 11 * 784 ∧
      qrhRemainderBoundAtTenPow s12_3 = 10 ^ 11 * 784) ∧
    (qrhRemainderBoundAtTenPow s24_1 = 10 ^ 18 * 3136 ∧
      10 * qrhRemainderBoundAtTenPow s24_1 < 10 ^ 24 ∧
      qrhRemainderBoundAtTenPow s24_2 = 10 ^ 21 * 3136 ∧
      qrhRemainderBoundAtTenPow s24_3 = 10 ^ 22 * 3136) ∧
    (qrhRemainderBoundAtTenPow s36_1 = 10 ^ 27 * 7056 ∧
      10 * qrhRemainderBoundAtTenPow s36_1 < 10 ^ 36 ∧
      qrhRemainderBoundAtTenPow s36_2 = 10 ^ 32 * 7056 ∧
      qrhRemainderBoundAtTenPow s36_3 = 10 ^ 33 * 7056) ∧
    (qrhRemainderBoundAtTenPow s48_1 = 10 ^ 36 * 12544 ∧
      10 * qrhRemainderBoundAtTenPow s48_1 < 10 ^ 48 ∧
      qrhRemainderBoundAtTenPow s48_2 = 10 ^ 42 * 12544 ∧
      10 * qrhRemainderBoundAtTenPow s48_2 < 10 ^ 48 ∧
      qrhRemainderBoundAtTenPow s48_3 = 10 ^ 44 * 12544 ∧
      qrhRemainderBoundAtTenPow s48_4 = 10 ^ 47 * 12544) ∧
    (tenPowThetaExactExp 28 θ₁ = 252 ∧
      tenPowThetaExactExp 28 θ₂ = 294 ∧
      tenPowThetaExactExp 28 θ₃ = 308 ∧
      tenPowThetaExactExp 28 θ₄ = 329 ∧
      10 * qrhRemainderBoundAtTenPow s336_1 < 10 ^ 336 ∧
      10 * qrhRemainderBoundAtTenPow s336_2 < 10 ^ 336 ∧
      10 * qrhRemainderBoundAtTenPow s336_3 < 10 ^ 336 ∧
      10 * qrhRemainderBoundAtTenPow s336_4 < 10 ^ 336) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hb1 : qrhRemainderBoundAtTenPow ⟨1, by decide, 1, by decide,
        qrhThresholdThreeQuarters, by decide, by decide⟩ = 10 ^ 9 * 784 := by
      dsimp [qrhRemainderBoundAtTenPow, chebyshevLogSqEnv, chebyshevLogEnv,
        tenPowThetaCeilExp, qrhThresholdThreeQuarters, QRat.mk']
    have hlt12 : 10 ^ 9 * 784 < 10 ^ 12 := by
      have hx : (10 : Nat) ^ 9 * 10 ^ 3 = 10 ^ 12 := (Nat.pow_add 10 9 3).symm
      rw [← hx]
      exact Nat.mul_lt_mul_of_pos_left (by decide : 784 < 10 ^ 3) (Nat.pow_pos (by decide))
    refine ⟨hb1, ?_, by decide, by decide⟩
    rw [hb1]
    exact hlt12
  · refine ⟨rfl, ?_, rfl, rfl⟩
    exact tenPow_rel_err_lt_inv10 2 24 (by decide) rfl 1 (by decide)
      qrhThresholdThreeQuarters (by decide) (by decide) (by decide) (by decide)
  · refine ⟨rfl, ?_, rfl, rfl⟩
    exact tenPow_rel_err_lt_inv10 3 36 (by decide) rfl 1 (by decide)
      qrhThresholdThreeQuarters (by decide) (by decide) (by decide) (by decide)
  · refine ⟨rfl, ?_, rfl, ?_, rfl, rfl⟩
    · exact tenPow_rel_err_lt_inv10 4 48 (by decide) rfl 1 (by decide)
        qrhThresholdThreeQuarters (by decide) (by decide) (by decide) (by decide)
    · exact tenPow_rel_err_lt_inv10 4 48 (by decide) rfl 1 (by decide)
        qrhThresholdSevenEighths (by decide) (by decide) (by decide) (by decide)
  · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact tenPow_rel_err_lt_inv10 28 336 (by decide) rfl 1 (by decide)
        qrhThresholdThreeQuarters (by decide) (by decide) (by decide) (by decide)
    · exact tenPow_rel_err_lt_inv10 28 336 (by decide) rfl 1 (by decide)
        qrhThresholdSevenEighths (by decide) (by decide) (by decide) (by decide)
    · exact tenPow_rel_err_lt_inv10 28 336 (by decide) rfl 1 (by decide)
        qrhThresholdElevenTwelfths (by decide) (by decide) (by decide) (by decide)
    · exact tenPow_rel_err_lt_inv10 28 336 (by decide) rfl 1 (by decide)
        qrhThresholdFortySevenFortyEighths (by decide) (by decide) (by decide) (by decide)

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean