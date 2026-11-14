-- Path: leanasm/src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean
-- Constructive short-interval prime guarantees, maximal prime-gap bounds, and
-- rational short-interval exponent ladder extending QRH Chebyshev envelopes.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.ZeroDensityBridge
import LeanAsm.EulerFactorNonVanishing

namespace QuasiRiemann

-- =============================================================================
-- 1. Short-Interval Chebyshev Specification & Prime-Existence Predicate
-- =============================================================================

/-- Constructive specification for a short interval `[x, x + h]` at decimal scales
`x = 10 ^ xScaleExp` and `h = 10 ^ hScaleExp` under a Chebyshev remainder envelope
`errUpper` at `2x` and prime-power discrepancy bound `primePowerCorr`. -/
structure ShortIntervalChebyshevSpec where
  thetaNum : Nat
  thetaDen : Nat
  xScaleExp : Nat
  hScaleExp : Nat
  errUpper : Nat
  primePowerCorr : Nat
  thetaDen_pos : 0 < thetaDen
  theta_lt_one : thetaNum < thetaDen

/-- Exact rational QRH exponent `θ = thetaNum / thetaDen` of a short-interval spec. -/
def ShortIntervalChebyshevSpec.thetaQRat (s : ShortIntervalChebyshevSpec) : QRat :=
  QRat.mk' (s.thetaNum : Int) s.thetaDen s.thetaDen_pos

/-- Prime-existence certificate `2 * errUpper + primePowerCorr < 10 ^ hScaleExp`.
Whenever `|ψ(x + h) - ψ(x) - h| ≤ 2 * errUpper` and the prime-power contribution
`ψ(x + h) - ψ(x) - (ϑ(x + h) - ϑ(x))` is at most `primePowerCorr`, this strict
inequality guarantees `ϑ(x + h) - ϑ(x) > 0`, hence at least one prime in `(x, x + h]`. -/
def ShortIntervalChebyshevSpec.HasGuaranteedPrime
    (s : ShortIntervalChebyshevSpec) : Prop :=
  2 * s.errUpper + s.primePowerCorr < 10 ^ s.hScaleExp

instance (s : ShortIntervalChebyshevSpec) : Decidable s.HasGuaranteedPrime :=
  inferInstanceAs (Decidable (2 * s.errUpper + s.primePowerCorr < 10 ^ s.hScaleExp))

/-- Conservative remainder upper bound at `2x = 2 * 10^(12k)` derived from a
`ChebyshevRemainderSpec`: using `(2x)^θ ≤ 2 * x^θ` (for `θ < 1`) and
`ln(2x) = ln 2 + ln x ≤ 29k` (`k ≥ 1`), giving `2 * C * 10^e_ceil * (29k)^2`. -/
def qrhRemainderBoundAtTwoTenPow (spec : ChebyshevRemainderSpec) : Nat :=
  2 * spec.prefactor * 10 ^ (tenPowThetaCeilExp spec.scaleK spec.theta) *
    ((29 * spec.scaleK) * (29 * spec.scaleK))

/-- The `2x` envelope dominates the `x` envelope `qrhRemainderBoundAtTenPow spec`. -/
theorem qrhRemainderBoundAtTenPow_le_twoTenPow (spec : ChebyshevRemainderSpec) :
    qrhRemainderBoundAtTenPow spec ≤ qrhRemainderBoundAtTwoTenPow spec := by
  dsimp [qrhRemainderBoundAtTenPow, qrhRemainderBoundAtTwoTenPow,
    chebyshevLogSqEnv, chebyshevLogEnv]
  have hlog : 28 * spec.scaleK ≤ 29 * spec.scaleK := by omega
  have hsq : 28 * spec.scaleK * (28 * spec.scaleK) ≤
      29 * spec.scaleK * (29 * spec.scaleK) :=
    Nat.mul_le_mul hlog hlog
  have hpref : spec.prefactor ≤ 2 * spec.prefactor := by omega
  have hbase : spec.prefactor * 10 ^ (tenPowThetaCeilExp spec.scaleK spec.theta) ≤
      2 * spec.prefactor * 10 ^ (tenPowThetaCeilExp spec.scaleK spec.theta) :=
    Nat.mul_le_mul_right _ hpref
  exact Nat.mul_le_mul hbase hsq

-- =============================================================================
-- 2. Differenced Chebyshev Bounds & Contrapositive Maximal Prime-Gap Theorem
-- =============================================================================

private theorem natAbs_le_of_bounds {z : Int} {n : Nat}
    (hLo : -(n : Int) ≤ z) (hHi : z ≤ (n : Int)) :
    Int.natAbs z ≤ n := by
  cases z with
  | ofNat m =>
    change m ≤ n
    exact Int.ofNat_le.mp hHi
  | negSucc m =>
    change m + 1 ≤ n
    have hNeg : -((m + 1 : Nat) : Int) = Int.negSucc m := rfl
    have h1 : -(n : Int) ≤ -((m + 1 : Nat) : Int) := hNeg ▸ hLo
    exact Int.ofNat_le.mp (Int.neg_le_neg_iff.mp h1)

private theorem bounds_of_natAbs_le {z : Int} {n : Nat}
    (h : Int.natAbs z ≤ n) :
    -(n : Int) ≤ z ∧ z ≤ (n : Int) := by
  cases z with
  | ofNat m =>
    change m ≤ n at h
    exact ⟨Int.le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg n))
      (Int.natCast_nonneg m), Int.ofNat_le.mpr h⟩
  | negSucc m =>
    change m + 1 ≤ n at h
    exact ⟨Int.neg_le_neg (Int.ofNat_le.mpr h),
      Int.le_trans (Int.le_of_lt (Int.negSucc_lt_zero m)) (Int.natCast_nonneg n)⟩

/-- Theorem (Differenced Chebyshev Short-Interval Bound):
For any `spec : ChebyshevRemainderSpec`, `1 ≤ h ≤ x`, and `E2x ≥ E(2x, θ)` bounding
both endpoint remainders `|ψ(x) - x| ≤ E2x` and `|ψ(x + h) - (x + h)| ≤ E2x`,
we derive:
1. The differenced Chebyshev remainder bound `|ψ(x + h) - ψ(x) - h| ≤ 2 * E2x`.
2. Two-sided bounds `h - 2 * E2x ≤ ψ(x + h) - ψ(x) ≤ h + 2 * E2x`.
3. Subtracting the prime-power correction `corr` bounds `ϑ(x + h) - ϑ(x)` below
   by `h - (2 * E2x + corr)`.
4. If `2 * E2x + corr < h` (the `HasGuaranteedPrime` criterion when `h = 10^hScaleExp`),
   then `0 < ϑ(x + h) - ϑ(x)`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem short_interval_psi_diff_bound
    (spec : ChebyshevRemainderSpec) (x h E2x corr : Nat)
    (_hPos : 1 ≤ h) (_hle : h ≤ x)
    (_hEnv : qrhRemainderBoundAtTwoTenPow spec ≤ E2x)
    (psiX psiXH thetaX thetaXH : Int)
    (hBoundX : Int.natAbs (psiX - (x : Int)) ≤ E2x)
    (hBoundXH : Int.natAbs (psiXH - ((x + h : Nat) : Int)) ≤ E2x)
    (hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (corr : Int)) :
    Int.natAbs (psiXH - psiX - (h : Int)) ≤ 2 * E2x ∧
    (h : Int) - ((2 * E2x : Nat) : Int) ≤ psiXH - psiX ∧
    psiXH - psiX ≤ (h : Int) + ((2 * E2x : Nat) : Int) ∧
    (h : Int) - ((2 * E2x + corr : Nat) : Int) ≤ thetaXH - thetaX ∧
    (2 * E2x + corr < h → (0 : Int) < thetaXH - thetaX) := by
  have hxAbs := bounds_of_natAbs_le hBoundX
  have hxhAbs := bounds_of_natAbs_le hBoundXH
  have hTwo : ((2 * E2x : Nat) : Int) = (E2x : Int) + (E2x : Int) := by omega
  have hDiffLo : -((2 * E2x : Nat) : Int) ≤ psiXH - psiX - (h : Int) := by
    rw [hTwo]
    have hxhLo := hxhAbs.1
    have hxHi := hxAbs.2
    rw [Int.natCast_add] at hxhLo
    omega
  have hDiffHi : psiXH - psiX - (h : Int) ≤ ((2 * E2x : Nat) : Int) := by
    rw [hTwo]
    have hxhHi := hxhAbs.2
    have hxLo := hxAbs.1
    rw [Int.natCast_add] at hxhHi
    omega
  have hAbsBound : Int.natAbs (psiXH - psiX - (h : Int)) ≤ 2 * E2x :=
    natAbs_le_of_bounds hDiffLo hDiffHi
  have hLowerPsi : (h : Int) - ((2 * E2x : Nat) : Int) ≤ psiXH - psiX := by omega
  have hUpperPsi : psiXH - psiX ≤ (h : Int) + ((2 * E2x : Nat) : Int) := by omega
  have hLowerTheta :
      (h : Int) - ((2 * E2x + corr : Nat) : Int) ≤ thetaXH - thetaX := by
    rw [Int.natCast_add]
    omega
  refine ⟨hAbsBound, hLowerPsi, hUpperPsi, hLowerTheta, ?_⟩
  intro hGap
  have hGapInt : ((2 * E2x + corr : Nat) : Int) < (h : Int) := Int.ofNat_lt.mpr hGap
  omega

/-- Specialization connecting `short_interval_psi_diff_bound` directly to a
`ShortIntervalChebyshevSpec` at `x = 10 ^ s.xScaleExp`, `h = 10 ^ s.hScaleExp`. -/
theorem short_interval_spec_guarantees_theta_pos
    (spec : ChebyshevRemainderSpec) (s : ShortIntervalChebyshevSpec)
    (hHleX : s.hScaleExp ≤ s.xScaleExp)
    (hEnv : qrhRemainderBoundAtTwoTenPow spec ≤ s.errUpper)
    (psiX psiXH thetaX thetaXH : Int)
    (hBoundX : Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ s.errUpper)
    (hBoundXH :
      Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤
        s.errUpper)
    (hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (s.primePowerCorr : Int))
    (hPrime : s.HasGuaranteedPrime) :
    (0 : Int) < thetaXH - thetaX := by
  have hOne : 1 ≤ 10 ^ s.hScaleExp := Nat.pow_pos (by decide)
  have hLe : 10 ^ s.hScaleExp ≤ 10 ^ s.xScaleExp :=
    Nat.pow_le_pow_right (by decide) hHleX
  have hDiff := short_interval_psi_diff_bound spec
    (10 ^ s.xScaleExp) (10 ^ s.hScaleExp) s.errUpper s.primePowerCorr
    hOne hLe hEnv psiX psiXH thetaX thetaXH hBoundX hBoundXH hCorr
  exact hDiff.2.2.2.2 hPrime

/-- Theorem (Contrapositive Maximal Prime-Gap Bound):
Under the differenced Chebyshev remainder and prime-power hypotheses on
`[x, x + h]` with `x = 10 ^ s.xScaleExp` and `h = 10 ^ s.hScaleExp`:
1. If `ϑ(x + h) - ϑ(x) ≤ 0` (i.e. no prime lies in `(x, x + h]`), then
   `¬ s.HasGuaranteedPrime`.
2. Contrapositively, `s.HasGuaranteedPrime` forces `0 < ϑ(x + h) - ϑ(x)`, and
   therefore any consecutive prime `pNext` satisfying `(x + h < pNext →
   thetaXH - thetaX ≤ 0)` must obey `pNext ≤ x + h` (so at `x = pCurr`, the prime
   gap satisfies `pNext - pCurr ≤ 10 ^ s.hScaleExp`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_maximal_prime_gap_bound
    (spec : ChebyshevRemainderSpec) (s : ShortIntervalChebyshevSpec)
    (hHleX : s.hScaleExp ≤ s.xScaleExp)
    (hEnv : qrhRemainderBoundAtTwoTenPow spec ≤ s.errUpper)
    (psiX psiXH thetaX thetaXH : Int)
    (hBoundX : Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ s.errUpper)
    (hBoundXH :
      Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤
        s.errUpper)
    (hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (s.primePowerCorr : Int)) :
    (thetaXH - thetaX ≤ 0 → ¬ s.HasGuaranteedPrime) ∧
    (s.HasGuaranteedPrime →
      ∀ pCurr pNext : Nat,
        pCurr ≤ 10 ^ s.xScaleExp →
        (10 ^ s.xScaleExp + 10 ^ s.hScaleExp < pNext → thetaXH - thetaX ≤ 0) →
        pNext ≤ 10 ^ s.xScaleExp + 10 ^ s.hScaleExp ∧
        (pCurr = 10 ^ s.xScaleExp → pNext - pCurr ≤ 10 ^ s.hScaleExp)) := by
  constructor
  · intro hNoPrime hCert
    have hPos := short_interval_spec_guarantees_theta_pos spec s hHleX hEnv
      psiX psiXH thetaX thetaXH hBoundX hBoundXH hCorr hCert
    omega
  · intro hCert pCurr pNext _hpCurr hEmpty
    have hPos := short_interval_spec_guarantees_theta_pos spec s hHleX hEnv
      psiX psiXH thetaX thetaXH hBoundX hBoundXH hCorr hCert
    have hpLe : pNext ≤ 10 ^ s.xScaleExp + 10 ^ s.hScaleExp := by
      by_cases hGt : 10 ^ s.xScaleExp + 10 ^ s.hScaleExp < pNext
      · exfalso
        have hLe0 := hEmpty hGt
        omega
      · omega
    refine ⟨hpLe, ?_⟩
    intro hEq
    have hpLeCurr : pNext ≤ pCurr + 10 ^ s.hScaleExp := hEq ▸ hpLe
    exact Nat.sub_le_of_le_add (by rw [Nat.add_comm]; exact hpLeCurr)

-- =============================================================================
-- 3. Benchmark Short-Interval Positivity Witnesses (7/8, 3/4, 1/2)
-- =============================================================================

/-- Chebyshev spec at `x = 10^336` (`k = 28`) for QRH `θ = 7/8`. -/
def chebyshevSpec336_78 : ChebyshevRemainderSpec :=
  ⟨28, by decide, 1, by decide, qrhThresholdSevenEighths, by decide, by decide⟩

/-- Chebyshev spec at `x = 10^168` (`k = 14`) for QRH `θ = 3/4`. -/
def chebyshevSpec168_34 : ChebyshevRemainderSpec :=
  ⟨14, by decide, 1, by decide, qrhThresholdThreeQuarters, by decide, by decide⟩

/-- Chebyshev spec at `x = 10^168` (`k = 14`) for RH `θ = 1/2`. -/
def chebyshevSpec168_12 : ChebyshevRemainderSpec :=
  ⟨14, by decide, 1, by decide, QRat.mk' 1 2, by decide, by decide⟩

/-- Short-interval spec at `x = 10^336, h = 10^308` under QRH `θ = 7/8`
(`x^(7/8) = 10^294`, `primePowerCorr = 10^173 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalQrh78Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 7
    thetaDen := 8
    xScaleExp := 336
    hScaleExp := 308
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec336_78
    primePowerCorr := 10 ^ 173
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Short-interval spec at `x = 10^168, h = 10^140` under QRH `θ = 3/4`
(`x^(3/4) = 10^126`, `primePowerCorr = 10^89 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalQrh34Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 3
    thetaDen := 4
    xScaleExp := 168
    hScaleExp := 140
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec168_34
    primePowerCorr := 10 ^ 89
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Short-interval spec at `x = 10^168, h = 10^98` under RH `θ = 1/2`
(`x^(1/2) = 10^84`, `primePowerCorr = 10^89 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalRh12Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 1
    thetaDen := 2
    xScaleExp := 168
    hScaleExp := 98
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec168_12
    primePowerCorr := 10 ^ 89
    thetaDen_pos := by decide
    theta_lt_one := by decide }

private theorem pow_ten_factor_lt
    (e c pExp gap coeff hExp : Nat)
    (hp : pExp ≤ e)
    (hc : e + gap = hExp)
    (hCoeff : 2 * c + 1 < coeff)
    (hGap : coeff < 10 ^ gap) :
    2 * (c * 10 ^ e) + 10 ^ pExp < 10 ^ hExp := by
  have hpLe : 10 ^ pExp ≤ 10 ^ e := Nat.pow_le_pow_right (by decide) hp
  have h1 : 2 * (c * 10 ^ e) + 10 ^ pExp ≤ (2 * c + 1) * 10 ^ e := by
    have hmul : 2 * (c * 10 ^ e) + 10 ^ e = (2 * c + 1) * 10 ^ e := by
      rw [Nat.add_mul, Nat.one_mul]
      ac_rfl
    omega
  have h2 : (2 * c + 1) * 10 ^ e < coeff * 10 ^ e :=
    Nat.mul_lt_mul_of_pos_right hCoeff (Nat.pow_pos (by decide))
  have h3 : coeff * 10 ^ e < 10 ^ gap * 10 ^ e :=
    Nat.mul_lt_mul_of_pos_right hGap (Nat.pow_pos (by decide))
  have h4 : 10 ^ gap * 10 ^ e = 10 ^ hExp := by
    rw [← Nat.pow_add, Nat.add_comm gap e, hc]
  omega

set_option exponentiation.threshold 2000 in
/-- Theorem (QRH & RH Short-Interval Prime Positivity Certificates):
Certifies `HasGuaranteedPrime` (`2 * errUpper + primePowerCorr < 10 ^ hScaleExp`)
at the three benchmark scales without unfolding huge decimal powers:
1. QRH `θ = 7/8` at `x = 10^336, h = 10^308` (`x^(7/8) = 10^294`).
2. QRH `θ = 3/4` at `x = 10^168, h = 10^140` (`x^(3/4) = 10^126`).
3. RH `θ = 1/2` benchmark at `x = 10^168, h = 10^98` (`x^(1/2) = 10^84`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem qrh_short_interval_positivity_certs :
    shortIntervalQrh78Spec.HasGuaranteedPrime ∧
    shortIntervalQrh34Spec.HasGuaranteedPrime ∧
    shortIntervalRh12Spec.HasGuaranteedPrime ∧
    tenPowThetaCeilExp 28 qrhThresholdSevenEighths = 294 ∧
    tenPowThetaCeilExp 14 qrhThresholdThreeQuarters = 126 ∧
    tenPowThetaCeilExp 14 (QRat.mk' 1 2) = 84 := by
  have h78Ceil : tenPowThetaCeilExp 28 qrhThresholdSevenEighths = 294 := by decide
  have h34Ceil : tenPowThetaCeilExp 14 qrhThresholdThreeQuarters = 126 := by decide
  have h12Ceil : tenPowThetaCeilExp 14 (QRat.mk' 1 2) = 84 := by decide
  have h78 : shortIntervalQrh78Spec.HasGuaranteedPrime := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh78Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec336_78]
    rw [h78Ceil]
    have hEq :
        2 * (2 * 1 * 10 ^ 294 * ((29 * 28) * (29 * 28))) + 10 ^ 173 =
          2 * (1318688 * 10 ^ 294) + 10 ^ 173 := by
      have hc : 2 * 1 * 10 ^ 294 * ((29 * 28) * (29 * 28)) = 1318688 * 10 ^ 294 := by
        have hmul : 2 * 1 * ((29 * 28) * (29 * 28)) = 1318688 := by decide
        calc 2 * 1 * 10 ^ 294 * ((29 * 28) * (29 * 28))
            = (2 * 1 * ((29 * 28) * (29 * 28))) * 10 ^ 294 := by ac_rfl
          _ = 1318688 * 10 ^ 294 := by rw [hmul]
      rw [hc]
    rw [hEq]
    exact pow_ten_factor_lt 294 1318688 173 14 3000000 308
      (by decide) (by decide) (by decide) (by decide)
  have h34 : shortIntervalQrh34Spec.HasGuaranteedPrime := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh34Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec168_34]
    rw [h34Ceil]
    have hEq :
        2 * (2 * 1 * 10 ^ 126 * ((29 * 14) * (29 * 14))) + 10 ^ 89 =
          2 * (329672 * 10 ^ 126) + 10 ^ 89 := by
      have hc : 2 * 1 * 10 ^ 126 * ((29 * 14) * (29 * 14)) = 329672 * 10 ^ 126 := by
        have hmul : 2 * 1 * ((29 * 14) * (29 * 14)) = 329672 := by decide
        calc 2 * 1 * 10 ^ 126 * ((29 * 14) * (29 * 14))
            = (2 * 1 * ((29 * 14) * (29 * 14))) * 10 ^ 126 := by ac_rfl
          _ = 329672 * 10 ^ 126 := by rw [hmul]
      rw [hc]
    rw [hEq]
    exact pow_ten_factor_lt 126 329672 89 14 700000 140
      (by decide) (by decide) (by decide) (by decide)
  have h12 : shortIntervalRh12Spec.HasGuaranteedPrime := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalRh12Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec168_12]
    rw [h12Ceil]
    have hPow89 : (10 : Nat) ^ 89 = 10 ^ 5 * 10 ^ 84 := by decide
    have hEq :
        2 * (2 * 1 * 10 ^ 84 * ((29 * 14) * (29 * 14))) + 10 ^ 89 =
          759344 * 10 ^ 84 := by
      have hmul : 2 * (2 * 1 * ((29 * 14) * (29 * 14))) + 10 ^ 5 = 759344 := by decide
      calc 2 * (2 * 1 * 10 ^ 84 * ((29 * 14) * (29 * 14))) + 10 ^ 89
          = (2 * (2 * 1 * ((29 * 14) * (29 * 14)))) * 10 ^ 84 + 10 ^ 5 * 10 ^ 84 := by
            rw [hPow89]
        _ = (2 * (2 * 1 * ((29 * 14) * (29 * 14))) + 10 ^ 5) * 10 ^ 84 := by
            rw [Nat.add_mul]
        _ = 759344 * 10 ^ 84 := by rw [hmul]
    rw [hEq]
    have hLt : 759344 * 10 ^ 84 < 10 ^ 14 * 10 ^ 84 :=
      Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
    have hPow98 : (10 : Nat) ^ 14 * 10 ^ 84 = 10 ^ 98 := by decide
    omega
  exact ⟨h78, h34, h12, h78Ceil, h34Ceil, h12Ceil⟩

-- =============================================================================
-- 4. Rational Short-Interval Exponent Ladder (1/2 < 17/30 < 7/12 < 2/3 < 3/4 < 7/8 < 1)
-- =============================================================================

/-- Constructive Huxley–Hoheisel short-interval prime exponent `1 - 1/A = 1 - aDen / aNum`
over `QRat` for zero-density slope `A = aNum / aDen` (`0 < aNum`). -/
def shortIntervalDensityExponent (aNum aDen : Nat) : QRat :=
  if ha : 0 < aNum then
    QRat.ofInt 1 - QRat.mk' (aDen : Int) aNum ha
  else
    QRat.ofInt 0

/-- Consistency between `shortIntervalDensityExponent aNum aDen` and
`QuasiRiemann.primeGapExponent (QRat.mk' aNum aDen)` for positive `aNum, aDen`. -/
theorem shortIntervalDensityExponent_eqv_primeGapExponent
    (aNum aDen : Nat) (ha : 0 < aNum) (hd : 0 < aDen) :
    QRat.eqv (shortIntervalDensityExponent aNum aDen)
      (primeGapExponent (QRat.mk' (aNum : Int) aDen hd)) := by
  dsimp [shortIntervalDensityExponent, primeGapExponent, QRat.divOrZero, QRat.div, QRat.mk']
  have hNumNe : (aNum : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt ha)
  have hNumPos : (0 : Int) < (aNum : Int) := Int.natCast_pos.mpr ha
  simp only [ha, hNumNe, hNumPos, ↓reduceDIte]
  dsimp [QRat.eqv, QRat.sub, QRat.ofInt]
  simp only [Nat.one_mul, Int.one_mul]

/-- Theorem (Strict Rational Short-Interval Exponent Ladder):
Certifies in cleared-denominator `QRat` arithmetic the full hierarchy linking the
Riemann Hypothesis, modern zero-density short-interval exponents, and QRH:
`1/2 (DH) < 17/30 (Guth–Maynard) < 7/12 (Huxley) < 2/3 (Ingham) < 3/4 (QRH) < 7/8 (QRH) < 1`,
alongside exact gap differences `7/12 - 17/30 = 1/60` and `7/8 - 17/30 = 37/120`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem short_interval_density_ladder_strict :
    let eDH := shortIntervalDensityExponent 2 1
    let eGM := shortIntervalDensityExponent 30 13
    let eHux := shortIntervalDensityExponent 12 5
    let eIng := shortIntervalDensityExponent 3 1
    let θ34 := qrhThresholdThreeQuarters
    let θ78 := qrhThresholdSevenEighths
    QRat.eqv eDH (QRat.mk' 1 2) ∧
    QRat.eqv eGM (QRat.mk' 17 30) ∧
    QRat.eqv eHux (QRat.mk' 7 12) ∧
    QRat.eqv eIng (QRat.mk' 2 3) ∧
    eDH < eGM ∧
    eGM < eHux ∧
    eHux < eIng ∧
    eIng < θ34 ∧
    θ34 < θ78 ∧
    θ78 < QRat.ofInt 1 ∧
    QRat.eqv (eHux - eGM) (QRat.mk' 1 60) ∧
    QRat.eqv (θ78 - eGM) (QRat.mk' 37 120) := by
  decide

-- =============================================================================
-- 5. Fermat-Tower Arithmetic-Progression Short-Interval Envelopes
-- =============================================================================

/-- Constructive arithmetic-progression short-interval specification extending
`ShortIntervalChebyshevSpec` with modulus `q` and totient `phiQ = φ(q)`. -/
structure ApShortIntervalSpec where
  base : ShortIntervalChebyshevSpec
  q : Nat
  phiQ : Nat
  phiQ_pos : 0 < phiQ
  phiQ_lt_q : phiQ < q

/-- Arithmetic-progression prime-existence predicate:
`phiQ * (2 * errUpper + primePowerCorr) < 10 ^ hScaleExp`.
Certifies `ϑ(x + h; q, a) - ϑ(x; q, a) > 0` (hence at least one prime
`p ≡ a (mod q)` in `(x, x + h]`) for every reduced residue class `gcd(a, q) = 1`. -/
def ApShortIntervalSpec.HasGuaranteedApPrime
    (s : ApShortIntervalSpec) : Prop :=
  s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) < 10 ^ s.base.hScaleExp

instance (s : ApShortIntervalSpec) : Decidable s.HasGuaranteedApPrime :=
  inferInstanceAs
    (Decidable
      (s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) <
        10 ^ s.base.hScaleExp))

/-- Constructive AP differenced Chebyshev bridge:
if `|φ(q) * ψ(x; q, a) - x| ≤ φ(q) * errUpper` and
`|φ(q) * ψ(x + h; q, a) - (x + h)| ≤ φ(q) * errUpper`, with AP prime-power
discrepancy at most `primePowerCorr`, then `s.HasGuaranteedApPrime` forces
`0 < ϑ(x + h; q, a) - ϑ(x; q, a)`. Zero `Classical.choice`, zero `sorryAx`. -/
theorem ap_short_interval_psi_diff_bound
    (s : ApShortIntervalSpec)
    (psiApX psiApXH thetaApX thetaApXH : Int)
    (hBoundX :
      Int.natAbs ((s.phiQ : Int) * psiApX - ((10 ^ s.base.xScaleExp : Nat) : Int)) ≤
        s.phiQ * s.base.errUpper)
    (hBoundXH :
      Int.natAbs ((s.phiQ : Int) * psiApXH -
          ((10 ^ s.base.xScaleExp + 10 ^ s.base.hScaleExp : Nat) : Int)) ≤
        s.phiQ * s.base.errUpper)
    (hCorr : (psiApXH - psiApX) - (thetaApXH - thetaApX) ≤ (s.base.primePowerCorr : Int))
    (hPrime : s.HasGuaranteedApPrime) :
    (0 : Int) < thetaApXH - thetaApX := by
  have hxAbs := bounds_of_natAbs_le hBoundX
  have hxhAbs := bounds_of_natAbs_le hBoundXH
  have hMulSub :
      (s.phiQ : Int) * (psiApXH - psiApX) =
        (s.phiQ : Int) * psiApXH - (s.phiQ : Int) * psiApX :=
    Int.mul_sub _ _ _
  have hLowerPsi :
      ((10 ^ s.base.hScaleExp : Nat) : Int) -
          ((2 * (s.phiQ * s.base.errUpper) : Nat) : Int) ≤
        (s.phiQ : Int) * (psiApXH - psiApX) := by
    have hxhLo := hxhAbs.1
    have hxHi := hxAbs.2
    rw [Int.natCast_add] at hxhLo
    have hTwo :
        ((2 * (s.phiQ * s.base.errUpper) : Nat) : Int) =
          ((s.phiQ * s.base.errUpper : Nat) : Int) +
          ((s.phiQ * s.base.errUpper : Nat) : Int) := by
      omega
    rw [hMulSub, hTwo]
    omega
  have hPhiNonneg : (0 : Int) ≤ (s.phiQ : Int) := Int.natCast_nonneg s.phiQ
  have hCorrMul := Int.mul_le_mul_of_nonneg_left hCorr hPhiNonneg
  have hCorrRewrite :
      (s.phiQ : Int) * ((psiApXH - psiApX) - (thetaApXH - thetaApX)) =
        (s.phiQ : Int) * (psiApXH - psiApX) - (s.phiQ : Int) * (thetaApXH - thetaApX) :=
    Int.mul_sub _ _ _
  rw [hCorrRewrite] at hCorrMul
  have hBoundInt :
      ((s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) : Nat) : Int) <
        ((10 ^ s.base.hScaleExp : Nat) : Int) :=
    Int.ofNat_lt.mpr hPrime
  have hMulBoundCast :
      ((s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) : Nat) : Int) =
        ((2 * (s.phiQ * s.base.errUpper) : Nat) : Int) +
          (s.phiQ : Int) * (s.base.primePowerCorr : Int) := by
    have hNat :
        s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) =
          2 * (s.phiQ * s.base.errUpper) + s.phiQ * s.base.primePowerCorr := by
      rw [Nat.mul_add]
      have hComm : s.phiQ * (2 * s.base.errUpper) = 2 * (s.phiQ * s.base.errUpper) := by
        ac_rfl
      rw [hComm]
    rw [hNat, Int.natCast_add, Int.natCast_mul, Int.natCast_mul]
    rfl
  have hThetaMulPos : (0 : Int) < (s.phiQ : Int) * (thetaApXH - thetaApX) := by
    rw [hMulBoundCast] at hBoundInt
    omega
  by_cases hPos : (0 : Int) < thetaApXH - thetaApX
  · exact hPos
  · exfalso
    have hNonpos : thetaApXH - thetaApX ≤ 0 := Int.not_lt.mp hPos
    have hProdNonpos : (s.phiQ : Int) * (thetaApXH - thetaApX) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos hPhiNonneg hNonpos
    omega

/-- AP short-interval spec at `(x = 10^336, h = 10^308, θ = 7/8)` for prime modulus `q ≥ 2`. -/
def fermatAp78Spec (q : Nat) (hq : 2 ≤ q) : ApShortIntervalSpec :=
  ⟨shortIntervalQrh78Spec, q, q - 1, by omega, by omega⟩

/-- AP short-interval spec at `(x = 10^168, h = 10^140, θ = 3/4)` for prime modulus `q ≥ 2`. -/
def fermatAp34Spec (q : Nat) (hq : 2 ≤ q) : ApShortIntervalSpec :=
  ⟨shortIntervalQrh34Spec, q, q - 1, by omega, by omega⟩

private theorem ap_pow_ten_factor_lt
    (phiQ e c pExp gap coeff hExp : Nat)
    (hPhi : phiQ < 10 ^ 5)
    (hp : pExp ≤ e)
    (hc : e + gap = hExp)
    (hCoeff : 2 * c + 1 < coeff)
    (hGap : 10 ^ 5 * coeff < 10 ^ gap) :
    phiQ * (2 * (c * 10 ^ e) + 10 ^ pExp) < 10 ^ hExp := by
  have hInner : 2 * (c * 10 ^ e) + 10 ^ pExp < coeff * 10 ^ e := by
    have hpLe : 10 ^ pExp ≤ 10 ^ e := Nat.pow_le_pow_right (by decide) hp
    have h1 : 2 * (c * 10 ^ e) + 10 ^ pExp ≤ (2 * c + 1) * 10 ^ e := by
      have hmul : 2 * (c * 10 ^ e) + 10 ^ e = (2 * c + 1) * 10 ^ e := by
        rw [Nat.add_mul, Nat.one_mul]
        ac_rfl
      omega
    have h2 : (2 * c + 1) * 10 ^ e < coeff * 10 ^ e :=
      Nat.mul_lt_mul_of_pos_right hCoeff (Nat.pow_pos (by decide))
    omega
  have hScaled :
      phiQ * (2 * (c * 10 ^ e) + 10 ^ pExp) < 10 ^ 5 * (coeff * 10 ^ e) := by
    have hPos : 0 < coeff * 10 ^ e :=
      Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    exact Nat.mul_lt_mul_of_lt_of_le' hPhi (Nat.le_of_lt hInner)
      (Nat.add_pos_right _ (Nat.pow_pos (by decide)))
  have hGapMul : 10 ^ 5 * (coeff * 10 ^ e) < 10 ^ gap * 10 ^ e := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hGap (Nat.pow_pos (by decide))
  have hExpEq : 10 ^ gap * 10 ^ e = 10 ^ hExp := by
    rw [← Nat.pow_add, Nat.add_comm gap e, hc]
  omega

set_option exponentiation.threshold 2000 in
/-- Theorem (Fermat-Tower AP Short-Interval Prime Certificates):
Connects `EulerFactorNonVanishing.fermatTowerPrimes` (`{5, 17, 257, 65537}`) and
`EulerFactorNonVanishing.FermatTowerStripCert` (`fermat_tower_euler_product_strip_certs`)
to `ApShortIntervalSpec`, certifying `HasGuaranteedApPrime` (every reduced residue class
`a mod q` contains a prime in `(x, x + h]`) for all four Fermat primes (`φ(65537) = 65536 < 10^5`)
under both `θ = 7/8` (`x = 10^336, h = 10^308`) and `θ = 3/4` (`x = 10^168, h = 10^140`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermat_tower_ap_short_interval_certs :
    EulerFactorNonVanishing.fermatTowerPrimes = [5, 17, 257, 65537] ∧
    (EulerFactorNonVanishing.fermatTowerPrimes.map (· - 1)).prod = 2 ^ 30 ∧
    EulerFactorNonVanishing.FermatTowerStripCert ∧
    ((fermatAp78Spec 5 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp78Spec 17 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp78Spec 257 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp78Spec 65537 (by decide)).HasGuaranteedApPrime) ∧
    ((fermatAp34Spec 5 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp34Spec 17 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp34Spec 257 (by decide)).HasGuaranteedApPrime ∧
     (fermatAp34Spec 65537 (by decide)).HasGuaranteedApPrime) := by
  have h78Ceil : tenPowThetaCeilExp 28 qrhThresholdSevenEighths = 294 := by decide
  have h34Ceil : tenPowThetaCeilExp 14 qrhThresholdThreeQuarters = 126 := by decide
  have h78Base :
      2 * shortIntervalQrh78Spec.errUpper + shortIntervalQrh78Spec.primePowerCorr =
        2 * (1318688 * 10 ^ 294) + 10 ^ 173 := by
    dsimp [shortIntervalQrh78Spec, qrhRemainderBoundAtTwoTenPow, chebyshevSpec336_78]
    rw [h78Ceil]
  have h34Base :
      2 * shortIntervalQrh34Spec.errUpper + shortIntervalQrh34Spec.primePowerCorr =
        2 * (329672 * 10 ^ 126) + 10 ^ 89 := by
    dsimp [shortIntervalQrh34Spec, qrhRemainderBoundAtTwoTenPow, chebyshevSpec168_34]
    rw [h34Ceil]
  have mk78 : ∀ q (hq : 2 ≤ q), q - 1 < 10 ^ 5 →
      (fermatAp78Spec q hq).HasGuaranteedApPrime := by
    intro q hq hPhi
    dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatAp78Spec]
    rw [h78Base]
    exact ap_pow_ten_factor_lt (q - 1) 294 1318688 173 14 3000000 308
      hPhi (by decide) (by decide) (by decide) (by decide)
  have mk34 : ∀ q (hq : 2 ≤ q), q - 1 < 10 ^ 5 →
      (fermatAp34Spec q hq).HasGuaranteedApPrime := by
    intro q hq hPhi
    dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatAp34Spec]
    rw [h34Base]
    exact ap_pow_ten_factor_lt (q - 1) 126 329672 89 14 700000 140
      hPhi (by decide) (by decide) (by decide) (by decide)
  exact ⟨rfl, rfl, EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs,
    ⟨mk78 5 (by decide) (by decide), mk78 17 (by decide) (by decide),
     mk78 257 (by decide) (by decide), mk78 65537 (by decide) (by decide)⟩,
    ⟨mk34 5 (by decide) (by decide), mk34 17 (by decide) (by decide),
     mk34 257 (by decide) (by decide), mk34 65537 (by decide) (by decide)⟩⟩

-- =============================================================================
-- 6. Sub-3/4 QRH Threshold Ladder (2/3, 5/8, 9/16) & Minimal Positivity Scales
-- =============================================================================

/-- Sub-3/4 QRH threshold rung `θ = 2/3`. -/
def qrhThresholdTwoThirds : QRat := QRat.mk' 2 3

/-- Sub-3/4 QRH threshold rung `θ = 5/8`. -/
def qrhThresholdFiveEighths : QRat := QRat.mk' 5 8

/-- Sub-3/4 QRH threshold rung `θ = 9/16`. -/
def qrhThresholdNineSixteenths : QRat := QRat.mk' 9 16

/-- Chebyshev spec at `x = 10^24` (`k = 2`) for `θ = 2/3`. -/
def chebyshevSpec24_23 : ChebyshevRemainderSpec :=
  ⟨2, by decide, 1, by decide, qrhThresholdTwoThirds, by decide, by decide⟩

/-- Chebyshev spec at `x = 10^24` (`k = 2`) for `θ = 5/8`. -/
def chebyshevSpec24_58 : ChebyshevRemainderSpec :=
  ⟨2, by decide, 1, by decide, qrhThresholdFiveEighths, by decide, by decide⟩

/-- Chebyshev spec at `x = 10^48` (`k = 4`) for `θ = 9/16`. -/
def chebyshevSpec48_916 : ChebyshevRemainderSpec :=
  ⟨4, by decide, 1, by decide, qrhThresholdNineSixteenths, by decide, by decide⟩

/-- Short-interval spec at minimal decimal scale `(x = 10^24, h = 10^21)` for `θ = 2/3`
(`x^(2/3) = 10^16`, `primePowerCorr = 10^15 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalQrh23Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 2
    thetaDen := 3
    xScaleExp := 24
    hScaleExp := 21
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec24_23
    primePowerCorr := 10 ^ 15
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Short-interval spec at minimal decimal scale `(x = 10^24, h = 10^20)` for `θ = 5/8`
(`x^(5/8) = 10^15`, `primePowerCorr = 10^15 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalQrh58Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 5
    thetaDen := 8
    xScaleExp := 24
    hScaleExp := 20
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec24_58
    primePowerCorr := 10 ^ 15
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Short-interval spec at minimal decimal scale `(x = 10^48, h = 10^32)` for `θ = 9/16`
(`x^(9/16) = 10^27`, `primePowerCorr = 10^27 > 2 * sqrt(2x) * ln(2x)`). -/
def shortIntervalQrh916Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 9
    thetaDen := 16
    xScaleExp := 48
    hScaleExp := 32
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec48_916
    primePowerCorr := 10 ^ 27
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Theorem (Sub-3/4 QRH Ladder & Minimal Positivity Scales):
1. Certifies the extended strict rational ladder
   `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` and its reversed Chebyshev remainder gap chain
   `0 < 1/8 < 1/4 < 1/3 < 3/8 < 7/16 < 1/2`.
2. Certifies `HasGuaranteedPrime` at the minimal decimal scales `(xScaleExp, hScaleExp)`:
   - `θ = 2/3`: `(24, 21)` with `x^(2/3) = 10^16` (and `10^20 < 2 * err + corr < 10^21`),
   - `θ = 5/8`: `(24, 20)` with `x^(5/8) = 10^15` (and `10^19 < 2 * err + corr < 10^20`),
   - `θ = 9/16`: `(48, 32)` with `x^(9/16) = 10^27` (and `10^31 < 2 * err + corr < 10^32`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem sub_three_quarters_qrh_ladder_certs :
    let θ12 := QRat.mk' 1 2
    let θ916 := qrhThresholdNineSixteenths
    let θ58 := qrhThresholdFiveEighths
    let θ23 := qrhThresholdTwoThirds
    let θ34 := qrhThresholdThreeQuarters
    let θ78 := qrhThresholdSevenEighths
    (θ12 < θ916 ∧ θ916 < θ58 ∧ θ58 < θ23 ∧
     θ23 < θ34 ∧ θ34 < θ78 ∧ θ78 < QRat.ofInt 1) ∧
    (QRat.ofInt 0 < chebyshevGap θ78 ∧
     chebyshevGap θ78 < chebyshevGap θ34 ∧
     chebyshevGap θ34 < chebyshevGap θ23 ∧
     chebyshevGap θ23 < chebyshevGap θ58 ∧
     chebyshevGap θ58 < chebyshevGap θ916 ∧
     chebyshevGap θ916 < chebyshevGap θ12) ∧
    (tenPowThetaCeilExp 2 θ23 = 16 ∧
     tenPowThetaCeilExp 2 θ58 = 15 ∧
     tenPowThetaCeilExp 4 θ916 = 27) ∧
    (shortIntervalQrh23Spec.HasGuaranteedPrime ∧
     10 ^ 20 < 2 * shortIntervalQrh23Spec.errUpper + shortIntervalQrh23Spec.primePowerCorr) ∧
    (shortIntervalQrh58Spec.HasGuaranteedPrime ∧
     10 ^ 19 < 2 * shortIntervalQrh58Spec.errUpper + shortIntervalQrh58Spec.primePowerCorr) ∧
    (shortIntervalQrh916Spec.HasGuaranteedPrime ∧
     10 ^ 31 < 2 * shortIntervalQrh916Spec.errUpper + shortIntervalQrh916Spec.primePowerCorr) := by
  have hLadder :
      QRat.mk' 1 2 < qrhThresholdNineSixteenths ∧
      qrhThresholdNineSixteenths < qrhThresholdFiveEighths ∧
      qrhThresholdFiveEighths < qrhThresholdTwoThirds ∧
      qrhThresholdTwoThirds < qrhThresholdThreeQuarters ∧
      qrhThresholdThreeQuarters < qrhThresholdSevenEighths ∧
      qrhThresholdSevenEighths < QRat.ofInt 1 := by decide
  have hGaps :
      QRat.ofInt 0 < chebyshevGap qrhThresholdSevenEighths ∧
      chebyshevGap qrhThresholdSevenEighths < chebyshevGap qrhThresholdThreeQuarters ∧
      chebyshevGap qrhThresholdThreeQuarters < chebyshevGap qrhThresholdTwoThirds ∧
      chebyshevGap qrhThresholdTwoThirds < chebyshevGap qrhThresholdFiveEighths ∧
      chebyshevGap qrhThresholdFiveEighths < chebyshevGap qrhThresholdNineSixteenths ∧
      chebyshevGap qrhThresholdNineSixteenths < chebyshevGap (QRat.mk' 1 2) := by decide
  have h23Ceil : tenPowThetaCeilExp 2 qrhThresholdTwoThirds = 16 := by decide
  have h58Ceil : tenPowThetaCeilExp 2 qrhThresholdFiveEighths = 15 := by decide
  have h916Ceil : tenPowThetaCeilExp 4 qrhThresholdNineSixteenths = 27 := by decide
  have h23 :
      shortIntervalQrh23Spec.HasGuaranteedPrime ∧
      10 ^ 20 < 2 * shortIntervalQrh23Spec.errUpper + shortIntervalQrh23Spec.primePowerCorr := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh23Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec24_23]
    rw [h23Ceil]
    constructor <;> decide
  have h58 :
      shortIntervalQrh58Spec.HasGuaranteedPrime ∧
      10 ^ 19 < 2 * shortIntervalQrh58Spec.errUpper + shortIntervalQrh58Spec.primePowerCorr := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh58Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec24_58]
    rw [h58Ceil]
    constructor <;> decide
  have h916 :
      shortIntervalQrh916Spec.HasGuaranteedPrime ∧
      10 ^ 31 < 2 * shortIntervalQrh916Spec.errUpper + shortIntervalQrh916Spec.primePowerCorr := by
    dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalQrh916Spec,
      qrhRemainderBoundAtTwoTenPow, chebyshevSpec48_916]
    rw [h916Ceil]
    have hPow27 : 2 * (2 * 1 * 10 ^ 27 * ((29 * 4) * (29 * 4))) + 10 ^ 27 =
        53825 * 10 ^ 27 := by
      have hc : 2 * (2 * 1 * ((29 * 4) * (29 * 4))) + 1 = 53825 := by decide
      calc 2 * (2 * 1 * 10 ^ 27 * ((29 * 4) * (29 * 4))) + 10 ^ 27
          = (2 * (2 * 1 * ((29 * 4) * (29 * 4)))) * 10 ^ 27 + 1 * 10 ^ 27 := by
            rw [Nat.one_mul]
        _ = (2 * (2 * 1 * ((29 * 4) * (29 * 4))) + 1) * 10 ^ 27 := by rw [Nat.add_mul]
        _ = 53825 * 10 ^ 27 := by rw [hc]
    rw [hPow27]
    constructor
    · have hLt : 53825 * 10 ^ 27 < 10 ^ 5 * 10 ^ 27 :=
        Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      have hPow32 : (10 : Nat) ^ 5 * 10 ^ 27 = 10 ^ 32 := by decide
      omega
    · have hGt : 10 ^ 4 * 10 ^ 27 < 53825 * 10 ^ 27 :=
        Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
      have hPow31 : (10 : Nat) ^ 4 * 10 ^ 27 = 10 ^ 31 := by decide
      omega
  exact ⟨hLadder, hGaps, ⟨h23Ceil, h58Ceil, h916Ceil⟩, h23, h58, h916⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean
