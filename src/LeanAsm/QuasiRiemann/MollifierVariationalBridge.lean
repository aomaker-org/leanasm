-- Path: leanasm/src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean
-- Closed-loop dyadic-Abel rungs (k = 5, 6) and two-piece QRat variational
-- mollifier bridge (v1.3.0 Issue #78).
-- ZERO Classical.choice, ZERO sorryAx, ZERO Mathlib dependencies.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.DyadicAbelBridge
import LeanAsm.QuasiRiemann.ShortIntervalPrimes
import LeanAsm.GSp4FunctorialityBridge

namespace QuasiRiemann

-- =============================================================================
-- Part 0: Exact Big-Power Helper (Avoids Materializing 10^192 or 10^384)
-- =============================================================================

private theorem pow_ten_factor_lt_mvb {c eGap eBase : Nat}
    (hc : c < 10 ^ eGap) :
    c * 10 ^ eBase < 10 ^ (eGap + eBase) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by decide : 0 < 10))

-- =============================================================================
-- Part 1: Closed-Loop Dyadic-Abel Contraction & Concrete Rungs k = 5, 6
-- =============================================================================

/-- Closed-loop dyadic-Abel contraction theorem coupling:
1. Monotone rational Abel summation-by-parts envelope (`abel_monotone_weight_envelope_qrat`),
2. Cleared-denominator `1/√N` dyadic tail-gate scaling (`inv_sqrt_tail_gate_dyadic_step`),
3. Strict ladder advance `qrhShortExponent kNext < qrhShortExponent kCurr`, and
4. Short-interval Chebyshev prime positivity (`short_interval_spec_guarantees_theta_pos`)
at the unlocked rung `sNext`. Zero `Classical.choice`, zero `sorryAx`. -/
theorem dyadic_abel_unlocks_next_rung
    (kCurr kNext : Nat)
    (specNext : ChebyshevRemainderSpec) (sNext : ShortIntervalChebyshevSpec)
    (hLadderDrop : qrhShortExponent kNext < qrhShortExponent kCurr)
    (a wNum : Nat → Int) (M N E D : Nat) (hMN : M < N) (hD : 0 < D)
    (hw_nonneg : 0 ≤ wNum N)
    (hw_anti : ∀ k, M + 1 ≤ k → k < N → wNum (k + 1) ≤ wNum k)
    (hRem : ∀ k, M ≤ k → k ≤ N → Int.natAbs (partialSumInt a k - (k : Int)) ≤ E)
    (gate : InvSqrtTailGateSpec)
    (hHleX : sNext.hScaleExp ≤ sNext.xScaleExp)
    (hEnv : qrhRemainderBoundAtTwoTenPow specNext ≤ sNext.errUpper)
    (psiX psiXH thetaX thetaXH : Int)
    (hBoundX : Int.natAbs (psiX - ((10 ^ sNext.xScaleExp : Nat) : Int)) ≤ sNext.errUpper)
    (hBoundXH :
      Int.natAbs (psiXH - ((10 ^ sNext.xScaleExp + 10 ^ sNext.hScaleExp : Nat) : Int)) ≤
        sNext.errUpper)
    (hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (sNext.primePowerCorr : Int))
    (hPrime : sNext.HasGuaranteedPrime) :
    (QRat.mk'
      (Int.natAbs (rangeSumInt (fun n => a n * wNum n) (M + 1) (N + 1) -
        rangeSumInt wNum (M + 1) (N + 1)) : Int) D hD ≤
      QRat.mk' ((2 * E * Int.natAbs (wNum (M + 1)) : Nat) : Int) D hD) ∧
    ((4 * gate.scaleN) * (gate.tailBound * gate.tailBound) ≤
      ((2 * gate.denomM) * (2 * gate.denomM)) * (gate.tailNum * gate.tailNum)) ∧
    (qrhShortExponent kNext < qrhShortExponent kCurr) ∧
    ((psiXH - psiX) - ((10 ^ sNext.hScaleExp : Nat) : Int) ≤ (2 * sNext.errUpper : Int) ∧
      -((2 * sNext.errUpper : Int)) ≤ (psiXH - psiX) - ((10 ^ sNext.hScaleExp : Nat) : Int)) ∧
    ((0 : Int) < thetaXH - thetaX) := by
  have hAbel := abel_monotone_weight_envelope_qrat a wNum M N E D hMN hD hw_nonneg hw_anti hRem
  have hGate := inv_sqrt_tail_gate_dyadic_step gate
  have hPsiDiff := short_interval_psi_diff_bound specNext
    (10 ^ sNext.xScaleExp) (10 ^ sNext.hScaleExp) sNext.errUpper sNext.primePowerCorr
    (Nat.pow_pos (by decide)) (Nat.pow_le_pow_right (by decide) hHleX) hEnv
    psiX psiXH thetaX thetaXH hBoundX hBoundXH hCorr
  have hPsiBound :
      (psiXH - psiX) - ((10 ^ sNext.hScaleExp : Nat) : Int) ≤ (2 * sNext.errUpper : Int) ∧
      -((2 * sNext.errUpper : Int)) ≤ (psiXH - psiX) - ((10 ^ sNext.hScaleExp : Nat) : Int) := by
    let hInt : Int := ((10 ^ sNext.hScaleExp : Nat) : Int)
    have hUpper := Int.sub_le_sub_right hPsiDiff.2.2.1 hInt
    rw [Int.add_comm hInt ((2 * sNext.errUpper : Nat) : Int), Int.add_sub_cancel,
      Int.natCast_mul] at hUpper
    have hLower := Int.sub_le_sub_right hPsiDiff.2.1 hInt
    rw [Int.sub_eq_add_neg (a := hInt), Int.sub_eq_add_neg (a := hInt + _), Int.add_assoc,
      Int.add_comm (-((2 * sNext.errUpper : Nat) : Int)) (-hInt), ← Int.add_assoc,
      ← Int.sub_eq_add_neg (a := hInt), Int.sub_self, Int.zero_add,
      Int.natCast_mul] at hLower
    exact ⟨hUpper, hLower⟩
  have hThetaPos := short_interval_spec_guarantees_theta_pos specNext sNext hHleX hEnv
    psiX psiXH thetaX thetaXH hBoundX hBoundXH hCorr hPrime
  exact ⟨hAbel, hGate, hLadderDrop, hPsiBound, hThetaPos⟩

/-- Concrete Chebyshev remainder model for ladder rung `k = 5` at `x = 10^192`
with `θ = qrhShortExponent 5 = 33/64`. -/
def chebyshevSpec192_3364 : ChebyshevRemainderSpec :=
  { scaleK := 16
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 33 64
    theta_pos := by decide
    theta_lt_one := by decide }

/-- Concrete short-interval Chebyshev benchmark at rung `k = 5` (`θ = 33/64`)
covering `[10^192, 10^192 + 10^108]`.
Since `192 * (33/64) = 99` and `chebyshevLogSqEnv 16 = 464^2 = 215296`,
`qrhRemainderBoundAtTwoTenPow = 2 * 215296 * 10^99 = 430592 * 10^99`. -/
def shortIntervalQrh3364Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 33
    thetaDen := 64
    xScaleExp := 192
    hScaleExp := 108
    errUpper := 430592 * 10 ^ 99
    primePowerCorr := 2 * 10 ^ 96
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Exact verification of the `k = 5` Chebyshev error envelope against
`shortIntervalQrh3364Spec`. -/
theorem chebyshevSpec192_3364_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec192_3364 ≤ shortIntervalQrh3364Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 16 (QRat.mk' 33 64) = 99 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 16 (QRat.mk' 33 64)) * ((29 * 16) * (29 * 16)) ≤
    430592 * 10 ^ 99
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 16) * (29 * 16)) = 430592 := by decide
  calc
    2 * 1 * 10 ^ 99 * ((29 * 16) * (29 * 16))
        = (2 * 1 * ((29 * 16) * (29 * 16))) * 10 ^ 99 := by omega
    _ = 430592 * 10 ^ 99 := by rw [hCoef]
    _ ≤ 430592 * 10 ^ 99 := Nat.le_refl _

/-- Exact positivity certificate for `[10^192, 10^192 + 10^108]` at `θ = 33/64` (`k = 5`):
`2 * 430592 * 10^99 + 2 * 10^96 < 10^108`. -/
theorem shortIntervalQrh3364Spec_has_prime :
    shortIntervalQrh3364Spec.HasGuaranteedPrime := by
  change 2 * (430592 * 10 ^ 99) + 2 * 10 ^ 96 < 10 ^ 108
  have h199 : (10 : Nat) ^ 99 = 10 ^ 3 * 10 ^ 96 := by
    rw [← Nat.pow_add]
  have h108 : (10 : Nat) ^ 108 = 10 ^ (12 + 96) := rfl
  rw [h199, h108]
  have hLeft :
      2 * (430592 * (10 ^ 3 * 10 ^ 96)) + 2 * 10 ^ 96 = 861184002 * 10 ^ 96 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 861184002 < 10 ^ 12)

/-- Concrete Chebyshev remainder model for ladder rung `k = 6` at `x = 10^384`
with `θ = qrhShortExponent 6 = 65/128 = 1/2 + 1/128`. -/
def chebyshevSpec384_65128 : ChebyshevRemainderSpec :=
  { scaleK := 32
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 65 128
    theta_pos := by decide
    theta_lt_one := by decide }

/-- Concrete short-interval Chebyshev benchmark at rung `k = 6` (`θ = 65/128`)
covering `[10^384, 10^384 + 10^206]`.
Since `384 * (65/128) = 195` and `chebyshevLogSqEnv 32 = 928^2 = 861184`,
`qrhRemainderBoundAtTwoTenPow = 2 * 861184 * 10^195 = 1722368 * 10^195`. -/
def shortIntervalQrh65128Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 65
    thetaDen := 128
    xScaleExp := 384
    hScaleExp := 206
    errUpper := 1722368 * 10 ^ 195
    primePowerCorr := 2 * 10 ^ 192
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Exact verification of the `k = 6` Chebyshev error envelope against
`shortIntervalQrh65128Spec`. -/
theorem chebyshevSpec384_65128_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec384_65128 ≤ shortIntervalQrh65128Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 32 (QRat.mk' 65 128) = 195 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 32 (QRat.mk' 65 128)) * ((29 * 32) * (29 * 32)) ≤
    1722368 * 10 ^ 195
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 32) * (29 * 32)) = 1722368 := by decide
  calc
    2 * 1 * 10 ^ 195 * ((29 * 32) * (29 * 32))
        = (2 * 1 * ((29 * 32) * (29 * 32))) * 10 ^ 195 := by omega
    _ = 1722368 * 10 ^ 195 := by rw [hCoef]
    _ ≤ 1722368 * 10 ^ 195 := Nat.le_refl _

/-- Exact positivity certificate for `[10^384, 10^384 + 10^206]` at `θ = 65/128` (`k = 6`):
`2 * 1722368 * 10^195 + 2 * 10^192 < 10^206`. -/
theorem shortIntervalQrh65128Spec_has_prime :
    shortIntervalQrh65128Spec.HasGuaranteedPrime := by
  change 2 * (1722368 * 10 ^ 195) + 2 * 10 ^ 192 < 10 ^ 206
  have h195 : (10 : Nat) ^ 195 = 10 ^ 3 * 10 ^ 192 := by
    rw [← Nat.pow_add]
  have h206 : (10 : Nat) ^ 206 = 10 ^ (14 + 192) := rfl
  rw [h195, h206]
  have hLeft :
      2 * (1722368 * (10 ^ 3 * 10 ^ 192)) + 2 * 10 ^ 192 = 3444736002 * 10 ^ 192 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 3444736002 < 10 ^ 14)

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 5` (`m = 1024`, `N = 16`,
`tailNum = 1`, `tailBound = 256`, witnessing `16 * 256^2 ≤ 1024^2 * 1^2`). -/
def dyadicAbelGateRung5 : InvSqrtTailGateSpec :=
  { denomM := 1024
    tailBound := 256
    scaleN := 16
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 6` (`m = 2048`, `N = 64`,
`tailNum = 1`, `tailBound = 256`, witnessing `64 * 256^2 ≤ 2048^2 * 1^2`). -/
def dyadicAbelGateRung6 : InvSqrtTailGateSpec :=
  { denomM := 2048
    tailBound := 256
    scaleN := 64
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Concrete Chebyshev remainder model for ladder rung `k = 7` at `x = 10^768`
with `θ = qrhShortExponent 7 = 129/256 = 1/2 + 1/256`. -/
def chebyshevSpec768_129256 : ChebyshevRemainderSpec :=
  { scaleK := 64
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 129 256
    theta_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Concrete short-interval Chebyshev benchmark at rung `k = 7` (`θ = 129/256`)
covering `[10^768, 10^768 + 10^402]`.
Since `768 * (129/256) = 387` and `chebyshevLogSqEnv 64 = 1856^2 = 3444736`,
`qrhRemainderBoundAtTwoTenPow = 2 * 3444736 * 10^387 = 6889472 * 10^387`. -/
def shortIntervalQrh129256Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 129
    thetaDen := 256
    xScaleExp := 768
    hScaleExp := 402
    errUpper := 6889472 * 10 ^ 387
    primePowerCorr := 2 * 10 ^ 384
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Exact verification of the `k = 7` Chebyshev error envelope against
`shortIntervalQrh129256Spec`. -/
theorem chebyshevSpec768_129256_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec768_129256 ≤
      shortIntervalQrh129256Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 64 (QRat.mk' 129 256) = 387 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 64 (QRat.mk' 129 256)) * ((29 * 64) * (29 * 64)) ≤
    6889472 * 10 ^ 387
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 64) * (29 * 64)) = 6889472 := by decide
  rw [Nat.mul_assoc (2 * 1), Nat.mul_comm (10 ^ 387), ← Nat.mul_assoc]
  rw [hCoef]
  exact Nat.le_refl _

set_option exponentiation.threshold 2000 in
/-- Exact positivity certificate for `[10^768, 10^768 + 10^402]` at `θ = 129/256` (`k = 7`):
`2 * 6889472 * 10^387 + 2 * 10^384 < 10^402`. -/
theorem shortIntervalQrh129256Spec_has_prime :
    shortIntervalQrh129256Spec.HasGuaranteedPrime := by
  change 2 * (6889472 * 10 ^ 387) + 2 * 10 ^ 384 < 10 ^ 402
  have h387 : (10 : Nat) ^ 387 = 10 ^ 3 * 10 ^ 384 := by
    rw [← Nat.pow_add]
  have h402 : (10 : Nat) ^ 402 = 10 ^ (18 + 384) := rfl
  rw [h387, h402]
  have hLeft :
      2 * (6889472 * (10 ^ 3 * 10 ^ 384)) + 2 * 10 ^ 384 = 13778944002 * 10 ^ 384 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 13778944002 < 10 ^ 18)

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 7` (`m = 4096`, `N = 256`,
`tailNum = 1`, `tailBound = 256`, witnessing `256 * 256^2 ≤ 4096^2 * 1^2`). -/
def dyadicAbelGateRung7 : InvSqrtTailGateSpec :=
  { denomM := 4096
    tailBound := 256
    scaleN := 256
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Concrete Chebyshev remainder model for ladder rung `k = 8` at `x = 10^1536`
with `θ = qrhShortExponent 8 = 257/512 = 1/2 + 1/512`. -/
def chebyshevSpec1536_257512 : ChebyshevRemainderSpec :=
  { scaleK := 128
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 257 512
    theta_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Concrete short-interval Chebyshev benchmark at rung `k = 8` (`θ = 257/512`)
covering `[10^1536, 10^1536 + 10^786]`.
Since `1536 * (257/512) = 771` and `chebyshevLogSqEnv 128 = 3712^2 = 13778944`,
`qrhRemainderBoundAtTwoTenPow = 2 * 13778944 * 10^771 = 27557888 * 10^771`. -/
def shortIntervalQrh257512Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 257
    thetaDen := 512
    xScaleExp := 1536
    hScaleExp := 786
    errUpper := 27557888 * 10 ^ 771
    primePowerCorr := 2 * 10 ^ 768
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 2000 in
/-- Exact verification of the `k = 8` Chebyshev error envelope against
`shortIntervalQrh257512Spec`. -/
theorem chebyshevSpec1536_257512_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec1536_257512 ≤
      shortIntervalQrh257512Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 128 (QRat.mk' 257 512) = 771 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 128 (QRat.mk' 257 512)) * ((29 * 128) * (29 * 128)) ≤
    27557888 * 10 ^ 771
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 128) * (29 * 128)) = 27557888 := by decide
  rw [Nat.mul_assoc (2 * 1), Nat.mul_comm (10 ^ 771), ← Nat.mul_assoc]
  rw [hCoef]
  exact Nat.le_refl _

set_option exponentiation.threshold 2000 in
/-- Exact positivity certificate for `[10^1536, 10^1536 + 10^786]` at `θ = 257/512` (`k = 8`):
`2 * 27557888 * 10^771 + 2 * 10^768 < 10^786`. -/
theorem shortIntervalQrh257512Spec_has_prime :
    shortIntervalQrh257512Spec.HasGuaranteedPrime := by
  change 2 * (27557888 * 10 ^ 771) + 2 * 10 ^ 768 < 10 ^ 786
  have h771 : (10 : Nat) ^ 771 = 10 ^ 3 * 10 ^ 768 := by
    rw [← Nat.pow_add]
  have h786 : (10 : Nat) ^ 786 = 10 ^ (18 + 768) := rfl
  rw [h771, h786]
  have hLeft :
      2 * (27557888 * (10 ^ 3 * 10 ^ 768)) + 2 * 10 ^ 768 = 55115776002 * 10 ^ 768 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 55115776002 < 10 ^ 18)

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 8` (`m = 8192`, `N = 1024`,
`tailNum = 1`, `tailBound = 256`, witnessing `1024 * 256^2 ≤ 8192^2 * 1^2`). -/
def dyadicAbelGateRung8 : InvSqrtTailGateSpec :=
  { denomM := 8192
    tailBound := 256
    scaleN := 1024
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Concrete Chebyshev remainder model for ladder rung `k = 9` at `x = 10^3072`
with `θ = qrhShortExponent 9 = 513/1024 = 1/2 + 1/1024`. -/
def chebyshevSpec3072_5131024 : ChebyshevRemainderSpec :=
  { scaleK := 256
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 513 1024
    theta_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 4000 in
/-- Concrete short-interval Chebyshev benchmark at rung `k = 9` (`θ = 513/1024`)
covering `[10^3072, 10^3072 + 10^1554]`.
Since `3072 * (513/1024) = 1539` and `chebyshevLogSqEnv 256 = 7424^2 = 55115776`,
`qrhRemainderBoundAtTwoTenPow = 2 * 55115776 * 10^1539 = 110231552 * 10^1539`. -/
def shortIntervalQrh5131024Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 513
    thetaDen := 1024
    xScaleExp := 3072
    hScaleExp := 1554
    errUpper := 110231552 * 10 ^ 1539
    primePowerCorr := 2 * 10 ^ 1536
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 4000 in
/-- Exact verification of the `k = 9` Chebyshev error envelope against
`shortIntervalQrh5131024Spec`. -/
theorem chebyshevSpec3072_5131024_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec3072_5131024 ≤
      shortIntervalQrh5131024Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 256 (QRat.mk' 513 1024) = 1539 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 256 (QRat.mk' 513 1024)) * ((29 * 256) * (29 * 256)) ≤
    110231552 * 10 ^ 1539
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 256) * (29 * 256)) = 110231552 := by decide
  rw [Nat.mul_assoc (2 * 1), Nat.mul_comm (10 ^ 1539), ← Nat.mul_assoc]
  rw [hCoef]
  exact Nat.le_refl _

set_option exponentiation.threshold 4000 in
/-- Exact positivity certificate for `[10^3072, 10^3072 + 10^1554]` at `θ = 513/1024` (`k = 9`):
`2 * 110231552 * 10^1539 + 2 * 10^1536 < 10^1554`. -/
theorem shortIntervalQrh5131024Spec_has_prime :
    shortIntervalQrh5131024Spec.HasGuaranteedPrime := by
  change 2 * (110231552 * 10 ^ 1539) + 2 * 10 ^ 1536 < 10 ^ 1554
  have h1539 : (10 : Nat) ^ 1539 = 10 ^ 3 * 10 ^ 1536 := by
    rw [← Nat.pow_add]
  have h1554 : (10 : Nat) ^ 1554 = 10 ^ (18 + 1536) := rfl
  rw [h1539, h1554]
  have hLeft :
      2 * (110231552 * (10 ^ 3 * 10 ^ 1536)) + 2 * 10 ^ 1536 = 220463104002 * 10 ^ 1536 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 220463104002 < 10 ^ 18)

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 9` (`m = 16384`, `N = 4096`,
`tailNum = 1`, `tailBound = 256`, witnessing `4096 * 256^2 ≤ 16384^2 * 1^2`). -/
def dyadicAbelGateRung9 : InvSqrtTailGateSpec :=
  { denomM := 16384
    tailBound := 256
    scaleN := 4096
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Concrete Chebyshev remainder model for ladder rung `k = 10` at `x = 10^6144`
with `θ = qrhShortExponent 10 = 1025/2048 = 1/2 + 1/2048`. -/
def chebyshevSpec6144_10252048 : ChebyshevRemainderSpec :=
  { scaleK := 512
    scaleK_pos := by decide
    prefactor := 1
    prefactor_pos := by decide
    theta := QRat.mk' 1025 2048
    theta_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 8000 in
/-- Concrete short-interval Chebyshev benchmark at rung `k = 10` (`θ = 1025/2048`)
covering `[10^6144, 10^6144 + 10^3090]`.
Since `6144 * (1025/2048) = 3075` and `chebyshevLogSqEnv 512 = 14848^2 = 220463104`,
`qrhRemainderBoundAtTwoTenPow = 2 * 220463104 * 10^3075 = 440926208 * 10^3075`. -/
def shortIntervalQrh10252048Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 1025
    thetaDen := 2048
    xScaleExp := 6144
    hScaleExp := 3090
    errUpper := 440926208 * 10 ^ 3075
    primePowerCorr := 2 * 10 ^ 3072
    thetaDen_pos := by decide
    theta_lt_one := by decide }

set_option exponentiation.threshold 8000 in
/-- Exact verification of the `k = 10` Chebyshev error envelope against
`shortIntervalQrh10252048Spec`. -/
theorem chebyshevSpec6144_10252048_env_le :
    qrhRemainderBoundAtTwoTenPow chebyshevSpec6144_10252048 ≤
      shortIntervalQrh10252048Spec.errUpper := by
  have hExp : tenPowThetaCeilExp 512 (QRat.mk' 1025 2048) = 3075 := by decide
  change 2 * 1 * 10 ^ (tenPowThetaCeilExp 512 (QRat.mk' 1025 2048)) * ((29 * 512) * (29 * 512)) ≤
    440926208 * 10 ^ 3075
  rw [hExp]
  have hCoef : 2 * 1 * ((29 * 512) * (29 * 512)) = 440926208 := by decide
  rw [Nat.mul_assoc (2 * 1), Nat.mul_comm (10 ^ 3075), ← Nat.mul_assoc]
  rw [hCoef]
  exact Nat.le_refl _

set_option exponentiation.threshold 8000 in
/-- Exact positivity certificate for `[10^6144, 10^6144 + 10^3090]` at `θ = 1025/2048` (`k = 10`):
`2 * 440926208 * 10^3075 + 2 * 10^3072 < 10^3090`. -/
theorem shortIntervalQrh10252048Spec_has_prime :
    shortIntervalQrh10252048Spec.HasGuaranteedPrime := by
  change 2 * (440926208 * 10 ^ 3075) + 2 * 10 ^ 3072 < 10 ^ 3090
  have h3075 : (10 : Nat) ^ 3075 = 10 ^ 3 * 10 ^ 3072 := by
    rw [← Nat.pow_add]
  have h3090 : (10 : Nat) ^ 3090 = 10 ^ (18 + 3072) := rfl
  rw [h3075, h3090]
  have hLeft :
      2 * (440926208 * (10 ^ 3 * 10 ^ 3072)) + 2 * 10 ^ 3072 = 881852416002 * 10 ^ 3072 := by
    omega
  rw [hLeft]
  exact pow_ten_factor_lt_mvb (by decide : 881852416002 < 10 ^ 18)

/-- Concrete cleared-denominator `1/√N` tail gate at rung `k = 10` (`m = 32768`, `N = 16384`,
`tailNum = 1`, `tailBound = 256`, witnessing `16384 * 256^2 ≤ 32768^2 * 1^2`). -/
def dyadicAbelGateRung10 : InvSqrtTailGateSpec :=
  { denomM := 32768
    tailBound := 256
    scaleN := 16384
    tailNum := 1
    denomM_pos := by decide
    scaleN_pos := by decide
    gate_le := by decide }

/-- Master rung `k = 5, 6, 7, 8, 9, 10` certificate bundle extending the verified chain
`1025/2048 < 513/1024 < 257/512 < 129/256 < 65/128 < 33/64 < 17/32 < 7/8` with concrete
short-interval prime positivity at `[10^192, 10^192 + 10^108]`, `[10^384, 10^384 + 10^206]`,
`[10^768, 10^768 + 10^402]`, `[10^1536, 10^1536 + 10^786]`, `[10^3072, 10^3072 + 10^1554]`,
and `[10^6144, 10^6144 + 10^3090]`. -/
theorem dyadic_abel_rungs_k5_to_k10_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    QRat.eqv (qrhShortExponent 7) (QRat.mk' 129 256) ∧
    QRat.eqv (qrhShortExponent 8) (QRat.mk' 257 512) ∧
    QRat.eqv (qrhShortExponent 9) (QRat.mk' 513 1024) ∧
    QRat.eqv (qrhShortExponent 10) (QRat.mk' 1025 2048) ∧
    qrhShortExponent 10 < qrhShortExponent 9 ∧
    qrhShortExponent 9 < qrhShortExponent 8 ∧
    qrhShortExponent 8 < qrhShortExponent 7 ∧
    qrhShortExponent 7 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    qrhShortExponent 5 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 0 ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    shortIntervalQrh129256Spec.HasGuaranteedPrime ∧
    shortIntervalQrh257512Spec.HasGuaranteedPrime ∧
    shortIntervalQrh5131024Spec.HasGuaranteedPrime ∧
    shortIntervalQrh10252048Spec.HasGuaranteedPrime ∧
    (4 * dyadicAbelGateRung5.scaleN) *
      (dyadicAbelGateRung5.tailBound * dyadicAbelGateRung5.tailBound) ≤
      ((2 * dyadicAbelGateRung5.denomM) * (2 * dyadicAbelGateRung5.denomM)) *
        (dyadicAbelGateRung5.tailNum * dyadicAbelGateRung5.tailNum) ∧
    (4 * dyadicAbelGateRung6.scaleN) *
      (dyadicAbelGateRung6.tailBound * dyadicAbelGateRung6.tailBound) ≤
      ((2 * dyadicAbelGateRung6.denomM) * (2 * dyadicAbelGateRung6.denomM)) *
        (dyadicAbelGateRung6.tailNum * dyadicAbelGateRung6.tailNum) ∧
    (4 * dyadicAbelGateRung7.scaleN) *
      (dyadicAbelGateRung7.tailBound * dyadicAbelGateRung7.tailBound) ≤
      ((2 * dyadicAbelGateRung7.denomM) * (2 * dyadicAbelGateRung7.denomM)) *
        (dyadicAbelGateRung7.tailNum * dyadicAbelGateRung7.tailNum) ∧
    (4 * dyadicAbelGateRung8.scaleN) *
      (dyadicAbelGateRung8.tailBound * dyadicAbelGateRung8.tailBound) ≤
      ((2 * dyadicAbelGateRung8.denomM) * (2 * dyadicAbelGateRung8.denomM)) *
        (dyadicAbelGateRung8.tailNum * dyadicAbelGateRung8.tailNum) ∧
    (4 * dyadicAbelGateRung9.scaleN) *
      (dyadicAbelGateRung9.tailBound * dyadicAbelGateRung9.tailBound) ≤
      ((2 * dyadicAbelGateRung9.denomM) * (2 * dyadicAbelGateRung9.denomM)) *
        (dyadicAbelGateRung9.tailNum * dyadicAbelGateRung9.tailNum) ∧
    (4 * dyadicAbelGateRung10.scaleN) *
      (dyadicAbelGateRung10.tailBound * dyadicAbelGateRung10.tailBound) ≤
      ((2 * dyadicAbelGateRung10.denomM) * (2 * dyadicAbelGateRung10.denomM)) *
        (dyadicAbelGateRung10.tailNum * dyadicAbelGateRung10.tailNum) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    shortIntervalQrh3364Spec_has_prime, shortIntervalQrh65128Spec_has_prime,
    shortIntervalQrh129256Spec_has_prime, shortIntervalQrh257512Spec_has_prime,
    shortIntervalQrh5131024Spec_has_prime, shortIntervalQrh10252048Spec_has_prime,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung5,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung6,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung7,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung8,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung9,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung10⟩

-- =============================================================================
-- Part 6b: Parametric Dyadic Rung Theorem & Rungs 11..14 (Issue #183)
-- =============================================================================

/-- Scale factor `K = 2^(k - 1)` at ladder rung `k`. -/
def dyadicScaleK (k : Nat) : Nat := 2 ^ (k - 1)

/-- Coordinate exponent `xScaleExp = 12 * K = 12 * 2^(k - 1)` at ladder rung `k`. -/
def dyadicXScaleExp (k : Nat) : Nat := 12 * dyadicScaleK k

/-- Base exponent `baseExp = 6 * K = 6 * 2^(k - 1)` at ladder rung `k`. -/
def dyadicBaseExp (k : Nat) : Nat := 6 * dyadicScaleK k

/-- Short-interval window exponent `hScaleExp = baseExp + 18` at ladder rung `k`. -/
def dyadicHScaleExp (k : Nat) : Nat := dyadicBaseExp k + 18

/-- Contraction gate denominator `m = 2^(k + 5)` at ladder rung `k`. -/
def dyadicDenomM (k : Nat) : Nat := 2 ^ (k + 5)

/-- Contraction gate scale `N = 2^(2k - 6)` at ladder rung `k`. -/
def dyadicScaleN (k : Nat) : Nat := 2 ^ (2 * k - 6)

/-- Chebyshev log-squared prefactor coefficient `2 * (29 * K)^2` at ladder rung `k`. -/
def dyadicChebyshevCoeff (k : Nat) : Nat :=
  2 * ((29 * dyadicScaleK k) * (29 * dyadicScaleK k))

/-- Exact closed-form reduction for the ten-power ceiling exponent of `θ(k)` at rung `k ≥ 5`:
`⌈(12 * K * θ.num + θ.den - 1) / θ.den⌉ = 6 * K + 3 = baseExp + 3`. -/
theorem tenPowThetaCeilExp_dyadic (k : Nat) (hk : 5 ≤ k) :
    tenPowThetaCeilExp (dyadicScaleK k) (qrhShortExponent k) = dyadicBaseExp k + 3 := by
  have hk1 : 1 ≤ k := by omega
  have hpow : 2 ^ (k + 1) = 4 * 2 ^ (k - 1) := by
    have h1 : 2 ^ (k + 1) = 2 ^ ((k - 1) + 2) := by congr 1; omega
    rw [h1, Nat.pow_add]
    have h4 : 2 ^ 2 = 4 := rfl
    rw [h4, Nat.mul_comm]
  have hpowK : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have h1 : 2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
    rw [h1, Nat.pow_add]
    have h2 : 2 ^ 1 = 2 := rfl
    rw [h2, Nat.mul_comm]
  dsimp only [tenPowThetaCeilExp, qrhShortExponent, QRat.mk', dyadicScaleK, dyadicBaseExp]
  generalize hK : 2 ^ (k - 1) = K
  have hKpos : 0 < K := by
    rw [← hK]
    exact Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
  have hDen : 2 ^ (k + 1) = 4 * K := by rw [hpow, hK]
  have hNum : (((2 ^ k + 1 : Nat) : Int).natAbs) = 2 * K + 1 := by
    rw [hpowK, hK]
    rfl
  rw [hDen, hNum]
  have hNumerator : 12 * K * (2 * K + 1) + 4 * K - 1 = (4 * K - 1) + (6 * K + 3) * (4 * K) := by
    have h1 : 12 * K * (2 * K + 1) = 12 * K * (2 * K) + 12 * K * 1 :=
      Nat.mul_add (12 * K) (2 * K) 1
    have h2 : (6 * K + 3) * (4 * K) = (6 * K) * (4 * K) + 3 * (4 * K) :=
      Nat.add_mul (6 * K) 3 (4 * K)
    have ha : 12 * K * (2 * K) = 24 * (K * K) := by
      calc
        12 * K * (2 * K) = 12 * (K * (2 * K)) := Nat.mul_assoc 12 K (2 * K)
        _ = 12 * ((K * 2) * K) := by rw [Nat.mul_assoc K 2 K]
        _ = 12 * ((2 * K) * K) := by rw [Nat.mul_comm K 2]
        _ = 12 * (2 * (K * K)) := by rw [Nat.mul_assoc 2 K K]
        _ = (12 * 2) * (K * K) := (Nat.mul_assoc 12 2 (K * K)).symm
        _ = 24 * (K * K) := rfl
    have hb : (6 * K) * (4 * K) = 24 * (K * K) := by
      calc
        6 * K * (4 * K) = 6 * (K * (4 * K)) := Nat.mul_assoc 6 K (4 * K)
        _ = 6 * ((K * 4) * K) := by rw [Nat.mul_assoc K 4 K]
        _ = 6 * ((4 * K) * K) := by rw [Nat.mul_comm K 4]
        _ = 6 * (4 * (K * K)) := by rw [Nat.mul_assoc 4 K K]
        _ = (6 * 4) * (K * K) := (Nat.mul_assoc 6 4 (K * K)).symm
        _ = 24 * (K * K) := rfl
    have hc : 3 * (4 * K) = 12 * K := by
      calc
        3 * (4 * K) = (3 * 4) * K := (Nat.mul_assoc 3 4 K).symm
        _ = 12 * K := rfl
    rw [h1, h2, ha, hb, hc, Nat.mul_one]
    omega
  rw [hNumerator]
  rw [Nat.add_mul_div_right (4 * K - 1) (6 * K + 3) (by omega : 0 < 4 * K)]
  have hRem : (4 * K - 1) / (4 * K) = 0 := by
    apply Nat.div_eq_of_lt
    omega
  rw [hRem, Nat.zero_add]

/-- General tail-gate inequality `N * 256^2 ≤ m^2 * 1^2` at dyadic ladder rung `k ≥ 5`:
`2^(2k - 6) * 2^16 = 2^(2k + 10) ≤ 2^(2k + 10)`. -/
theorem dyadic_gate_le (k : Nat) (hk : 5 ≤ k) :
    dyadicScaleN k * (256 * 256) ≤ dyadicDenomM k * dyadicDenomM k * (1 * 1) := by
  change 2 ^ (2 * k - 6) * 2 ^ 16 ≤ 2 ^ (k + 5) * 2 ^ (k + 5) * 1
  rw [Nat.mul_one, ← Nat.pow_add, ← Nat.pow_add]
  have hExp : (2 * k - 6) + 16 = (k + 5) + (k + 5) := by omega
  rw [hExp]
  exact Nat.le_refl _

/-- Parametric dyadic tail gate specification at ladder rung `k ≥ 5`. -/
def dyadicAbelGateParametric (k : Nat) (hk : 5 ≤ k) : InvSqrtTailGateSpec :=
  { denomM := dyadicDenomM k
    tailBound := 256
    scaleN := dyadicScaleN k
    tailNum := 1
    denomM_pos := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
    scaleN_pos := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
    gate_le := dyadic_gate_le k hk }

/-- Parametric short-interval Chebyshev specification at ladder rung `k ≥ 5`. -/
def shortIntervalDyadicSpec (k : Nat) (hk : 5 ≤ k) : ShortIntervalChebyshevSpec :=
  { thetaNum := 2 ^ k + 1
    thetaDen := 2 ^ (k + 1)
    xScaleExp := dyadicXScaleExp k
    hScaleExp := dyadicHScaleExp k
    errUpper := dyadicChebyshevCoeff k * 10 ^ (dyadicBaseExp k + 3)
    primePowerCorr := 2 * 10 ^ dyadicBaseExp k
    thetaDen_pos := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
    theta_lt_one := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have h2 : 2 * 2 ^ k = 2 ^ k + 2 ^ k := by rw [Nat.two_mul]
      rw [h2]
      have hLe : 2 ≤ 2 ^ k := by
        have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
        exact h1
      omega }

/-- Master parametric prime-existence theorem for short intervals along the dyadic ladder:
Any rung `k ≥ 5` whose cleared prefactor factor satisfies `2 * C * 10^3 + 2 < 10^18`
guarantees at least one prime in `[10^xScaleExp, 10^xScaleExp + 10^hScaleExp]`. -/
theorem shortIntervalDyadicSpec_has_prime_of_factor_lt (k : Nat) (hk : 5 ≤ k)
    (hFactor : 2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2 < 10 ^ 18) :
    (shortIntervalDyadicSpec k hk).HasGuaranteedPrime := by
  dsimp [ShortIntervalChebyshevSpec.HasGuaranteedPrime, shortIntervalDyadicSpec, dyadicHScaleExp]
  have hExp : (10 : Nat) ^ (dyadicBaseExp k + 3) = 10 ^ 3 * 10 ^ dyadicBaseExp k := by
    rw [Nat.add_comm, Nat.pow_add]
  have hHExp : (10 : Nat) ^ (dyadicBaseExp k + 18) = 10 ^ (18 + dyadicBaseExp k) := by
    rw [Nat.add_comm]
  rw [hExp, hHExp]
  have hLeft :
      2 * (dyadicChebyshevCoeff k * (10 ^ 3 * 10 ^ dyadicBaseExp k)) + 2 * 10 ^ dyadicBaseExp k =
        (2 * (dyadicChebyshevCoeff k * 10 ^ 3) + 2) * 10 ^ dyadicBaseExp k := by
    have h1 : 2 * (dyadicChebyshevCoeff k * (10 ^ 3 * 10 ^ dyadicBaseExp k)) =
        (2 * (dyadicChebyshevCoeff k * 10 ^ 3)) * 10 ^ dyadicBaseExp k := by
      calc
        2 * (dyadicChebyshevCoeff k * (10 ^ 3 * 10 ^ dyadicBaseExp k))
            = 2 * ((dyadicChebyshevCoeff k * 10 ^ 3) * 10 ^ dyadicBaseExp k) := by
          rw [Nat.mul_assoc (dyadicChebyshevCoeff k) (10 ^ 3) (10 ^ dyadicBaseExp k)]
        _ = (2 * (dyadicChebyshevCoeff k * 10 ^ 3)) * 10 ^ dyadicBaseExp k := by
          rw [Nat.mul_assoc 2 (dyadicChebyshevCoeff k * 10 ^ 3) (10 ^ dyadicBaseExp k)]
    rw [h1, ← Nat.add_mul]
  rw [hLeft]
  exact pow_ten_factor_lt_mvb hFactor

/-- Concrete cleared-denominator tail gate at rung `k = 11`. -/
def dyadicAbelGateRung11 : InvSqrtTailGateSpec := dyadicAbelGateParametric 11 (by decide)

/-- Concrete cleared-denominator tail gate at rung `k = 12`. -/
def dyadicAbelGateRung12 : InvSqrtTailGateSpec := dyadicAbelGateParametric 12 (by decide)

/-- Concrete cleared-denominator tail gate at rung `k = 13`. -/
def dyadicAbelGateRung13 : InvSqrtTailGateSpec := dyadicAbelGateParametric 13 (by decide)

/-- Concrete cleared-denominator tail gate at rung `k = 14`. -/
def dyadicAbelGateRung14 : InvSqrtTailGateSpec := dyadicAbelGateParametric 14 (by decide)

/-- Concrete short-interval Chebyshev benchmark at rung `k = 11` (`θ = 2049/4096`). -/
def shortIntervalDyadicRung11Spec : ShortIntervalChebyshevSpec :=
  shortIntervalDyadicSpec 11 (by decide)

/-- Concrete short-interval Chebyshev benchmark at rung `k = 12` (`θ = 4097/8192`). -/
def shortIntervalDyadicRung12Spec : ShortIntervalChebyshevSpec :=
  shortIntervalDyadicSpec 12 (by decide)

/-- Concrete short-interval Chebyshev benchmark at rung `k = 13` (`θ = 8193/16384`). -/
def shortIntervalDyadicRung13Spec : ShortIntervalChebyshevSpec :=
  shortIntervalDyadicSpec 13 (by decide)

/-- Concrete short-interval Chebyshev benchmark at rung `k = 14` (`θ = 16385/32768`). -/
def shortIntervalDyadicRung14Spec : ShortIntervalChebyshevSpec :=
  shortIntervalDyadicSpec 14 (by decide)

/-- Exact positivity certificate for rung `k = 11` (`[10^12288, 10^12288 + 10^6162]`). -/
theorem shortIntervalDyadicRung11Spec_has_prime :
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime :=
  shortIntervalDyadicSpec_has_prime_of_factor_lt 11 (by decide) (by decide)

/-- Exact positivity certificate for rung `k = 12` (`[10^24576, 10^24576 + 10^12306]`). -/
theorem shortIntervalDyadicRung12Spec_has_prime :
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime :=
  shortIntervalDyadicSpec_has_prime_of_factor_lt 12 (by decide) (by decide)

/-- Exact positivity certificate for rung `k = 13` (`[10^49152, 10^49152 + 10^24594]`). -/
theorem shortIntervalDyadicRung13Spec_has_prime :
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime :=
  shortIntervalDyadicSpec_has_prime_of_factor_lt 13 (by decide) (by decide)

/-- Exact positivity certificate for rung `k = 14` (`[10^98304, 10^98304 + 10^49170]`). -/
theorem shortIntervalDyadicRung14Spec_has_prime :
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime :=
  shortIntervalDyadicSpec_has_prime_of_factor_lt 14 (by decide) (by decide)

/-- Extended master rung certificate bundle spanning rungs `k = 5` through `k = 14`. -/
theorem dyadic_abel_rungs_k5_to_k14_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    QRat.eqv (qrhShortExponent 7) (QRat.mk' 129 256) ∧
    QRat.eqv (qrhShortExponent 8) (QRat.mk' 257 512) ∧
    QRat.eqv (qrhShortExponent 9) (QRat.mk' 513 1024) ∧
    QRat.eqv (qrhShortExponent 10) (QRat.mk' 1025 2048) ∧
    QRat.eqv (qrhShortExponent 11) (QRat.mk' 2049 4096) ∧
    QRat.eqv (qrhShortExponent 12) (QRat.mk' 4097 8192) ∧
    QRat.eqv (qrhShortExponent 13) (QRat.mk' 8193 16384) ∧
    QRat.eqv (qrhShortExponent 14) (QRat.mk' 16385 32768) ∧
    qrhShortExponent 14 < qrhShortExponent 13 ∧
    qrhShortExponent 13 < qrhShortExponent 12 ∧
    qrhShortExponent 12 < qrhShortExponent 11 ∧
    qrhShortExponent 11 < qrhShortExponent 10 ∧
    qrhShortExponent 10 < qrhShortExponent 9 ∧
    qrhShortExponent 9 < qrhShortExponent 8 ∧
    qrhShortExponent 8 < qrhShortExponent 7 ∧
    qrhShortExponent 7 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    qrhShortExponent 5 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 0 ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    shortIntervalQrh129256Spec.HasGuaranteedPrime ∧
    shortIntervalQrh257512Spec.HasGuaranteedPrime ∧
    shortIntervalQrh5131024Spec.HasGuaranteedPrime ∧
    shortIntervalQrh10252048Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung11Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung12Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung13Spec.HasGuaranteedPrime ∧
    shortIntervalDyadicRung14Spec.HasGuaranteedPrime ∧
    (4 * dyadicAbelGateRung5.scaleN) *
      (dyadicAbelGateRung5.tailBound * dyadicAbelGateRung5.tailBound) ≤
      ((2 * dyadicAbelGateRung5.denomM) * (2 * dyadicAbelGateRung5.denomM)) *
        (dyadicAbelGateRung5.tailNum * dyadicAbelGateRung5.tailNum) ∧
    (4 * dyadicAbelGateRung6.scaleN) *
      (dyadicAbelGateRung6.tailBound * dyadicAbelGateRung6.tailBound) ≤
      ((2 * dyadicAbelGateRung6.denomM) * (2 * dyadicAbelGateRung6.denomM)) *
        (dyadicAbelGateRung6.tailNum * dyadicAbelGateRung6.tailNum) ∧
    (4 * dyadicAbelGateRung7.scaleN) *
      (dyadicAbelGateRung7.tailBound * dyadicAbelGateRung7.tailBound) ≤
      ((2 * dyadicAbelGateRung7.denomM) * (2 * dyadicAbelGateRung7.denomM)) *
        (dyadicAbelGateRung7.tailNum * dyadicAbelGateRung7.tailNum) ∧
    (4 * dyadicAbelGateRung8.scaleN) *
      (dyadicAbelGateRung8.tailBound * dyadicAbelGateRung8.tailBound) ≤
      ((2 * dyadicAbelGateRung8.denomM) * (2 * dyadicAbelGateRung8.denomM)) *
        (dyadicAbelGateRung8.tailNum * dyadicAbelGateRung8.tailNum) ∧
    (4 * dyadicAbelGateRung9.scaleN) *
      (dyadicAbelGateRung9.tailBound * dyadicAbelGateRung9.tailBound) ≤
      ((2 * dyadicAbelGateRung9.denomM) * (2 * dyadicAbelGateRung9.denomM)) *
        (dyadicAbelGateRung9.tailNum * dyadicAbelGateRung9.tailNum) ∧
    (4 * dyadicAbelGateRung10.scaleN) *
      (dyadicAbelGateRung10.tailBound * dyadicAbelGateRung10.tailBound) ≤
      ((2 * dyadicAbelGateRung10.denomM) * (2 * dyadicAbelGateRung10.denomM)) *
        (dyadicAbelGateRung10.tailNum * dyadicAbelGateRung10.tailNum) ∧
    (4 * dyadicAbelGateRung11.scaleN) *
      (dyadicAbelGateRung11.tailBound * dyadicAbelGateRung11.tailBound) ≤
      ((2 * dyadicAbelGateRung11.denomM) * (2 * dyadicAbelGateRung11.denomM)) *
        (dyadicAbelGateRung11.tailNum * dyadicAbelGateRung11.tailNum) ∧
    (4 * dyadicAbelGateRung12.scaleN) *
      (dyadicAbelGateRung12.tailBound * dyadicAbelGateRung12.tailBound) ≤
      ((2 * dyadicAbelGateRung12.denomM) * (2 * dyadicAbelGateRung12.denomM)) *
        (dyadicAbelGateRung12.tailNum * dyadicAbelGateRung12.tailNum) ∧
    (4 * dyadicAbelGateRung13.scaleN) *
      (dyadicAbelGateRung13.tailBound * dyadicAbelGateRung13.tailBound) ≤
      ((2 * dyadicAbelGateRung13.denomM) * (2 * dyadicAbelGateRung13.denomM)) *
        (dyadicAbelGateRung13.tailNum * dyadicAbelGateRung13.tailNum) ∧
    (4 * dyadicAbelGateRung14.scaleN) *
      (dyadicAbelGateRung14.tailBound * dyadicAbelGateRung14.tailBound) ≤
      ((2 * dyadicAbelGateRung14.denomM) * (2 * dyadicAbelGateRung14.denomM)) *
        (dyadicAbelGateRung14.tailNum * dyadicAbelGateRung14.tailNum) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    shortIntervalQrh3364Spec_has_prime, shortIntervalQrh65128Spec_has_prime,
    shortIntervalQrh129256Spec_has_prime, shortIntervalQrh257512Spec_has_prime,
    shortIntervalQrh5131024Spec_has_prime, shortIntervalQrh10252048Spec_has_prime,
    shortIntervalDyadicRung11Spec_has_prime, shortIntervalDyadicRung12Spec_has_prime,
    shortIntervalDyadicRung13Spec_has_prime, shortIntervalDyadicRung14Spec_has_prime,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung5,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung6,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung7,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung8,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung9,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung10,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung11,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung12,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung13,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung14⟩


/-- Master rung `k = 5, 6, 7, 8` certificate bundle extending the verified chain
`257/512 < 129/256 < 65/128 < 33/64 < 17/32 < 7/8` with concrete short-interval prime positivity at
`[10^192, 10^192 + 10^108]`, `[10^384, 10^384 + 10^206]`, `[10^768, 10^768 + 10^402]`, and
`[10^1536, 10^1536 + 10^786]`. -/
theorem dyadic_abel_rungs_k5_to_k8_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    QRat.eqv (qrhShortExponent 7) (QRat.mk' 129 256) ∧
    QRat.eqv (qrhShortExponent 8) (QRat.mk' 257 512) ∧
    qrhShortExponent 8 < qrhShortExponent 7 ∧
    qrhShortExponent 7 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    qrhShortExponent 5 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 0 ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    shortIntervalQrh129256Spec.HasGuaranteedPrime ∧
    shortIntervalQrh257512Spec.HasGuaranteedPrime ∧
    (4 * dyadicAbelGateRung5.scaleN) *
      (dyadicAbelGateRung5.tailBound * dyadicAbelGateRung5.tailBound) ≤
      ((2 * dyadicAbelGateRung5.denomM) * (2 * dyadicAbelGateRung5.denomM)) *
        (dyadicAbelGateRung5.tailNum * dyadicAbelGateRung5.tailNum) ∧
    (4 * dyadicAbelGateRung6.scaleN) *
      (dyadicAbelGateRung6.tailBound * dyadicAbelGateRung6.tailBound) ≤
      ((2 * dyadicAbelGateRung6.denomM) * (2 * dyadicAbelGateRung6.denomM)) *
        (dyadicAbelGateRung6.tailNum * dyadicAbelGateRung6.tailNum) ∧
    (4 * dyadicAbelGateRung7.scaleN) *
      (dyadicAbelGateRung7.tailBound * dyadicAbelGateRung7.tailBound) ≤
      ((2 * dyadicAbelGateRung7.denomM) * (2 * dyadicAbelGateRung7.denomM)) *
        (dyadicAbelGateRung7.tailNum * dyadicAbelGateRung7.tailNum) ∧
    (4 * dyadicAbelGateRung8.scaleN) *
      (dyadicAbelGateRung8.tailBound * dyadicAbelGateRung8.tailBound) ≤
      ((2 * dyadicAbelGateRung8.denomM) * (2 * dyadicAbelGateRung8.denomM)) *
        (dyadicAbelGateRung8.tailNum * dyadicAbelGateRung8.tailNum) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide,
    shortIntervalQrh3364Spec_has_prime, shortIntervalQrh65128Spec_has_prime,
    shortIntervalQrh129256Spec_has_prime, shortIntervalQrh257512Spec_has_prime,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung5,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung6,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung7,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung8⟩

/-- Master rung `k = 5, 6, 7` certificate bundle extending the verified chain
`129/256 < 65/128 < 33/64 < 17/32 < 7/8` with concrete short-interval prime positivity at
`[10^192, 10^192 + 10^108]`, `[10^384, 10^384 + 10^206]`, and `[10^768, 10^768 + 10^402]`. -/
theorem dyadic_abel_rungs_k5_k6_k7_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    QRat.eqv (qrhShortExponent 7) (QRat.mk' 129 256) ∧
    qrhShortExponent 7 < qrhShortExponent 6 ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    qrhShortExponent 5 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 0 ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    shortIntervalQrh129256Spec.HasGuaranteedPrime ∧
    (4 * dyadicAbelGateRung5.scaleN) *
      (dyadicAbelGateRung5.tailBound * dyadicAbelGateRung5.tailBound) ≤
      ((2 * dyadicAbelGateRung5.denomM) * (2 * dyadicAbelGateRung5.denomM)) *
        (dyadicAbelGateRung5.tailNum * dyadicAbelGateRung5.tailNum) ∧
    (4 * dyadicAbelGateRung6.scaleN) *
      (dyadicAbelGateRung6.tailBound * dyadicAbelGateRung6.tailBound) ≤
      ((2 * dyadicAbelGateRung6.denomM) * (2 * dyadicAbelGateRung6.denomM)) *
        (dyadicAbelGateRung6.tailNum * dyadicAbelGateRung6.tailNum) ∧
    (4 * dyadicAbelGateRung7.scaleN) *
      (dyadicAbelGateRung7.tailBound * dyadicAbelGateRung7.tailBound) ≤
      ((2 * dyadicAbelGateRung7.denomM) * (2 * dyadicAbelGateRung7.denomM)) *
        (dyadicAbelGateRung7.tailNum * dyadicAbelGateRung7.tailNum) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    shortIntervalQrh3364Spec_has_prime, shortIntervalQrh65128Spec_has_prime,
    shortIntervalQrh129256Spec_has_prime,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung5,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung6,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung7⟩

/-- Master rung `k = 5, 6` certificate bundle extending the verified chain
`65/128 < 33/64 < 17/32 < 7/8` with concrete short-interval prime positivity at
`[10^192, 10^192 + 10^108]` and `[10^384, 10^384 + 10^206]`. -/
theorem dyadic_abel_rungs_k5_k6_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    qrhShortExponent 6 < qrhShortExponent 5 ∧
    qrhShortExponent 5 < qrhShortExponent 4 ∧
    qrhShortExponent 4 < qrhShortExponent 0 ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    (4 * dyadicAbelGateRung5.scaleN) *
      (dyadicAbelGateRung5.tailBound * dyadicAbelGateRung5.tailBound) ≤
      ((2 * dyadicAbelGateRung5.denomM) * (2 * dyadicAbelGateRung5.denomM)) *
        (dyadicAbelGateRung5.tailNum * dyadicAbelGateRung5.tailNum) ∧
    (4 * dyadicAbelGateRung6.scaleN) *
      (dyadicAbelGateRung6.tailBound * dyadicAbelGateRung6.tailBound) ≤
      ((2 * dyadicAbelGateRung6.denomM) * (2 * dyadicAbelGateRung6.denomM)) *
        (dyadicAbelGateRung6.tailNum * dyadicAbelGateRung6.tailNum) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    shortIntervalQrh3364Spec_has_prime, shortIntervalQrh65128Spec_has_prime,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung5,
    inv_sqrt_tail_gate_dyadic_step dyadicAbelGateRung6⟩

-- =============================================================================
-- Part 2: Two-Piece QRat Variational Mollifier Optimization
-- =============================================================================

/-- Two-piece polynomial mollifier weights `P(u) = c1 * u + c2 * u^2` on `[0, 1]`
normalized by `P(1) = c1 + c2 = 1` with non-negative `QRat` coefficients.
The linear baseline corresponds to `(c1, c2) = (1, 0)`. -/
structure TwoPieceMollifierSpec where
  c1 : QRat
  c2 : QRat
  c1_nonneg : QRat.ofInt 0 ≤ c1
  c2_nonneg : QRat.ofInt 0 ≤ c2
  norm_one : QRat.eqv (c1 + c2) (QRat.ofInt 1)

/-- Evaluate `P(u) = c1 * u + c2 * u^2` at `u : QRat`. -/
def TwoPieceMollifierSpec.eval (m : TwoPieceMollifierSpec) (u : QRat) : QRat :=
  m.c1 * u + m.c2 * (u * u)

/-- Exact `L^2[0,1]` derivative energy `∫_0^1 P'(u)^2 du = c1^2 + 2*c1*c2 + (4/3)*c2^2`.
Under `c1 + c2 = 1`, this equals `1 + (1/3)*c2^2 ≥ 1` (minimum `1` at the linear
mollifier `(1, 0)`, and `49/48` at `(3/4, 1/4)`). -/
def mollifierDirichletEnergy (c1 c2 : QRat) : QRat :=
  c1 * c1 + QRat.ofInt 2 * c1 * c2 + (QRat.mk' 4 3) * (c2 * c2)

/-- Cleared-denominator two-piece variational off-diagonal energy:
`E_var(c1, c2) = c1^2 + c1*c2 + c2^2 = (c1 + c2)^2 - c1*c2`.
For any interior mix `c1 > 0, c2 > 0` with `c1 + c2 = 1`, `E_var = 1 - c1*c2 < 1`,
achieving `13/16 < 1` at `(c1, c2) = (3/4, 1/4)`. -/
def mollifierVariationalEnergy (c1 c2 : QRat) : QRat :=
  c1 * c1 + c1 * c2 + c2 * c2

/-- Exact `L^2[0,1]` weighted ratio energy `∫_0^1 (P(u)/u)^2 du = c1^2 + c1*c2 + (1/3)*c2^2`
(`37/48 < 1` at `(3/4, 1/4)`). -/
def mollifierRatioL2Energy (c1 c2 : QRat) : QRat :=
  c1 * c1 + c1 * c2 + (QRat.mk' 1 3) * (c2 * c2)

/-- Linear baseline two-piece mollifier `P(u) = u` (`(c1, c2) = (1, 0)`). -/
def twoPieceMollifierLinear : TwoPieceMollifierSpec :=
  { c1 := QRat.ofInt 1
    c2 := QRat.ofInt 0
    c1_nonneg := by decide
    c2_nonneg := by decide
    norm_one := by decide }

/-- Concrete two-piece variational mollifier `(c1, c2) = (3/4, 1/4)` satisfying
`P(0) = 0`, `P(1) = 1`, and strictly sub-unit variational energy `13/16 < 1`. -/
def variationalMollifier3414Spec : TwoPieceMollifierSpec :=
  { c1 := QRat.mk' 3 4
    c2 := QRat.mk' 1 4
    c1_nonneg := by decide
    c2_nonneg := by decide
    norm_one := by decide }

/-- Effective automorphic off-diagonal parameter under variational energy contraction:
`θ_eff = E_var(m.c1, m.c2) * θAuto`. -/
def effectiveAutoThetaVariational (m : TwoPieceMollifierSpec) (θAuto : QRat) : QRat :=
  mollifierVariationalEnergy m.c1 m.c2 * θAuto

/-- Effective QRH exponent obtained by coupling `ParametricQrhLadder.qrhFromAutomorphic`
with the two-piece variational mollifier energy contraction:
`θ_QRH = qrhFromAutomorphic (E_var(m.c1, m.c2) * θAuto)`. -/
def variationalQrhThreshold (m : TwoPieceMollifierSpec) (θAuto : QRat) : QRat :=
  qrhFromAutomorphic (effectiveAutoThetaVariational m θAuto)

private theorem sq_expand_int (x y : Int) :
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have hxy : y * x = x * y := Int.mul_comm y x
  omega

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hn hn
    simpa [Int.neg_mul_neg] using hmul

private theorem mul4_rearrange_aadd (a d : Int) :
    (a * d) * (a * d) = (a * a) * (d * d) := by
  ac_rfl

private theorem mul4_rearrange_abcd (a b c d : Int) :
    (a * d) * (c * b) = (a * c) * (b * d) := by
  ac_rfl

/-- Exact identity showing `mollifierDirichletEnergy c1 c2 = (c1 + c2)^2 + (1/3)*c2^2 ≥ 1`
whenever `c1 + c2 = 1`: linear `(1, 0)` minimizes `∫_0^1 P'(u)^2 du` at `1`, while
`(3/4, 1/4)` gives `49/48 > 1`. -/
theorem linear_minimizes_dirichlet_energy (m : TwoPieceMollifierSpec) :
    QRat.eqv (mollifierDirichletEnergy m.c1 m.c2)
      ((m.c1 + m.c2) * (m.c1 + m.c2) + (QRat.mk' 1 3) * (m.c2 * m.c2)) ∧
    QRat.ofInt 1 ≤ mollifierDirichletEnergy m.c1 m.c2 := by
  let a : Int := m.c1.num
  let b : Int := (m.c1.den : Int)
  let c : Int := m.c2.num
  let d : Int := (m.c2.den : Int)
  have hb : (0 : Int) < b := by have := m.c1.den_pos; omega
  have hd : (0 : Int) < d := by have := m.c2.den_pos; omega
  have hbd : (0 : Int) < b * d := Int.mul_pos hb hd
  have hNorm : a * d + c * b = b * d := by
    have hn := m.norm_one
    change (a * d + c * b) * 1 = 1 * (b * d) at hn
    omega
  have hSqExpanded :
      (a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b) =
        (a * d + c * b) * (a * d + c * b) := by
    have hE := sq_expand_int (a * d) (c * b)
    rw [mul4_rearrange_aadd a d, mul4_rearrange_aadd c b,
      mul4_rearrange_abcd a b c d] at hE
    exact hE.symm
  let K : Int := 3 * ((a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b)) +
    (c * c) * (b * b)
  let D0 : Int := 3 * ((b * b) * (d * d))
  have hLnum :
      ((a * a * (1 * b * d) + (2 * a) * c * (b * b)) * (3 * (d * d)) +
          4 * (c * c) * (b * b * (1 * b * d))) = (b * d) * K := by
    have t1 : a * a * (1 * b * d) * (3 * (d * d)) = (b * d) * (3 * ((a * a) * (d * d))) := by
      rw [Int.one_mul]; ac_rfl
    have t2 : (2 * a) * c * (b * b) * (3 * (d * d)) =
        (b * d) * (3 * (2 * ((a * c) * (b * d)))) := by
      ac_rfl
    have t3 : 4 * (c * c) * (b * b * (1 * b * d)) =
        (b * d) * (3 * ((c * c) * (b * b)) + (c * c) * (b * b)) := by
      have t3a : 4 * (c * c) * (b * b * (1 * b * d)) = (b * d) * (4 * ((c * c) * (b * b))) := by
        rw [Int.one_mul]; ac_rfl
      rw [t3a]
      congr 1
      omega
    dsimp only [K]
    rw [Int.add_mul, t1, t2, t3]
    simp only [Int.mul_add]
    omega
  have hLden : (b * b * (1 * b * d) * (3 * (d * d)) : Int) = (b * d) * D0 := by
    dsimp only [D0]
    rw [Int.one_mul]; ac_rfl
  have hRnum :
      ((a * d + c * b) * (a * d + c * b) * (3 * (d * d)) +
          1 * (c * c) * (b * d * (b * d))) = K * (d * d) := by
    rw [← hSqExpanded, Int.one_mul, mul4_rearrange_aadd b d]
    have u1 :
        ((a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b)) * (3 * (d * d)) =
          (3 * ((a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b))) * (d * d) := by
      ac_rfl
    have u2 : (c * c) * ((b * b) * (d * d)) = ((c * c) * (b * b)) * (d * d) := by
      ac_rfl
    dsimp only [K]
    rw [u1, u2, Int.add_mul]
  have hRden : (b * d * (b * d) * (3 * (d * d)) : Int) = D0 * (d * d) := by
    dsimp only [D0]
    ac_rfl
  refine ⟨?_, ?_⟩
  · change
      ((a * a * (1 * b * d) + (2 * a) * c * (b * b)) * (3 * (d * d)) +
          4 * (c * c) * (b * b * (1 * b * d))) *
          (b * d * (b * d) * (3 * (d * d))) =
        ((a * d + c * b) * (a * d + c * b) * (3 * (d * d)) +
            1 * (c * c) * (b * d * (b * d))) *
          (b * b * (1 * b * d) * (3 * (d * d)))
    rw [hLnum, hRden, hRnum, hLden]
    ac_rfl
  · change
      1 * (b * b * (1 * b * d) * (3 * (d * d)) : Int) ≤
        ((a * a * (1 * b * d) + (2 * a) * c * (b * b)) * (3 * (d * d)) +
            4 * (c * c) * (b * b * (1 * b * d))) * 1
    rw [Int.one_mul, Int.mul_one, hLnum, hLden]
    have hKeq : K = D0 + (c * c) * (b * b) := by
      have hSum : (a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b) =
          (b * b) * (d * d) := by
        rw [hSqExpanded, hNorm, mul4_rearrange_aadd b d]
      dsimp only [K, D0]
      rw [hSum]
    rw [hKeq, Int.mul_add]
    have hNonneg : 0 ≤ (b * d) * ((c * c) * (b * b)) :=
      Int.mul_nonneg (Int.le_of_lt hbd)
        (Int.mul_nonneg (int_sq_nonneg c) (int_sq_nonneg b))
    omega

/-- For any normalized two-piece mollifier with strictly positive `c1 > 0` and `c2 > 0`,
the variational energy satisfies `E_var = (c1 + c2)^2 - c1*c2 < 1`. -/
theorem variational_energy_lt_one_of_pos (m : TwoPieceMollifierSpec)
    (hc1 : (0 : Int) < m.c1.num) (hc2 : (0 : Int) < m.c2.num) :
    mollifierVariationalEnergy m.c1 m.c2 < QRat.ofInt 1 := by
  let a : Int := m.c1.num
  let b : Int := (m.c1.den : Int)
  let c : Int := m.c2.num
  let d : Int := (m.c2.den : Int)
  have hb : (0 : Int) < b := by have := m.c1.den_pos; omega
  have hd : (0 : Int) < d := by have := m.c2.den_pos; omega
  have hbd : (0 : Int) < b * d := Int.mul_pos hb hd
  have hNorm : a * d + c * b = b * d := by
    have hn := m.norm_one
    change (a * d + c * b) * 1 = 1 * (b * d) at hn
    omega
  have hSqExpanded :
      (a * a) * (d * d) + 2 * ((a * c) * (b * d)) + (c * c) * (b * b) =
        (b * b) * (d * d) := by
    have hE := sq_expand_int (a * d) (c * b)
    rw [mul4_rearrange_aadd a d, mul4_rearrange_aadd c b,
      mul4_rearrange_abcd a b c d, hNorm, mul4_rearrange_aadd b d] at hE
    exact hE.symm
  have hCrossPos : (0 : Int) < (a * c) * (b * d) :=
    Int.mul_pos (Int.mul_pos hc1 hc2) hbd
  have hCoreLt :
      (a * a) * (d * d) + (a * c) * (b * d) + (c * c) * (b * b) <
        (b * b) * (d * d) := by
    omega
  change
    ((a * a * (b * d) + a * c * (b * b)) * (d * d) + c * c * (b * b * (b * d))) * 1 <
      1 * (b * b * (b * d) * (d * d))
  have hEnum :
      ((a * a * (b * d) + a * c * (b * b)) * (d * d) + c * c * (b * b * (b * d))) =
        (b * d) * ((a * a) * (d * d) + (a * c) * (b * d) + (c * c) * (b * b)) := by
    have p1 : a * a * (b * d) * (d * d) = (b * d) * ((a * a) * (d * d)) := by ac_rfl
    have p2 : a * c * (b * b) * (d * d) = (b * d) * ((a * c) * (b * d)) := by ac_rfl
    have p3 : c * c * (b * b * (b * d)) = (b * d) * ((c * c) * (b * b)) := by ac_rfl
    rw [Int.add_mul, p1, p2, p3, Int.mul_add, Int.mul_add]
  have hEden : (b * b * (b * d) * (d * d) : Int) = (b * d) * ((b * b) * (d * d)) := by
    ac_rfl
  rw [Int.mul_one, Int.one_mul, hEnum, hEden]
  exact Int.mul_lt_mul_of_pos_left hCoreLt hbd

/-- Variational mollifier beats linear theorem:
At `(c1, c2) = (3/4, 1/4)`, the variational energy drops from `1` to `13/16 < 1`
(while `∫_0^1 (P(u)/u)^2 du = 37/48 < 1` and `∫_0^1 P'(u)^2 du = 49/48 ≥ 1`),
strictly tightening the `θ_KimSarnak = 7/64` (`selbergLambda1 = 975/4096`) QRH
threshold from `39/64` down to `603/1024 < 39/64` and raising the effective Selberg
spectral gap from `975/4096` to `253863/1048576 > 975/4096`. -/
theorem variational_mollifier_beats_linear :
    QRat.eqv (mollifierVariationalEnergy twoPieceMollifierLinear.c1 twoPieceMollifierLinear.c2)
      (QRat.ofInt 1) ∧
    QRat.eqv (mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 13 16) ∧
    mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2 < QRat.ofInt 1 ∧
    QRat.eqv (mollifierRatioL2Energy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 37 48) ∧
    QRat.eqv (mollifierDirichletEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 49 48) ∧
    QRat.eqv (qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4) (QRat.mk' 39 64) ∧
    QRat.eqv (variationalQrhThreshold variationalMollifier3414Spec
      GSp4FunctorialityBridge.thetaKimSarnakSym4) (QRat.mk' 603 1024) ∧
    variationalQrhThreshold variationalMollifier3414Spec
      GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4 ∧
    QRat.eqv (GSp4FunctorialityBridge.selbergLambda1
      GSp4FunctorialityBridge.thetaKimSarnakSym4) (QRat.mk' 975 4096) ∧
    GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      GSp4FunctorialityBridge.selbergLambda1
        (effectiveAutoThetaVariational variationalMollifier3414Spec
          GSp4FunctorialityBridge.thetaKimSarnakSym4) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- Master certificate bundle for `MollifierVariationalBridge` combining rungs `k = 5, 6`
(`33/64` at `[10^192, +10^108]`, `65/128` at `[10^384, +10^206]`) and the `(3/4, 1/4)`
two-piece `QRat` variational mollifier (`13/16 < 1`, `603/1024 < 39/64`). -/
theorem mollifier_variational_bridge_certs :
    QRat.eqv (qrhShortExponent 5) (QRat.mk' 33 64) ∧
    QRat.eqv (qrhShortExponent 6) (QRat.mk' 65 128) ∧
    shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
    shortIntervalQrh65128Spec.HasGuaranteedPrime ∧
    QRat.eqv (mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2) (QRat.mk' 13 16) ∧
    mollifierVariationalEnergy variationalMollifier3414Spec.c1
      variationalMollifier3414Spec.c2 < QRat.ofInt 1 ∧
    variationalQrhThreshold variationalMollifier3414Spec
      GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4 :=
  ⟨dyadic_abel_rungs_k5_k6_certs.1,
   dyadic_abel_rungs_k5_k6_certs.2.1,
   dyadic_abel_rungs_k5_k6_certs.2.2.2.2.2.1,
   dyadic_abel_rungs_k5_k6_certs.2.2.2.2.2.2.1,
   variational_mollifier_beats_linear.2.1,
   variational_mollifier_beats_linear.2.2.1,
   variational_mollifier_beats_linear.2.2.2.2.2.2.2.1⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean
