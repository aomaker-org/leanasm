-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Certificates.lean
-- Rational box contraction and zero-free certificate for N = 1024 at t ~ 10^24.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.Bounds

namespace QuasiRiemann

/-- Step 0 `t ~ 10^24` rectangle for `1/3` contraction (`radL1 = 3600`). -/
def nestedBox1e24_0 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 503600
  tLo6 := 1000000000000000000000001538200
  tHi6 := 1000000000000000000000001541800
  sMid6 := 501800
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 1 `t ~ 10^24` rectangle after `1/3` contraction (`radL1 = 1200`). -/
def nestedBox1e24_1 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 501200
  tLo6 := 1000000000000000000000001539400
  tHi6 := 1000000000000000000000001540600
  sMid6 := 500600
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 2 `N = 1024`, `σ = 0.500125` (`radL1 = 400`) box matching `highTruncTiles_1e24_N1024`. -/
def nestedBox1e24_2 : NestedBox2D where
  sLo6 := 500125
  sHi6 := 500525
  tLo6 := 1000000000000000000000001539800
  tHi6 := 1000000000000000000000001540200
  sMid6 := 500325
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Indexed `1/3`-contraction family ending at `nestedBox1e24_2` (`N = 1024`, `σ = 0.500125`). -/
def nestedBoxSeq1e24_N1024 : Nat → NestedBox2D
  | 0 => nestedBox1e24_0
  | 1 => nestedBox1e24_1
  | _ => nestedBox1e24_2

/-- Drift sequence with exact `1/3` contraction (`1152000000000 → 384000000000 → 128000000000`). -/
def driftSeq1e24_N1024 : Nat → Nat
  | 0 => 1152000000000
  | 1 => 384000000000
  | _ => 128000000000

/-- Concrete `RationalBoxContractionSpec` (`q = 1/3`, shrunk `M / (r - δ)`) for `N = 1024`. -/
def rationalBoxSpec_N1024 : RationalBoxContractionSpec where
  qNum := 1
  qDen := 3
  qNum_pos := by decide
  qNum_lt_qDen := by decide
  lipNumerator := 320000000
  radius := nestedBox1e24_2.radL1
  deltaShrink := 100
  shrink_lt_radius := by decide
  centerLower := 2500000000000
  centerLower_pos := by decide
  lip_margin_ok := by decide

/-- Theorem (`N = 1024`, `σ = 0.500125 = 1/2 + 1/8000`, `t ~ 10^24` Contraction & Tiling): -/
theorem ultraDeep72_N1024_rational_rect_cert :
    nestedBox1e24_2.SubBox nestedBox1e24_0 ∧
    3 ^ 2 * driftSeq1e24_N1024 2 ≤ 1 ^ 2 * driftSeq1e24_N1024 0 ∧
    QRat.eqv (QRat.mk' 4001 8000 (by decide))
      (QRat.mk' 1 2 (by decide) + QRat.mk' 1 8000 (by decide)) ∧
    rationalBoxSpec_N1024.lipNumerator * rationalBoxSpec_N1024.radius <
      rationalBoxSpec_N1024.centerLower *
        (rationalBoxSpec_N1024.radius - rationalBoxSpec_N1024.deltaShrink) ∧
    (∀ centerMag pointMag dist : Nat,
      2500000000000 ≤ centerMag →
      dist ≤ 400 →
      300 * Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤ 320000000 * dist →
      1250000000000 ≤ pointMag ∧ 0 < pointMag) ∧
    dirichletGradBoundScaled6_2048 500125 1024 = 319421067 ∧
    16 * 999 * 999 < 5 * 17 * 257 * 65537 ∧
    eulerMaclaurinB2TailRect2DForN 1024 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 512 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ∧
    highTruncSpec_1e24_N1024.HasCertifiedNonVanishing ∧
    (∀ s6 t6 : Nat,
      InBox2D nestedBox1e24_2.sLo6 nestedBox1e24_2.sHi6
        nestedBox1e24_2.tLo6 nestedBox1e24_2.tHi6 s6 t6 →
      ∃ tile ∈ highTruncTiles_1e24_N1024,
        IsValidLipTile2D tile ∧
        InBox2D tile.sLo6 tile.sHi6 tile.tLo6 tile.tHi6 s6 t6 ∧
        (∀ zRe0 zIm0 zRe zIm : Int,
          tile.anchorRe.lo * 1000000 ≤ zRe0 ∧ zRe0 ≤ tile.anchorRe.hi * 1000000 →
          tile.anchorIm.lo * 1000000 ≤ zIm0 ∧ zIm0 ≤ tile.anchorIm.hi * 1000000 →
          Int.natAbs (zRe - zRe0) ≤
            tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
              ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
          Int.natAbs (zIm - zIm0) ≤
            tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
              ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
          0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) := by
  have hChain := rational_telescoping_chain_cert 1 3 (by decide) (by decide)
    nestedBoxSeq1e24_N1024 (fun _ => 320000000) driftSeq1e24_N1024 2500000000000
    (by decide) (by decide) 2
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | i + 2 => omega)
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | i + 2 => omega)
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | i + 3 => omega)
  have hGrad : dirichletGradBoundScaled6_2048 500125 1024 = 319421067 := by
    dsimp [dirichletGradBoundScaled6_2048]
    rw [lnPrimeTable108_eq, lnHighPrimes108Tree_eq, intMul192ViaCrtNtt_fn_eq, rawMul18_fn_eq]
    exact grad24_fast_valid
  have hTail :
      eulerMaclaurinB2TailRect2DForN 1024 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 512 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) := by
    dsimp [eulerMaclaurinB2TailRect2DForN]
    have h1 : nPowNegUpperForN 1024 500125 = (1, 32) := by decide
    have h2 : nPowNegUpperForN 512 500125 = (1, 22) := by decide
    rw [h1, h2]
    exact tail_mono_of_den (by decide) (by decide) (by decide) (by decide)
  have hRect := crtNtt_highTrunc108_N1024_rect
  refine ⟨hChain.1, hChain.2.1, by decide, rationalBoxSpec_N1024.lip_mul_radius_lt, ?_, hGrad,
    by decide, hTail, hRect.2.2.2, ?_⟩
  · intro centerMag pointMag dist hCenter hDist hLip
    have hStep := rational_box_contraction_step rationalBoxSpec_N1024
      centerMag pointMag dist (driftSeq1e24_N1024 0) (driftSeq1e24_N1024 1)
      hCenter hDist hLip (by decide)
    exact ⟨hStep.1, hStep.2.2.1⟩
  · intro s6 t6 hmem
    exact hRect.2.2.1 s6 t6 hmem

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Certificates.lean
