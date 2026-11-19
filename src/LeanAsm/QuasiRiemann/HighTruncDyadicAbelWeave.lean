-- Path: leanasm/src/LeanAsm/QuasiRiemann/HighTruncDyadicAbelWeave.lean
-- Constructive weave linking dyadic-shell Abel summation bounds and cleared-denominator
-- tail gates with high-truncation 2D zero-free strip certificates.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.DyadicAbelBridge
import LeanAsm.QuasiRiemann.ZeroDensityBridge
import LeanAsm.QuasiRiemann.UltraDeep108

namespace QuasiRiemann

open ConstructiveOpenaiBridge

-- =============================================================================
-- Part 1: Constructive Cleared-Denominator Weave Bridge
-- =============================================================================

/-- High-truncation dyadic-Abel certificate structure bundling a certified zero-free strip
with an inverse square-root tail gate scaled to the strip's Dirichlet truncation `nTrunc`. -/
structure HighTruncDyadicAbelSpec where
  strip : CertifiedStripWidthSpec
  gate : InvSqrtTailGateSpec
  nTrunc_eq_scaleN : strip.rectSpec.nTrunc = gate.scaleN
  margin_pos : strip.rectSpec.eTail + strip.rectSpec.epsCrt < strip.rectSpec.deltaN

/-- Non-vanishing margin of the high-truncation zero-free rectangle. -/
def HighTruncDyadicAbelSpec.margin (spec : HighTruncDyadicAbelSpec) : Nat :=
  spec.strip.rectSpec.deltaN - (spec.strip.rectSpec.eTail + spec.strip.rectSpec.epsCrt)

/-- Theorem (Constructive Cleared-Denominator Dyadic-Abel Strip-Width Bridge):
Connects a dyadic-shell partition and monotone Abel weight envelope with a certified
high-truncation zero-free strip. Proves:
1. Exact dyadic-shell sum decomposition `∑_{M ≤ n < M * 2^k} = ∑_{j < k} shell_j`,
2. Abel monotone-weight envelope bound on partial sums,
3. Cleared-denominator `4 * scaleN` quadratic tail-gate contraction step,
4. Positive zero-free non-vanishing margin `eTail + epsCrt < deltaN`,
5. Strict interior critical-strip penetration `1/2 < strip.sigmaLo < θ`, and
6. Strict zero-density exponent contraction `zdSpec.exponent strip.sigmaLo < zdSpec.exponent (1/2)`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem hightrunc_dyadic_abel_weave_bridge
    (weave : HighTruncDyadicAbelSpec)
    (zdSpec : ZeroDensitySpec) (θ : QRat)
    (hThetaLo : weave.strip.sigmaLo < θ) (hThetaHi : θ < QRat.ofInt 1)
    (a w : Nat → Int) (M N E : Nat) (hMN : M < N)
    (hw_nonneg : 0 ≤ w N)
    (hw_anti : ∀ k, M + 1 ≤ k → k < N → w (k + 1) ≤ w k)
    (hRem : ∀ k, M ≤ k → k ≤ N → Int.natAbs (partialSumInt a k - (k : Int)) ≤ E)
    (f : Nat → Int) (M_shell k_shell : Nat) :
    rangeSumInt f M_shell (M_shell * 2 ^ k_shell) =
      listSum (List.range k_shell) (fun j => listSum (dyadicShell M_shell j) f) ∧
    Int.natAbs (rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) -
        rangeSumInt w (M + 1) (N + 1)) ≤
      2 * E * Int.natAbs (w (M + 1)) ∧
    (4 * weave.gate.scaleN) * (weave.gate.tailBound * weave.gate.tailBound) ≤
      ((2 * weave.gate.denomM) * (2 * weave.gate.denomM)) *
        (weave.gate.tailNum * weave.gate.tailNum) ∧
    0 < weave.margin ∧
    QRat.mk' 1 2 < weave.strip.sigmaLo ∧
    weave.strip.sigmaLo < θ ∧
    zdSpec.exponent weave.strip.sigmaLo < zdSpec.exponent (QRat.mk' 1 2) ∧
    zdSpec.exponent θ < zdSpec.exponent weave.strip.sigmaLo ∧
    weave.strip.rectSpec.HasCertifiedNonVanishing := by
  have hShell := dyadic_shell_sum_partition M_shell k_shell f
  have hAbel := abel_monotone_weight_envelope a w M N E hMN hw_nonneg hw_anti hRem
  have hGate := inv_sqrt_tail_gate_dyadic_step weave.gate
  have hMargin : 0 < weave.margin := by
    dsimp [HighTruncDyadicAbelSpec.margin]
    have h := weave.margin_pos
    omega
  have hZd := ultradeep72_strip_to_zero_density_bridge weave.strip zdSpec θ hThetaLo hThetaHi
  exact ⟨hShell, hAbel.2.2, hGate, hMargin, hZd.1, hThetaLo, hZd.2.1, hZd.2.2.1,
    weave.strip.rect_certified⟩

-- =============================================================================
-- Part 2: Concrete High-Truncation Strip-Width Tail Gates & Specifications
-- =============================================================================

/-- Inverse square-root tail gate for `N = 1024` with `denomM = 32`, `tailBound = 1`,
`tailNum = 1`, satisfying `1024 * 1^2 ≤ 32^2 * 1^2 = 1024`. -/
def invSqrtGate1024 : InvSqrtTailGateSpec where
  denomM := 32
  tailBound := 1
  scaleN := 1024
  tailNum := 1
  denomM_pos := by decide
  scaleN_pos := by decide
  gate_le := by decide

/-- Inverse square-root tail gate for `N = 2048` with `denomM = 64`, `tailBound = 1`,
`tailNum = 2`, satisfying `2048 * 1^2 ≤ 64^2 * 2^2 = 4096 * 4 = 16384`. -/
def invSqrtGate2048 : InvSqrtTailGateSpec where
  denomM := 64
  tailBound := 1
  scaleN := 2048
  tailNum := 2
  denomM_pos := by decide
  scaleN_pos := by decide
  gate_le := by decide

/-- Certified `HighTruncDyadicAbelSpec` at `(σ = 0.500125, N = 1024, t ~ 10^24)`. -/
def highTruncDyadicAbel1024Spec : HighTruncDyadicAbelSpec where
  strip := certifiedStrip0500125_N1024
  gate := invSqrtGate1024
  nTrunc_eq_scaleN := rfl
  margin_pos := by decide

/-- Certified `HighTruncDyadicAbelSpec` at `(σ = 0.5000625, N = 2048, t ~ 10^30)`. -/
def highTruncDyadicAbel2048Spec : HighTruncDyadicAbelSpec where
  strip := certifiedStrip05000625_N2048
  gate := invSqrtGate2048
  nTrunc_eq_scaleN := rfl
  margin_pos := by decide

-- =============================================================================
-- Part 3: Concrete End-to-End Weave Certificate Theorems
-- =============================================================================

/-- Theorem (Concrete High-Truncation 108-Digit Dyadic-Abel Weave Certificate at N = 1024):
Demonstrates the weave on the certified `N = 1024` parameter box:
1. Exact non-vanishing margin `2522000 - (1 + 2) = 2521997 > 0`,
2. Inverse square-root tail gate inequality `4 * 1024 * 1 ≤ 64^2 * 1^2`,
3. Strict strip penetration `1/2 < 4001/8000 < 3/4`,
4. Zero-density slope contraction under Guth-Maynard (`30/13`) and Huxley (`12/5`), and
5. Compositional 2D Lipschitz box tiling non-vanishing on `[10^24, 10^24 + 400]`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem hightrunc_dyadic_abel_weave_N1024_cert :
    highTruncDyadicAbel1024Spec.margin = 2521997 ∧
    (4 * highTruncDyadicAbel1024Spec.gate.scaleN) *
        (highTruncDyadicAbel1024Spec.gate.tailBound *
          highTruncDyadicAbel1024Spec.gate.tailBound) ≤
      ((2 * highTruncDyadicAbel1024Spec.gate.denomM) *
        (2 * highTruncDyadicAbel1024Spec.gate.denomM)) *
        (highTruncDyadicAbel1024Spec.gate.tailNum *
          highTruncDyadicAbel1024Spec.gate.tailNum) ∧
    QRat.mk' 1 2 < highTruncDyadicAbel1024Spec.strip.sigmaLo ∧
    highTruncDyadicAbel1024Spec.strip.sigmaLo < QRat.mk' 3 4 ∧
    zdGuthMaynard.exponent highTruncDyadicAbel1024Spec.strip.sigmaLo <
      zdGuthMaynard.exponent (QRat.mk' 1 2) ∧
    zdHuxley.exponent highTruncDyadicAbel1024Spec.strip.sigmaLo <
      zdHuxley.exponent (QRat.mk' 1 2) ∧
    highTruncDyadicAbel1024Spec.strip.rectSpec.HasCertifiedNonVanishing ∧
    (highTruncTiles_1e24_N1024.length = 4 ∧
      (∀ t ∈ highTruncTiles_1e24_N1024, IsValidLipTile2D t)) := by
  have h1024 := crtNtt_highTrunc108_N1024_rect
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide,
    highTruncDyadicAbel1024Spec.strip.rect_certified, h1024.1, h1024.2.1⟩

/-- Theorem (Concrete High-Truncation 108-Digit Dyadic-Abel Weave Certificate at N = 2048):
Demonstrates the weave on the ultra-deep `N = 2048` parameter box:
1. Exact non-vanishing margin `2683000 - (1 + 2) = 2682997 > 0`,
2. Inverse square-root tail gate inequality `4 * 2048 * 1 ≤ 128^2 * 2^2`,
3. Strict strip penetration `1/2 < 8001/16000 < 3/4`,
4. Zero-density slope contraction under Guth-Maynard (`30/13`) and Huxley (`12/5`), and
5. Compositional 2D Lipschitz box tiling non-vanishing on `[10^30, 10^30 + 400]`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem hightrunc_dyadic_abel_weave_N2048_cert :
    highTruncDyadicAbel2048Spec.margin = 2682997 ∧
    (4 * highTruncDyadicAbel2048Spec.gate.scaleN) *
        (highTruncDyadicAbel2048Spec.gate.tailBound *
          highTruncDyadicAbel2048Spec.gate.tailBound) ≤
      ((2 * highTruncDyadicAbel2048Spec.gate.denomM) *
        (2 * highTruncDyadicAbel2048Spec.gate.denomM)) *
        (highTruncDyadicAbel2048Spec.gate.tailNum *
          highTruncDyadicAbel2048Spec.gate.tailNum) ∧
    QRat.mk' 1 2 < highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
    highTruncDyadicAbel2048Spec.strip.sigmaLo < QRat.mk' 3 4 ∧
    zdGuthMaynard.exponent highTruncDyadicAbel2048Spec.strip.sigmaLo <
      zdGuthMaynard.exponent (QRat.mk' 1 2) ∧
    zdHuxley.exponent highTruncDyadicAbel2048Spec.strip.sigmaLo <
      zdHuxley.exponent (QRat.mk' 1 2) ∧
    highTruncDyadicAbel2048Spec.strip.rectSpec.HasCertifiedNonVanishing ∧
    (highTruncTiles_1e30_N2048.length = 4 ∧
      (∀ t ∈ highTruncTiles_1e30_N2048, IsValidLipTile2D t)) := by
  have h2048 := crtNtt_highTrunc108_N2048_rect
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide,
    highTruncDyadicAbel2048Spec.strip.rect_certified, h2048.1, h2048.2.1⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/HighTruncDyadicAbelWeave.lean
