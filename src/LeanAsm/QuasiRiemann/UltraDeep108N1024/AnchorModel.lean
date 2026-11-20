-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/AnchorModel.lean
-- Shared anchor definitions, step function, and grid setup for N = 1024 at t ~ 10^24.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108Eval

namespace QuasiRiemann

/-- Partitioned `2 × 2` tile grid for `(σ = 0.500125, N = 1024, t ~ 10^24)` covering
`[0.500125, 0.500525] × [10^24 + 1.5398, 10^24 + 1.5402]`. -/
def highTruncTiles_1e24_N1024 : List LipTile2D :=
  buildLipTile2x2_108Core twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt rawMul108Crt
    intMul192ViaCrtNtt rawMul18Crt 1024
    500125 500325 500525 1000000000000000000000001539800 1000000000000000000000001540000
      1000000000000000000000001540200 2

theorem grad24_fast_valid :
    dirichletGradBoundScaled6_2048Core lnPrimeTable108Lit lnHighPrimes108TreeLit Int.mul
      rawMul18Fast 500125 1024 = 319421067 := by
  decide +kernel

def step24 (sMid6 tMid6 : Nat) :
    Nat → ScaledInterval × ScaledInterval → ScaledInterval × ScaledInterval :=
  zetaAnchorStep108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
    rawMul108Fast Int.mul rawMul18Fast
    ((sMid6 : Int) * scale12TInt, (sMid6 : Int) * scale12TInt)
    ((tMid6 : Int) * scale102Int, (tMid6 : Int) * scale102Int)

def anchor0Iv24 : ScaledInterval × ScaledInterval := (⟨1000000, 1000000⟩, ⟨0, 0⟩)

theorem evalStep24_eq (sm tm : Nat) :
    evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 sm tm =
    foldNatStep 1023 0 anchor0Iv24 (step24 sm tm) := rfl

/-- High-height `HighTruncZeroFreeRectSpec` for `(σ = 0.500125, N = 1024, t ~ 10^24)`. -/
def highTruncSpec_1e24_N1024 : HighTruncZeroFreeRectSpec where
  nTrunc := 1024
  sigmaNum := 4001
  sigmaDen := 8000
  tLoScaled := 1000000000000000000000001539800
  tHiScaled := 1000000000000000000000001540200
  deltaN := 2522000
  eTail := 1
  epsCrt := 2
  nTrunc_valid := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  sigma_above_half := by decide
  t_ordered := by decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/AnchorModel.lean