-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1/Bounds.lean
-- Chunked Dirichlet partial-sum fold evaluation and bounds for N = 2048 (Part 1, Tile 0).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108Tables
import LeanAsm.QuasiRiemann.UltraDeep108N1024
import LeanAsm.QuasiRiemann.UltraDeep108Eval

namespace QuasiRiemann

def step30 (sMid6 tMid6 : Nat) :
    Nat → ScaledInterval × ScaledInterval → ScaledInterval × ScaledInterval :=
  zetaAnchorStep108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
    rawMul108Fast Int.mul rawMul18Fast
    ((sMid6 : Int) * scale12TInt, (sMid6 : Int) * scale12TInt)
    ((tMid6 : Int) * scale102Int, (tMid6 : Int) * scale102Int)

def anchor0Iv : ScaledInterval × ScaledInterval := (⟨1000000, 1000000⟩, ⟨0, 0⟩)

theorem evalStep30_eq (sm tm : Nat) :
    evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 sm tm =
    foldNatStep 2047 0 anchor0Iv (step30 sm tm) := rfl

private theorem t30_0_c1 :
    foldNatStep 128 0 anchor0Iv (step30 500162 1000000000000000000000000000001069900) =
      (⟨1964389, 1964617⟩, ⟨-421958, -421726⟩) := by decide +kernel
private theorem t30_0_c2 :
    foldNatStep 128 128 (⟨1964389, 1964617⟩, ⟨-421958, -421726⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨1646478, 1646930⟩, ⟨-439444, -438998⟩) := by decide +kernel
private theorem t30_0_c3 :
    foldNatStep 128 256 (⟨1646478, 1646930⟩, ⟨-439444, -438998⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨1981879, 1982549⟩, ⟨493219, 493887⟩) := by decide +kernel
private theorem t30_0_c4 :
    foldNatStep 128 384 (⟨1981879, 1982549⟩, ⟨493219, 493887⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2515077, 2515960⟩, ⟨-66249, -65372⟩) := by decide +kernel
private theorem t30_0_c5 :
    foldNatStep 128 512 (⟨2515077, 2515960⟩, ⟨-66249, -65372⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2506334, 2507429⟩, ⟨141901, 142992⟩) := by decide +kernel
private theorem t30_0_c6 :
    foldNatStep 128 640 (⟨2506334, 2507429⟩, ⟨141901, 142992⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2603965, 2605277⟩, ⟨317047, 318352⟩) := by decide +kernel
private theorem t30_0_c7 :
    foldNatStep 128 768 (⟨2603965, 2605277⟩, ⟨317047, 318352⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2355587, 2357112⟩, ⟨-31004, -29478⟩) := by decide +kernel
private theorem t30_0_c8 :
    foldNatStep 128 896 (⟨2355587, 2357112⟩, ⟨-31004, -29478⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2332207, 2333944⟩, ⟨-381268, -379532⟩) := by decide +kernel
private theorem t30_0_c9 :
    foldNatStep 128 1024 (⟨2332207, 2333944⟩, ⟨-381268, -379532⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2157438, 2159392⟩, ⟨-283450, -281503⟩) := by decide +kernel
private theorem t30_0_c10 :
    foldNatStep 128 1152 (⟨2157438, 2159392⟩, ⟨-283450, -281503⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2345306, 2347473⟩, ⟨-183771, -181608⟩) := by decide +kernel
private theorem t30_0_c11 :
    foldNatStep 128 1280 (⟨2345306, 2347473⟩, ⟨-183771, -181608⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2573748, 2576122⟩, ⟨-206364, -203986⟩) := by decide +kernel
private theorem t30_0_c12 :
    foldNatStep 128 1408 (⟨2573748, 2576122⟩, ⟨-206364, -203986⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2844190, 2846780⟩, ⟨200395, 202986⟩) := by decide +kernel
private theorem t30_0_c13 :
    foldNatStep 128 1536 (⟨2844190, 2846780⟩, ⟨200395, 202986⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2944995, 2947796⟩, ⟨171233, 174031⟩) := by decide +kernel
private theorem t30_0_c14 :
    foldNatStep 128 1664 (⟨2944995, 2947796⟩, ⟨171233, 174031⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2875678, 2878690⟩, ⟨216047, 219059⟩) := by decide +kernel
private theorem t30_0_c15 :
    foldNatStep 128 1792 (⟨2875678, 2878690⟩, ⟨216047, 219059⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2789291, 2792515⟩, ⟨-221948, -218734⟩) := by decide +kernel
private theorem t30_0_c16 :
    foldNatStep 127 1920 (⟨2789291, 2792515⟩, ⟨-221948, -218734⟩)
      (step30 500162 1000000000000000000000000000001069900) =
      (⟨2787532, 2790957⟩, ⟨-340904, -337470⟩) := by decide +kernel

theorem tile30_0_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 2048 500062 500262
        1000000000000000000000000000001069800
        1000000000000000000000000000001070000 512891320 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 2048 500162
        1000000000000000000000000000001069900 =
        (⟨2787532, 2790957⟩, ⟨-340904, -337470⟩) := by
    rw [evalStep30_eq]
    exact foldNatStep_2047_chunks (step30 500162 1000000000000000000000000000001069900)
      anchor0Iv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      t30_0_c1 t30_0_c2 t30_0_c3 t30_0_c4 t30_0_c5 t30_0_c6 t30_0_c7 t30_0_c8
      t30_0_c9 t30_0_c10 t30_0_c11 t30_0_c12 t30_0_c13 t30_0_c14 t30_0_c15 t30_0_c16
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500062, 500262, 1000000000000000000000000000001069800,
    1000000000000000000000000000001070000, 500162, 1000000000000000000000000000001069900,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500162
      1000000000000000000000000000001069900).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500162
      1000000000000000000000000000001069900).2, 512891320, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1/Bounds.lean
