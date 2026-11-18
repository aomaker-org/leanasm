-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1.lean
import LeanAsm.QuasiRiemann.UltraDeep108Tables
import LeanAsm.QuasiRiemann.UltraDeep108N1024
import LeanAsm.QuasiRiemann.UltraDeep108Eval

namespace QuasiRiemann

/-- Partitioned `2 × 2` tile grid for `(σ = 0.500062, N = 2048, t ~ 10^30)` covering
`[0.500062, 0.500462] × [10^30 + 1.0698, 10^30 + 1.0702]` (containing `σ = 0.5000625`). -/
def highTruncTiles_1e30_N2048 : List LipTile2D :=
  buildLipTile2x2_108Core twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt rawMul108Crt
    intMul192ViaCrtNtt rawMul18Crt 2048
    500062 500262 500462
    1000000000000000000000000000001069800 1000000000000000000000000000001070000
    1000000000000000000000000000001070200 2


theorem grad30_fast_valid :
    dirichletGradBoundScaled6_2048Core lnPrimeTable108Lit lnHighPrimes108TreeLit Int.mul
      rawMul18Fast 500062 2048 = 512891320 := by
  decide +kernel

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

private theorem t30_1_c1 :
    foldNatStep 128 0 anchor0Iv (step30 500162 1000000000000000000000000000001070100) =
      (⟨1964247, 1964473⟩, ⟨-422388, -422157⟩) := by decide +kernel
private theorem t30_1_c2 :
    foldNatStep 128 128 (⟨1964247, 1964473⟩, ⟨-422388, -422157⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨1646330, 1646777⟩, ⟨-439581, -439129⟩) := by decide +kernel
private theorem t30_1_c3 :
    foldNatStep 128 256 (⟨1646330, 1646777⟩, ⟨-439581, -439129⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨1982802, 1983470⟩, ⟨492705, 493372⟩) := by decide +kernel
private theorem t30_1_c4 :
    foldNatStep 128 384 (⟨1982802, 1983470⟩, ⟨492705, 493372⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2515325, 2516203⟩, ⟨-67416, -66532⟩) := by decide +kernel
private theorem t30_1_c5 :
    foldNatStep 128 512 (⟨2515325, 2516203⟩, ⟨-67416, -66532⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2506852, 2507935⟩, ⟨140740, 141839⟩) := by decide +kernel
private theorem t30_1_c6 :
    foldNatStep 128 640 (⟨2506852, 2507935⟩, ⟨140740, 141839⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2604715, 2606016⟩, ⟨315760, 317066⟩) := by decide +kernel
private theorem t30_1_c7 :
    foldNatStep 128 768 (⟨2604715, 2606016⟩, ⟨315760, 317066⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2355873, 2357391⟩, ⟨-31956, -30440⟩) := by decide +kernel
private theorem t30_1_c8 :
    foldNatStep 128 896 (⟨2355873, 2357391⟩, ⟨-31956, -30440⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2332014, 2333740⟩, ⟨-382192, -380456⟩) := by decide +kernel
private theorem t30_1_c9 :
    foldNatStep 128 1024 (⟨2332014, 2333740⟩, ⟨-382192, -380456⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2157390, 2159333⟩, ⟨-284128, -282181⟩) := by decide +kernel
private theorem t30_1_c10 :
    foldNatStep 128 1152 (⟨2157390, 2159333⟩, ⟨-284128, -282181⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2345394, 2347553⟩, ⟨-184719, -182556⟩) := by decide +kernel
private theorem t30_1_c11 :
    foldNatStep 128 1280 (⟨2345394, 2347553⟩, ⟨-184719, -182556⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2573796, 2576163⟩, ⟨-207645, -205271⟩) := by decide +kernel
private theorem t30_1_c12 :
    foldNatStep 128 1408 (⟨2573796, 2576163⟩, ⟨-207645, -205271⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2844834, 2847418⟩, ⟨198720, 201306⟩) := by decide +kernel
private theorem t30_1_c13 :
    foldNatStep 128 1536 (⟨2844834, 2847418⟩, ⟨198720, 201306⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2945605, 2948395⟩, ⟨169416, 172214⟩) := by decide +kernel
private theorem t30_1_c14 :
    foldNatStep 128 1664 (⟨2945605, 2948395⟩, ⟨169416, 172214⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2876352, 2879354⟩, ⟨214329, 217346⟩) := by decide +kernel
private theorem t30_1_c15 :
    foldNatStep 128 1792 (⟨2876352, 2879354⟩, ⟨214329, 217346⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2789303, 2792518⟩, ⟨-223545, -220311⟩) := by decide +kernel
private theorem t30_1_c16 :
    foldNatStep 127 1920 (⟨2789303, 2792518⟩, ⟨-223545, -220311⟩)
      (step30 500162 1000000000000000000000000000001070100) =
      (⟨2787364, 2790783⟩, ⟨-342502, -339055⟩) := by decide +kernel

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

theorem tile30_1_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 2048 500062 500262
        1000000000000000000000000000001070000
        1000000000000000000000000000001070200 512891320 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 2048 500162
        1000000000000000000000000000001070100 =
        (⟨2787364, 2790783⟩, ⟨-342502, -339055⟩) := by
    rw [evalStep30_eq]
    exact foldNatStep_2047_chunks (step30 500162 1000000000000000000000000000001070100)
      anchor0Iv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      t30_1_c1 t30_1_c2 t30_1_c3 t30_1_c4 t30_1_c5 t30_1_c6 t30_1_c7 t30_1_c8
      t30_1_c9 t30_1_c10 t30_1_c11 t30_1_c12 t30_1_c13 t30_1_c14 t30_1_c15 t30_1_c16
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500062, 500262, 1000000000000000000000000000001070000,
    1000000000000000000000000000001070200, 500162, 1000000000000000000000000000001070100,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500162
      1000000000000000000000000000001070100).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500162
      1000000000000000000000000000001070100).2, 512891320, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1.lean
