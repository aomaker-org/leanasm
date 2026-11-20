-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2/Bounds.lean
-- Chunked Dirichlet partial-sum fold evaluation and bounds for N = 2048 (Part 2, Tile 2).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N2048Part1

namespace QuasiRiemann

private theorem t30_2_c1 :
    foldNatStep 128 0 anchor0Iv (step30 500362 1000000000000000000000000000001069900) =
      (⟨1963959, 1964185⟩, ⟨-421812, -421580⟩) := by decide +kernel
private theorem t30_2_c2 :
    foldNatStep 128 128 (⟨1963959, 1964185⟩, ⟨-421812, -421580⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨1646337, 1646787⟩, ⟨-439288, -438837⟩) := by decide +kernel
private theorem t30_2_c3 :
    foldNatStep 128 256 (⟨1646337, 1646787⟩, ⟨-439288, -438837⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨1981351, 1982019⟩, ⟨492297, 492970⟩) := by decide +kernel
private theorem t30_2_c4 :
    foldNatStep 128 384 (⟨1981351, 1982019⟩, ⟨492297, 492970⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2513907, 2514787⟩, ⟨-66489, -65596⟩) := by decide +kernel
private theorem t30_2_c5 :
    foldNatStep 128 512 (⟨2513907, 2514787⟩, ⟨-66489, -65596⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2505167, 2506261⟩, ⟨141391, 142499⟩) := by decide +kernel
private theorem t30_2_c6 :
    foldNatStep 128 640 (⟨2505167, 2506261⟩, ⟨141391, 142499⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2602680, 2603992⟩, ⟨316304, 317624⟩) := by decide +kernel
private theorem t30_2_c7 :
    foldNatStep 128 768 (⟨2602680, 2603992⟩, ⟨316304, 317624⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2354630, 2356159⟩, ⟨-31271, -29737⟩) := by decide +kernel
private theorem t30_2_c8 :
    foldNatStep 128 896 (⟨2354630, 2356159⟩, ⟨-31271, -29737⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2331285, 2333028⟩, ⟨-381063, -379313⟩) := by decide +kernel
private theorem t30_2_c9 :
    foldNatStep 128 1024 (⟨2331285, 2333028⟩, ⟨-381063, -379313⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2156763, 2158719⟩, ⟨-283385, -281417⟩) := by decide +kernel
private theorem t30_2_c10 :
    foldNatStep 128 1152 (⟨2156763, 2158719⟩, ⟨-283385, -281417⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2344366, 2346527⟩, ⟨-183839, -181654⟩) := by decide +kernel
private theorem t30_2_c11 :
    foldNatStep 128 1280 (⟨2344366, 2346527⟩, ⟨-183839, -181654⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2572472, 2574845⟩, ⟨-206411, -204008⟩) := by decide +kernel
private theorem t30_2_c12 :
    foldNatStep 128 1408 (⟨2572472, 2574845⟩, ⟨-206411, -204008⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2842517, 2845109⟩, ⟨199762, 202374⟩) := by decide +kernel
private theorem t30_2_c13 :
    foldNatStep 128 1536 (⟨2842517, 2845109⟩, ⟨199762, 202374⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2943172, 2945973⟩, ⟨170650, 173474⟩) := by decide +kernel
private theorem t30_2_c14 :
    foldNatStep 128 1664 (⟨2943172, 2945973⟩, ⟨170650, 173474⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2873949, 2876964⟩, ⟨215401, 218439⟩) := by decide +kernel
private theorem t30_2_c15 :
    foldNatStep 128 1792 (⟨2873949, 2876964⟩, ⟨215401, 218439⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2787687, 2790913⟩, ⟨-221937, -218688⟩) := by decide +kernel
private theorem t30_2_c16 :
    foldNatStep 127 1920 (⟨2787687, 2790913⟩, ⟨-221937, -218688⟩)
      (step30 500362 1000000000000000000000000000001069900) =
      (⟨2785937, 2789369⟩, ⟨-340717, -337254⟩) := by decide +kernel

theorem tile30_2_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 2048 500262 500462
        1000000000000000000000000000001069800
        1000000000000000000000000000001070000 512891320 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 2048 500362
        1000000000000000000000000000001069900 =
        (⟨2785937, 2789369⟩, ⟨-340717, -337254⟩) := by
    rw [evalStep30_eq]
    exact foldNatStep_2047_chunks (step30 500362 1000000000000000000000000000001069900)
      anchor0Iv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      t30_2_c1 t30_2_c2 t30_2_c3 t30_2_c4 t30_2_c5 t30_2_c6 t30_2_c7 t30_2_c8
      t30_2_c9 t30_2_c10 t30_2_c11 t30_2_c12 t30_2_c13 t30_2_c14 t30_2_c15 t30_2_c16
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500262, 500462, 1000000000000000000000000000001069800,
    1000000000000000000000000000001070000, 500362, 1000000000000000000000000000001069900,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500362
      1000000000000000000000000000001069900).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500362
      1000000000000000000000000000001069900).2, 512891320, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2/Bounds.lean
