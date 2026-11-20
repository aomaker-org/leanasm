-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1/Certificates.lean
-- High-height Dirichlet partial-sum tile certificate for N = 2048 (Part 1, Tile 1).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N2048Part1.Bounds

namespace QuasiRiemann

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

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part1/Certificates.lean
