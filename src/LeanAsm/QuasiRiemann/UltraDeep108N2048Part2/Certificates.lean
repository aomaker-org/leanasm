-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2/Certificates.lean
-- High-height Dirichlet partial-sum tile certificate for N = 2048 (Part 2, Tile 3).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N2048Part2.Bounds

namespace QuasiRiemann

private theorem t30_3_c1 :
    foldNatStep 128 0 anchor0Iv (step30 500362 1000000000000000000000000000001070100) =
      (⟨1963817, 1964050⟩, ⟨-422242, -422009⟩) := by decide +kernel
private theorem t30_3_c2 :
    foldNatStep 128 128 (⟨1963817, 1964050⟩, ⟨-422242, -422009⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨1646186, 1646639⟩, ⟨-439422, -438977⟩) := by decide +kernel
private theorem t30_3_c3 :
    foldNatStep 128 256 (⟨1646186, 1646639⟩, ⟨-439422, -438977⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨1982274, 1982947⟩, ⟨491782, 492450⟩) := by decide +kernel
private theorem t30_3_c4 :
    foldNatStep 128 384 (⟨1982274, 1982947⟩, ⟨491782, 492450⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2514145, 2515033⟩, ⟨-67652, -66770⟩) := by decide +kernel
private theorem t30_3_c5 :
    foldNatStep 128 512 (⟨2514145, 2515033⟩, ⟨-67652, -66770⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2505673, 2506777⟩, ⟨140232, 141330⟩) := by decide +kernel
private theorem t30_3_c6 :
    foldNatStep 128 640 (⟨2505673, 2506777⟩, ⟨140232, 141330⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2603414, 2604736⟩, ⟨315027, 316322⟩) := by decide +kernel
private theorem t30_3_c7 :
    foldNatStep 128 768 (⟨2603414, 2604736⟩, ⟨315027, 316322⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2354898, 2356434⟩, ⟨-32217, -30707⟩) := by decide +kernel
private theorem t30_3_c8 :
    foldNatStep 128 896 (⟨2354898, 2356434⟩, ⟨-32217, -30707⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2331069, 2332814⟩, ⟨-381969, -380250⟩) := by decide +kernel
private theorem t30_3_c9 :
    foldNatStep 128 1024 (⟨2331069, 2332814⟩, ⟨-381969, -380250⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2156687, 2158643⟩, ⟨-284047, -282117⟩) := by decide +kernel
private theorem t30_3_c10 :
    foldNatStep 128 1152 (⟨2156687, 2158643⟩, ⟨-284047, -282117⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2344427, 2346593⟩, ⟨-184769, -182627⟩) := by decide +kernel
private theorem t30_3_c11 :
    foldNatStep 128 1280 (⟨2344427, 2346593⟩, ⟨-184769, -182627⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2572510, 2574876⟩, ⟨-207665, -205307⟩) := by decide +kernel
private theorem t30_3_c12 :
    foldNatStep 128 1408 (⟨2572510, 2574876⟩, ⟨-207665, -205307⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2843151, 2845731⟩, ⟨198113, 200678⟩) := by decide +kernel
private theorem t30_3_c13 :
    foldNatStep 128 1536 (⟨2843151, 2845731⟩, ⟨198113, 200678⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2943767, 2946556⟩, ⟨168850, 171632⟩) := by decide +kernel
private theorem t30_3_c14 :
    foldNatStep 128 1664 (⟨2943767, 2946556⟩, ⟨168850, 171632⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2874611, 2877607⟩, ⟨213701, 216687⟩) := by decide +kernel
private theorem t30_3_c15 :
    foldNatStep 128 1792 (⟨2874611, 2877607⟩, ⟨213701, 216687⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2787689, 2790899⟩, ⟨-223506, -220314⟩) := by decide +kernel
private theorem t30_3_c16 :
    foldNatStep 127 1920 (⟨2787689, 2790899⟩, ⟨-223506, -220314⟩)
      (step30 500362 1000000000000000000000000000001070100) =
      (⟨2785752, 2789176⟩, ⟨-342281, -338878⟩) := by decide +kernel

theorem tile30_3_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 2048 500262 500462
        1000000000000000000000000000001070000
        1000000000000000000000000000001070200 512891320 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 2048 500362
        1000000000000000000000000000001070100 =
        (⟨2785752, 2789176⟩, ⟨-342281, -338878⟩) := by
    rw [evalStep30_eq]
    exact foldNatStep_2047_chunks (step30 500362 1000000000000000000000000000001070100)
      anchor0Iv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      t30_3_c1 t30_3_c2 t30_3_c3 t30_3_c4 t30_3_c5 t30_3_c6 t30_3_c7 t30_3_c8
      t30_3_c9 t30_3_c10 t30_3_c11 t30_3_c12 t30_3_c13 t30_3_c14 t30_3_c15 t30_3_c16
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500262, 500462, 1000000000000000000000000000001070000,
    1000000000000000000000000000001070200, 500362, 1000000000000000000000000000001070100,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500362
      1000000000000000000000000000001070100).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 2048 500362
      1000000000000000000000000000001070100).2, 512891320, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2/Certificates.lean
