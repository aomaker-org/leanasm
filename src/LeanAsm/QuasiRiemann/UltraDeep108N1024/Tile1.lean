-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile1.lean
-- Chunked anchor fold evaluations and validity for Tile 1 (N = 1024 at t ~ 10^24).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.AnchorModel

namespace QuasiRiemann

private theorem t24_1_c1 :
    foldNatStep 128 0 anchor0Iv24 (step24 500225 1000000000000000000000001540100) =
      (⟨2341449, 2341683⟩, ⟨741979, 742204⟩) := by decide +kernel
private theorem t24_1_c2 :
    foldNatStep 128 128 (⟨2341449, 2341683⟩, ⟨741979, 742204⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2530312, 2530764⟩, ⟨124923, 125369⟩) := by decide +kernel
private theorem t24_1_c3 :
    foldNatStep 128 256 (⟨2530312, 2530764⟩, ⟨124923, 125369⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2369978, 2370644⟩, ⟨702844, 703507⟩) := by decide +kernel
private theorem t24_1_c4 :
    foldNatStep 128 384 (⟨2369978, 2370644⟩, ⟨702844, 703507⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨1998503, 1999386⟩, ⟨362617, 363494⟩) := by decide +kernel
private theorem t24_1_c5 :
    foldNatStep 128 512 (⟨1998503, 1999386⟩, ⟨362617, 363494⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2174810, 2175905⟩, ⟨228014, 229110⟩) := by decide +kernel
private theorem t24_1_c6 :
    foldNatStep 128 640 (⟨2174810, 2175905⟩, ⟨228014, 229110⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2378345, 2379651⟩, ⟨464515, 465834⟩) := by decide +kernel
private theorem t24_1_c7 :
    foldNatStep 128 768 (⟨2378345, 2379651⟩, ⟨464515, 465834⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2734714, 2736234⟩, ⟨745266, 746804⟩) := by decide +kernel
private theorem t24_1_c8 :
    foldNatStep 127 896 (⟨2734714, 2736234⟩, ⟨745266, 746804⟩)
      (step24 500225 1000000000000000000000001540100) =
      (⟨2587036, 2588766⟩, ⟨411729, 413475⟩) := by decide +kernel

theorem tile24_1_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 1024 500125 500325
        1000000000000000000000001540000 1000000000000000000000001540200 319421067 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 1024 500225
        1000000000000000000000001540100 =
        (⟨2587036, 2588766⟩, ⟨411729, 413475⟩) := by
    rw [evalStep24_eq]
    exact foldNatStep_1023_chunks (step24 500225 1000000000000000000000001540100) anchor0Iv24
      _ _ _ _ _ _ _ _
      t24_1_c1 t24_1_c2 t24_1_c3 t24_1_c4 t24_1_c5 t24_1_c6 t24_1_c7 t24_1_c8
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500125, 500325, 1000000000000000000000001540000,
    1000000000000000000000001540200, 500225, 1000000000000000000000001540100,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500225
      1000000000000000000000001540100).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500225
      1000000000000000000000001540100).2, 319421067, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile1.lean