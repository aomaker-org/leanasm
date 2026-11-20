-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile3.lean
-- Chunked anchor fold evaluations and validity for Tile 3 (N = 1024 at t ~ 10^24).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.AnchorModel

namespace QuasiRiemann

private theorem t24_3_c1 :
    foldNatStep 128 0 anchor0Iv24 (step24 500425 1000000000000000000000001540100) =
      (⟨2340553, 2340785⟩, ⟨741433, 741653⟩) := by decide +kernel
private theorem t24_3_c2 :
    foldNatStep 128 128 (⟨2340553, 2340785⟩, ⟨741433, 741653⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2529167, 2529626⟩, ⟨125022, 125461⟩) := by decide +kernel
private theorem t24_3_c3 :
    foldNatStep 128 256 (⟨2529167, 2529626⟩, ⟨125022, 125461⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2369020, 2369704⟩, ⟨702301, 702950⟩) := by decide +kernel
private theorem t24_3_c4 :
    foldNatStep 128 384 (⟨2369020, 2369704⟩, ⟨702301, 702950⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨1997984, 1998884⟩, ⟨362494, 363353⟩) := by decide +kernel
private theorem t24_3_c5 :
    foldNatStep 128 512 (⟨1997984, 1998884⟩, ⟨362494, 363353⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2174070, 2175180⟩, ⟨228060, 229137⟩) := by decide +kernel
private theorem t24_3_c6 :
    foldNatStep 128 640 (⟨2174070, 2175180⟩, ⟨228060, 229137⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2377347, 2378660⟩, ⟨464254, 465548⟩) := by decide +kernel
private theorem t24_3_c7 :
    foldNatStep 128 768 (⟨2377347, 2378660⟩, ⟨464254, 465548⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2733229, 2734759⟩, ⟨744625, 746140⟩) := by decide +kernel
private theorem t24_3_c8 :
    foldNatStep 127 896 (⟨2733229, 2734759⟩, ⟨744625, 746140⟩)
      (step24 500425 1000000000000000000000001540100) =
      (⟨2585752, 2587493⟩, ⟨411546, 413271⟩) := by decide +kernel

theorem tile24_3_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 1024 500325 500525
        1000000000000000000000001540000 1000000000000000000000001540200 319421067 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 1024 500425
        1000000000000000000000001540100 =
        (⟨2585752, 2587493⟩, ⟨411546, 413271⟩) := by
    rw [evalStep24_eq]
    exact foldNatStep_1023_chunks (step24 500425 1000000000000000000000001540100) anchor0Iv24
      _ _ _ _ _ _ _ _
      t24_3_c1 t24_3_c2 t24_3_c3 t24_3_c4 t24_3_c5 t24_3_c6 t24_3_c7 t24_3_c8
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500325, 500525, 1000000000000000000000001540000,
    1000000000000000000000001540200, 500425, 1000000000000000000000001540100,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500425
      1000000000000000000000001540100).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500425
      1000000000000000000000001540100).2, 319421067, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile3.lean