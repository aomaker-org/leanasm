-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile2.lean
-- Chunked anchor fold evaluations and validity for Tile 2 (N = 1024 at t ~ 10^24).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.AnchorModel

namespace QuasiRiemann

private theorem t24_2_c1 :
    foldNatStep 128 0 anchor0Iv24 (step24 500425 1000000000000000000000001539900) =
      (⟨2339996, 2340233⟩, ⟨742320, 742539⟩) := by decide +kernel
private theorem t24_2_c2 :
    foldNatStep 128 128 (⟨2339996, 2340233⟩, ⟨742320, 742539⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2529250, 2529709⟩, ⟨126148, 126585⟩) := by decide +kernel
private theorem t24_2_c3 :
    foldNatStep 128 256 (⟨2529250, 2529709⟩, ⟨126148, 126585⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2368441, 2369133⟩, ⟨703228, 703883⟩) := by decide +kernel
private theorem t24_2_c4 :
    foldNatStep 128 384 (⟨2368441, 2369133⟩, ⟨703228, 703883⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨1997823, 1998729⟩, ⟨362971, 363837⟩) := by decide +kernel
private theorem t24_2_c5 :
    foldNatStep 128 512 (⟨1997823, 1998729⟩, ⟨362971, 363837⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2174074, 2175191⟩, ⟨228762, 229846⟩) := by decide +kernel
private theorem t24_2_c6 :
    foldNatStep 128 640 (⟨2174074, 2175191⟩, ⟨228762, 229846⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2377036, 2378363⟩, ⟨465225, 466523⟩) := by decide +kernel
private theorem t24_2_c7 :
    foldNatStep 128 768 (⟨2377036, 2378363⟩, ⟨465225, 466523⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2732545, 2734087⟩, ⟨746080, 747598⟩) := by decide +kernel
private theorem t24_2_c8 :
    foldNatStep 127 896 (⟨2732545, 2734087⟩, ⟨746080, 747598⟩)
      (step24 500425 1000000000000000000000001539900) =
      (⟨2585533, 2587275⟩, ⟨412797, 414528⟩) := by decide +kernel

theorem tile24_2_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 1024 500325 500525
        1000000000000000000000001539800 1000000000000000000000001540000 319421067 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 1024 500425
        1000000000000000000000001539900 =
        (⟨2585533, 2587275⟩, ⟨412797, 414528⟩) := by
    rw [evalStep24_eq]
    exact foldNatStep_1023_chunks (step24 500425 1000000000000000000000001539900) anchor0Iv24
      _ _ _ _ _ _ _ _
      t24_2_c1 t24_2_c2 t24_2_c3 t24_2_c4 t24_2_c5 t24_2_c6 t24_2_c7 t24_2_c8
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500325, 500525, 1000000000000000000000001539800,
    1000000000000000000000001540000, 500425, 1000000000000000000000001539900,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500425
      1000000000000000000000001539900).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500425
      1000000000000000000000001539900).2, 319421067, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile2.lean