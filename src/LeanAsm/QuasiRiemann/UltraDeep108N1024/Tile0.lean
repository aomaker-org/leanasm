-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile0.lean
-- Chunked anchor fold evaluations and validity for Tile 0 (N = 1024 at t ~ 10^24).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.AnchorModel

namespace QuasiRiemann

private theorem t24_0_c1 :
    foldNatStep 128 0 anchor0Iv24 (step24 500225 1000000000000000000000001539900) =
      (⟨2340895, 2341128⟩, ⟨742871, 743098⟩) := by decide +kernel
private theorem t24_0_c2 :
    foldNatStep 128 128 (⟨2340895, 2341128⟩, ⟨742871, 743098⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2530396, 2530847⟩, ⟨126059, 126496⟩) := by decide +kernel
private theorem t24_0_c3 :
    foldNatStep 128 256 (⟨2530396, 2530847⟩, ⟨126059, 126496⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2369403, 2370073⟩, ⟨703791, 704446⟩) := by decide +kernel
private theorem t24_0_c4 :
    foldNatStep 128 384 (⟨2369403, 2370073⟩, ⟨703791, 704446⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨1998343, 1999229⟩, ⟨363119, 363987⟩) := by decide +kernel
private theorem t24_0_c5 :
    foldNatStep 128 512 (⟨1998343, 1999229⟩, ⟨363119, 363987⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2174823, 2175918⟩, ⟨228737, 229827⟩) := by decide +kernel
private theorem t24_0_c6 :
    foldNatStep 128 640 (⟨2174823, 2175918⟩, ⟨228737, 229827⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2378054, 2379354⟩, ⟨465505, 466809⟩) := by decide +kernel
private theorem t24_0_c7 :
    foldNatStep 128 768 (⟨2378054, 2379354⟩, ⟨465505, 466809⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2734042, 2735557⟩, ⟨746740, 748257⟩) := by decide +kernel
private theorem t24_0_c8 :
    foldNatStep 127 896 (⟨2734042, 2735557⟩, ⟨746740, 748257⟩)
      (step24 500225 1000000000000000000000001539900) =
      (⟨2586828, 2588550⟩, ⟨412993, 414730⟩) := by decide +kernel

theorem tile24_0_valid :
    IsValidLipTile2D
      (evalLipTile108 twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit rawMul108Fast
        Int.mul rawMul18Fast 1024 500125 500325
        1000000000000000000000001539800 1000000000000000000000001540000 319421067 2) := by
  have hev :
      evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
        rawMul108Fast Int.mul rawMul18Fast 1024 500225
        1000000000000000000000001539900 =
        (⟨2586828, 2588550⟩, ⟨412993, 414730⟩) := by
    rw [evalStep24_eq]
    exact foldNatStep_1023_chunks (step24 500225 1000000000000000000000001539900) anchor0Iv24
      _ _ _ _ _ _ _ _
      t24_0_c1 t24_0_c2 t24_0_c3 t24_0_c4 t24_0_c5 t24_0_c6 t24_0_c7 t24_0_c8
  dsimp only [evalLipTile108]
  change IsValidLipTile2D ⟨500125, 500325, 1000000000000000000000001539800,
    1000000000000000000000001540000, 500225, 1000000000000000000000001539900,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500225
      1000000000000000000000001539900).1,
    (evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 500225
      1000000000000000000000001539900).2, 319421067, 2⟩
  rw [hev]
  decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Tile0.lean