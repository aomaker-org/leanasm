-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Bounds.lean
-- High-height Dirichlet partial-sum chunked interval bounds at t ~ 10^24 (N = 1024).
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep108N1024.AnchorModel
import LeanAsm.QuasiRiemann.UltraDeep108N1024.Tile0
import LeanAsm.QuasiRiemann.UltraDeep108N1024.Tile1
import LeanAsm.QuasiRiemann.UltraDeep108N1024.Tile2
import LeanAsm.QuasiRiemann.UltraDeep108N1024.Tile3

namespace QuasiRiemann

/-- Certified `2 × 2` tiling zero-free rectangle for `(σ = 0.500125, N = 1024, t ~ 10^24)`. -/
theorem crtNtt_highTrunc108_N1024_rect :
    highTruncTiles_1e24_N1024.length = 4 ∧
    (∀ t ∈ highTruncTiles_1e24_N1024, IsValidLipTile2D t) ∧
    (∀ s6 t6 : Nat,
      InBox2D 500125 500525 1000000000000000000000001539800
        1000000000000000000000001540200 s6 t6 →
      ∃ tile ∈ highTruncTiles_1e24_N1024,
        IsValidLipTile2D tile ∧
        InBox2D tile.sLo6 tile.sHi6 tile.tLo6 tile.tHi6 s6 t6 ∧
        (∀ zRe0 zIm0 zRe zIm : Int,
          tile.anchorRe.lo * 1000000 ≤ zRe0 ∧ zRe0 ≤ tile.anchorRe.hi * 1000000 →
          tile.anchorIm.lo * 1000000 ≤ zIm0 ∧ zIm0 ≤ tile.anchorIm.hi * 1000000 →
          Int.natAbs (zRe - zRe0) ≤
            tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
              ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
          Int.natAbs (zIm - zIm0) ≤
            tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
              ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
          0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) ∧
    highTruncSpec_1e24_N1024.HasCertifiedNonVanishing := by
  have hval24 : ∀ t ∈ highTruncTiles_1e24_N1024, IsValidLipTile2D t := by
    dsimp [highTruncTiles_1e24_N1024, buildLipTile2x2_108Core]
    rw [twoPiRaw108_eq, lnPrimeTable108_eq, lnHighPrimes108Tree_eq,
      rawMul108_fn_eq, intMul192ViaCrtNtt_fn_eq, rawMul18_fn_eq, grad24_fast_valid]
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h0 | h1 | h2 | h3
    · rw [h0]; exact tile24_0_valid
    · rw [h1]; exact tile24_1_valid
    · rw [h2]; exact tile24_2_valid
    · rw [h3]; exact tile24_3_valid
  have hpart24 : IsPartition2x2Tiles 500125 500325 500525
      1000000000000000000000001539800 1000000000000000000000001540000
      1000000000000000000000001540200 highTruncTiles_1e24_N1024 :=
    buildLipTile2x2_108Core_part twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt
      rawMul108Crt intMul192ViaCrtNtt rawMul18Crt 1024
      500125 500325 500525 1000000000000000000000001539800
      1000000000000000000000001540000 1000000000000000000000001540200 2
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨rfl, hval24, ?_, by decide⟩
  intro s6 t6 hmem
  obtain ⟨tile, htmem, hbox⟩ := partition2x2_covers_all_points _ _ _ _ _ _ _ hpart24 s6 t6 hmem
  have hvt := hval24 tile htmem
  refine ⟨tile, htmem, hvt, hbox, ?_⟩
  intro zRe0 zIm0 zRe zIm hre0 him0 hlipRe hlipIm
  have hsnd := isValidLipTile2D_sound tile hvt s6 t6 hbox zRe0 zIm0 zRe zIm hre0 him0 hlipRe hlipIm
  exact ⟨hsnd.1, hsnd.2.1⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024/Bounds.lean