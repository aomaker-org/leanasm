-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108.lean
import LeanAsm.QuasiRiemann.UltraDeep108Tables
import LeanAsm.QuasiRiemann.UltraDeep108Eval
import LeanAsm.QuasiRiemann.UltraDeep108N1024
import LeanAsm.QuasiRiemann.UltraDeep108N2048

namespace QuasiRiemann

/-- Theorem (108-Digit Compositional 2D `(σ, t)`-Box Tiling Zero-Free Rectangles):
Certifies partitioned 2D sub-rectangles for `(σ = 0.500125, N = 1024, t ~ 10^24)` and
`(σ = 0.5000625, N = 2048, t ~ 10^30)` via 108-digit Chudnovsky phase reduction and
cleared-denominator Lipschitz derivative bounds. Zero `Classical.choice`, zero `sorryAx`. -/
theorem crtNtt_highTrunc108_2d_zero_free_rect :
    highTruncTiles_1e24_N1024.length = 4 ∧
    highTruncTiles_1e30_N2048.length = 4 ∧
    (∀ t ∈ highTruncTiles_1e24_N1024, IsValidLipTile2D t) ∧
    (∀ t ∈ highTruncTiles_1e30_N2048, IsValidLipTile2D t) ∧
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
    (∀ s6 t6 : Nat,
      InBox2D 500062 500462 1000000000000000000000000000001069800
        1000000000000000000000000000001070200 s6 t6 →
      ∃ tile ∈ highTruncTiles_1e30_N2048,
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
    highTruncSpec_1e24_N1024.HasCertifiedNonVanishing ∧
    highTruncSpec_1e30_N2048.HasCertifiedNonVanishing :=
  let h24 := crtNtt_highTrunc108_N1024_rect
  let h30 := crtNtt_highTrunc108_N2048_rect
  ⟨h24.1, h30.1, h24.2.1, h30.2.1, h24.2.2.1, h30.2.2.1, h24.2.2.2, h30.2.2.2⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108.lean
