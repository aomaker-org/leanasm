-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024.lean
import LeanAsm.QuasiRiemann.UltraDeep108Eval

namespace QuasiRiemann

/-- Partitioned `2 × 2` tile grid for `(σ = 0.500125, N = 1024, t ~ 10^24)` covering
`[0.500125, 0.500525] × [10^24 + 1.5398, 10^24 + 1.5402]`. -/
def highTruncTiles_1e24_N1024 : List LipTile2D :=
  buildLipTile2x2_108Core twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt rawMul108Crt
    intMul192ViaCrtNtt rawMul18Crt 1024
    500125 500325 500525 1000000000000000000000001539800 1000000000000000000000001540000
      1000000000000000000000001540200 2

private theorem grad24_fast_valid :
    dirichletGradBoundScaled6_2048Core lnPrimeTable108Lit lnHighPrimes108TreeLit Int.mul
      rawMul18Fast 500125 1024 = 319421067 := by
  decide +kernel

private def step24 (sMid6 tMid6 : Nat) :
    Nat → ScaledInterval × ScaledInterval → ScaledInterval × ScaledInterval :=
  zetaAnchorStep108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
    rawMul108Fast Int.mul rawMul18Fast
    ((sMid6 : Int) * scale12TInt, (sMid6 : Int) * scale12TInt)
    ((tMid6 : Int) * scale102Int, (tMid6 : Int) * scale102Int)

private def anchor0Iv : ScaledInterval × ScaledInterval := (⟨1000000, 1000000⟩, ⟨0, 0⟩)

private theorem evalStep24_eq (sm tm : Nat) :
    evalZetaAnchorHigh108Core twoPiRaw108Lit lnPrimeTable108Lit lnHighPrimes108TreeLit
      rawMul108Fast Int.mul rawMul18Fast 1024 sm tm =
    foldNatStep 1023 0 anchor0Iv (step24 sm tm) := rfl

private theorem t24_0_c1 :
    foldNatStep 128 0 anchor0Iv (step24 500225 1000000000000000000000001539900) =
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

private theorem t24_1_c1 :
    foldNatStep 128 0 anchor0Iv (step24 500225 1000000000000000000000001540100) =
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

private theorem t24_2_c1 :
    foldNatStep 128 0 anchor0Iv (step24 500425 1000000000000000000000001539900) =
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

private theorem t24_3_c1 :
    foldNatStep 128 0 anchor0Iv (step24 500425 1000000000000000000000001540100) =
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

private theorem tile24_0_valid :
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
    exact foldNatStep_1023_chunks (step24 500225 1000000000000000000000001539900) anchor0Iv
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

private theorem tile24_1_valid :
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
    exact foldNatStep_1023_chunks (step24 500225 1000000000000000000000001540100) anchor0Iv
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

private theorem tile24_2_valid :
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
    exact foldNatStep_1023_chunks (step24 500425 1000000000000000000000001539900) anchor0Iv
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

private theorem tile24_3_valid :
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
    exact foldNatStep_1023_chunks (step24 500425 1000000000000000000000001540100) anchor0Iv
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

/-- High-height `HighTruncZeroFreeRectSpec` for `(σ = 0.500125, N = 1024, t ~ 10^24)`. -/
def highTruncSpec_1e24_N1024 : HighTruncZeroFreeRectSpec where
  nTrunc := 1024
  sigmaNum := 4001
  sigmaDen := 8000
  tLoScaled := 1000000000000000000000001539800
  tHiScaled := 1000000000000000000000001540200
  deltaN := 2522000
  eTail := 1
  epsCrt := 2
  nTrunc_valid := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  sigma_above_half := by decide
  t_ordered := by decide

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

/-- Step 0 `t ~ 10^24` rectangle for `1/3` contraction (`radL1 = 3600`). -/
def nestedBox1e24_0 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 503600
  tLo6 := 1000000000000000000000001538200
  tHi6 := 1000000000000000000000001541800
  sMid6 := 501800
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 1 `t ~ 10^24` rectangle after `1/3` contraction (`radL1 = 1200`). -/
def nestedBox1e24_1 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 501200
  tLo6 := 1000000000000000000000001539400
  tHi6 := 1000000000000000000000001540600
  sMid6 := 500600
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 2 `N = 1024`, `σ = 0.500125` (`radL1 = 400`) box matching `highTruncTiles_1e24_N1024`. -/
def nestedBox1e24_2 : NestedBox2D where
  sLo6 := 500125
  sHi6 := 500525
  tLo6 := 1000000000000000000000001539800
  tHi6 := 1000000000000000000000001540200
  sMid6 := 500325
  tMid6 := 1000000000000000000000001540000
  s_ordered := by decide
  t_ordered := by decide

/-- Indexed `1/3`-contraction family ending at `nestedBox1e24_2` (`N = 1024`, `σ = 0.500125`). -/
def nestedBoxSeq1e24_N1024 : Nat → NestedBox2D
  | 0 => nestedBox1e24_0
  | 1 => nestedBox1e24_1
  | _ => nestedBox1e24_2

/-- Drift sequence with exact `1/3` contraction (`1152000000000 → 384000000000 → 128000000000`). -/
def driftSeq1e24_N1024 : Nat → Nat
  | 0 => 1152000000000
  | 1 => 384000000000
  | _ => 128000000000

/-- Concrete `RationalBoxContractionSpec` (`q = 1/3`, shrunk `M / (r - δ)`) for `N = 1024`. -/
def rationalBoxSpec_N1024 : RationalBoxContractionSpec where
  qNum := 1
  qDen := 3
  qNum_pos := by decide
  qNum_lt_qDen := by decide
  lipNumerator := 320000000
  radius := nestedBox1e24_2.radL1
  deltaShrink := 100
  shrink_lt_radius := by decide
  centerLower := 2500000000000
  centerLower_pos := by decide
  lip_margin_ok := by decide

/-- Theorem (`N = 1024`, `σ = 0.500125 = 1/2 + 1/8000`, `t ~ 10^24` Contraction & Tiling): -/
theorem ultraDeep72_N1024_rational_rect_cert :
    nestedBox1e24_2.SubBox nestedBox1e24_0 ∧
    3 ^ 2 * driftSeq1e24_N1024 2 ≤ 1 ^ 2 * driftSeq1e24_N1024 0 ∧
    QRat.eqv (QRat.mk' 4001 8000 (by decide))
      (QRat.mk' 1 2 (by decide) + QRat.mk' 1 8000 (by decide)) ∧
    rationalBoxSpec_N1024.lipNumerator * rationalBoxSpec_N1024.radius <
      rationalBoxSpec_N1024.centerLower *
        (rationalBoxSpec_N1024.radius - rationalBoxSpec_N1024.deltaShrink) ∧
    (∀ centerMag pointMag dist : Nat,
      2500000000000 ≤ centerMag →
      dist ≤ 400 →
      300 * Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤ 320000000 * dist →
      1250000000000 ≤ pointMag ∧ 0 < pointMag) ∧
    dirichletGradBoundScaled6_2048 500125 1024 = 319421067 ∧
    16 * 999 * 999 < 5 * 17 * 257 * 65537 ∧
    eulerMaclaurinB2TailRect2DForN 1024 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 512 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ∧
    highTruncSpec_1e24_N1024.HasCertifiedNonVanishing ∧
    (∀ s6 t6 : Nat,
      InBox2D nestedBox1e24_2.sLo6 nestedBox1e24_2.sHi6
        nestedBox1e24_2.tLo6 nestedBox1e24_2.tHi6 s6 t6 →
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
          0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) := by
  have hChain := rational_telescoping_chain_cert 1 3 (by decide) (by decide)
    nestedBoxSeq1e24_N1024 (fun _ => 320000000) driftSeq1e24_N1024 2500000000000
    (by decide) (by decide) 2
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | i + 2 => omega)
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | i + 2 => omega)
    (fun i hi => by
      match i with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | i + 3 => omega)
  have hGrad : dirichletGradBoundScaled6_2048 500125 1024 = 319421067 := by
    dsimp [dirichletGradBoundScaled6_2048]
    rw [lnPrimeTable108_eq, lnHighPrimes108Tree_eq, intMul192ViaCrtNtt_fn_eq, rawMul18_fn_eq]
    exact grad24_fast_valid
  have hTail :
      eulerMaclaurinB2TailRect2DForN 1024 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 512 500125
        (10 ^ 24 * 1000000) (10 ^ 24 * 1000000 + 2000000) := by
    dsimp [eulerMaclaurinB2TailRect2DForN]
    have h1 : nPowNegUpperForN 1024 500125 = (1, 32) := by decide
    have h2 : nPowNegUpperForN 512 500125 = (1, 22) := by decide
    rw [h1, h2]
    exact tail_mono_of_den (by decide) (by decide) (by decide) (by decide)
  have hRect := crtNtt_highTrunc108_N1024_rect
  refine ⟨hChain.1, hChain.2.1, by decide, rationalBoxSpec_N1024.lip_mul_radius_lt, ?_, hGrad,
    by decide, hTail, hRect.2.2.2, ?_⟩
  · intro centerMag pointMag dist hCenter hDist hLip
    have hStep := rational_box_contraction_step rationalBoxSpec_N1024
      centerMag pointMag dist (driftSeq1e24_N1024 0) (driftSeq1e24_N1024 1)
      hCenter hDist hLip (by decide)
    exact ⟨hStep.1, hStep.2.2.1⟩
  · intro s6 t6 hmem
    exact hRect.2.2.1 s6 t6 hmem

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N1024.lean
