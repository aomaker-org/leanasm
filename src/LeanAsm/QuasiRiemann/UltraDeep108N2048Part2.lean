-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2.lean
import LeanAsm.QuasiRiemann.UltraDeep108N2048Part1

namespace QuasiRiemann

/-- Partitioned `2 × 2` tile grid for `(σ = 0.500062, N = 2048, t ~ 10^30)` covering
`[0.500062, 0.500462] × [10^30 + 1.0698, 10^30 + 1.0702]` (containing `σ = 0.5000625`). -/
def highTruncTiles_1e30_N2048 : List LipTile2D :=
  buildLipTile2x2_108Core twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt rawMul108Crt
    intMul192ViaCrtNtt rawMul18Crt 2048
    500062 500262 500462
    1000000000000000000000000000001069800 1000000000000000000000000000001070000
    1000000000000000000000000000001070200 2


private theorem grad30_fast_valid :
    dirichletGradBoundScaled6_2048Core lnPrimeTable108Lit lnHighPrimes108TreeLit Int.mul
      rawMul18Fast 500062 2048 = 512891320 := by
  decide +kernel


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

private theorem tile30_2_valid :
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

private theorem tile30_3_valid :
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

/-- High-height `HighTruncZeroFreeRectSpec` for `(σ = 0.5000625, N = 2048, t ~ 10^30)`. -/
def highTruncSpec_1e30_N2048 : HighTruncZeroFreeRectSpec where
  nTrunc := 2048
  sigmaNum := 8001
  sigmaDen := 16000
  tLoScaled := 1000000000000000000000000000001069800
  tHiScaled := 1000000000000000000000000000001070200
  deltaN := 2683000
  eTail := 1
  epsCrt := 2
  nTrunc_valid := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  sigma_above_half := by decide
  t_ordered := by decide

/-- Certified `2 × 2` tiling zero-free rectangle for `(σ = 0.5000625, N = 2048, t ~ 10^30)`. -/
theorem crtNtt_highTrunc108_N2048_rect :
    highTruncTiles_1e30_N2048.length = 4 ∧
    (∀ t ∈ highTruncTiles_1e30_N2048, IsValidLipTile2D t) ∧
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
    highTruncSpec_1e30_N2048.HasCertifiedNonVanishing := by
  have hval30 : ∀ t ∈ highTruncTiles_1e30_N2048, IsValidLipTile2D t := by
    dsimp [highTruncTiles_1e30_N2048, buildLipTile2x2_108Core]
    rw [twoPiRaw108_eq, lnPrimeTable108_eq, lnHighPrimes108Tree_eq,
      rawMul108_fn_eq, intMul192ViaCrtNtt_fn_eq, rawMul18_fn_eq, grad30_fast_valid]
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h0 | h1 | h2 | h3
    · rw [h0]; exact tile30_0_valid
    · rw [h1]; exact tile30_1_valid
    · rw [h2]; exact tile30_2_valid
    · rw [h3]; exact tile30_3_valid
  have hpart30 : IsPartition2x2Tiles 500062 500262 500462
      1000000000000000000000000000001069800 1000000000000000000000000000001070000
      1000000000000000000000000000001070200 highTruncTiles_1e30_N2048 :=
    buildLipTile2x2_108Core_part twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt
      rawMul108Crt intMul192ViaCrtNtt rawMul18Crt 2048
      500062 500262 500462 1000000000000000000000000000001069800
      1000000000000000000000000000001070000 1000000000000000000000000000001070200 2
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨rfl, hval30, ?_, by decide⟩
  intro s6 t6 hmem
  obtain ⟨tile, htmem, hbox⟩ := partition2x2_covers_all_points _ _ _ _ _ _ _ hpart30 s6 t6 hmem
  have hvt := hval30 tile htmem
  refine ⟨tile, htmem, hvt, hbox, ?_⟩
  intro zRe0 zIm0 zRe zIm hre0 him0 hlipRe hlipIm
  have hsnd := isValidLipTile2D_sound tile hvt s6 t6 hbox zRe0 zIm0 zRe zIm hre0 him0 hlipRe hlipIm
  exact ⟨hsnd.1, hsnd.2.1⟩

/-- Step 0 `t ~ 10^30` rectangle for `2/5` contraction (`radL1 = 2500`). -/
def nestedBox1e30_0 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 502500
  tLo6 := 1000000000000000000000000000001068750
  tHi6 := 1000000000000000000000000000001071250
  sMid6 := 501250
  tMid6 := 1000000000000000000000000000001070000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 1 `t ~ 10^30` rectangle after `2/5` contraction (`radL1 = 1000`). -/
def nestedBox1e30_1 : NestedBox2D where
  sLo6 := 500000
  sHi6 := 501000
  tLo6 := 1000000000000000000000000000001069500
  tHi6 := 1000000000000000000000000000001070500
  sMid6 := 500500
  tMid6 := 1000000000000000000000000000001070000
  s_ordered := by decide
  t_ordered := by decide

/-- Step 2 `N = 2048`, `σ = 0.5000625` (`radL1 = 400`) box matching `highTruncTiles_1e30_N2048`. -/
def nestedBox1e30_2 : NestedBox2D where
  sLo6 := 500062
  sHi6 := 500462
  tLo6 := 1000000000000000000000000000001069800
  tHi6 := 1000000000000000000000000000001070200
  sMid6 := 500262
  tMid6 := 1000000000000000000000000000001070000
  s_ordered := by decide
  t_ordered := by decide

/-- Indexed `2/5`-contraction family ending at `nestedBox1e30_2` (`N = 2048`). -/
def nestedBoxSeq1e30_N2048 : Nat → NestedBox2D
  | 0 => nestedBox1e30_0
  | 1 => nestedBox1e30_1
  | _ => nestedBox1e30_2

/-- Drift sequence with exact `2/5` contraction (`1282500000000 → 513000000000 → 205200000000`). -/
def driftSeq1e30_N2048 : Nat → Nat
  | 0 => 1282500000000
  | 1 => 513000000000
  | _ => 205200000000

/-- Concrete `RationalBoxContractionSpec` (`q = 2/5`, shrunk `M / (r - δ)`) for `N = 2048`. -/
def rationalBoxSpec_N2048 : RationalBoxContractionSpec where
  qNum := 2
  qDen := 5
  qNum_pos := by decide
  qNum_lt_qDen := by decide
  lipNumerator := 513000000
  radius := nestedBox1e30_2.radL1
  deltaShrink := 100
  shrink_lt_radius := by decide
  centerLower := 2700000000000
  centerLower_pos := by decide
  lip_margin_ok := by decide

/-- Theorem (`N = 2048`, `σ = 0.5000625 = 1/2 + 1/16000`, `t ~ 10^30` Contraction & Tiling): -/
theorem ultraDeep72_N2048_rational_rect_cert :
    nestedBox1e30_2.SubBox nestedBox1e30_0 ∧
    5 ^ 2 * driftSeq1e30_N2048 2 ≤ 2 ^ 2 * driftSeq1e30_N2048 0 ∧
    QRat.eqv (QRat.mk' 8001 16000 (by decide))
      (QRat.mk' 1 2 (by decide) + QRat.mk' 1 16000 (by decide)) ∧
    rationalBoxSpec_N2048.lipNumerator * rationalBoxSpec_N2048.radius <
      rationalBoxSpec_N2048.centerLower *
        (rationalBoxSpec_N2048.radius - rationalBoxSpec_N2048.deltaShrink) ∧
    (∀ centerMag pointMag dist : Nat,
      2700000000000 ≤ centerMag →
      dist ≤ 400 →
      300 * Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤ 513000000 * dist →
      1350000000000 ≤ pointMag ∧ 0 < pointMag) ∧
    dirichletGradBoundScaled6_2048 500062 2048 = 512891320 ∧
    16 * 999 * 999 < 5 * 17 * 257 * 65537 ∧
    eulerMaclaurinB2TailRect2DForN 2048 500062
        (10 ^ 30 * 1000000) (10 ^ 30 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 1024 500062
        (10 ^ 30 * 1000000) (10 ^ 30 * 1000000 + 2000000) ∧
    highTruncSpec_1e30_N2048.HasCertifiedNonVanishing ∧
    (∀ s6 t6 : Nat,
      InBox2D nestedBox1e30_2.sLo6 nestedBox1e30_2.sHi6
        nestedBox1e30_2.tLo6 nestedBox1e30_2.tHi6 s6 t6 →
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
          0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) := by
  have hChain := rational_telescoping_chain_cert 2 5 (by decide) (by decide)
    nestedBoxSeq1e30_N2048 (fun _ => 513000000) driftSeq1e30_N2048 2700000000000
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
  have hGrad : dirichletGradBoundScaled6_2048 500062 2048 = 512891320 := by
    dsimp [dirichletGradBoundScaled6_2048]
    rw [lnPrimeTable108_eq, lnHighPrimes108Tree_eq, intMul192ViaCrtNtt_fn_eq, rawMul18_fn_eq]
    exact grad30_fast_valid
  have hTail :
      eulerMaclaurinB2TailRect2DForN 2048 500062
        (10 ^ 30 * 1000000) (10 ^ 30 * 1000000 + 2000000) ≤
      eulerMaclaurinB2TailRect2DForN 1024 500062
        (10 ^ 30 * 1000000) (10 ^ 30 * 1000000 + 2000000) := by
    dsimp [eulerMaclaurinB2TailRect2DForN]
    have h1 : nPowNegUpperForN 2048 500062 = (1, 45) := by decide
    have h2 : nPowNegUpperForN 1024 500062 = (1, 32) := by decide
    rw [h1, h2]
    exact tail_mono_of_den (by decide) (by decide) (by decide) (by decide)
  have hRect := crtNtt_highTrunc108_N2048_rect
  refine ⟨hChain.1, hChain.2.1, by decide, rationalBoxSpec_N2048.lip_mul_radius_lt, ?_, hGrad,
    by decide, hTail, hRect.2.2.2, ?_⟩
  · intro centerMag pointMag dist hCenter hDist hLip
    have hStep := rational_box_contraction_step rationalBoxSpec_N2048
      centerMag pointMag dist (driftSeq1e30_N2048 0) (driftSeq1e30_N2048 1)
      hCenter hDist hLip (by decide)
    exact ⟨hStep.1, hStep.2.2.1⟩
  · intro s6 t6 hmem
    exact hRect.2.2.1 s6 t6 hmem

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108N2048Part2.lean
