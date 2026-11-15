-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108Eval.lean
import LeanAsm.QuasiRiemann.UltraDeep108Tables

namespace QuasiRiemann

def dirichletGradBoundScaled6_2048Core
    (t31 : LnPrimeTable72) (hiTree : PrimeTree108)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (sLo6 nMax : Nat) : Nat :=
  let sigmaIv18 : RawIv72 := ((sLo6 : Int) * scale12TInt, (sLo6 : Int) * scale12TInt)
  foldNatStep (nMax - 1) 0 0 (fun idx acc =>
    let n := idx + 2
    let ln18 := rawTo18From108 (lnRaw108_2048 t31 hiTree n)
    let ampHi := (rawTaylorExpNeg18 mulS (mul18 sigmaIv18 ln18)).2
    let term18 := (ln18.2 * ampHi + scale18TInt - 1) / scale18TInt
    let term6 := (term18 * 1000000 + scale18TInt - 1) / scale18TInt
    acc + term6.natAbs)

/-- True `10^6`-scaled constructive Lipschitz gradient upper bound `∑_{n=2}^N (ln n) n^{-σ_0}`
for `N ≤ 2048`, computed via `intMul192ViaCrtNtt` and `lnInterval108_2048`. -/
def dirichletGradBoundScaled6_2048 : Nat → Nat → Nat :=
  dirichletGradBoundScaled6_2048Core lnPrimeTable108Crt lnHighPrimes108TreeCrt
    intMul192ViaCrtNtt rawMul18Crt

theorem foldNatStep_add {α : Type} (a b k : Nat) (acc : α) (step : Nat → α → α) :
    foldNatStep (a + b) k acc step =
      foldNatStep b (k + a) (foldNatStep a k acc step) step := by
  induction a generalizing k acc with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
    rfl
  | succ a' ih =>
    rw [Nat.succ_add]
    dsimp [foldNatStep]
    rw [ih (k + 1) (step k acc), Nat.add_right_comm k 1 a', Nat.add_assoc k a' 1]

theorem foldNatStep_1023_chunks {α : Type} (step : Nat → α → α)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 : α)
    (h0 : foldNatStep 128 0 v0 step = v1)
    (h1 : foldNatStep 128 128 v1 step = v2)
    (h2 : foldNatStep 128 256 v2 step = v3)
    (h3 : foldNatStep 128 384 v3 step = v4)
    (h4 : foldNatStep 128 512 v4 step = v5)
    (h5 : foldNatStep 128 640 v5 step = v6)
    (h6 : foldNatStep 128 768 v6 step = v7)
    (h7 : foldNatStep 127 896 v7 step = v8) :
    foldNatStep 1023 0 v0 step = v8 := by
  have hc0 : foldNatStep (128 + 895) 0 v0 step = foldNatStep 895 128 v1 step := by
    rw [foldNatStep_add, Nat.zero_add, h0]
  have hc1 : foldNatStep (128 + 767) 128 v1 step = foldNatStep 767 256 v2 step := by
    rw [foldNatStep_add, h1]
  have hc2 : foldNatStep (128 + 639) 256 v2 step = foldNatStep 639 384 v3 step := by
    rw [foldNatStep_add, h2]
  have hc3 : foldNatStep (128 + 511) 384 v3 step = foldNatStep 511 512 v4 step := by
    rw [foldNatStep_add, h3]
  have hc4 : foldNatStep (128 + 383) 512 v4 step = foldNatStep 383 640 v5 step := by
    rw [foldNatStep_add, h4]
  have hc5 : foldNatStep (128 + 255) 640 v5 step = foldNatStep 255 768 v6 step := by
    rw [foldNatStep_add, h5]
  have hc6 : foldNatStep (128 + 127) 768 v6 step = foldNatStep 127 896 v7 step := by
    rw [foldNatStep_add, h6]
  exact hc0.trans (hc1.trans (hc2.trans (hc3.trans (hc4.trans (hc5.trans (hc6.trans h7))))))

theorem foldNatStep_2047_chunks {α : Type} (step : Nat → α → α)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : α)
    (h0 : foldNatStep 128 0 v0 step = v1)
    (h1 : foldNatStep 128 128 v1 step = v2)
    (h2 : foldNatStep 128 256 v2 step = v3)
    (h3 : foldNatStep 128 384 v3 step = v4)
    (h4 : foldNatStep 128 512 v4 step = v5)
    (h5 : foldNatStep 128 640 v5 step = v6)
    (h6 : foldNatStep 128 768 v6 step = v7)
    (h7 : foldNatStep 128 896 v7 step = v8)
    (h8 : foldNatStep 128 1024 v8 step = v9)
    (h9 : foldNatStep 128 1152 v9 step = v10)
    (h10 : foldNatStep 128 1280 v10 step = v11)
    (h11 : foldNatStep 128 1408 v11 step = v12)
    (h12 : foldNatStep 128 1536 v12 step = v13)
    (h13 : foldNatStep 128 1664 v13 step = v14)
    (h14 : foldNatStep 128 1792 v14 step = v15)
    (h15 : foldNatStep 127 1920 v15 step = v16) :
    foldNatStep 2047 0 v0 step = v16 := by
  have hc0 : foldNatStep (128 + 1919) 0 v0 step = foldNatStep 1919 128 v1 step := by
    rw [foldNatStep_add, Nat.zero_add, h0]
  have hc1 : foldNatStep (128 + 1791) 128 v1 step = foldNatStep 1791 256 v2 step := by
    rw [foldNatStep_add, h1]
  have hc2 : foldNatStep (128 + 1663) 256 v2 step = foldNatStep 1663 384 v3 step := by
    rw [foldNatStep_add, h2]
  have hc3 : foldNatStep (128 + 1535) 384 v3 step = foldNatStep 1535 512 v4 step := by
    rw [foldNatStep_add, h3]
  have hc4 : foldNatStep (128 + 1407) 512 v4 step = foldNatStep 1407 640 v5 step := by
    rw [foldNatStep_add, h4]
  have hc5 : foldNatStep (128 + 1279) 640 v5 step = foldNatStep 1279 768 v6 step := by
    rw [foldNatStep_add, h5]
  have hc6 : foldNatStep (128 + 1151) 768 v6 step = foldNatStep 1151 896 v7 step := by
    rw [foldNatStep_add, h6]
  have hc7 : foldNatStep (128 + 1023) 896 v7 step = foldNatStep 1023 1024 v8 step := by
    rw [foldNatStep_add, h7]
  have hc8 : foldNatStep (128 + 895) 1024 v8 step = foldNatStep 895 1152 v9 step := by
    rw [foldNatStep_add, h8]
  have hc9 : foldNatStep (128 + 767) 1152 v9 step = foldNatStep 767 1280 v10 step := by
    rw [foldNatStep_add, h9]
  have hc10 : foldNatStep (128 + 639) 1280 v10 step = foldNatStep 639 1408 v11 step := by
    rw [foldNatStep_add, h10]
  have hc11 : foldNatStep (128 + 511) 1408 v11 step = foldNatStep 511 1536 v12 step := by
    rw [foldNatStep_add, h11]
  have hc12 : foldNatStep (128 + 383) 1536 v12 step = foldNatStep 383 1664 v13 step := by
    rw [foldNatStep_add, h12]
  have hc13 : foldNatStep (128 + 255) 1664 v13 step = foldNatStep 255 1792 v14 step := by
    rw [foldNatStep_add, h13]
  have hc14 : foldNatStep (128 + 127) 1792 v14 step = foldNatStep 127 1920 v15 step := by
    rw [foldNatStep_add, h14]
  exact hc0.trans (hc1.trans (hc2.trans (hc3.trans (hc4.trans (hc5.trans (hc6.trans
    (hc7.trans (hc8.trans (hc9.trans (hc10.trans (hc11.trans (hc12.trans (hc13.trans
      (hc14.trans h15))))))))))))))

def zetaAnchorStep108Core
    (tp108 : RawIv72) (t31 : LnPrimeTable72) (hiTree : PrimeTree108)
    (mul108 : RawIv72 → RawIv72 → RawIv72)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (sigmaIv18 tIv108 : RawIv72) (idx : Nat)
    (acc : ScaledInterval × ScaledInterval) : ScaledInterval × ScaledInterval :=
  let n := idx + 2
  let ln108 := lnRaw108_2048 t31 hiTree n
  let ln18 := rawTo18From108 ln108
  let amp6 := rawToScaled6From18 (rawTaylorExpNeg18 mulS (mul18 sigmaIv18 ln18))
  let r108 := reduceModTwoPiRaw72With tp108 (mul108 tIv108 ln108)
  let (cosRaw, sinRaw) := rawTaylorCosSin18 mulS mul18 (rawTo18From108 r108)
  let c6 := rawToScaled6From18 cosRaw
  let s6 := rawToScaled6From18 sinRaw
  (ivAdd acc.1 (ivMulScaled_local amp6 c6),
   ivAdd acc.2 (ivMulScaled_local amp6 ⟨-s6.hi, -s6.lo⟩))

def evalZetaAnchorHigh108Core
    (tp108 : RawIv72) (t31 : LnPrimeTable72) (hiTree : PrimeTree108)
    (mul108 : RawIv72 → RawIv72 → RawIv72)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (nMax sMid6 tMid6 : Nat) : ScaledInterval × ScaledInterval :=
  let sigmaIv18 : RawIv72 := ((sMid6 : Int) * scale12TInt, (sMid6 : Int) * scale12TInt)
  let tIv108 : RawIv72 := ((tMid6 : Int) * scale102Int, (tMid6 : Int) * scale102Int)
  foldNatStep (nMax - 1) 0 (⟨1000000, 1000000⟩, ⟨0, 0⟩)
    (zetaAnchorStep108Core tp108 t31 hiTree mul108 mulS mul18 sigmaIv18 tIv108)

/-- Evaluates a `108`-digit CRT-NTT phase-reduced Dirichlet anchor interval `ζ_N(s_0)`
for `N ≤ 2048` at `(sMid6, tMid6)` in `10^6` units. -/
def evalZetaAnchorHigh108 : Nat → Nat → Nat → ScaledInterval × ScaledInterval :=
  evalZetaAnchorHigh108Core twoPiRaw108 lnPrimeTable108Crt lnHighPrimes108TreeCrt
    rawMul108Crt intMul192ViaCrtNtt rawMul18Crt

def evalLipTile108
    (tp108 : RawIv72) (t31 : LnPrimeTable72) (hiTree : PrimeTree108)
    (mul108 : RawIv72 → RawIv72 → RawIv72)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (nMax sLo6 sHi6 tLo6 tHi6 g epsCrt6 : Nat) : LipTile2D :=
  let sm := (sLo6 + sHi6) / 2
  let tm := (tLo6 + tHi6) / 2
  let (reIv, imIv) := evalZetaAnchorHigh108Core tp108 t31 hiTree mul108 mulS mul18 nMax sm tm
  ⟨sLo6, sHi6, tLo6, tHi6, sm, tm, reIv, imIv, g, epsCrt6⟩

def buildLipTile2x2_108Core
    (tp108 : RawIv72) (t31 : LnPrimeTable72) (hiTree : PrimeTree108)
    (mul108 : RawIv72 → RawIv72 → RawIv72)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (nMax sLo6 sCut6 sHi6 tLo6 tCut6 tHi6 epsCrt6 : Nat) : List LipTile2D :=
  let g := dirichletGradBoundScaled6_2048Core t31 hiTree mulS mul18 sLo6 nMax
  [ evalLipTile108 tp108 t31 hiTree mul108 mulS mul18 nMax sLo6 sCut6 tLo6 tCut6 g epsCrt6,
    evalLipTile108 tp108 t31 hiTree mul108 mulS mul18 nMax sLo6 sCut6 tCut6 tHi6 g epsCrt6,
    evalLipTile108 tp108 t31 hiTree mul108 mulS mul18 nMax sCut6 sHi6 tLo6 tCut6 g epsCrt6,
    evalLipTile108 tp108 t31 hiTree mul108 mulS mul18 nMax sCut6 sHi6 tCut6 tHi6 g epsCrt6 ]

theorem buildLipTile2x2_108Core_part (tp108 : RawIv72) (t31 : LnPrimeTable72)
    (hiTree : PrimeTree108) (mul108 : RawIv72 → RawIv72 → RawIv72)
    (mulS : Int → Int → Int) (mul18 : RawIv72 → RawIv72 → RawIv72)
    (nMax sLo6 sCut6 sHi6 tLo6 tCut6 tHi6 epsCrt6 : Nat)
    (hs1 : sLo6 ≤ sCut6) (hs2 : sCut6 ≤ sHi6) (ht1 : tLo6 ≤ tCut6) (ht2 : tCut6 ≤ tHi6) :
    IsPartition2x2Tiles sLo6 sCut6 sHi6 tLo6 tCut6 tHi6
      (buildLipTile2x2_108Core tp108 t31 hiTree mul108 mulS mul18
        nMax sLo6 sCut6 sHi6 tLo6 tCut6 tHi6 epsCrt6) := by
  dsimp [IsPartition2x2Tiles, buildLipTile2x2_108Core, evalLipTile108]
  exact ⟨hs1, hs2, ht1, ht2, _, _, _, _, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep108Eval.lean
