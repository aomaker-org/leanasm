-- Path: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep72Core/Certificates.lean
-- High-height 2D Dirichlet partial-sum certificates and zero-free boxes at t ~ 10^12.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.UltraDeep72Core.Bounds

namespace QuasiRiemann

-- -----------------------------------------------------------------------------
-- High-Height 2D Dirichlet Partial-Sum Certifier (t >= 10^12, N <= 128)
-- -----------------------------------------------------------------------------

/-- High-height critical-strip box `[sLo6, sHi6] × [tLo6, tHi6]` at `t ≥ 10^12`
(`tLo6 ≥ 10^18` in `10^-6` grid units) without `InRemainingUnknownRect2D`'s `t < 10^6` cap. -/
def InHighHeightRect2D (sLo6 sHi6 tLo6 tHi6 : Nat) : Prop :=
  500000 < sLo6 ∧ sLo6 ≤ sHi6 ∧ sHi6 ≤ 875000 ∧
  1000000000000000000 ≤ tLo6 ∧ tLo6 ≤ tHi6

instance (sLo6 sHi6 tLo6 tHi6 : Nat) : Decidable (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) :=
  inferInstanceAs (Decidable (500000 < sLo6 ∧ sLo6 ≤ sHi6 ∧ sHi6 ≤ 875000 ∧
    1000000000000000000 ≤ tLo6 ∧ tLo6 ≤ tHi6))

/-- Constructive 2D gradient-envelope upper bound `∑_{n=2}^N (ln n) n^{-σ_0}` scaled by `10^6`. -/
def dirichletGradBoundScaled6 (sLo6 nMax : Nat) : Nat :=
  let sigmaIv72 : RawIv72 := ((sLo6 : Int) * scale66Int, (sLo6 : Int) * scale66Int)
  foldNatStep (nMax - 1) 0 0 (fun idx acc =>
    let n := idx + 2
    let lnIv := lnRaw72 n
    let ampHi := (rawTaylorExpNeg72 intMul192ViaCrtNtt (rawMul72Crt sigmaIv72 lnIv)).2
    let termHi := ((lnIv.2 * ampHi) / scale72Int + scale72Int - 1) / scale72Int
    let term6 := (termHi * 1000000 + scale72Int - 1) / scale72Int
    acc + term6.natAbs)

/-- Validity predicate for a high-height `N ≤ 128` 2D rectangle certificate of `ζ_N(s)`:
lies in `InHighHeightRect2D`, valid term table with `length ≤ 128`, `tailBoundScaled = 0`,
and strictly positive complex interval minimum squared norm `0 < complexIntervalMinNormSq reIv imIv`. -/
def IsValidDirichletRect2DN128 (r : DirichletRect2DCert) : Prop :=
  InHighHeightRect2D r.sLo6 r.sHi6 r.tLo6 r.tHi6 ∧
  IsValidTermTable (r.sLo6 / 125000) (r.tHi6 / 1000000) r.entries ∧
  r.entries.length ≤ 128 ∧
  r.tailBoundScaled = 0 ∧
  let (reIv, imIv) := evalDirichletPolyInterval r.entries
  0 < complexIntervalMinNormSq reIv imIv

instance (r : DirichletRect2DCert) : Decidable (IsValidDirichletRect2DN128 r) :=
  inferInstanceAs (Decidable (InHighHeightRect2D r.sLo6 r.sHi6 r.tLo6 r.tHi6 ∧
    IsValidTermTable (r.sLo6 / 125000) (r.tHi6 / 1000000) r.entries ∧
    r.entries.length ≤ 128 ∧
    r.tailBoundScaled = 0 ∧
    let (reIv, imIv) := evalDirichletPolyInterval r.entries
    0 < complexIntervalMinNormSq reIv imIv))

/-- Interval-pair addition matching `evalDirichletPolyInterval`. -/
private def highPairAdd (p q : ScaledInterval × ScaledInterval) : ScaledInterval × ScaledInterval :=
  (ivAdd p.1 q.1, ivAdd p.2 q.2)

private theorem highPairAdd_assoc (p q r : ScaledInterval × ScaledInterval) :
    highPairAdd (highPairAdd p q) r = highPairAdd p (highPairAdd q r) := by
  rcases p with ⟨⟨p1l, p1h⟩, ⟨p2l, p2h⟩⟩
  rcases q with ⟨⟨q1l, q1h⟩, ⟨q2l, q2h⟩⟩
  rcases r with ⟨⟨r1l, r1h⟩, ⟨r2l, r2h⟩⟩
  simp [highPairAdd, ivAdd, Int.add_assoc]

private theorem highPairAdd_zero_left (p : ScaledInterval × ScaledInterval) :
    highPairAdd (⟨0, 0⟩, ⟨0, 0⟩) p = p := by
  rcases p with ⟨⟨p1l, p1h⟩, ⟨p2l, p2h⟩⟩
  simp [highPairAdd, ivAdd]

private def highEntryTermPair (e : DirichletTermEntry) : ScaledInterval × ScaledInterval :=
  (ivMulScaled e.ampIv e.cosIv, ivMulScaled e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩)

private def highEntryOk (e : DirichletTermEntry) : Prop :=
  e.ampIv.isValid ∧ e.cosIv.isValid ∧ e.sinIv.isValid ∧
  0 ≤ e.ampIv.lo ∧ e.ampIv.hi ≤ 1000000 ∧
  -1000000 ≤ e.cosIv.lo ∧ e.cosIv.hi ≤ 1000000 ∧
  -1000000 ≤ e.sinIv.lo ∧ e.sinIv.hi ≤ 1000000 ∧
  intervalMinSq e.cosIv + intervalMinSq e.sinIv ≤ 1000000000000

private instance (e : DirichletTermEntry) : Decidable (highEntryOk e) := by
  dsimp [highEntryOk]; infer_instance

private inductive HighEntriesTree where
  | leaf (e : DirichletTermEntry)
  | node (l r : HighEntriesTree)

private def highTreeToListAux :
    HighEntriesTree → List DirichletTermEntry → List DirichletTermEntry
  | .leaf e, acc => e :: acc
  | .node l r, acc => highTreeToListAux l (highTreeToListAux r acc)

private def highTreeToList (t : HighEntriesTree) : List DirichletTermEntry :=
  highTreeToListAux t []

private def highTreeLen : HighEntriesTree → Nat
  | .leaf _ => 1
  | .node l r => highTreeLen l + highTreeLen r

private theorem highTreeLen_toList (t : HighEntriesTree) :
    (highTreeToList t).length = highTreeLen t := by
  have haux : ∀ acc, (highTreeToListAux t acc).length = highTreeLen t + acc.length := by
    intro acc
    induction t generalizing acc with
    | leaf e => dsimp [highTreeToListAux, highTreeLen]; omega
    | node l r ihl ihr => dsimp [highTreeToListAux, highTreeLen]; rw [ihl, ihr]; omega
  dsimp [highTreeToList]
  rw [haux []]
  simp [List.length_nil]

private theorem highTreeLen_pos (t : HighEntriesTree) : 0 < highTreeLen t := by
  induction t with
  | leaf _ => dsimp [highTreeLen]; omega
  | node l r _ _ => dsimp [highTreeLen]; omega

private def highTreeSum : HighEntriesTree → ScaledInterval × ScaledInterval
  | .leaf e => highEntryTermPair e
  | .node l r => highPairAdd (highTreeSum l) (highTreeSum r)

private theorem highTreeSum_evalPoly (t : HighEntriesTree) :
    evalDirichletPolyInterval (highTreeToList t) = highTreeSum t := by
  have hfold : ∀ (tr : HighEntriesTree) (rest : List DirichletTermEntry)
      (acc : ScaledInterval × ScaledInterval),
      (highTreeToListAux tr rest).foldl (fun a e => highPairAdd a (highEntryTermPair e)) acc =
        rest.foldl (fun a e => highPairAdd a (highEntryTermPair e))
          (highPairAdd acc (highTreeSum tr)) := by
    intro tr
    induction tr with
    | leaf e =>
      intro rest acc
      rfl
    | node l r ihl ihr =>
      intro rest acc
      dsimp [highTreeToListAux, highTreeSum]
      rw [ihl (highTreeToListAux r rest) acc, ihr rest (highPairAdd acc (highTreeSum l)),
          highPairAdd_assoc]
  dsimp [evalDirichletPolyInterval, highTreeToList]
  change (highTreeToListAux t []).foldl (fun a e => highPairAdd a (highEntryTermPair e))
      (⟨0, 0⟩, ⟨0, 0⟩) = _
  rw [hfold t [] (⟨0, 0⟩, ⟨0, 0⟩), highPairAdd_zero_left]
  rfl

private def highTreeAllOk : HighEntriesTree → Bool
  | .leaf e => decide (highEntryOk e)
  | .node l r => highTreeAllOk l && highTreeAllOk r

private theorem highTreeAllOk_sound (t : HighEntriesTree) (ht : highTreeAllOk t = true) :
    ∀ e ∈ highTreeToList t, highEntryOk e := by
  have haux : ∀ (tr : HighEntriesTree) (rest : List DirichletTermEntry),
      highTreeAllOk tr = true → (∀ e ∈ rest, highEntryOk e) →
      ∀ e ∈ highTreeToListAux tr rest, highEntryOk e := by
    intro tr
    induction tr with
    | leaf e =>
      intro rest htr hrest x hx
      dsimp [highTreeToListAux] at hx
      dsimp [highTreeAllOk] at htr
      cases hx with
      | head => exact of_decide_eq_true htr
      | tail _ hm => exact hrest x hm
    | node l r ihl ihr =>
      intro rest htr hrest
      dsimp [highTreeToListAux]
      dsimp [highTreeAllOk] at htr
      have hlr := Bool.and_eq_true _ _ |>.mp htr
      exact ihl (highTreeToListAux r rest) hlr.1 (ihr rest hlr.2 hrest)
  exact haux t [] ht (fun _ h => by cases h)

private def highTreeCheckSeq : HighEntriesTree → Nat → Bool
  | .leaf e, k => e.n == k
  | .node l r, k => highTreeCheckSeq l k && highTreeCheckSeq r (k + highTreeLen l)

private theorem highTreeCheckSeq_sound (t : HighEntriesTree) (ht : highTreeCheckSeq t 1 = true) :
    checkSequentialIndices (highTreeToList t) 1 = true := by
  have haux : ∀ (tr : HighEntriesTree) (rest : List DirichletTermEntry) (k : Nat),
      checkSequentialIndices (highTreeToListAux tr rest) k =
        (highTreeCheckSeq tr k && checkSequentialIndices rest (k + highTreeLen tr)) := by
    intro tr
    induction tr with
    | leaf e => intro rest k; rfl
    | node l r ihl ihr =>
      intro rest k
      dsimp [highTreeToListAux, highTreeCheckSeq, highTreeLen]
      rw [ihl (highTreeToListAux r rest) k, ihr rest (k + highTreeLen l),
          Nat.add_assoc, Bool.and_assoc]
  dsimp [highTreeToList]
  rw [haux t [] 1]
  simp [checkSequentialIndices, ht]

/-- Fast boolean tree validator for high-height `N ≤ 128` truncated Dirichlet boxes. -/
def isValidHighDirichletTreeN128 (sLo6 sHi6 tLo6 tHi6 : Nat) (t : HighEntriesTree) : Bool :=
  let (reIv, imIv) := highTreeSum t
  decide (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) &&
    decide (highTreeLen t ≤ 128) &&
    highTreeAllOk t && highTreeCheckSeq t 1 &&
    decide (0 < complexIntervalMinNormSq reIv imIv)

theorem isValidHighDirichletTreeN128_sound (sLo6 sHi6 tLo6 tHi6 : Nat) (t : HighEntriesTree)
    (h : isValidHighDirichletTreeN128 sLo6 sHi6 tLo6 tHi6 t = true) :
    IsValidDirichletRect2DN128 ⟨sLo6, sHi6, tLo6, tHi6, highTreeToList t, 0⟩ := by
  dsimp [isValidHighDirichletTreeN128] at h
  have h1 : (decide (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) &&
      decide (highTreeLen t ≤ 128) && highTreeAllOk t && highTreeCheckSeq t 1) = true ∧
      decide (0 < complexIntervalMinNormSq (highTreeSum t).1 (highTreeSum t).2) = true :=
    Bool.and_eq_true _ _ |>.mp h
  have h2 : (decide (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) &&
      decide (highTreeLen t ≤ 128) && highTreeAllOk t) = true ∧
      highTreeCheckSeq t 1 = true := Bool.and_eq_true _ _ |>.mp h1.1
  have h3 : (decide (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) &&
      decide (highTreeLen t ≤ 128)) = true ∧
      highTreeAllOk t = true := Bool.and_eq_true _ _ |>.mp h2.1
  have h4 : decide (InHighHeightRect2D sLo6 sHi6 tLo6 tHi6) = true ∧
      decide (highTreeLen t ≤ 128) = true := Bool.and_eq_true _ _ |>.mp h3.1
  have hlen : 0 < (highTreeToList t).length := by rw [highTreeLen_toList]; exact highTreeLen_pos t
  refine ⟨of_decide_eq_true h4.1, ⟨hlen, highTreeCheckSeq_sound t h2.2, ?_⟩, ?_, rfl, ?_⟩
  · exact highTreeAllOk_sound t h3.2
  · rw [highTreeLen_toList]; exact of_decide_eq_true h4.2
  · rw [highTreeSum_evalPoly]; exact of_decide_eq_true h1.2

private def genHighTree72Pow2
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sigmaIv72 tIv72 : RawIv72) : Nat → Nat → Nat → HighEntriesTree
  | 0, base, _ =>
    .leaf (generateDirichletRectTermEntryN128Core tp tbl mulS mul sigmaIv72 tIv72 base)
  | d + 1, base, half =>
    .node
      (genHighTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 d base (half / 2))
      (genHighTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 d (base + half) (half / 2))

private def buildDirichletRect2DCertN128Core
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  if sLo6 ≤ sHi6 ∧ tLo6 ≤ tHi6 then
    let sigmaIv72 : RawIv72 := ((sLo6 : Int) * scale66Int, (sHi6 : Int) * scale66Int)
    let tIv72 : RawIv72 := ((tLo6 : Int) * scale66Int, (tHi6 : Int) * scale66Int)
    let tree := genHighTree72Pow2 tp tbl mulS mul sigmaIv72 tIv72 7 1 64
    if isValidHighDirichletTreeN128 sLo6 sHi6 tLo6 tHi6 tree then
      some ⟨sLo6, sHi6, tLo6, tHi6, highTreeToList tree, 0⟩
    else
      none
  else
    none

private def sweepDirichletRectangles2DN128Core
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72) :
    List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert
  | [] => []
  | (sLo6, sHi6, tLo6, tHi6) :: rest =>
    match buildDirichletRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
    | some r => r :: sweepDirichletRectangles2DN128Core tp tbl mulS mul rest
    | none => sweepDirichletRectangles2DN128Core tp tbl mulS mul rest

/-- Builds a high-height `N = 128` 2D Dirichlet polynomial certificate (`t ≥ 10^12`) evaluated at
72-digit (`rawMul72Crt` / `intMul192ViaCrtNtt`) precision via `reducePhaseModTwoPi72`. -/
def buildDirichletRect2DCertN128 (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  buildDirichletRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt
    sLo6 sHi6 tLo6 tHi6

/-- Sweeps candidate high-height `N = 128` 2D rectangles at 72-digit precision. -/
def sweepDirichletRectangles2DN128 :
    List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert :=
  sweepDirichletRectangles2DN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt rawMul72Crt

/-- Real-part and imaginary-part cleared-denominator (`10^12`-scaled) value of a truncated
Dirichlet polynomial `ζ_N(s) = ∑_{n=1}^N n^{-s}` at local term realizations `(amp, cos, sin)`. -/
def zetaPartialEvalScaled12 (terms : List (Int × Int × Int)) : Int × Int :=
  terms.foldl (fun (reAcc, imAcc) (a, c, s) => (reAcc + a * c, imAcc - a * s)) (0, 0)

/-- Predicate stating that local term coordinates `(amp, cos, sin)` are enclosed inside a
`DirichletTermEntry` list `entries`. -/
def TermWitnessesEnclosed :
    List DirichletTermEntry → List (Int × Int × Int) → Prop
  | [], [] => True
  | e :: es, (a, c, s) :: ts =>
    (e.ampIv.lo ≤ a ∧ a ≤ e.ampIv.hi ∧
     e.cosIv.lo ≤ c ∧ c ≤ e.cosIv.hi ∧
     e.sinIv.lo ≤ s ∧ s ≤ e.sinIv.hi) ∧ TermWitnessesEnclosed es ts
  | _, _ => False

private theorem ivMulScaled_encloses (a b : ScaledInterval) (x y : Int)
    (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi) :
    (ivMulScaled a b).lo * 1000000 ≤ x * y ∧ x * y ≤ (ivMulScaled a b).hi * 1000000 := by
  dsimp [ivMulScaled]
  have hcb := corner_bounds a.lo a.hi b.lo b.hi x y hx hy
  have hpos : (0 : Int) < 1000000 := by decide
  have h1 : 1000000 * ((min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))).ediv 1000000) +
      (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))).emod 1000000 =
      min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)) :=
    Int.mul_ediv_add_emod _ 1000000
  have h2 : (-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).emod 1000000 < 1000000 :=
    Int.emod_lt_of_pos _ hpos
  have h2_nonneg : 0 ≤ (-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).emod 1000000 :=
    Int.emod_nonneg _ (by decide : (1000000 : Int) ≠ 0)
  have h3 : 1000000 * ((-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).ediv 1000000) +
      (-(max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)))).emod 1000000 =
      -(max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))) :=
    Int.mul_ediv_add_emod _ 1000000
  have h4 : 0 ≤ (min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))).emod 1000000 :=
    Int.emod_nonneg _ (by decide : (1000000 : Int) ≠ 0)
  have hnegm : (-((-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).ediv 1000000)) * 1000000 =
      -(((-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).ediv 1000000) * 1000000) := Int.neg_mul _ _
  have hc1 : 1000000 * ((min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))).ediv 1000000) =
      (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))).ediv 1000000 *
        1000000 := Int.mul_comm _ _
  have hc2 : 1000000 * ((-(max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)))).ediv 1000000) =
      (-(max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)))).ediv 1000000 *
        1000000 := Int.mul_comm _ _
  rw [hnegm, ← hc2]
  constructor <;> omega

private theorem intervalMinSq_le_sq_of_mem (iv : ScaledInterval) (z : Int)
    (hz : iv.lo * 1000000 ≤ z ∧ z ≤ iv.hi * 1000000) :
    (intervalMinSq iv : Int) * 1000000000000 ≤ z * z := by
  dsimp [intervalMinSq]
  split
  · simp
    if h0 : 0 ≤ z then exact Int.mul_nonneg h0 h0
    else
      have hn : 0 ≤ -z := by omega
      have hsq : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
      have heq : (-z) * (-z) = z * z := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
  · rename_i hnot
    split
    · rename_i hpos
      have hnat : (iv.lo.natAbs : Int) = iv.lo := Int.natAbs_of_nonneg (by omega)
      have hcast : ((iv.lo.natAbs * iv.lo.natAbs : Nat) : Int) = iv.lo * iv.lo := by
        rw [Int.natCast_mul, hnat]
      rw [hcast]
      have hl : iv.lo * 1000000 ≤ z := hz.1
      have hmul : (iv.lo * 1000000) * (iv.lo * 1000000) ≤ z * z :=
        Int.mul_le_mul hl hl (by omega) (by omega)
      have heq : (iv.lo * 1000000) * (iv.lo * 1000000) =
          (iv.lo * iv.lo) * 1000000000000 := by ac_rfl
      omega
    · rename_i hnonpos
      have hlo_neg : iv.lo ≤ 0 := by omega
      have hhi_neg : iv.hi < 0 := by
        cases Int.decLt iv.hi 0 with
        | isTrue hlt => exact hlt
        | isFalse hnlt => exact False.elim (hnot ⟨hlo_neg, by omega⟩)
      clear hnot
      have hnat : (iv.hi.natAbs : Int) = -iv.hi := Int.ofNat_natAbs_of_nonpos (by omega)
      have hcast : ((iv.hi.natAbs * iv.hi.natAbs : Nat) : Int) = (-iv.hi) * (-iv.hi) := by
        rw [Int.natCast_mul, hnat]
      rw [hcast]
      have hzneg : (-iv.hi) * 1000000 ≤ -z := by
        rw [Int.neg_mul]; omega
      have hmul : ((-iv.hi) * 1000000) * ((-iv.hi) * 1000000) ≤ (-z) * (-z) :=
        Int.mul_le_mul hzneg hzneg (by omega) (by omega)
      have heq1 : ((-iv.hi) * 1000000) * ((-iv.hi) * 1000000) =
          ((-iv.hi) * (-iv.hi)) * 1000000000000 := by ac_rfl
      have heq2 : (-z) * (-z) = z * z := by simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega

/-- Theorem (Soundness of `IsValidDirichletRect2DN128`):
Every valid `N ≤ 128` 2D certificate satisfies `InHighHeightRect2D r.sLo6 r.sHi6 r.tLo6 r.tHi6`,
`r.entries.length ≤ 128`, and guarantees that any witness list `terms` enclosed by `r.entries`
(`TermWitnessesEnclosed r.entries terms`) evaluates via `zetaPartialEvalScaled12 terms` to a
strictly positive squared modulus `0 < zRe * zRe + zIm * zIm` and `zRe ≠ 0 ∨ zIm ≠ 0`. -/
theorem isValidDirichletRect2DN128_sound (r : DirichletRect2DCert)
    (hr : IsValidDirichletRect2DN128 r) :
    InHighHeightRect2D r.sLo6 r.sHi6 r.tLo6 r.tHi6 ∧
    r.entries.length ≤ 128 ∧
    (∀ terms : List (Int × Int × Int),
      TermWitnessesEnclosed r.entries terms →
      let (zRe, zIm) := zetaPartialEvalScaled12 terms
      0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0)) := by
  rcases hr with ⟨hh, _, hlen, _, hnorm⟩
  refine ⟨hh, hlen, ?_⟩
  intro terms htw
  have hfold_gen :
      ∀ (es : List DirichletTermEntry) (ts : List (Int × Int × Int))
        (reIv imIv : ScaledInterval) (reAcc imAcc : Int),
        TermWitnessesEnclosed es ts →
        reIv.lo * 1000000 ≤ reAcc ∧ reAcc ≤ reIv.hi * 1000000 →
        imIv.lo * 1000000 ≤ imAcc ∧ imAcc ≤ imIv.hi * 1000000 →
        let (reOut, imOut) := es.foldl (fun (rA, iA) e =>
          (ivAdd rA (ivMulScaled e.ampIv e.cosIv),
           ivAdd iA (ivMulScaled e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩))) (reIv, imIv)
        let (zRe, zIm) := ts.foldl (fun (rA, iA) (a, c, s) => (rA + a * c, iA - a * s))
          (reAcc, imAcc)
        reOut.lo * 1000000 ≤ zRe ∧ zRe ≤ reOut.hi * 1000000 ∧
        imOut.lo * 1000000 ≤ zIm ∧ zIm ≤ imOut.hi * 1000000 := by
    intro es
    induction es with
    | nil =>
      intro ts reIv imIv reAcc imAcc htw0 hre him
      cases ts with
      | nil => exact ⟨hre.1, hre.2, him.1, him.2⟩
      | cons _ _ => cases htw0
    | cons e rest ih =>
      intro ts reIv imIv reAcc imAcc htw0 hre him
      cases ts with
      | nil => cases htw0
      | cons t ts_rest =>
        rcases t with ⟨a, c, s⟩
        rcases htw0 with ⟨⟨ha1, ha2, hc1, hc2, hs1, hs2⟩, htail⟩
        have hreTerm := ivMulScaled_encloses e.ampIv e.cosIv a c ⟨ha1, ha2⟩ ⟨hc1, hc2⟩
        have himTerm := ivMulScaled_encloses e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩ a (-s)
          ⟨ha1, ha2⟩ ⟨by dsimp; omega, by dsimp; omega⟩
        have hre_next :
            (ivAdd reIv (ivMulScaled e.ampIv e.cosIv)).lo * 1000000 ≤ reAcc + a * c ∧
            reAcc + a * c ≤ (ivAdd reIv (ivMulScaled e.ampIv e.cosIv)).hi * 1000000 := by
          dsimp [ivAdd]
          rw [Int.add_mul, Int.add_mul]
          constructor <;> omega
        have him_next :
            (ivAdd imIv (ivMulScaled e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩)).lo * 1000000 ≤
              imAcc - a * s ∧
            imAcc - a * s ≤
              (ivAdd imIv (ivMulScaled e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩)).hi * 1000000 := by
          dsimp [ivAdd]
          rw [Int.add_mul, Int.add_mul]
          have hneg : a * (-s) = -(a * s) := Int.mul_neg a s
          constructor <;> omega
        exact ih ts_rest _ _ (reAcc + a * c) (imAcc - a * s) htail hre_next him_next
  have hmem := hfold_gen r.entries terms ⟨0, 0⟩ ⟨0, 0⟩ 0 0 htw
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  have h1 := intervalMinSq_le_sq_of_mem (evalDirichletPolyInterval r.entries).1
    (zetaPartialEvalScaled12 terms).1 ⟨hmem.1, hmem.2.1⟩
  have h2 := intervalMinSq_le_sq_of_mem (evalDirichletPolyInterval r.entries).2
    (zetaPartialEvalScaled12 terms).2 ⟨hmem.2.2.1, hmem.2.2.2⟩
  dsimp [complexIntervalMinNormSq] at hnorm
  have hpos_z : 0 < (zetaPartialEvalScaled12 terms).1 * (zetaPartialEvalScaled12 terms).1 +
      (zetaPartialEvalScaled12 terms).2 * (zetaPartialEvalScaled12 terms).2 := by
    have hm : (0 : Int) < ((intervalMinSq (evalDirichletPolyInterval r.entries).1 +
        intervalMinSq (evalDirichletPolyInterval r.entries).2 : Nat) : Int) * 1000000000000 :=
      Int.mul_pos (Int.natCast_pos.mpr hnorm) (by decide)
    rw [Int.natCast_add, Int.add_mul] at hm
    omega
  refine ⟨hpos_z, ?_⟩
  cases Int.decEq (zetaPartialEvalScaled12 terms).1 0 with
  | isTrue hz =>
    right
    intro him0
    change (zetaPartialEvalScaled12 terms).2 = 0 at him0
    rw [hz, him0] at hpos_z
    omega
  | isFalse hz => exact Or.inl hz

/-- Theorem: Any certificate produced by `buildDirichletRect2DCertN128` satisfies
`IsValidDirichletRect2DN128`. -/
theorem buildDirichletRect2DCertN128_implies_valid (sLo6 sHi6 tLo6 tHi6 : Nat)
    (r : DirichletRect2DCert) :
    buildDirichletRect2DCertN128 sLo6 sHi6 tLo6 tHi6 = some r → IsValidDirichletRect2DN128 r := by
  dsimp [buildDirichletRect2DCertN128, buildDirichletRect2DCertN128Core]
  split
  · split
    · rename_i hvalid
      intro h
      injection h with hreq
      subst hreq
      exact isValidHighDirichletTreeN128_sound _ _ _ _ _ hvalid
    · intro h; contradiction
  · intro h; contradiction

/-- Theorem (Universal Soundness of High-Height `N = 128` 2D Sweeper):
EVERY rectangle returned by `sweepDirichletRectangles2DN128` satisfies `IsValidDirichletRect2DN128`. -/
theorem sweepDirichletRectangles2DN128_all_valid (rects : List (Nat × Nat × Nat × Nat))
    (r : DirichletRect2DCert) :
    r ∈ sweepDirichletRectangles2DN128 rects → IsValidDirichletRect2DN128 r := by
  dsimp [sweepDirichletRectangles2DN128]
  induction rects with
  | nil =>
    intro hmem
    cases hmem
  | cons rect tail ih =>
    rcases rect with ⟨sLo6, sHi6, tLo6, tHi6⟩
    dsimp [sweepDirichletRectangles2DN128Core]
    have hopt :
        buildDirichletRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt
          rawMul72Crt sLo6 sHi6 tLo6 tHi6 = none ∨
        ∃ b, buildDirichletRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt
          rawMul72Crt sLo6 sHi6 tLo6 tHi6 = some b := by
      cases buildDirichletRect2DCertN128Core twoPiRaw72 lnPrimeTable72Crt intMul192ViaCrtNtt
          rawMul72Crt sLo6 sHi6 tLo6 tHi6 with
      | none => left; rfl
      | some b => right; exact ⟨b, rfl⟩
    rcases hopt with hnone | ⟨b, hsome⟩
    · rw [hnone]; intro hmem; exact ih hmem
    · rw [hsome]; intro hmem
      cases hmem with
      | head => exact buildDirichletRect2DCertN128_implies_valid sLo6 sHi6 tLo6 tHi6 r hsome
      | tail _ hrest => exact ih hrest

private theorem sweep_high_dirichlet_step_128
    (tp : RawIv72) (tbl : LnPrimeTable72)
    (mulS : Int → Int → Int) (mul : RawIv72 → RawIv72 → RawIv72)
    (sLo6 sHi6 tLo6 tHi6 : Nat) (rest : List (Nat × Nat × Nat × Nat))
    (hsome : (buildDirichletRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6).isSome = true) :
    ∃ r, sweepDirichletRectangles2DN128Core tp tbl mulS mul ((sLo6, sHi6, tLo6, tHi6) :: rest) =
           r :: sweepDirichletRectangles2DN128Core tp tbl mulS mul rest ∧
         r.sLo6 = sLo6 ∧ r.sHi6 = sHi6 ∧ r.tLo6 = tLo6 ∧ r.tHi6 = tHi6 := by
  dsimp [sweepDirichletRectangles2DN128Core]
  cases hbuild : buildDirichletRect2DCertN128Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
  | none => rw [hbuild] at hsome; simp at hsome
  | some r =>
    dsimp [buildDirichletRect2DCertN128Core] at hbuild
    split at hbuild
    · split at hbuild
      · injection hbuild with hreq; subst hreq; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      · cases hbuild
    · cases hbuild

/-- Candidate high-height 2D rectangles near `t = 10^12 + 6.1` spanning `σ ∈ [0.501, 0.750]`
where `ζ_128(s)` is uniformly zero-free. -/
def highHeightRectGrid2D_1e12_N128 : List (Nat × Nat × Nat × Nat) :=
  [ (501000, 750000, 1000000000006095000, 1000000000006105000),
    (501000, 550000, 1000000000006195000, 1000000000006205000),
    (501000, 600000, 1000000000005995000, 1000000000006005000),
    (550000, 700000, 1000000000006295000, 1000000000006305000),
    (600000, 750000, 1000000000005895000, 1000000000005905000) ]

private theorem highRect1e12_0_valid :
    (buildDirichletRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 750000 1000000000006095000 1000000000006105000).isSome = true := by
  decide +kernel

private theorem highRect1e12_1_valid :
    (buildDirichletRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 550000 1000000000006195000 1000000000006205000).isSome = true := by
  decide +kernel

private theorem highRect1e12_2_valid :
    (buildDirichletRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      501000 600000 1000000000005995000 1000000000006005000).isSome = true := by
  decide +kernel

private theorem highRect1e12_3_valid :
    (buildDirichletRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      550000 700000 1000000000006295000 1000000000006305000).isSome = true := by
  decide +kernel

private theorem highRect1e12_4_valid :
    (buildDirichletRect2DCertN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
      600000 750000 1000000000005895000 1000000000005905000).isSome = true := by
  decide +kernel

/-- Theorem (High-Height `t ~ 10^12` 2D Zero-Free Rectangles Certified for `ζ_128`):
All 5 pairwise `t`-disjoint high-height 2D boxes near `t = 10^12 + 6.1` spanning
`σ ∈ [0.501, 0.750]` pass 72-digit `twoPiInterval72` phase reduction and `N = 128` evaluation,
with strictly positive total area `Δσ · Δt = 6970000000 / 10^12` and ZERO `Classical.choice` / `sorryAx`. -/
theorem high_height_dirichlet_rects_1e12_certified :
    let swept := sweepDirichletRectangles2DN128 highHeightRectGrid2D_1e12_N128
    0 < swept.length ∧
    swept.length = 5 ∧
    0 < totalCertifiedAreaScaled12 swept ∧
    totalCertifiedAreaScaled12 swept = 6970000000 ∧
    (∀ r ∈ swept, IsValidDirichletRect2DN128 r) ∧
    (∃ r ∈ swept, r.sLo6 = 501000 ∧ 1000000000000000000 ≤ r.tLo6) := by
  have hswap : sweepDirichletRectangles2DN128 highHeightRectGrid2D_1e12_N128 =
      sweepDirichletRectangles2DN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul rawMul72Fast
        highHeightRectGrid2D_1e12_N128 := by
    dsimp [sweepDirichletRectangles2DN128]
    rw [twoPiRaw72_eq, lnPrimeTable72_eq, intMul192ViaCrtNtt_fn_eq, rawMul72_fn_eq]
  have hall := sweepDirichletRectangles2DN128_all_valid highHeightRectGrid2D_1e12_N128
  rw [hswap]
  dsimp [highHeightRectGrid2D_1e12_N128]
  obtain ⟨r0, hs0, h0s, h0S, h0t, h0T⟩ := sweep_high_dirichlet_step_128 twoPiRaw72Lit
    lnPrimeTable72Lit Int.mul rawMul72Fast 501000 750000 1000000000006095000 1000000000006105000 _
    highRect1e12_0_valid
  obtain ⟨r1, hs1, h1s, h1S, h1t, h1T⟩ := sweep_high_dirichlet_step_128 twoPiRaw72Lit
    lnPrimeTable72Lit Int.mul rawMul72Fast 501000 550000 1000000000006195000 1000000000006205000 _
    highRect1e12_1_valid
  obtain ⟨r2, hs2, h2s, h2S, h2t, h2T⟩ := sweep_high_dirichlet_step_128 twoPiRaw72Lit
    lnPrimeTable72Lit Int.mul rawMul72Fast 501000 600000 1000000000005995000 1000000000006005000 _
    highRect1e12_2_valid
  obtain ⟨r3, hs3, h3s, h3S, h3t, h3T⟩ := sweep_high_dirichlet_step_128 twoPiRaw72Lit
    lnPrimeTable72Lit Int.mul rawMul72Fast 550000 700000 1000000000006295000 1000000000006305000 _
    highRect1e12_3_valid
  obtain ⟨r4, hs4, h4s, h4S, h4t, h4T⟩ := sweep_high_dirichlet_step_128 twoPiRaw72Lit
    lnPrimeTable72Lit Int.mul rawMul72Fast 600000 750000 1000000000005895000 1000000000005905000 []
    highRect1e12_4_valid
  have hnil : sweepDirichletRectangles2DN128Core twoPiRaw72Lit lnPrimeTable72Lit Int.mul
      rawMul72Fast [] = [] := rfl
  rw [hs0, hs1, hs2, hs3, hs4, hnil]
  refine ⟨by simp, by rfl, ?_, ?_, ?_, ⟨r0, List.Mem.head _, h0s, by rw [h0t]; decide⟩⟩
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T]
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T]
  · intro r hmem
    apply hall r
    rw [hswap]
    dsimp [highHeightRectGrid2D_1e12_N128]
    rw [hs0, hs1, hs2, hs3, hs4, hnil]
    exact hmem

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/UltraDeep72Core/Certificates.lean
