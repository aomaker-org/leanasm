-- Path: leanasm/src/LeanAsm/Genus2/Cantor.lean
-- Mumford divisor representation and Cantor group law on J(C)(F_5).
-- Max Column: 120 Columns

import LeanAsm.Constants.CurveTables
import LeanAsm.Genus2.PolyF5

namespace LeanAsm.Genus2.Cantor

open LeanAsm.Constants.CurveTables
open LeanAsm.Genus2.PolyF5

/-! ## Part 5: Hyperelliptic Curve C : y^2 = x^5 - x + 1 & Cantor-Mumford Divisors -/

/-- Curve polynomial `f(x) = x^5 - x + 1 = x^5 + 4x + 1` over `F_5`. -/
def curveF5 : PolyF5 := curveF5Coeffs

/-- Reduced Mumford divisor representation `(u, v)` on `J(C)(F_5)`. -/
structure MumfordDivisor where
  u : PolyF5
  v : PolyF5
  deriving DecidableEq, Repr, Inhabited

/-- Axiom-free boolean equality on `MumfordDivisor`. -/
def divEqB (D1 D2 : MumfordDivisor) : Bool :=
  polyEqB D1.u D2.u && polyEqB D1.v D2.v

theorem divEqB_iff {D1 D2 : MumfordDivisor} : divEqB D1 D2 = true ↔ D1 = D2 := by
  rcases D1 with ⟨u1, v1⟩
  rcases D2 with ⟨u2, v2⟩
  simp only [divEqB, Bool.and_eq_true, polyEqB_iff]
  constructor
  · intro ⟨hu, hv⟩; rw [hu, hv]
  · intro h; injection h with hu hv; exact ⟨hu, hv⟩

/-- Identity element `0_J = (1, 0)`. -/
def MumfordDivisor.zero : MumfordDivisor := ⟨[1], []⟩

/-- Reduced Mumford invariant: `u, v` trimmed, `u` monic of deg ≤ 2 (`u.length ≤ 3`),
`deg(v) < deg(u)` (`v.length < u.length`), and `u` divides `v^2 - (x^5 - x + 1)`. -/
def isReducedMumford (u v : PolyF5) : Bool :=
  isTrimmedB u &&
  isTrimmedB v &&
  isMonic u &&
  (u.length ≤ 3) &&
  (v.length < u.length) &&
  (polyMod (polySub (polyMul v v) curveF5) u).isEmpty

/-- Cantor composition step (generalized CRT via `polyXgcd`). -/
def cantorCompose (D1 D2 : MumfordDivisor) : MumfordDivisor :=
  let u1 := D1.u
  let v1 := D1.v
  let u2 := D2.u
  let v2 := D2.v
  let (d1, e1, e2) := polyXgcd u1 u2
  if polyEqB d1 [1] then
    let u := polyMul u1 u2
    let w := polyMod (polyMul e1 (polySub v2 v1)) u2
    let v := polyAdd (polyMul u1 w) v1
    ⟨u, if v.length < u.length then v else polyMod v u⟩
  else
    let (d, c1, c2) := polyXgcd d1 (polyAdd v1 v2)
    let s1 := polyMul c1 e1
    let s2 := polyMul c1 e2
    let s3 := c2
    let u := polyMul (polyDiv u1 d) (polyDiv u2 d)
    let term1 := polyMul (polyMul s1 u1) v2
    let term2 := polyMul (polyMul s2 u2) v1
    let term3 := polyMul s3 (polyAdd (polyMul v1 v2) curveF5)
    let v := polyMod (polyDiv (polyAdd term1 (polyAdd term2 term3)) d) u
    ⟨u, v⟩

/-- Cantor reduction loop until `deg(u) ≤ 2` (`u.length ≤ 3`). -/
def cantorReduceAux : Nat → PolyF5 → PolyF5 → MumfordDivisor
  | 0, u, v => ⟨u, if v.length < u.length then v else polyMod v u⟩
  | fuel + 1, u, v =>
    if u.length ≤ 3 then ⟨u, if v.length < u.length then v else polyMod v u⟩
    else
      let u' := polyMonic (polyDiv (polySub curveF5 (polyMul v v)) u)
      let v' := polyMod (polyNeg v) u'
      cantorReduceAux fuel u' v'

/-- Full Cantor addition on reduced Mumford divisors. -/
def cantorAdd (D1 D2 : MumfordDivisor) : MumfordDivisor :=
  let comp := cantorCompose D1 D2
  cantorReduceAux 2 comp.u comp.v

/-- Additive inverse on reduced Mumford divisors: `-(u, v) = (u, -v mod u)`. -/
def cantorNeg (D : MumfordDivisor) : MumfordDivisor :=
  ⟨D.u, polyMod (polyNeg D.v) D.u⟩

/-- Double-and-add scalar multiplication with structural fuel. -/
def cantorSmulFuel : Nat → Nat → MumfordDivisor → MumfordDivisor → MumfordDivisor
  | 0, _, acc, _ => acc
  | fuel + 1, n, acc, base =>
    if n == 0 then acc
    else
      let acc' := if n % 2 == 1 then cantorAdd acc base else acc
      cantorSmulFuel fuel (n / 2) acc' (cantorAdd base base)

/-- Scalar multiplication `n • D` on `J(C)(F_5)`. -/
def cantorSmul (n : Nat) (D : MumfordDivisor) : MumfordDivisor :=
  cantorSmulFuel (n + 1) n MumfordDivisor.zero D

/-- Base divisor `D0 = [P_0 - ∞]` for `P_0 = (0, 1)`: `u(x) = x`, `v(x) = 1`. -/
def D0 : MumfordDivisor := ⟨[0, 1], [1]⟩

theorem D0_is_reduced : isReducedMumford D0.u D0.v = true := by
  decide

theorem zero_is_reduced : isReducedMumford MumfordDivisor.zero.u MumfordDivisor.zero.v = true := by
  decide

/-! ## Part 6: Full 71-Element Cyclic Orbit & Exhaustive Reduced-Divisor Classification -/

/-- Precomputed 71-element cyclic orbit `[k • D0 | 0 ≤ k < 71]`. -/
def orbitList : List MumfordDivisor := [
  ⟨[1], []⟩, ⟨[0, 1], [1]⟩, ⟨[0, 0, 1], [1, 2]⟩, ⟨[3, 1, 1], [3, 1]⟩, ⟨[0, 3, 1], [4, 1]⟩,
  ⟨[3, 1], [1]⟩, ⟨[0, 3, 1], [1]⟩, ⟨[1, 1, 1], [3, 2]⟩, ⟨[4, 0, 1], [1]⟩, ⟨[1, 0, 1], [4]⟩,
  ⟨[4, 1, 1], [2, 2]⟩, ⟨[2, 3, 1], [1]⟩, ⟨[2, 2, 1], [4]⟩, ⟨[0, 2, 1], [4]⟩, ⟨[2, 1], [4]⟩,
  ⟨[0, 2, 1], [1, 1]⟩, ⟨[0, 4, 1], [4]⟩, ⟨[4, 1], [4]⟩, ⟨[0, 4, 1], [1, 3]⟩, ⟨[1, 0, 1], [0, 3]⟩,
  ⟨[3, 4, 1], [2, 1]⟩, ⟨[1, 2, 1], [2, 3]⟩, ⟨[2, 2, 1], [2, 2]⟩, ⟨[1, 4, 1], [1, 2]⟩, ⟨[0, 1, 1], [4, 3]⟩,
  ⟨[1, 1], [1]⟩, ⟨[0, 1, 1], [1]⟩, ⟨[2, 0, 1], [3, 3]⟩, ⟨[4, 4, 1], [0, 3]⟩, ⟨[4, 0, 1], [0, 1]⟩,
  ⟨[3, 4, 1], [1]⟩, ⟨[3, 1, 1], [4]⟩, ⟨[2, 3, 1], [2, 3]⟩, ⟨[3, 3, 1], [0, 2]⟩, ⟨[1, 3, 1], [1, 3]⟩,
  ⟨[3, 2, 1], [4, 2]⟩, ⟨[3, 2, 1], [1, 3]⟩, ⟨[1, 3, 1], [4, 2]⟩, ⟨[3, 3, 1], [0, 3]⟩, ⟨[2, 3, 1], [3, 2]⟩,
  ⟨[3, 1, 1], [1]⟩, ⟨[3, 4, 1], [4]⟩, ⟨[4, 0, 1], [0, 4]⟩, ⟨[4, 4, 1], [0, 2]⟩, ⟨[2, 0, 1], [2, 2]⟩,
  ⟨[0, 1, 1], [4]⟩, ⟨[1, 1], [4]⟩, ⟨[0, 1, 1], [1, 2]⟩, ⟨[1, 4, 1], [4, 3]⟩, ⟨[2, 2, 1], [3, 3]⟩,
  ⟨[1, 2, 1], [3, 2]⟩, ⟨[3, 4, 1], [3, 4]⟩, ⟨[1, 0, 1], [0, 2]⟩, ⟨[0, 4, 1], [4, 2]⟩, ⟨[4, 1], [1]⟩,
  ⟨[0, 4, 1], [1]⟩, ⟨[0, 2, 1], [4, 4]⟩, ⟨[2, 1], [1]⟩, ⟨[0, 2, 1], [1]⟩, ⟨[2, 2, 1], [1]⟩,
  ⟨[2, 3, 1], [4]⟩, ⟨[4, 1, 1], [3, 3]⟩, ⟨[1, 0, 1], [1]⟩, ⟨[4, 0, 1], [4]⟩, ⟨[1, 1, 1], [2, 3]⟩,
  ⟨[0, 3, 1], [4]⟩, ⟨[3, 1], [4]⟩, ⟨[0, 3, 1], [1, 4]⟩, ⟨[3, 1, 1], [2, 4]⟩, ⟨[0, 0, 1], [4, 3]⟩,
  ⟨[0, 1], [4]⟩
]

def orbitAt (i : Fin 71) : MumfordDivisor :=
  orbitList.getD i.val MumfordDivisor.zero

theorem orbitList_length : orbitList.length = 71 := by decide

theorem orbitAt_eq_smul : ∀ i : Fin 71, divEqB (orbitAt i) (cantorSmul i.val D0) = true := by
  decide

theorem orbitAt_smul (i : Fin 71) : orbitAt i = cantorSmul i.val D0 :=
  divEqB_iff.mp (orbitAt_eq_smul i)

theorem orbitAt_all_reduced :
    ∀ i : Fin 71, isReducedMumford (orbitAt i).u (orbitAt i).v = true := by
  decide

theorem orbitAt_zero : orbitAt ⟨0, by decide⟩ = MumfordDivisor.zero := by
  decide

theorem cantorNeg_orbitAt :
    ∀ i : Fin 71,
      divEqB (cantorNeg (orbitAt i))
        (orbitAt ⟨(71 - i.val) % 71, Nat.mod_lt _ (by decide)⟩) = true := by
  decide

/-- All 651 monic bounded-degree candidates `(u, v)` with `isTrimmedB`, `deg(u) ≤ 2`, `deg(v) < deg(u)`. -/
def candidateDivisors : List MumfordDivisor :=
  let fs := List.finRange 5
  let nz := fs.filter (fun x => !(x.val == 0))
  let deg0 : List MumfordDivisor := [⟨[1], []⟩]
  let deg1 : List MumfordDivisor :=
    fs.flatMap fun u0 =>
      [⟨[u0, 1], []⟩] ++ nz.map fun v0 => ⟨[u0, 1], [v0]⟩
  let deg2 : List MumfordDivisor :=
    fs.flatMap fun u0 =>
      fs.flatMap fun u1 =>
        [⟨[u0, u1, 1], []⟩] ++
        (nz.map fun v0 => ⟨[u0, u1, 1], [v0]⟩) ++
        (fs.flatMap fun v0 => nz.map fun v1 => ⟨[u0, u1, 1], [v0, v1]⟩)
  deg0 ++ deg1 ++ deg2

def memListB (D : MumfordDivisor) : List MumfordDivisor → Bool
  | [] => false
  | x :: xs => divEqB D x || memListB D xs

theorem mem_of_memListB {D : MumfordDivisor} :
    ∀ {xs : List MumfordDivisor}, memListB D xs = true → D ∈ xs
  | [], h => by cases h
  | x :: xs, h => by
    simp only [memListB, Bool.or_eq_true] at h
    cases h with
    | inl heq => rw [divEqB_iff.mp heq]; exact List.Mem.head _
    | inr hmem => exact List.Mem.tail _ (mem_of_memListB hmem)

def indexedMemOrbitAux (D : MumfordDivisor) : Nat → List MumfordDivisor → Option (Fin 71)
  | _, [] => none
  | idx, x :: xs =>
    if divEqB D x then
      if h : idx < 71 then some ⟨idx, h⟩ else none
    else
      indexedMemOrbitAux D (idx + 1) xs

theorem indexedMemOrbitAux_sound {D : MumfordDivisor} :
    ∀ (idx : Nat) (xs : List MumfordDivisor) (k : Fin 71),
      (∀ (j : Nat) (hj : idx + j < 71), xs[j]? = some (orbitAt ⟨idx + j, hj⟩)) →
      indexedMemOrbitAux D idx xs = some k →
      D = orbitAt k
  | _, [], _, _, h => by cases h
  | idx, x :: xs, k, hxs, h => by
    simp only [indexedMemOrbitAux] at h
    cases heq : divEqB D x with
    | true =>
      simp only [heq, ↓reduceIte] at h
      split at h
      · rename_i hlt
        injection h with hk
        subst hk
        have hx0 := hxs 0 (by simpa [Nat.add_zero] using hlt)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx0
        rw [divEqB_iff.mp heq]
        simpa [Nat.add_zero] using hx0
      · cases h
    | false =>
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
      refine indexedMemOrbitAux_sound (idx + 1) xs k ?_ h
      intro j hj
      have hj' : idx + (j + 1) < 71 := by
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj
      have hget := hxs (j + 1) hj'
      simp only [List.getElem?_cons_succ] at hget
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hget

theorem finRange5_mem (x : Fin 5) : x ∈ List.finRange 5 := by
  have h : (List.finRange 5).any (fun y => eqF5 x y) = true := by
    revert x
    decide
  rw [List.any_eq_true] at h
  rcases h with ⟨y, hy, hxy⟩
  rw [eqF5_iff.mp hxy]
  exact hy

theorem mem_candidates_of_reduced (D : MumfordDivisor)
    (h : isReducedMumford D.u D.v = true) : D ∈ candidateDivisors := by
  rcases D with ⟨u, v⟩
  simp only [isReducedMumford, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨htu, htv⟩, hmonic⟩, hulen⟩, hvlen⟩, _⟩
  cases u with
  | nil => cases hmonic
  | cons u0 u_tail =>
    cases u_tail with
    | nil =>
      dsimp only [isMonic, List.isEmpty, Bool.not_false, Bool.true_and, leadCoeff,
        List.getLastD] at hmonic
      have hu0 : u0 = 1 := Fin.ext (Nat.eq_of_beq_eq_true hmonic)
      cases v with
      | nil =>
        rw [hu0]
        simp [candidateDivisors]
      | cons _ _ =>
        simp at hvlen
    | cons u1 u_tail2 =>
      cases u_tail2 with
      | nil =>
        dsimp only [isMonic, List.isEmpty, Bool.not_false, Bool.true_and, leadCoeff,
          List.getLastD] at hmonic
        have hu1 : u1 = 1 := Fin.ext (Nat.eq_of_beq_eq_true hmonic)
        rw [hu1]
        cases v with
        | nil =>
          simp only [candidateDivisors, List.mem_append]
          left; right
          refine List.mem_flatMap.mpr ⟨u0, finRange5_mem u0, ?_⟩
          simp
        | cons v0 v_tail =>
          cases v_tail with
          | nil =>
            simp only [isTrimmedB, Bool.not_eq_true'] at htv
            simp only [candidateDivisors, List.mem_append]
            left; right
            refine List.mem_flatMap.mpr ⟨u0, finRange5_mem u0, ?_⟩
            simp only [List.mem_append, List.mem_map, List.mem_filter]
            right
            exact ⟨v0, ⟨finRange5_mem v0, by simp [htv]⟩, rfl⟩
          | cons _ _ =>
            simp only [List.length_cons] at hvlen
            exact absurd hvlen (Nat.not_lt_of_ge (Nat.le_add_left 2 _))
      | cons u2 u_tail3 =>
        cases u_tail3 with
        | nil =>
          dsimp only [isMonic, List.isEmpty, Bool.not_false, Bool.true_and, leadCoeff,
            List.getLastD] at hmonic
          have hu2 : u2 = 1 := Fin.ext (Nat.eq_of_beq_eq_true hmonic)
          rw [hu2]
          cases v with
          | nil =>
            simp only [candidateDivisors, List.mem_append]
            right
            refine List.mem_flatMap.mpr ⟨u0, finRange5_mem u0, ?_⟩
            refine List.mem_flatMap.mpr ⟨u1, finRange5_mem u1, ?_⟩
            simp
          | cons v0 v_tail =>
            cases v_tail with
            | nil =>
              simp only [isTrimmedB, Bool.not_eq_true'] at htv
              simp only [candidateDivisors, List.mem_append]
              right
              refine List.mem_flatMap.mpr ⟨u0, finRange5_mem u0, ?_⟩
              refine List.mem_flatMap.mpr ⟨u1, finRange5_mem u1, ?_⟩
              simp only [List.mem_append, List.mem_map, List.mem_filter]
              left; right
              exact ⟨v0, ⟨finRange5_mem v0, by simp [htv]⟩, rfl⟩
            | cons v1 v_tail2 =>
              cases v_tail2 with
              | nil =>
                have htv1 : (v1.val == 0) = false := by
                  simpa [isTrimmedB, Bool.not_eq_true'] using htv
                simp only [candidateDivisors, List.mem_append]
                right
                refine List.mem_flatMap.mpr ⟨u0, finRange5_mem u0, ?_⟩
                refine List.mem_flatMap.mpr ⟨u1, finRange5_mem u1, ?_⟩
                simp only [List.mem_append]
                right
                refine List.mem_flatMap.mpr ⟨v0, finRange5_mem v0, ?_⟩
                refine List.mem_map.mpr ⟨v1, List.mem_filter.mpr ⟨finRange5_mem v1, ?_⟩, rfl⟩
                simp [htv1]
              | cons _ _ =>
                simp only [List.length_cons] at hvlen
                exact absurd hvlen (Nat.not_lt_of_ge (Nat.le_add_left 3 _))
        | cons _ _ =>
          simp only [List.length_cons] at hulen
          exact absurd hulen (Nat.not_le_of_lt (Nat.lt_of_lt_of_le (by decide : 3 < 4)
            (Nat.le_add_left 4 _)))

theorem candidates_reduced_in_orbit :
    candidateDivisors.all (fun D => !isReducedMumford D.u D.v || memListB D orbitList) = true := by
  decide +kernel

theorem exists_orbitAt_of_reduced (D : MumfordDivisor)
    (h : isReducedMumford D.u D.v = true) : ∃ i : Fin 71, D = orbitAt i := by
  have hmemC : D ∈ candidateDivisors := mem_candidates_of_reduced D h
  have hall := candidates_reduced_in_orbit
  rw [List.all_eq_true] at hall
  have hD := hall D hmemC
  simp only [h, Bool.not_true, Bool.false_or] at hD
  have hmemO : D ∈ orbitList := mem_of_memListB hD
  have hfind : ∀ xs : List MumfordDivisor, D ∈ xs →
      ∀ (idx : Nat), (∀ (j : Nat) (hj : idx + j < 71), xs[j]? = some (orbitAt ⟨idx + j, hj⟩)) →
      idx + xs.length = 71 → ∃ i : Fin 71, D = orbitAt i := by
    intro xs hxs
    induction xs with
    | nil => cases hxs
    | cons x xs ih =>
      intro idx hidx hlen
      cases hxs with
      | head =>
        have hlt : idx < 71 :=
          Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ xs.length))
            (Nat.le_of_eq hlen)
        have hx0 := hidx 0 hlt
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx0
        exact ⟨⟨idx, hlt⟩, hx0⟩
      | tail _ hmem =>
        refine ih hmem (idx + 1) ?_ ?_
        · intro j hj
          have hj' : idx + (j + 1) < 71 := by
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using hj
          have hget := hidx (j + 1) hj'
          simp only [List.getElem?_cons_succ] at hget
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using hget
        · simpa [Nat.add_assoc, Nat.add_comm 1 xs.length] using hlen
  refine hfind orbitList hmemO 0 ?_ (by simpa using orbitList_length)
  intro j hj
  simp only [Nat.zero_add] at hj ⊢
  change orbitList[j]? = some (orbitList.getD j MumfordDivisor.zero)
  have hjlen : j < orbitList.length := by rw [orbitList_length]; exact hj
  rw [List.getElem?_eq_getElem hjlen, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjlen]
  rfl

/-! ## Part 7: Constructive 71 × 71 Cayley Table Verification & Group Axioms -/

def checkPairZip (di : MumfordDivisor) : List MumfordDivisor → List MumfordDivisor → Bool
  | [], _ => true
  | _ :: _, [] => false
  | dj :: js, dk :: ks => divEqB (cantorAdd di dj) dk && checkPairZip di js ks

def checkRow (i : Nat) : Bool :=
  let di := orbitList.getD i MumfordDivisor.zero
  let rot := orbitList.drop i ++ orbitList.take i
  checkPairZip di orbitList rot

def checkRange (lo hi : Nat) : Bool :=
  (List.range (hi - lo)).all (fun k => checkRow (lo + k))

theorem cayley_rows_0_9   : checkRange 0  9  = true := by decide +kernel
theorem cayley_rows_9_18  : checkRange 9  18 = true := by decide +kernel
theorem cayley_rows_18_27 : checkRange 18 27 = true := by decide +kernel
theorem cayley_rows_27_36 : checkRange 27 36 = true := by decide +kernel
theorem cayley_rows_36_45 : checkRange 36 45 = true := by decide +kernel
theorem cayley_rows_45_54 : checkRange 45 54 = true := by decide +kernel
theorem cayley_rows_54_63 : checkRange 54 63 = true := by decide +kernel
theorem cayley_rows_63_71 : checkRange 63 71 = true := by decide +kernel

theorem checkRow_all (i : Nat) (hi : i < 71) : checkRow i = true := by
  have sliceCheck : ∀ lo len : Nat, (List.range len).all (fun k => checkRow (lo + k)) = true →
      ∀ x : Nat, lo ≤ x → x < lo + len → checkRow x = true := by
    intro lo len hrange x hx1 hx2
    rw [List.all_eq_true] at hrange
    have hk : x - lo ∈ List.range len := List.mem_range.mpr (Nat.sub_lt_left_of_lt_add hx1 hx2)
    have hr := hrange (x - lo) hk
    rwa [Nat.add_sub_of_le hx1] at hr
  if h9 : i < 9 then
    exact sliceCheck 0 9 cayley_rows_0_9 i (Nat.zero_le _) h9
  else if h18 : i < 18 then
    exact sliceCheck 9 9 cayley_rows_9_18 i (Nat.le_of_not_lt h9) h18
  else if h27 : i < 27 then
    exact sliceCheck 18 9 cayley_rows_18_27 i (Nat.le_of_not_lt h18) h27
  else if h36 : i < 36 then
    exact sliceCheck 27 9 cayley_rows_27_36 i (Nat.le_of_not_lt h27) h36
  else if h45 : i < 45 then
    exact sliceCheck 36 9 cayley_rows_36_45 i (Nat.le_of_not_lt h36) h45
  else if h54 : i < 54 then
    exact sliceCheck 45 9 cayley_rows_45_54 i (Nat.le_of_not_lt h45) h54
  else if h63 : i < 63 then
    exact sliceCheck 54 9 cayley_rows_54_63 i (Nat.le_of_not_lt h54) h63
  else
    exact sliceCheck 63 8 cayley_rows_63_71 i (Nat.le_of_not_lt h63) hi

theorem checkPairZip_sound (di : MumfordDivisor) :
    ∀ (js ks : List MumfordDivisor),
      checkPairZip di js ks = true →
      ∀ (j : Nat), j < js.length → j < ks.length →
        cantorAdd di (js.getD j MumfordDivisor.zero) = ks.getD j MumfordDivisor.zero
  | [], _, _, _, hj, _ => by cases hj
  | _ :: _, [], h, _, _, _ => by cases h
  | dj :: js, dk :: ks, h, 0, _, _ => by
    simp only [checkPairZip, Bool.and_eq_true] at h
    exact divEqB_iff.mp h.1
  | dj :: js, dk :: ks, h, j + 1, hj, hjk => by
    simp only [checkPairZip, Bool.and_eq_true] at h
    exact checkPairZip_sound di js ks h.2 j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hjk)

theorem getD_rot_eq (i j : Nat) (hi : i < 71) (hj : j < 71) :
    (orbitList.drop i ++ orbitList.take i).getD j MumfordDivisor.zero =
      orbitList.getD ((i + j) % 71) MumfordDivisor.zero := by
  have hlen : orbitList.length = 71 := orbitList_length
  have hdrop : (orbitList.drop i).length = 71 - i := by
    rw [List.length_drop, hlen]
  have hi_le : i ≤ 71 := Nat.le_of_lt hi
  cases Nat.lt_or_ge (i + j) 71 with
  | inl hsum =>
    have hj_drop : j < (orbitList.drop i).length := by
      rw [hdrop]
      exact Nat.lt_sub_of_add_lt (by simpa [Nat.add_comm] using hsum)
    have hmod : (i + j) % 71 = i + j := Nat.mod_eq_of_lt hsum
    rw [hmod]
    change (orbitList.drop i ++ orbitList.take i)[j]?.getD MumfordDivisor.zero = _
    rw [List.getElem?_append_left hj_drop, List.getElem?_drop]
    rfl
  | inr hsum =>
    have hj_nlt : ¬ (j < (orbitList.drop i).length) := by
      rw [hdrop]
      intro hlt
      exact Nat.not_le_of_lt (Nat.add_lt_of_lt_sub' hlt) (by simpa [Nat.add_comm] using hsum)
    have hge_drop : (orbitList.drop i).length ≤ j := Nat.le_of_not_lt hj_nlt
    have hj_sub : j - (orbitList.drop i).length = i + j - 71 := by
      rw [hdrop]
      have h1 : 71 - i ≤ j := by rw [← hdrop]; exact hge_drop
      apply Nat.eq_sub_of_add_eq
      calc j - (71 - i) + 71
          = (j - (71 - i)) + ((71 - i) + i) := by rw [Nat.sub_add_cancel hi_le]
        _ = ((j - (71 - i)) + (71 - i)) + i := by rw [Nat.add_assoc]
        _ = j + i := by rw [Nat.sub_add_cancel h1]
        _ = i + j := Nat.add_comm j i
    have hlt_take : i + j - 71 < i :=
      Nat.sub_lt_left_of_lt_add hsum (by rw [Nat.add_comm 71 i]; exact Nat.add_lt_add_left hj i)
    have hmod : (i + j) % 71 = i + j - 71 := by
      have hsub_lt : i + j - 71 < 71 := Nat.lt_trans hlt_take hi
      have hsum_eq : i + j = (i + j - 71) + 71 := (Nat.sub_add_cancel hsum).symm
      have hcalc : ((i + j - 71) + 71) % 71 = i + j - 71 := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_lt]
      rwa [← hsum_eq] at hcalc
    rw [hmod]
    change (orbitList.drop i ++ orbitList.take i)[j]?.getD MumfordDivisor.zero = _
    rw [List.getElem?_append_right hge_drop, hj_sub, List.getElem?_take_of_lt hlt_take]
    rfl

/-- Main Cayley table theorem: `cantorAdd` on the 71-element orbit equals addition mod 71. -/
theorem orbitAt_cayley (i j : Fin 71) :
    cantorAdd (orbitAt i) (orbitAt j) =
      orbitAt ⟨(i.val + j.val) % 71, Nat.mod_lt _ (by decide)⟩ := by
  have hrow := checkRow_all i.val i.isLt
  dsimp [checkRow] at hrow
  have hlen : orbitList.length = 71 := orbitList_length
  have hrot_len : (orbitList.drop i.val ++ orbitList.take i.val).length = 71 := by
    rw [List.length_append, List.length_drop, List.length_take, hlen]
    have hi_le : i.val ≤ 71 := Nat.le_of_lt i.isLt
    rw [Nat.min_eq_left hi_le]
    exact Nat.sub_add_cancel hi_le
  have hzip := checkPairZip_sound (orbitList.getD i.val MumfordDivisor.zero)
    orbitList (orbitList.drop i.val ++ orbitList.take i.val) hrow j.val
    (by rw [hlen]; exact j.isLt) (by rw [hrot_len]; exact j.isLt)
  rw [getD_rot_eq i.val j.val i.isLt j.isLt] at hzip
  exact hzip

/-- Constructive closure theorem: `cantorAdd` preserves the reduced Mumford invariant. -/
theorem cantorAdd_preserves_reduced (D1 D2 : MumfordDivisor)
    (h1 : isReducedMumford D1.u D1.v = true)
    (h2 : isReducedMumford D2.u D2.v = true) :
    isReducedMumford (cantorAdd D1 D2).u (cantorAdd D1 D2).v = true := by
  rcases exists_orbitAt_of_reduced D1 h1 with ⟨i, hi⟩
  rcases exists_orbitAt_of_reduced D2 h2 with ⟨j, hj⟩
  rw [hi, hj, orbitAt_cayley]
  exact orbitAt_all_reduced _

theorem cantorSmulFuel_preserves_reduced (fuel n : Nat) (acc base : MumfordDivisor)
    (hacc : isReducedMumford acc.u acc.v = true)
    (hbase : isReducedMumford base.u base.v = true) :
    isReducedMumford (cantorSmulFuel fuel n acc base).u
      (cantorSmulFuel fuel n acc base).v = true := by
  induction fuel generalizing n acc base with
  | zero => exact hacc
  | succ fuel ih =>
    simp only [cantorSmulFuel]
    split
    · exact hacc
    · have hacc' : isReducedMumford
          (if n % 2 == 1 then cantorAdd acc base else acc).u
          (if n % 2 == 1 then cantorAdd acc base else acc).v = true := by
        split
        · exact cantorAdd_preserves_reduced acc base hacc hbase
        · exact hacc
      exact ih (n / 2) _ (cantorAdd base base) hacc'
        (cantorAdd_preserves_reduced base base hbase hbase)

/-- Constructive closure theorem: `cantorSmul` preserves the reduced Mumford invariant. -/
theorem cantorSmul_preserves_reduced (n : Nat) (D : MumfordDivisor)
    (hD : isReducedMumford D.u D.v = true) :
    isReducedMumford (cantorSmul n D).u (cantorSmul n D).v = true :=
  cantorSmulFuel_preserves_reduced (n + 1) n MumfordDivisor.zero D zero_is_reduced hD

/-! ## Part 8: Order 71, Primitivity & Cyclic Group Axioms on J(C)(F_5) -/

/-- Constructive kernel proof that `71 • [P_0 - ∞] = 0` in `J(C)(F_5)`. -/
theorem jacobian_D0_order_71 : cantorSmul 71 D0 = MumfordDivisor.zero := by
  have h : divEqB (cantorSmul 71 D0) MumfordDivisor.zero = true := by decide
  exact divEqB_iff.mp h

/-- Constructive proof that `[P_0 - ∞]` has no smaller positive order (`1 ≤ k ≤ 70`). -/
theorem jacobian_D0_primitive :
    ∀ k : Nat, 1 ≤ k → k ≤ 70 → cantorSmul k D0 ≠ MumfordDivisor.zero := by
  intro k hk1 hk70 heq
  have hlt : k < 71 := Nat.lt_succ_of_le hk70
  have hne : ∀ i : Fin 71, 1 ≤ i.val →
      !divEqB (cantorSmul i.val D0) MumfordDivisor.zero = true := by
    decide
  have hbad := hne ⟨k, hlt⟩ hk1
  have heqB : divEqB (cantorSmul k D0) MumfordDivisor.zero = true := divEqB_iff.mpr heq
  change !divEqB (cantorSmul k D0) MumfordDivisor.zero = true at hbad
  rw [heqB] at hbad
  cases hbad

/-- Orbit membership predicate `{cantorSmul k D0 | k < 71}`. -/
def inD0Orbit (D : MumfordDivisor) : Prop :=
  ∃ k : Fin 71, D = orbitAt k

theorem inD0Orbit_iff_smul (D : MumfordDivisor) :
    inD0Orbit D ↔ ∃ k : Nat, k < 71 ∧ D = cantorSmul k D0 := by
  constructor
  · intro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi.trans (orbitAt_smul i)⟩
  · intro ⟨k, hk, heq⟩
    exact ⟨⟨k, hk⟩, heq.trans (orbitAt_smul ⟨k, hk⟩).symm⟩

/-- Associativity, commutativity, identity, and inverse group axioms verified across the
full 71-element cyclic orbit generated by `D0`, establishing `J(C)(F_5) ≅ Z/71Z`. -/
theorem jacobian_group_axioms_on_orbit :
    (∀ A B C, inD0Orbit A → inD0Orbit B → inD0Orbit C →
      cantorAdd (cantorAdd A B) C = cantorAdd A (cantorAdd B C)) ∧
    (∀ A B, inD0Orbit A → inD0Orbit B →
      cantorAdd A B = cantorAdd B A) ∧
    (∀ A, inD0Orbit A →
      cantorAdd A MumfordDivisor.zero = A ∧
      cantorAdd MumfordDivisor.zero A = A) ∧
    (∀ A, inD0Orbit A →
      inD0Orbit (cantorNeg A) ∧
      cantorAdd A (cantorNeg A) = MumfordDivisor.zero ∧
      cantorAdd (cantorNeg A) A = MumfordDivisor.zero) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B C ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    rw [ha, hb, hc, orbitAt_cayley, orbitAt_cayley, orbitAt_cayley, orbitAt_cayley]
    congr 1
    apply Fin.ext
    dsimp
    rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  · intro A B ⟨a, ha⟩ ⟨b, hb⟩
    rw [ha, hb, orbitAt_cayley, orbitAt_cayley]
    congr 1
    apply Fin.ext
    dsimp
    rw [Nat.add_comm]
  · intro A ⟨a, ha⟩
    rw [ha, ← orbitAt_zero, orbitAt_cayley, orbitAt_cayley]
    constructor <;> {
      congr 1
      apply Fin.ext
      dsimp
      try rw [Nat.add_zero]
      try rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt a.isLt
    }
  · intro A ⟨a, ha⟩
    let invIdx : Fin 71 := ⟨(71 - a.val) % 71, Nat.mod_lt _ (by decide)⟩
    have hneg : cantorNeg (orbitAt a) = orbitAt invIdx := divEqB_iff.mp (cantorNeg_orbitAt a)
    refine ⟨⟨invIdx, by rw [ha, hneg]⟩, ?_, ?_⟩
    · rw [ha, hneg, orbitAt_cayley, ← orbitAt_zero]
      congr 1
      apply Fin.ext
      dsimp [invIdx]
      rw [Nat.add_mod_mod, Nat.add_sub_of_le (Nat.le_of_lt a.isLt), Nat.mod_self]
    · rw [ha, hneg, orbitAt_cayley, ← orbitAt_zero]
      congr 1
      apply Fin.ext
      dsimp [invIdx]
      rw [Nat.mod_add_mod, Nat.sub_add_cancel (Nat.le_of_lt a.isLt), Nat.mod_self]


end LeanAsm.Genus2.Cantor

-- end of file: leanasm/src/LeanAsm/Genus2/Cantor.lean
