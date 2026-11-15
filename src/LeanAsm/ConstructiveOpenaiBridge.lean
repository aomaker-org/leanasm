-- Path: leanasm/src/LeanAsm/ConstructiveOpenaiBridge.lean
-- Constructive port of discrete lattice routes, box-layer slab foliation,
-- oriented plaquette faces, and gauge-covariant holonomy from the 4 substantive
-- pure constructive openai-20261028 files (Route, Foliation, Faces, Connection).
-- Max Column: 120 Columns

import LeanAsm.YangMillsQ8

namespace ConstructiveOpenaiBridge

-- =============================================================================
-- Part 1: 4D Lattice Sites, Signed Hyperoctahedral Symmetries & Routes
-- =============================================================================

/-- Coordinate axis on the 4D hypercubic lattice (`0..3`). -/
abbrev Axis := Fin 4

/-- Concrete 4D integer lattice site `(x0, x1, x2, x3)`. -/
structure Cover4 where
  x0 : Int
  x1 : Int
  x2 : Int
  x3 : Int
  deriving DecidableEq, Repr

namespace Cover4

/-- Zero site `(0, 0, 0, 0)`. -/
def zero : Cover4 := ⟨0, 0, 0, 0⟩

/-- Read coordinate `i : Axis` of a 4D lattice site. -/
def get (x : Cover4) (i : Axis) : Int :=
  match i.val with
  | 0 => x.x0
  | 1 => x.x1
  | 2 => x.x2
  | _ => x.x3

/-- Build a `Cover4` from a coordinate function `Axis -> Int`. -/
def ofFn (f : Axis → Int) : Cover4 :=
  ⟨f 0, f 1, f 2, f 3⟩

/-- Update coordinate `i` of `x` to `v`. -/
def update (x : Cover4) (i : Axis) (v : Int) : Cover4 :=
  match i.val with
  | 0 => ⟨v, x.x1, x.x2, x.x3⟩
  | 1 => ⟨x.x0, v, x.x2, x.x3⟩
  | 2 => ⟨x.x0, x.x1, v, x.x3⟩
  | _ => ⟨x.x0, x.x1, x.x2, v⟩

/-- Unit basis increment along axis `i`. -/
def step (i : Axis) : Cover4 :=
  update zero i 1

/-- Componentwise site addition. -/
def add (x y : Cover4) : Cover4 :=
  ⟨x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2, x.x3 + y.x3⟩

/-- Componentwise site negation. -/
def neg (x : Cover4) : Cover4 :=
  ⟨-x.x0, -x.x1, -x.x2, -x.x3⟩

/-- Componentwise site subtraction. -/
def sub (x y : Cover4) : Cover4 :=
  ⟨x.x0 - y.x0, x.x1 - y.x1, x.x2 - y.x2, x.x3 - y.x3⟩

/-- Scalar multiplication of a site by `c : Int`. -/
def smul (c : Int) (x : Cover4) : Cover4 :=
  ⟨c * x.x0, c * x.x1, c * x.x2, c * x.x3⟩

theorem ext {x y : Cover4} (h : ∀ i : Axis, x.get i = y.get i) : x = y := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rcases x with ⟨a0, a1, a2, a3⟩
  rcases y with ⟨b0, b1, b2, b3⟩
  dsimp [get] at h0 h1 h2 h3
  subst h0 h1 h2 h3
  rfl

theorem get_ofFn (f : Axis → Int) (i : Axis) : (ofFn f).get i = f i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_zero (i : Axis) : zero.get i = 0 := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_add (x y : Cover4) (i : Axis) : (add x y).get i = x.get i + y.get i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_sub (x y : Cover4) (i : Axis) : (sub x y).get i = x.get i - y.get i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_neg (x : Cover4) (i : Axis) : (neg x).get i = -x.get i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_smul (c : Int) (x : Cover4) (i : Axis) : (smul c x).get i = c * x.get i := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_update_same (x : Cover4) (i : Axis) (v : Int) :
    (x.update i v).get i = v := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_update_ne (x : Cover4) {i j : Axis} (hne : j ≠ i) (v : Int) :
    (x.update i v).get j = x.get j := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have hval : j ≠ i := fun h => hne (Fin.ext h)
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => exact absurd rfl hval
  | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 => rfl
  | _ + 4, _ => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))
  | _, _ + 4 => exact absurd hj (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem get_step (i j : Axis) : (step i).get j = if j = i then 1 else 0 := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => rfl
  | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 => rfl
  | _ + 4, _ => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))
  | _, _ + 4 => exact absurd hj (Nat.not_lt_of_le (Nat.le_add_left 4 _))

theorem add_assoc (x y z : Cover4) : add (add x y) z = add x (add y z) := by
  rcases x with ⟨_, _, _, _⟩
  rcases y with ⟨_, _, _, _⟩
  rcases z with ⟨_, _, _, _⟩
  simp [add, Int.add_assoc]

theorem add_comm (x y : Cover4) : add x y = add y x := by
  rcases x with ⟨_, _, _, _⟩
  rcases y with ⟨_, _, _, _⟩
  simp [add, Int.add_comm]

theorem add_zero (x : Cover4) : add x zero = x := by
  rcases x with ⟨_, _, _, _⟩
  simp [add, zero]

theorem zero_add (x : Cover4) : add zero x = x := by
  rcases x with ⟨_, _, _, _⟩
  simp [add, zero]

theorem add_sub_step (x : Cover4) (i : Axis) :
    sub (add x (step i)) (step i) = x := by
  apply ext
  intro j
  rw [get_sub, get_add]
  omega

theorem sub_add_step (x : Cover4) (i : Axis) :
    add (sub x (step i)) (step i) = x := by
  apply ext
  intro j
  rw [get_add, get_sub]
  omega

theorem add_neg_eq_sub (x y : Cover4) : add x (neg y) = sub x y := by
  rcases x with ⟨_, _, _, _⟩
  rcases y with ⟨_, _, _, _⟩
  simp [add, neg, sub, Int.sub_eq_add_neg]

theorem one_smul (x : Cover4) : smul 1 x = x := by
  rcases x with ⟨_, _, _, _⟩
  simp [smul]

theorem neg_one_smul (x : Cover4) : smul (-1) x = neg x := by
  rcases x with ⟨_, _, _, _⟩
  simp [smul, neg]

theorem add_smul (a b : Int) (x : Cover4) :
    smul (a + b) x = add (smul a x) (smul b x) := by
  rcases x with ⟨_, _, _, _⟩
  simp [smul, add, Int.add_mul]

theorem smul_step_add_step (x : Cover4) (d : Int) (j : Axis) :
    add (add x (smul d (step j))) (step j) = add x (smul (d + 1) (step j)) := by
  apply ext
  intro i
  rw [get_add, get_add, get_add, get_smul, get_smul, Int.add_mul, Int.one_mul]
  omega

theorem smul_add1_sub_step (x : Cover4) (d : Int) (j : Axis) :
    sub (add x (smul (d + 1) (step j))) (step j) = add x (smul d (step j)) := by
  apply ext
  intro i
  rw [get_sub, get_add, get_add, get_smul, get_smul, Int.add_mul, Int.one_mul]
  omega

theorem step_smul_eq_update {x : Cover4} {i : Axis} (w : Int) :
    add x (smul (w - x.get i) (step i)) = x.update i w := by
  apply ext
  intro j
  rw [get_add, get_smul, get_step]
  by_cases hj : j = i
  · subst hj
    rw [get_update_same]
    simp
    omega
  · rw [get_update_ne _ hj]
    simp [hj]

theorem add_left_inj {a b c : Cover4} (h : add a b = add a c) : b = c := by
  apply ext
  intro i
  have hi := congrArg (fun p => p.get i) h
  rw [get_add, get_add] at hi
  omega

end Cover4

/-- Explicit permutation on `Fin 4`. -/
structure Perm4 where
  toFun : Axis → Axis
  invFun : Axis → Axis
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

namespace Perm4

/-- Identity permutation on `Axis`. -/
def refl : Perm4 :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- Inverse permutation. -/
def inv (p : Perm4) : Perm4 :=
  ⟨p.invFun, p.toFun, p.right_inv, p.left_inv⟩

/-- Composition `p ∘ q`. -/
def comp (p q : Perm4) : Perm4 :=
  ⟨fun i => p.toFun (q.toFun i),
   fun i => q.invFun (p.invFun i),
   fun i => by simp only [p.left_inv, q.left_inv],
   fun i => by simp only [q.right_inv, p.right_inv]⟩

/-- Axis reversal permutation `Fin.rev` (`0↔3`, `1↔2`). -/
def rev : Perm4 :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

theorem injective (p : Perm4) {a b : Axis} (h : p.toFun a = p.toFun b) : a = b := by
  have := congrArg p.invFun h
  rwa [p.left_inv, p.left_inv] at this

theorem ne (p : Perm4) {a b : Axis} (h : a ≠ b) : p.toFun a ≠ p.toFun b :=
  fun heq => h (p.injective heq)

end Perm4

/-- Hyperoctahedral signed symmetry `B_4` (axis permutation + sign flips). -/
structure SignedSym4 where
  perm : Perm4
  flip : Axis → Bool

namespace SignedSym4

/-- Inverse signed symmetry `s⁻¹`. -/
def inv (s : SignedSym4) : SignedSym4 :=
  ⟨s.perm.inv, fun j => s.flip (s.perm.invFun j)⟩

/-- Linear orthogonal action of `s` on `Cover4`: coordinate `s.perm i` gets
`± x.get i`. -/
def act (s : SignedSym4) (x : Cover4) : Cover4 :=
  Cover4.ofFn fun j =>
    let i := s.perm.invFun j
    if s.flip i then -x.get i else x.get i

theorem act_at (s : SignedSym4) (x : Cover4) (i : Axis) :
    (s.act x).get (s.perm.toFun i) = if s.flip i then -x.get i else x.get i := by
  dsimp [act]
  rw [Cover4.get_ofFn, s.perm.left_inv]

theorem act_inv (s : SignedSym4) (x : Cover4) : s.inv.act (s.act x) = x := by
  apply Cover4.ext
  intro i
  dsimp [inv, act]
  rw [Cover4.get_ofFn, Cover4.get_ofFn]
  dsimp [Perm4.inv]
  simp only [s.perm.left_inv]
  cases s.flip i <;> simp <;> omega

theorem act_add (s : SignedSym4) (x y : Cover4) :
    s.act (Cover4.add x y) = Cover4.add (s.act x) (s.act y) := by
  apply Cover4.ext
  intro j
  rw [Cover4.get_add]
  dsimp [act]
  rw [Cover4.get_ofFn, Cover4.get_ofFn, Cover4.get_ofFn, Cover4.get_add]
  cases s.flip (s.perm.invFun j) <;> simp <;> omega

theorem act_step (s : SignedSym4) (i : Axis) :
    s.act (Cover4.step i) =
      if s.flip i then Cover4.neg (Cover4.step (s.perm.toFun i))
      else Cover4.step (s.perm.toFun i) := by
  apply Cover4.ext
  intro j
  dsimp [act]
  rw [Cover4.get_ofFn]
  have hne : ∀ a : Axis, a ≠ s.perm.toFun i → s.perm.invFun a ≠ i := by
    intro a ha heq
    apply ha
    calc a = s.perm.toFun (s.perm.invFun a) := (s.perm.right_inv a).symm
         _ = s.perm.toFun i := by rw [heq]
  by_cases hj : j = s.perm.toFun i
  · subst hj
    rw [s.perm.left_inv, Cover4.get_step]
    cases s.flip i <;> simp [Cover4.get_neg, Cover4.get_step]
  · have hi := hne j hj
    rw [Cover4.get_step]
    simp [hi]
    cases s.flip i
    · simp [Cover4.get_step, hj]
    · simp [Cover4.get_neg, Cover4.get_step, hj]

theorem act_neg (s : SignedSym4) (x : Cover4) :
    s.act (Cover4.neg x) = Cover4.neg (s.act x) := by
  apply Cover4.ext
  intro j
  dsimp [act]
  rw [Cover4.get_neg, Cover4.get_ofFn, Cover4.get_ofFn, Cover4.get_neg]
  cases s.flip (s.perm.invFun j) <;> simp <;> omega

theorem act_injective (s : SignedSym4) {x y : Cover4} (h : s.act x = s.act y) :
    x = y := by
  have := congrArg s.inv.act h
  rwa [s.act_inv, s.act_inv] at this

/-- Affine hyperoctahedral action `x ↦ s · x + t`. -/
def affine (s : SignedSym4) (t x : Cover4) : Cover4 :=
  Cover4.add (s.act x) t

theorem affine_injective (s : SignedSym4) (t : Cover4) {x y : Cover4}
    (h : affine s t x = affine s t y) : x = y := by
  dsimp [affine] at h
  rw [Cover4.add_comm (s.act x) t, Cover4.add_comm (s.act y) t] at h
  exact s.act_injective (Cover4.add_left_inj h)

theorem affine_add (s : SignedSym4) (t x y : Cover4) :
    affine s t (Cover4.add x y) = Cover4.add (affine s t x) (s.act y) := by
  dsimp [affine]
  rw [s.act_add, Cover4.add_assoc, Cover4.add_comm (s.act y) t, ← Cover4.add_assoc]

end SignedSym4

/-- Directed lattice step along axis `dir` (negative orientation if `neg = true`). -/
structure LatticeStep where
  dir : Axis
  neg : Bool
  deriving DecidableEq, Repr

/-- Lattice walk as a list of directed unit steps. -/
abbrev Walk := List LatticeStep

/-- Positive unit step along axis `i`. -/
def posDir (i : Axis) : LatticeStep := ⟨i, false⟩

/-- Negative unit step along axis `i`. -/
def negDir (i : Axis) : LatticeStep := ⟨i, true⟩

namespace LatticeStep

/-- Reverse the orientation of a step. -/
def rev (d : LatticeStep) : LatticeStep := ⟨d.dir, !d.neg⟩

/-- Signed coordinate displacement of a step on `Cover4`. -/
def vec (d : LatticeStep) : Cover4 :=
  if d.neg then Cover4.neg (Cover4.step d.dir) else Cover4.step d.dir

/-- Rotate a directed step under a signed symmetry `s`. -/
def rotate (d : LatticeStep) (s : SignedSym4) : LatticeStep :=
  ⟨s.perm.toFun d.dir, Bool.xor d.neg (s.flip d.dir)⟩

theorem rev_pos (i : Axis) : (posDir i).rev = negDir i := rfl
theorem rev_neg (i : Axis) : (negDir i).rev = posDir i := rfl

theorem rev_rev (d : LatticeStep) : d.rev.rev = d := by
  rcases d with ⟨i, b⟩
  cases b <;> rfl

theorem rev_rotate (d : LatticeStep) (s : SignedSym4) :
    d.rev.rotate s = (d.rotate s).rev := by
  rcases d with ⟨i, b⟩
  dsimp [rotate, rev]
  cases b <;> cases s.flip i <;> rfl

theorem vec_rev (d : LatticeStep) : d.rev.vec = Cover4.neg d.vec := by
  rcases d with ⟨i, b⟩
  rcases Cover4.step i with ⟨a0, a1, a2, a3⟩
  cases b <;> simp [vec, rev, Cover4.neg]

theorem vec_rotate (d : LatticeStep) (s : SignedSym4) :
    (d.rotate s).vec = s.act d.vec := by
  have hpos : ∀ i : Axis, ((posDir i).rotate s).vec = s.act (posDir i).vec := by
    intro i
    dsimp [rotate, vec, posDir]
    cases hf : s.flip i <;> simp [SignedSym4.act_step, hf]
  rcases d with ⟨i, b⟩
  cases b
  · exact hpos i
  · change (((posDir i).rev).rotate s).vec = s.act ((posDir i).rev).vec
    rw [rev_rotate, vec_rev, hpos i, vec_rev, s.act_neg]

end LatticeStep

/-- Endpoint of walk `w` starting at `x`. -/
def walkStop (x : Cover4) : Walk → Cover4
  | [] => x
  | d :: w => walkStop (Cover4.add x d.vec) w

/-- List of sites visited by walk `w` starting at `x`. -/
def walkVisits (x : Cover4) : Walk → List Cover4
  | [] => [x]
  | d :: w => x :: walkVisits (Cover4.add x d.vec) w

/-- Reverse a walk (reversing order and inverting each step). -/
def walkReverse (w : Walk) : Walk :=
  w.reverse.map LatticeStep.rev

theorem walkStop_append (x : Cover4) (a b : Walk) :
    walkStop x (a ++ b) = walkStop (walkStop x a) b := by
  induction a generalizing x with
  | nil => rfl
  | cons d l ih => exact ih (Cover4.add x d.vec)

theorem walkReverse_append (p q : Walk) :
    walkReverse (p ++ q) = walkReverse q ++ walkReverse p := by
  simp [walkReverse, List.reverse_append, List.map_append]

/-- Straight signed leg of integer length `d` along axis `i`. -/
def straightWalk (i : Axis) (d : Int) : Walk :=
  List.replicate d.natAbs ⟨i, decide (d < 0)⟩

theorem reverse_straightWalk (i : Axis) (d : Int) :
    walkReverse (straightWalk i d) = straightWalk i (-d) := by
  dsimp [walkReverse, straightWalk]
  rw [List.reverse_replicate, List.map_replicate]
  by_cases h0 : d = 0
  · subst h0; simp
  · have hna : d.natAbs = (-d).natAbs := by omega
    have hb : LatticeStep.rev ⟨i, decide (d < 0)⟩ = ⟨i, decide (-d < 0)⟩ := by
      dsimp [LatticeStep.rev]
      congr 1
      by_cases hl : d < 0
      · rw [decide_eq_true hl, decide_eq_false (by omega : ¬(-d < 0))]
        rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega : -d < 0)]
        rfl
    rw [hna, hb]

theorem walkStop_replicate (x : Cover4) (n : Nat) (s : LatticeStep) :
    walkStop x (List.replicate n s) = Cover4.add x (Cover4.smul n s.vec) := by
  induction n generalizing x with
  | zero =>
    simp [walkStop]
    apply Cover4.ext
    intro j
    rw [Cover4.get_add, Cover4.get_smul]
    omega
  | succ k ih =>
    rw [List.replicate_succ, walkStop, ih]
    rw [Cover4.add_assoc]
    congr 1
    apply Cover4.ext
    intro j
    rw [Cover4.get_add, Cover4.get_smul, Cover4.get_smul, Int.natCast_succ, Int.add_mul,
        Int.one_mul, Int.add_comm]

theorem straightWalk_stop (x : Cover4) (i : Axis) (d : Int) :
    walkStop x (straightWalk i d) = Cover4.add x (Cover4.smul d (Cover4.step i)) := by
  rw [straightWalk, walkStop_replicate]
  congr 1
  by_cases hl : d < 0
  · simp only [hl, decide_true, LatticeStep.vec, ↓reduceIte]
    have hd : (d.natAbs : Int) = -d := by omega
    rw [hd]
    apply Cover4.ext
    intro j
    rw [Cover4.get_smul, Cover4.get_smul, Cover4.get_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  · simp only [hl, decide_false, Bool.false_eq_true, LatticeStep.vec, ↓reduceIte]
    have hd : (d.natAbs : Int) = d := by omega
    rw [hd]

/-- Coordinate-ordered lattice route from `x` to `y` along axis list `l`. -/
def axisRoute (x y : Cover4) (l : List Axis) : Walk :=
  l.flatMap fun a => straightWalk a (y.get a - x.get a)

theorem axisRoute_append (p q : List Axis) (x y : Cover4) :
    axisRoute x y (p ++ q) = axisRoute x y p ++ axisRoute x y q := by
  simp [axisRoute, List.flatMap_append]

theorem axisRoute_reverse (l : List Axis) (x y : Cover4) :
    axisRoute y x l.reverse = walkReverse (axisRoute x y l) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, axisRoute_append, ih]
    dsimp [axisRoute]
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [List.flatMap_cons, walkReverse_append]
    congr 1
    rw [reverse_straightWalk]
    congr 1
    omega

theorem axisRoute_support (o x y : Cover4) (l : List Axis)
    (h : ∀ i ∈ l, x.get i = y.get i) :
    axisRoute o x l = axisRoute o y l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha : x.get a = y.get a := h a (List.Mem.head _)
    have hr : ∀ i ∈ rest, x.get i = y.get i := fun i hi => h i (List.Mem.tail _ hi)
    have hrest : axisRoute o x rest = axisRoute o y rest := ih hr
    dsimp [axisRoute]
    dsimp [axisRoute] at hrest
    rw [List.flatMap_cons, List.flatMap_cons, ha, hrest]

theorem rev_range : (List.finRange 4).map Fin.rev = (List.finRange 4).reverse := by
  decide

/-- Axis list ordered by `o : Perm4`. -/
def allAxes (o : Perm4) : List Axis :=
  (List.finRange 4).map o.toFun

/-- Complete 4-axis route from `x` to `y` following permutation order `o`. -/
def routeWalk (x y : Cover4) (o : Perm4) : Walk :=
  axisRoute x y (allAxes o)

/-- Reversed order `o ∘ Fin.rev`. -/
def backOrder4 (o : Perm4) : Perm4 :=
  Perm4.comp o Perm4.rev

theorem backOrder4_invol (o : Perm4) : backOrder4 (backOrder4 o) = o := by
  rcases o with ⟨f, g, hl, hr⟩
  dsimp [backOrder4, Perm4.comp, Perm4.rev]
  have hf : (fun i => f (Fin.rev (Fin.rev i))) = f := funext fun i => by rw [Fin.rev_rev]
  have hg : (fun i => Fin.rev (Fin.rev (g i))) = g := funext fun i => by rw [Fin.rev_rev]
  congr 1

theorem back_axes (o : Perm4) : allAxes (backOrder4 o) = (allAxes o).reverse := by
  dsimp [allAxes, backOrder4, Perm4.comp, Perm4.rev]
  rw [← List.map_reverse, ← rev_range, List.map_map]
  rfl

theorem back_route (x y : Cover4) (o : Perm4) :
    routeWalk x y (backOrder4 o) = walkReverse (routeWalk y x o) := by
  dsimp [routeWalk]
  rw [back_axes, axisRoute_reverse]

/-- Rotated axis order under `s : SignedSym4`. -/
def orderPerm4 (s : SignedSym4) (o : Perm4) : Perm4 :=
  Perm4.comp s.perm o

theorem indexRoute (d : Int) (a : Axis) (s : SignedSym4) :
    List.map (fun st => st.rotate s) (straightWalk a d) =
      straightWalk (s.perm.toFun a) (if s.flip a then -d else d) := by
  dsimp [straightWalk]
  rw [List.map_replicate]
  cases hf : s.flip a
  · simp [hf, LatticeStep.rotate]
  · by_cases h0 : d = 0
    · subst h0; simp [hf, LatticeStep.rotate]
    · have hna : d.natAbs = (-d).natAbs := by omega
      have hst : (⟨a, decide (d < 0)⟩ : LatticeStep).rotate s =
          ⟨s.perm.toFun a, decide (-d < 0)⟩ := by
        dsimp [LatticeStep.rotate]
        congr 1
        by_cases hl : d < 0
        · rw [decide_eq_true hl, decide_eq_false (by omega : ¬(-d < 0)), hf]
          rfl
        · rw [decide_eq_false hl, decide_eq_true (by omega : -d < 0), hf]
          rfl
      simp only [↓reduceIte]
      rw [hna, hst]

theorem send_route (x y : Cover4) (o : Perm4) (s : SignedSym4) (b : Cover4) :
    List.map (fun st => st.rotate s) (routeWalk x y o) =
      routeWalk (s.affine b x) (s.affine b y) (orderPerm4 s o) := by
  have he : allAxes (orderPerm4 s o) = List.map s.perm.toFun (allAxes o) := by
    dsimp [allAxes, orderPerm4, Perm4.comp]
    rw [List.map_map]
    rfl
  dsimp [routeWalk]
  rw [he]
  dsimp [axisRoute]
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext i
  rw [indexRoute]
  congr 1
  dsimp [SignedSym4.affine]
  rw [Cover4.get_add, Cover4.get_add, s.act_at, s.act_at]
  cases hf : s.flip i <;> simp <;> omega

/-- Standard unit plaquette boundary walk along axes `(a, b)`. -/
def squareWalk (a b : Axis) : Walk :=
  [posDir a, posDir b, negDir a, negDir b]

theorem squareWalk_corners (x : Cover4) (a b : Axis) :
    walkVisits x (squareWalk a b) =
      [x,
       Cover4.add x (Cover4.step a),
       Cover4.add (Cover4.add x (Cover4.step a)) (Cover4.step b),
       Cover4.add x (Cover4.step b),
       x] := by
  dsimp [squareWalk, walkVisits, posDir, negDir, LatticeStep.vec]
  refine congrArg (x :: ·) (congrArg (Cover4.add x (Cover4.step a) :: ·)
    (congrArg (Cover4.add (Cover4.add x (Cover4.step a)) (Cover4.step b) :: ·) ?_))
  have h1 : Cover4.add (Cover4.add (Cover4.add x (Cover4.step a)) (Cover4.step b))
      (Cover4.neg (Cover4.step a)) = Cover4.add x (Cover4.step b) := by
    apply Cover4.ext; intro j
    rw [Cover4.get_add, Cover4.get_add, Cover4.get_add, Cover4.get_neg, Cover4.get_add]
    omega
  have h2 : Cover4.add (Cover4.add x (Cover4.step b)) (Cover4.neg (Cover4.step b)) = x := by
    apply Cover4.ext; intro j
    rw [Cover4.get_add, Cover4.get_add, Cover4.get_neg]
    omega
  rw [h1, h2]

-- =============================================================================
-- Part 2: Finite Box Layers, Slab Decomposition & Constructive Sum Foliation
-- =============================================================================

/-- Duplicate-free coordinate layer `[-r, r]`. -/
def layerRange (r : Nat) : List Int :=
  (List.range (2 * r + 1)).map (fun (k : Nat) => (k : Int) - (r : Int))

theorem layerRange_length (r : Nat) : (layerRange r).length = 2 * r + 1 := by
  simp [layerRange]

theorem mem_layerRange_iff {r : Nat} {z : Int} :
    z ∈ layerRange r ↔ -(r : Int) ≤ z ∧ z ≤ (r : Int) := by
  dsimp [layerRange]
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(z + r).toNat, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · omega

private theorem nodup_map_inj {α β : Type} (l : List α) (f : α → β)
    (hinj : ∀ a b, f a = f b → a = b) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons]
    have hcons := List.nodup_cons.mp hl
    refine ⟨?_, ih hcons.2⟩
    intro hm
    rw [List.mem_map] at hm
    rcases hm with ⟨b, hb, hfab⟩
    exact hcons.1 ((hinj b a hfab) ▸ hb)

private theorem nodup_filter_keep {α : Type} (l : List α) (p : α → Bool)
    (hl : l.Nodup) : (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hcons := List.nodup_cons.mp hl
    dsimp [List.filter]
    cases hp : p a
    · exact ih hcons.2
    · rw [List.nodup_cons]
      refine ⟨?_, ih hcons.2⟩
      intro hm
      rw [List.mem_filter] at hm
      exact hcons.1 hm.1

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
    rw [List.range_succ, List.nodup_append]
    refine ⟨ih, List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil, ?_⟩
    intro a ha b hb heq
    subst heq
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_range] at ha
    exact Nat.lt_irrefl a ha

theorem layerRange_nodup (r : Nat) : (layerRange r).Nodup := by
  dsimp [layerRange]
  apply nodup_map_inj
  · intro a b h
    omega
  · exact range_nodup (2 * r + 1)

/-- Duplicate-free finite 4D box `[-r, r]^4`. -/
def boxSites (r : Nat) : List Cover4 :=
  (layerRange r).flatMap fun a0 =>
    (layerRange r).flatMap fun a1 =>
      (layerRange r).flatMap fun a2 =>
        (layerRange r).map fun a3 => ⟨a0, a1, a2, a3⟩

private theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (k : Nat)
    (hk : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons, List.length_append]
    rw [hk a (List.Mem.head _)]
    rw [ih (fun b hb => hk b (List.Mem.tail _ hb))]
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem boxSites_length (r : Nat) : (boxSites r).length = (2 * r + 1) ^ 4 := by
  dsimp [boxSites]
  rw [length_flatMap_const _ _ ((2 * r + 1) ^ 3)]
  · rw [layerRange_length]
    have h4 : (2 * r + 1) ^ 4 = (2 * r + 1) * (2 * r + 1) ^ 3 := by
      rw [Nat.pow_succ, Nat.mul_comm]
    exact h4.symm
  · intro a0 _
    rw [length_flatMap_const _ _ ((2 * r + 1) ^ 2)]
    · rw [layerRange_length]
      have h3 : (2 * r + 1) ^ 3 = (2 * r + 1) * (2 * r + 1) ^ 2 := by
        rw [Nat.pow_succ, Nat.mul_comm]
      exact h3.symm
    · intro a1 _
      rw [length_flatMap_const _ _ (2 * r + 1)]
      · rw [layerRange_length, Nat.pow_two]
      · intro a2 _
        rw [List.length_map, layerRange_length]

theorem box_iff_layers {r : Nat} {x : Cover4} :
    x ∈ boxSites r ↔ ∀ i : Axis, x.get i ∈ layerRange r := by
  rcases x with ⟨a0, a1, a2, a3⟩
  dsimp [boxSites]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨b0, hb0, b1, hb1, b2, hb2, b3, hb3, heq⟩
    cases heq
    intro i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => exact hb0
    | 1 => exact hb1
    | 2 => exact hb2
    | 3 => exact hb3
    | _ + 4 => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 4 _))
  · intro h
    refine ⟨a0, h 0, a1, h 1, a2, h 2, a3, h 3, rfl⟩

private theorem nodup_flatMap_inj {α β : Type} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a b, a ∈ l → b ∈ l → a ≠ b → ∀ y, y ∈ f a → y ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons, List.nodup_append]
    have hcons := List.nodup_cons.mp hl
    refine ⟨hf a (List.Mem.head _), ?_, ?_⟩
    · exact ih hcons.2 (fun b hb => hf b (List.Mem.tail _ hb))
        (fun x y hx hy hne z => hdisj x y (List.Mem.tail _ hx) (List.Mem.tail _ hy) hne z)
    · intro y hy1 z hy2 heq
      subst heq
      rw [List.mem_flatMap] at hy2
      rcases hy2 with ⟨b, hb, hyb⟩
      have hne : a ≠ b := fun heq => hcons.1 (heq ▸ hb)
      exact hdisj a b (List.Mem.head _) (List.Mem.tail _ hb) hne y hy1 hyb

theorem boxSites_nodup (r : Nat) : (boxSites r).Nodup := by
  have hr := layerRange_nodup r
  dsimp [boxSites]
  apply nodup_flatMap_inj _ _ hr
  · intro a0 _
    apply nodup_flatMap_inj _ _ hr
    · intro a1 _
      apply nodup_flatMap_inj _ _ hr
      · intro a2 _
        apply nodup_map_inj _ _ _ hr
        intro x y h
        cases h
        rfl
      · intro a2 b2 _ _ hne y hy1 hy2
        rw [List.mem_map] at hy1 hy2
        rcases hy1 with ⟨c1, _, rfl⟩
        rcases hy2 with ⟨c2, _, heq⟩
        cases heq
        exact hne rfl
    · intro a1 b1 _ _ hne y hy1 hy2
      simp only [List.mem_flatMap, List.mem_map] at hy1 hy2
      rcases hy1 with ⟨_, _, _, _, rfl⟩
      rcases hy2 with ⟨_, _, _, _, heq⟩
      cases heq
      exact hne rfl
  · intro a0 b0 _ _ hne y hy1 hy2
    simp only [List.mem_flatMap, List.mem_map] at hy1 hy2
    rcases hy1 with ⟨_, _, _, _, _, _, rfl⟩
    rcases hy2 with ⟨_, _, _, _, _, _, heq⟩
    cases heq
    exact hne rfl

theorem update_box_mem {x : Cover4} {r : Nat} (hx : x ∈ boxSites r)
    {v : Int} (hv : v ∈ layerRange r) (i : Axis) :
    x.update i v ∈ boxSites r := by
  rw [box_iff_layers] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Cover4.get_update_same]
    exact hv
  · rw [Cover4.get_update_ne _ hj]
    exact hx j

private def axisInList (l : List Axis) (i : Axis) : Bool :=
  l.any (fun a => decide (a.val = i.val))

private theorem axisInList_eq_true {l : List Axis} {i : Axis} :
    axisInList l i = true ↔ i ∈ l := by
  dsimp [axisInList]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, heq⟩
    have hv : a = i := Fin.ext (of_decide_eq_true heq)
    subst hv
    exact ha
  · intro hi
    exact ⟨i, hi, decide_eq_true rfl⟩

/-- Computable boolean predicate testing `∀ i ∉ l, y.get i = x.get i`. -/
def agreeOutside (l : List Axis) (x y : Cover4) : Bool :=
  (axisInList l 0 || decide (y.x0 = x.x0)) &&
  (axisInList l 1 || decide (y.x1 = x.x1)) &&
  (axisInList l 2 || decide (y.x2 = x.x2)) &&
  (axisInList l 3 || decide (y.x3 = x.x3))

theorem agreeOutside_iff {l : List Axis} {x y : Cover4} :
    agreeOutside l x y = true ↔ ∀ i : Axis, i ∉ l → y.get i = x.get i := by
  dsimp [agreeOutside]
  simp only [Bool.and_eq_true, Bool.or_eq_true, axisInList_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i hi
    rcases i with ⟨i, hi4⟩
    match i with
    | 0 => rcases h0 with h | h; exact absurd h hi; exact h
    | 1 => rcases h1 with h | h; exact absurd h hi; exact h
    | 2 => rcases h2 with h | h; exact absurd h hi; exact h
    | 3 => rcases h3 with h | h; exact absurd h hi; exact h
    | _ + 4 => exact absurd hi4 (Nat.not_lt_of_le (Nat.le_add_left 4 _))
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · cases hm : axisInList l 0
      · exact Or.inr (h 0 (fun hi => by simp [axisInList_eq_true.mpr hi] at hm))
      · exact Or.inl (axisInList_eq_true.mp hm)
    · cases hm : axisInList l 1
      · exact Or.inr (h 1 (fun hi => by simp [axisInList_eq_true.mpr hi] at hm))
      · exact Or.inl (axisInList_eq_true.mp hm)
    · cases hm : axisInList l 2
      · exact Or.inr (h 2 (fun hi => by simp [axisInList_eq_true.mpr hi] at hm))
      · exact Or.inl (axisInList_eq_true.mp hm)
    · cases hm : axisInList l 3
      · exact Or.inr (h 3 (fun hi => by simp [axisInList_eq_true.mpr hi] at hm))
      · exact Or.inl (axisInList_eq_true.mp hm)

/-- Pinned lattice slab: sites in `boxSites r` matching `x` outside `l`. -/
def slabSites (r : Nat) (x : Cover4) (l : List Axis) : List Cover4 :=
  (boxSites r).filter fun y => agreeOutside l x y

theorem slab_iff {x y : Cover4} {l : List Axis} {r : Nat} :
    y ∈ slabSites r x l ↔ y ∈ boxSites r ∧ ∀ i : Axis, i ∉ l → y.get i = x.get i := by
  dsimp [slabSites]
  rw [List.mem_filter, agreeOutside_iff]

theorem slabSites_nodup (r : Nat) (x : Cover4) (l : List Axis) :
    (slabSites r x l).Nodup :=
  nodup_filter_keep _ _ (boxSites_nodup r)

theorem lower_pin_mem {r : Nat} {o : Cover4} {l : List Axis} {i : Axis} {z : Int}
    (hi : i ∉ l) (x : Cover4) :
    x ∈ slabSites r (o.update i z) l ↔
      x ∈ slabSites r o (l ++ [i]) ∧ x.get i = z := by
  rw [slab_iff, slab_iff]
  simp only [List.mem_append, List.mem_singleton, not_or]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨⟨hx, fun j ⟨hj1, hj2⟩ => ?_⟩, ?_⟩
    · rw [h j hj1, Cover4.get_update_ne _ hj2]
    · rw [h i hi, Cover4.get_update_same]
  · rintro ⟨⟨hx, h⟩, he⟩
    refine ⟨hx, fun j hj => ?_⟩
    by_cases hij : j = i
    · subst hij
      rw [he, Cover4.get_update_same]
    · rw [h j ⟨hj, hij⟩, Cover4.get_update_ne _ hij]

theorem step_between_mem {r : Nat} {o : Cover4} {l : List Axis} {i : Axis}
    (hi : i ∉ l) (z w : Int) (hw : w ∈ layerRange r) {x : Cover4}
    (hx : x ∈ slabSites r (o.update i z) l) :
    Cover4.add x (Cover4.smul (w - z) (Cover4.step i)) ∈ slabSites r (o.update i w) l := by
  have hx' := (lower_pin_mem hi x).mp hx
  have hsub := Cover4.step_smul_eq_update (x := x) (i := i) w
  rw [hx'.2] at hsub
  rw [hsub]
  rw [lower_pin_mem hi]
  refine ⟨slab_iff.mpr ⟨update_box_mem (slab_iff.mp hx'.1).1 hw i, fun k hk => ?_⟩,
          Cover4.get_update_same _ _ _⟩
  have hne : k ≠ i := fun heq => hk (by simp [heq])
  rw [Cover4.get_update_ne _ hne]
  exact (slab_iff.mp hx'.1).2 k hk

theorem axis_orthogonal {l : List Axis} {o x y : Cover4} {j : Axis} {r : Nat} {w : Int}
    (hx : x ∈ slabSites r (o.update j w) l)
    (hy : y ∈ slabSites r (o.update j w) l)
    (hj : j ∉ l) {i : Axis} (he : y = Cover4.add x (Cover4.step i)) :
    i ≠ j := by
  have h1 := ((lower_pin_mem hj x).mp hx).2
  have h2 := ((lower_pin_mem hj y).mp hy).2
  intro hij
  subst hij
  rw [he, Cover4.get_add, Cover4.get_step] at h2
  simp [h1] at h2
  omega

/-- Constructive finite-list sum of an integer-valued observable. -/
def listSum {α : Type} (l : List α) (f : α → Int) : Int :=
  (l.map f).sum

theorem listSum_append {α : Type} (a b : List α) (f : α → Int) :
    listSum (a ++ b) f = listSum a f + listSum b f := by
  dsimp [listSum]
  rw [List.map_append, List.sum_append]

theorem listSum_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Int) :
    listSum (l.flatMap g) f = listSum l (fun a => listSum (g a) f) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    dsimp [listSum]
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    dsimp [listSum] at ih
    rw [ih]

private theorem listSum_erase [DecidableEq α] (a : α) (l : List α) (ha : a ∈ l) (f : α → Int) :
    listSum l f = f a + listSum (l.erase a) f := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    dsimp [listSum]
    by_cases hx : x = a
    · subst hx
      simp [List.erase_cons_head]
    · have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | hmem
        · exact absurd rfl hx
        · exact hmem
      have hne : (x == a) = false := beq_false_of_ne hx
      rw [List.erase_cons_tail (by simp [hne])]
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      have ih' := ih ha'
      dsimp [listSum] at ih'
      rw [ih']
      omega

private theorem mem_erase_of_ne [DecidableEq α] {a b : α} {l : List α}
    (hb : b ∈ l) (hne : b ≠ a) : b ∈ l.erase a := by
  induction l with
  | nil => cases hb
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst hxa
      rw [List.erase_cons_head]
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact absurd rfl hne
      · exact hmem
    · have hf : (x == a) = false := beq_false_of_ne hxa
      rw [List.erase_cons_tail (by simp [hf])]
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact List.Mem.head _
      · exact List.Mem.tail _ (ih hmem)

private theorem mem_of_mem_erase [DecidableEq α] {a b : α} {l : List α}
    (h : b ∈ l.erase a) : b ∈ l :=
  List.mem_of_mem_erase h

private theorem not_mem_erase_of_nodup [DecidableEq α] {a : α} {l : List α}
    (hl : l.Nodup) : a ∉ l.erase a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hc := List.nodup_cons.mp hl
    by_cases hxa : x = a
    · subst hxa
      rw [List.erase_cons_head]
      exact hc.1
    · have hf : (x == a) = false := beq_false_of_ne hxa
      rw [List.erase_cons_tail (by simp [hf])]
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact hxa rfl
      · exact ih hc.2 hrest

private theorem listSum_eq_of_nodup_equiv [DecidableEq α] (l1 l2 : List α)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (heqv : ∀ x, x ∈ l1 ↔ x ∈ l2) (f : α → Int) :
    listSum l1 f = listSum l2 f := by
  induction l1 generalizing l2 with
  | nil =>
    have hl2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons b bs => exact absurd ((heqv b).mpr (List.Mem.head _)) (by simp)
    subst hl2
    rfl
  | cons a rest ih =>
    have hc := List.nodup_cons.mp h1
    have ha2 : a ∈ l2 := (heqv a).mp (List.Mem.head _)
    have h2e : (l2.erase a).Nodup := List.Nodup.erase a h2
    have hsum2 := listSum_erase a l2 ha2 f
    have heqv' : ∀ x, x ∈ rest ↔ x ∈ l2.erase a := by
      intro x
      constructor
      · intro hx
        have hne : x ≠ a := fun h => hc.1 (h ▸ hx)
        exact mem_erase_of_ne ((heqv x).mp (List.Mem.tail _ hx)) hne
      · intro hx
        have hx2 := mem_of_mem_erase hx
        have hne : x ≠ a := fun h => (not_mem_erase_of_nodup h2) (h ▸ hx)
        rcases List.mem_cons.mp ((heqv x).mpr hx2) with rfl | hmem
        · exact absurd rfl hne
        · exact hmem
    have ih' := ih (l2.erase a) hc.2 h2e heqv'
    dsimp [listSum] at ih' ⊢
    rw [List.map_cons, List.sum_cons]
    dsimp [listSum] at hsum2
    rw [hsum2, ih']

/-- Constructive slab sum foliation theorem: summing any observable over
`slabSites r o (l ++ [i])` equals summing over coordinate layers `z ∈ layerRange r`
and pinned slices `slabSites r (o.update i z) l`. -/
theorem slab_sum_foliation (r : Nat) (o : Cover4) {i : Axis} {l : List Axis}
    (hi : i ∉ l) (f : Cover4 → Int) :
    listSum (slabSites r o (l ++ [i])) f =
      listSum (layerRange r) (fun z => listSum (slabSites r (o.update i z) l) f) := by
  rw [← listSum_flatMap]
  apply listSum_eq_of_nodup_equiv
  · exact slabSites_nodup r o (l ++ [i])
  · apply nodup_flatMap_inj _ _ (layerRange_nodup r)
    · intro z _
      exact slabSites_nodup r (o.update i z) l
    · intro z1 z2 _ _ hne x hx1 hx2
      have h1 := ((lower_pin_mem hi x).mp hx1).2
      have h2 := ((lower_pin_mem hi x).mp hx2).2
      exact hne (h1.symm.trans h2)
  · intro x
    rw [List.mem_flatMap]
    constructor
    · intro hx
      refine ⟨x.get i, ?_, ?_⟩
      · exact (box_iff_layers.mp (slab_iff.mp hx).1) i
      · exact (lower_pin_mem hi x).mpr ⟨hx, rfl⟩
    · rintro ⟨z, _, hxz⟩
      exact ((lower_pin_mem hi x).mp hxz).1

-- =============================================================================
-- Part 3: Constructive Gauge Connections, Holonomy & Face Trace Invariance
-- =============================================================================

/-- Constructive discrete group interface (no Mathlib, no `Classical.choice`). -/
structure LatticeGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_inv : ∀ a, mul a (inv a) = one
  inv_mul : ∀ a, mul (inv a) a = one

namespace LatticeGroup

theorem inv_unique {G : Type} (L : LatticeGroup G) {a b : G}
    (h : L.mul a b = L.one) : b = L.inv a := by
  calc b = L.mul L.one b := (L.one_mul b).symm
       _ = L.mul (L.mul (L.inv a) a) b := by rw [L.inv_mul]
       _ = L.mul (L.inv a) (L.mul a b) := L.mul_assoc _ _ _
       _ = L.mul (L.inv a) L.one := by rw [h]
       _ = L.inv a := L.mul_one _

theorem inv_inv {G : Type} (L : LatticeGroup G) (a : G) :
    L.inv (L.inv a) = a :=
  (inv_unique L (L.inv_mul a)).symm

theorem inv_one {G : Type} (L : LatticeGroup G) :
    L.inv L.one = L.one :=
  (inv_unique L (L.one_mul L.one)).symm

theorem mul_inv_rev {G : Type} (L : LatticeGroup G) (a b : G) :
    L.inv (L.mul a b) = L.mul (L.inv b) (L.inv a) := by
  apply (inv_unique L ?_).symm
  calc L.mul (L.mul a b) (L.mul (L.inv b) (L.inv a))
      = L.mul a (L.mul (L.mul b (L.inv b)) (L.inv a)) := by
          rw [L.mul_assoc a b _, ← L.mul_assoc b (L.inv b) (L.inv a)]
    _ = L.mul a (L.inv a) := by rw [L.mul_inv, L.one_mul]
    _ = L.one := L.mul_inv a

theorem inv_mul_cancel_mid {G : Type} (L : LatticeGroup G) (a g b : G) :
    L.mul (L.mul a (L.inv g)) (L.mul g b) = L.mul a b := by
  calc L.mul (L.mul a (L.inv g)) (L.mul g b)
      = L.mul a (L.mul (L.mul (L.inv g) g) b) := by
          rw [L.mul_assoc a (L.inv g) _, ← L.mul_assoc (L.inv g) g b]
    _ = L.mul a b := by rw [L.inv_mul, L.one_mul]

theorem mul_inv_cancel_mid {G : Type} (L : LatticeGroup G) (a g b : G) :
    L.mul (L.mul a g) (L.mul (L.inv g) b) = L.mul a b := by
  calc L.mul (L.mul a g) (L.mul (L.inv g) b)
      = L.mul a (L.mul (L.mul g (L.inv g)) b) := by
          rw [L.mul_assoc a g _, ← L.mul_assoc g (L.inv g) b]
    _ = L.mul a b := by rw [L.mul_inv, L.one_mul]

end LatticeGroup

/-- Non-abelian quaternion group `Q8 ⊂ SU(2)` as a constructive `LatticeGroup`. -/
def q8LatticeGroup : LatticeGroup YangMillsQ8.Q8 where
  mul := YangMillsQ8.Q8.mul
  one := YangMillsQ8.Q8.one
  inv := YangMillsQ8.Q8.inv
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_inv a := by cases a <;> rfl
  inv_mul a := by cases a <;> rfl

/-- Lattice link gauge connection assigning a group element to every edge `(x, μ)`. -/
abbrev GaugeConnection (G : Type) := Cover4 × Axis → G

/-- Gauge transformation assigning a group element to every lattice site. -/
abbrev GaugeTransform (G : Type) := Cover4 → G

/-- Symmetric torus lattice plaquette anchored at `site` along axes `dir1 < dir2`. -/
structure LatticePlaquette4 where
  site : Cover4
  dir1 : Axis
  dir2 : Axis
  h_lt : dir1.val < dir2.val

/-- Apply a local gauge transformation: `U'(x, μ) = g(x) · U(x, μ) · g(x + e_μ)⁻¹`. -/
def gaugeTransformConnection {G : Type} (L : LatticeGroup G)
    (g : GaugeTransform G) (U : GaugeConnection G) : GaugeConnection G :=
  fun (x, μ) => L.mul (L.mul (g x) (U (x, μ))) (L.inv (g (Cover4.add x (Cover4.step μ))))

/-- Oriented link readout along unit step `d` starting from site `x`. -/
def readStep {G : Type} (L : LatticeGroup G) (d : LatticeStep)
    (U : GaugeConnection G) (x : Cover4) : G :=
  if d.neg then L.inv (U (Cover4.sub x (Cover4.step d.dir), d.dir)) else U (x, d.dir)

/-- Ordered parallel transport along walk `w` starting at site `x`. -/
def walkTransport {G : Type} (L : LatticeGroup G) (U : GaugeConnection G)
    (x : Cover4) : Walk → G
  | [] => L.one
  | d :: w => L.mul (readStep L d U x) (walkTransport L U (Cover4.add x d.vec) w)

/-- Explicit 4-link plaquette holonomy `U(l1) · U(l2) · U(l3)⁻¹ · U(l4)⁻¹`. -/
def plaquetteHolonomy {G : Type} (L : LatticeGroup G)
    (U : GaugeConnection G) (p : LatticePlaquette4) : G :=
  let s0 := p.site
  let s1 := Cover4.add s0 (Cover4.step p.dir1)
  let s2 := Cover4.add s0 (Cover4.step p.dir2)
  L.mul (L.mul (L.mul (U (s0, p.dir1)) (U (s1, p.dir2))) (L.inv (U (s2, p.dir1))))
        (L.inv (U (s0, p.dir2)))

theorem walkTransport_append {G : Type} (L : LatticeGroup G) (U : GaugeConnection G)
    (x : Cover4) (a b : Walk) :
    walkTransport L U x (a ++ b) =
      L.mul (walkTransport L U x a) (walkTransport L U (walkStop x a) b) := by
  induction a generalizing x with
  | nil =>
    dsimp [walkTransport, walkStop]
    rw [L.one_mul]
  | cons d rest ih =>
    dsimp [walkTransport, walkStop]
    rw [ih (Cover4.add x d.vec), L.mul_assoc]

theorem readStep_rev {G : Type} (L : LatticeGroup G) (d : LatticeStep)
    (U : GaugeConnection G) (x : Cover4) :
    readStep L d.rev U (Cover4.add x d.vec) = L.inv (readStep L d U x) := by
  rcases d with ⟨i, b⟩
  cases b
  · dsimp [readStep, LatticeStep.rev, LatticeStep.vec]
    rw [Cover4.add_sub_step]
  · dsimp [readStep, LatticeStep.rev, LatticeStep.vec]
    rw [Cover4.add_neg_eq_sub, L.inv_inv]

private theorem walkStop_walkReverse (x : Cover4) (w : Walk) :
    walkStop (walkStop x w) (walkReverse w) = x := by
  induction w generalizing x with
  | nil => rfl
  | cons s l ihl =>
    dsimp [walkStop, walkReverse]
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, walkStop_append]
    dsimp [walkReverse] at ihl
    rw [ihl (Cover4.add x s.vec)]
    dsimp [walkStop]
    rw [LatticeStep.vec_rev, Cover4.add_neg_eq_sub]
    apply Cover4.ext; intro j; rw [Cover4.get_sub, Cover4.get_add]; omega

theorem walkTransport_reverse {G : Type} (L : LatticeGroup G) (U : GaugeConnection G)
    (x : Cover4) (w : Walk) :
    walkTransport L U (walkStop x w) (walkReverse w) =
      L.inv (walkTransport L U x w) := by
  induction w generalizing x with
  | nil =>
    dsimp [walkReverse, walkStop, walkTransport]
    exact L.inv_one.symm
  | cons d rest ih =>
    dsimp [walkStop, walkTransport, walkReverse]
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    change walkTransport L U (walkStop (Cover4.add x d.vec) rest)
        (walkReverse rest ++ [d.rev]) =
      L.inv (L.mul (readStep L d U x) (walkTransport L U (Cover4.add x d.vec) rest))
    rw [walkTransport_append, ih (Cover4.add x d.vec), walkStop_walkReverse]
    dsimp [walkTransport, walkStop]
    rw [readStep_rev, L.mul_one, L.mul_inv_rev]

theorem carry_succ_transport {G : Type} (L : LatticeGroup G) (U : GaugeConnection G)
    (x : Cover4) (j : Axis) (d : Int) :
    walkTransport L U x (straightWalk j (d + 1)) =
      L.mul (walkTransport L U x (straightWalk j d))
            (U (Cover4.add x (Cover4.smul d (Cover4.step j)), j)) := by
  by_cases hneg : d < 0
  · have hh : straightWalk j d = straightWalk j (d + 1) ++ [negDir j] := by
      dsimp [straightWalk]
      by_cases hd1 : d + 1 = 0
      · have hd : d = -1 := by omega
        subst hd
        rfl
      · have hneg1 : d + 1 < 0 := by omega
        have hna : d.natAbs = (d + 1).natAbs + 1 := by omega
        simp [hneg, hneg1, hna, negDir, List.replicate_succ']
    rw [hh, walkTransport_append, straightWalk_stop]
    dsimp [walkTransport, readStep, negDir]
    rw [L.mul_one, Cover4.smul_add1_sub_step, L.mul_assoc, L.inv_mul, L.mul_one]
  · have hh : straightWalk j (d + 1) = straightWalk j d ++ [posDir j] := by
      dsimp [straightWalk]
      have hpos : ¬(d + 1 < 0) := by omega
      have hna : (d + 1).natAbs = d.natAbs + 1 := by omega
      simp [hneg, hpos, hna, posDir, List.replicate_succ']
    rw [hh, walkTransport_append, straightWalk_stop]
    dsimp [walkTransport, readStep, posDir]
    rw [L.mul_one]

theorem readStep_gauge {G : Type} (L : LatticeGroup G) (d : LatticeStep)
    (g : GaugeTransform G) (U : GaugeConnection G) (x : Cover4) :
    readStep L d (gaugeTransformConnection L g U) x =
      L.mul (L.mul (g x) (readStep L d U x)) (L.inv (g (Cover4.add x d.vec))) := by
  rcases d with ⟨μ, b⟩
  cases b
  · dsimp [readStep, gaugeTransformConnection, LatticeStep.vec]
  · dsimp [readStep, gaugeTransformConnection, LatticeStep.vec]
    rw [Cover4.add_neg_eq_sub, Cover4.sub_add_step]
    rw [L.mul_inv_rev, L.mul_inv_rev, L.inv_inv, L.mul_assoc]

theorem walkTransport_gauge {G : Type} (L : LatticeGroup G)
    (g : GaugeTransform G) (U : GaugeConnection G) (x : Cover4) (w : Walk) :
    walkTransport L (gaugeTransformConnection L g U) x w =
      L.mul (L.mul (g x) (walkTransport L U x w)) (L.inv (g (walkStop x w))) := by
  induction w generalizing x with
  | nil =>
    dsimp [walkTransport, walkStop]
    rw [L.mul_one, L.mul_inv]
  | cons d rest ih =>
    dsimp [walkTransport, walkStop]
    rw [readStep_gauge, ih (Cover4.add x d.vec)]
    have hmid := L.inv_mul_cancel_mid
      (L.mul (g x) (readStep L d U x))
      (g (Cover4.add x d.vec))
      (walkTransport L U (Cover4.add x d.vec) rest)
    calc L.mul (L.mul (L.mul (g x) (readStep L d U x)) (L.inv (g (Cover4.add x d.vec))))
            (L.mul (L.mul (g (Cover4.add x d.vec)) (walkTransport L U (Cover4.add x d.vec) rest))
              (L.inv (g (walkStop (Cover4.add x d.vec) rest))))
        = L.mul (L.mul (L.mul (L.mul (g x) (readStep L d U x)) (L.inv (g (Cover4.add x d.vec))))
              (L.mul (g (Cover4.add x d.vec)) (walkTransport L U (Cover4.add x d.vec) rest)))
            (L.inv (g (walkStop (Cover4.add x d.vec) rest))) := (L.mul_assoc _ _ _).symm
      _ = L.mul (L.mul (L.mul (g x) (readStep L d U x))
              (walkTransport L U (Cover4.add x d.vec) rest))
            (L.inv (g (walkStop (Cover4.add x d.vec) rest))) := by rw [hmid]
      _ = L.mul (L.mul (g x) (L.mul (readStep L d U x)
              (walkTransport L U (Cover4.add x d.vec) rest)))
            (L.inv (g (walkStop (Cover4.add x d.vec) rest))) := by rw [L.mul_assoc (g x)]

theorem plaquetteHolonomy_eq_walkTransport {G : Type} (L : LatticeGroup G)
    (U : GaugeConnection G) (p : LatticePlaquette4) :
    plaquetteHolonomy L U p = walkTransport L U p.site (squareWalk p.dir1 p.dir2) := by
  dsimp [plaquetteHolonomy, squareWalk, walkTransport, readStep, posDir, negDir, LatticeStep.vec]
  have h1 : Cover4.sub (Cover4.add (Cover4.add p.site (Cover4.step p.dir1)) (Cover4.step p.dir2))
      (Cover4.step p.dir1) = Cover4.add p.site (Cover4.step p.dir2) := by
    apply Cover4.ext; intro j; simp only [Cover4.get_sub, Cover4.get_add]; omega
  have h2 : Cover4.sub (Cover4.add (Cover4.add (Cover4.add p.site (Cover4.step p.dir1))
      (Cover4.step p.dir2)) (Cover4.neg (Cover4.step p.dir1))) (Cover4.step p.dir2) = p.site := by
    apply Cover4.ext; intro j
    simp only [Cover4.get_sub, Cover4.get_add, Cover4.get_neg]; omega
  rw [h1, h2, L.mul_one, ← L.mul_assoc, ← L.mul_assoc]

/-- Plaquette holonomy covariance under local gauge transformation `g`:
`U'_p = g(p.site) · U_p · g(p.site)⁻¹` (direct zero-axiom port of
`LGT.GaugeField.Connection.holonomy_gauge_covariant`). -/
theorem holonomy_gauge_covariant {G : Type} (L : LatticeGroup G)
    (g : GaugeTransform G) (U : GaugeConnection G) (p : LatticePlaquette4) :
    plaquetteHolonomy L (gaugeTransformConnection L g U) p =
      L.mul (L.mul (g p.site) (plaquetteHolonomy L U p)) (L.inv (g p.site)) := by
  rw [plaquetteHolonomy_eq_walkTransport, plaquetteHolonomy_eq_walkTransport, walkTransport_gauge]
  have hs : walkStop p.site (squareWalk p.dir1 p.dir2) = p.site := by
    dsimp [squareWalk, walkStop, posDir, negDir, LatticeStep.vec]
    apply Cover4.ext; intro j
    rw [Cover4.get_add, Cover4.get_add, Cover4.get_add, Cover4.get_add,
        Cover4.get_neg, Cover4.get_neg]
    omega
  rw [hs]

/-- Unordered axis pair with `a < b`. -/
abbrev PlaqAxes := { x : Axis × Axis // x.1.val < x.2.val }

/-- Oriented lattice face `(base, axes)`. -/
abbrev Face := Cover4 × PlaqAxes

namespace PlaqAxes

/-- Canonical ordered axis pair from distinct `a ≠ b`. -/
def ordered (a b : Axis) (h : a ≠ b) : PlaqAxes :=
  if hlt : a.val < b.val then ⟨(a, b), hlt⟩
  else ⟨(b, a), by
    have hne : a.val ≠ b.val := fun eq => h (Fin.ext eq)
    have ha := a.isLt
    have hb := b.isLt
    dsimp only
    omega⟩

/-- Rotate an axis pair under signed symmetry `s`. -/
def rotate (s : SignedSym4) (q : PlaqAxes) : PlaqAxes :=
  ordered (s.perm.toFun q.val.1) (s.perm.toFun q.val.2)
    (s.perm.ne (fun heq => by
      have hq := q.property
      have h0 : q.val.1.val = q.val.2.val := congrArg Fin.val heq
      omega))

theorem rotate_inv (s : SignedSym4) (q : PlaqAxes) :
    rotate s.inv (rotate s q) = q := by
  rcases q with ⟨⟨a, b⟩, hq⟩
  have ha : a.val < 4 := a.isLt
  have hb : b.val < 4 := b.isLt
  change a.val < b.val at hq
  dsimp [rotate, ordered, SignedSym4.inv, Perm4.inv]
  by_cases h : (s.perm.toFun a).val < (s.perm.toFun b).val
  · simp [h, s.perm.left_inv, hq]
  · have hswap : (s.perm.toFun b).val < (s.perm.toFun a).val := by
      have hne : s.perm.toFun a ≠ s.perm.toFun b :=
        s.perm.ne (fun eq => by cases eq; exact Nat.lt_irrefl _ hq)
      have hvn : (s.perm.toFun a).val ≠ (s.perm.toFun b).val := fun eq => hne (Fin.ext eq)
      have hsa := (s.perm.toFun a).isLt
      have hsb := (s.perm.toFun b).isLt
      omega
    have hq_not : ¬(b.val < a.val) := by omega
    simp [h, s.perm.left_inv, hq_not]

end PlaqAxes

/-- Ordered boundary walk `[a, b, a.rev, b.rev]` for an oriented square. -/
def orientedWalk (a b : LatticeStep) : Walk :=
  [a, b, a.rev, b.rev]

theorem stop_oriented (a b : LatticeStep) (x : Cover4) :
    walkStop x (orientedWalk a b) = x := by
  dsimp [orientedWalk, walkStop]
  apply Cover4.ext
  intro j
  rw [Cover4.get_add, Cover4.get_add, Cover4.get_add, Cover4.get_add,
      LatticeStep.vec_rev, LatticeStep.vec_rev, Cover4.get_neg, Cover4.get_neg]
  omega

theorem oriented_swap_transport {G : Type} (L : LatticeGroup G) (a b : LatticeStep)
    (x : Cover4) (U : GaugeConnection G) :
    walkTransport L U x (orientedWalk b a) =
      L.inv (walkTransport L U x (orientedWalk a b)) := by
  have hrev : walkReverse (orientedWalk a b) = orientedWalk b a := by
    dsimp [walkReverse, orientedWalk]
    simp [LatticeStep.rev_rev]
  have h := walkTransport_reverse L U x (orientedWalk a b)
  rwa [stop_oriented, hrev] at h

theorem oriented_next_transport {G : Type} (L : LatticeGroup G) (a b : LatticeStep)
    (x : Cover4) (U : GaugeConnection G) :
    walkTransport L U (Cover4.add x a.vec) (orientedWalk b a.rev) =
      L.mul (L.mul (L.inv (readStep L a U x)) (walkTransport L U x (orientedWalk a b)))
            (readStep L a U x) := by
  have heq : orientedWalk b a.rev = [b, a.rev, b.rev] ++ [a] := by
    dsimp [orientedWalk]
    rw [LatticeStep.rev_rev]
  have hstop : walkStop (Cover4.add x a.vec) [b, a.rev, b.rev] = x := by
    dsimp [walkStop]
    apply Cover4.ext; intro j
    rw [Cover4.get_add, Cover4.get_add, Cover4.get_add, Cover4.get_add,
        LatticeStep.vec_rev, LatticeStep.vec_rev, Cover4.get_neg, Cover4.get_neg]
    omega
  rw [heq, walkTransport_append, hstop]
  dsimp [walkTransport, orientedWalk]
  rw [L.mul_one, L.mul_one]
  rw [← L.mul_assoc (L.inv (readStep L a U x)) (readStep L a U x)]
  rw [L.inv_mul, L.one_mul, L.mul_assoc, L.mul_assoc]

/-- Transport value around face `p`. -/
def faceValue {G : Type} (L : LatticeGroup G) (U : GaugeConnection G) (p : Face) : G :=
  walkTransport L U p.1 (squareWalk p.2.val.1 p.2.val.2)

theorem face_gauge_covariant {G : Type} (L : LatticeGroup G) (g : GaugeTransform G)
    (U : GaugeConnection G) (p : Face) :
    faceValue L (gaugeTransformConnection L g U) p =
      L.mul (L.mul (g p.1) (faceValue L U p)) (L.inv (g p.1)) := by
  dsimp [faceValue]
  have hstop : walkStop p.1 (squareWalk p.2.val.1 p.2.val.2) = p.1 :=
    stop_oriented (posDir p.2.val.1) (posDir p.2.val.2) p.1
  rw [walkTransport_gauge, hstop]

/-- Pull-back of gauge connection `U` under affine signed symmetry `(s, t)`. -/
def pullConnection {G : Type} (L : LatticeGroup G) (s : SignedSym4) (t : Cover4)
    (U : GaugeConnection G) : GaugeConnection G :=
  fun (x, i) => readStep L ((posDir i).rotate s) U (s.affine t x)

theorem readStep_pull {G : Type} (L : LatticeGroup G) (s : SignedSym4) (t : Cover4)
    (U : GaugeConnection G) (d : LatticeStep) (x : Cover4) :
    readStep L d (pullConnection L s t U) x =
      readStep L (d.rotate s) U (s.affine t x) := by
  rcases d with ⟨i, b⟩
  cases b
  · dsimp [readStep, pullConnection]
    rfl
  · dsimp [readStep, pullConnection]
    have hs : s.affine t (Cover4.sub x (Cover4.step i)) =
        Cover4.sub (s.affine t x) (s.act (Cover4.step i)) := by
      apply Cover4.ext; intro j
      dsimp [SignedSym4.affine, SignedSym4.act]
      rw [Cover4.get_add, Cover4.get_ofFn, Cover4.get_sub, Cover4.get_sub,
          Cover4.get_add, Cover4.get_ofFn, Cover4.get_ofFn]
      cases s.flip (s.perm.invFun j) <;> simp <;> omega
    rw [hs]
    have hv : ((posDir i).rotate s).vec = s.act (Cover4.step i) :=
      LatticeStep.vec_rotate (posDir i) s
    rw [← hv]
    have hrot : (negDir i).rotate s = ((posDir i).rotate s).rev := by
      rw [← LatticeStep.rev_pos i, LatticeStep.rev_rotate]
    change L.inv (readStep L ((posDir i).rotate s) U
      (Cover4.sub (s.affine t x) ((posDir i).rotate s).vec)) =
      readStep L ((negDir i).rotate s) U (s.affine t x)
    rw [hrot]
    have hstep := readStep_rev L ((posDir i).rotate s) U
      (Cover4.sub (s.affine t x) ((posDir i).rotate s).vec)
    have hsubadd : Cover4.add (Cover4.sub (s.affine t x) ((posDir i).rotate s).vec)
        ((posDir i).rotate s).vec = s.affine t x := by
      apply Cover4.ext; intro j
      rw [Cover4.get_add, Cover4.get_sub]
      omega
    rw [hsubadd] at hstep
    exact hstep.symm

theorem walkTransport_pull {G : Type} (L : LatticeGroup G) (s : SignedSym4) (t : Cover4)
    (U : GaugeConnection G) (x : Cover4) (w : Walk) :
    walkTransport L (pullConnection L s t U) x w =
      walkTransport L U (s.affine t x) (w.map (fun d => d.rotate s)) := by
  induction w generalizing x with
  | nil => rfl
  | cons d rest ih =>
    rw [List.map_cons, walkTransport, walkTransport, readStep_pull, ih]
    rw [SignedSym4.affine_add, LatticeStep.vec_rotate]

section ClassFn

variable {G M : Type} (L : LatticeGroup G) (price : G → M) (U : GaugeConnection G)
  (hπ : ∀ u : G, price (L.inv u) = price u)
  (hconj : ∀ u g : G, price (L.mul (L.mul g u) (L.inv g)) = price u)

include hπ hconj in
theorem classFn_price_flip (a b : LatticeStep) (x : Cover4) :
    price (walkTransport L U x (orientedWalk a b)) =
      price (walkTransport L U (Cover4.add x a.vec) (orientedWalk a.rev b)) := by
  rw [oriented_swap_transport L b a.rev, hπ, oriented_next_transport]
  have hc := hconj (walkTransport L U x (orientedWalk a b)) (L.inv (readStep L a U x))
  rw [L.inv_inv] at hc
  exact hc.symm

/-- Canonical corner base aligned to positive axis orientations. -/
def atFace (x : Cover4) (a b : LatticeStep) : Cover4 :=
  Cover4.add (Cover4.add x (if a.neg then a.vec else Cover4.zero))
             (if b.neg then b.vec else Cover4.zero)

include hπ hconj in
theorem classFn_price_shift_pos (a b : LatticeStep) (x : Cover4) :
    price (walkTransport L U x (orientedWalk a b)) =
      price (walkTransport L U (atFace x a b) (squareWalk a.dir b.dir)) := by
  have second (i : Axis) (v : LatticeStep) (y : Cover4) :
      price (walkTransport L U y (orientedWalk (posDir i) v)) =
        price (walkTransport L U (atFace y (posDir i) v) (squareWalk i v.dir)) := by
    rcases v with ⟨j, bv⟩
    cases bv
    · dsimp [atFace, posDir, orientedWalk, squareWalk]
      rw [Cover4.add_zero, Cover4.add_zero]
      rfl
    · change price (walkTransport L U y (orientedWalk (posDir i) (negDir j))) =
        price (walkTransport L U (atFace y (posDir i) (negDir j)) (squareWalk i j))
      rw [oriented_swap_transport, hπ]
      rw [classFn_price_flip L price U hπ hconj (negDir j) (posDir i) y]
      rw [oriented_swap_transport, hπ]
      dsimp [atFace, posDir, negDir]
      rw [Cover4.add_zero]
      rfl
  rcases a with ⟨i, ba⟩
  cases ba
  · exact second i b x
  · change price (walkTransport L U x (orientedWalk (negDir i) b)) =
      price (walkTransport L U (atFace x (negDir i) b) (squareWalk i b.dir))
    rw [classFn_price_flip L price U hπ hconj, LatticeStep.rev_neg]
    have hbase : atFace (Cover4.add x (negDir i).vec) (posDir i) b = atFace x (negDir i) b := by
      dsimp [atFace, posDir, negDir]
      rw [Cover4.add_zero]
    rw [← hbase]
    exact second i b (Cover4.add x (negDir i).vec)

/-- Shifted lower-left corner for transformed face under `(s, t)`. -/
def Face.lower (p : Face) (s : SignedSym4) (t : Cover4) : Cover4 :=
  atFace (s.affine t p.1) ((posDir p.2.val.1).rotate s) ((posDir p.2.val.2).rotate s)

/-- Induced hyperoctahedral action on oriented faces. -/
def Face.send (s : SignedSym4) (t : Cover4) (p : Face) : Face :=
  (Face.lower p s t, PlaqAxes.rotate s p.2)

theorem Face.injective_send (s : SignedSym4) (t : Cover4) :
    ∀ p1 p2 : Face, Face.send s t p1 = Face.send s t p2 → p1 = p2 := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  have hj : PlaqAxes.rotate s i = PlaqAxes.rotate s j := congrArg Prod.snd h
  have hij : i = j := by
    have := congrArg (PlaqAxes.rotate s.inv) hj
    rwa [PlaqAxes.rotate_inv, PlaqAxes.rotate_inv] at this
  subst hij
  have h1 : Face.lower (a, i) s t = Face.lower (b, i) s t := congrArg Prod.fst h
  dsimp [Face.lower, atFace] at h1
  have hab : s.affine t a = s.affine t b := by
    apply Cover4.ext; intro u
    have hu := congrArg (fun p => p.get u) h1
    rw [Cover4.get_add, Cover4.get_add, Cover4.get_add, Cover4.get_add] at hu
    omega
  exact congrArg (·, i) (s.affine_injective t hab)

include hπ hconj in
theorem classFn_send_price (p : Face) (s : SignedSym4) (t : Cover4) :
    price (faceValue L (pullConnection L s t U) p) =
      price (faceValue L U (Face.send s t p)) := by
  let a := p.2.val.1
  let b := p.2.val.2
  dsimp [faceValue]
  rw [walkTransport_pull]
  have hmap : List.map (fun d => d.rotate s) (squareWalk a b) =
      orientedWalk ((posDir a).rotate s) ((posDir b).rotate s) := by
    dsimp [squareWalk, orientedWalk]
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil]
    rw [← LatticeStep.rev_pos a, ← LatticeStep.rev_pos b]
    rw [LatticeStep.rev_rotate, LatticeStep.rev_rotate]
  rw [hmap, classFn_price_shift_pos L price U hπ hconj]
  dsimp [Face.send, Face.lower, PlaqAxes.rotate, PlaqAxes.ordered, LatticeStep.rotate]
  split
  · rfl
  · change price (walkTransport L U _ (orientedWalk (posDir (s.perm.toFun a))
        (posDir (s.perm.toFun b)))) =
      price (walkTransport L U _ (orientedWalk (posDir (s.perm.toFun b))
        (posDir (s.perm.toFun a))))
    rw [oriented_swap_transport, hπ]

end ClassFn

-- =============================================================================
-- Part 4: Concrete Non-Abelian Q_8 Instantiation & Headline Theorems
-- =============================================================================

theorem q8_reTrace_inv (u : YangMillsQ8.Q8) :
    YangMillsQ8.Q8.reTrace (q8LatticeGroup.inv u) = YangMillsQ8.Q8.reTrace u := by
  cases u <;> rfl

/-- Non-abelian `Q_8 ⊂ SU(2)` gauge invariance of plaquette holonomy trace under
arbitrary local gauge transforms `g : GaugeTransform Q8`. -/
theorem q8_plaquette_holonomy_gauge_invariant
    (g : GaugeTransform YangMillsQ8.Q8) (U : GaugeConnection YangMillsQ8.Q8)
    (p : LatticePlaquette4) :
    YangMillsQ8.Q8.reTrace
        (plaquetteHolonomy q8LatticeGroup
          (gaugeTransformConnection q8LatticeGroup g U) p) =
      YangMillsQ8.Q8.reTrace (plaquetteHolonomy q8LatticeGroup U p) := by
  rw [holonomy_gauge_covariant]
  exact YangMillsQ8.q8_trace_conjugation_invariant (g p.site) _

/-- Non-abelian `Q_8 ⊂ SU(2)` signed-hyperoctahedral invariance of oriented face
Wilson trace observables (`Face.send`). -/
theorem q8_send_price_trace_invariant
    (U : GaugeConnection YangMillsQ8.Q8) (p : Face) (s : SignedSym4) (t : Cover4) :
    YangMillsQ8.Q8.reTrace
        (faceValue q8LatticeGroup (pullConnection q8LatticeGroup s t U) p) =
      YangMillsQ8.Q8.reTrace (faceValue q8LatticeGroup U (Face.send s t p)) :=
  classFn_send_price q8LatticeGroup YangMillsQ8.Q8.reTrace U
    q8_reTrace_inv
    (fun u g => YangMillsQ8.q8_trace_conjugation_invariant g u)
    p s t

end ConstructiveOpenaiBridge

-- end of file: leanasm/src/LeanAsm/ConstructiveOpenaiBridge.lean