-- Path: leanasm/src/LeanAsm/Genus2Jacobian.lean
-- Cantor's Mumford divisor group law on J(C)(F_5) for C : y^2 = x^5 - x + 1.
-- Constructively proves 71 * [P_0 - ∞] = 0, primitivity, and the 71x71 group law (ZERO axioms).
-- Max Column: 100 Columns

namespace Genus2Jacobian

/-! ## Part 1: Multiplicative Inverse & Algebraic Lemmas in F_5 -/

/-- Multiplicative inverse in `Fin 5` (returning `0` on `0`). -/
def invF5 (a : Fin 5) : Fin 5 :=
  match a.val with
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | _ => 0

theorem invF5_mul : ∀ a : Fin 5, a ≠ 0 → a * invF5 a = 1 := by decide
theorem mul_invF5 : ∀ a : Fin 5, a ≠ 0 → invF5 a * a = 1 := by decide

@[simp] theorem f5_zero_mul : ∀ a : Fin 5, 0 * a = 0 := by decide
@[simp] theorem f5_mul_zero : ∀ a : Fin 5, a * 0 = 0 := by decide
@[simp] theorem f5_one_mul : ∀ a : Fin 5, 1 * a = a := by decide
@[simp] theorem f5_mul_one : ∀ a : Fin 5, a * 1 = a := by decide
@[simp] theorem f5_zero_add : ∀ a : Fin 5, 0 + a = a := by decide
@[simp] theorem f5_add_zero : ∀ a : Fin 5, a + 0 = a := by decide
@[simp] theorem f5_neg_zero : -(0 : Fin 5) = 0 := by decide
@[simp] theorem f5_sub_self : ∀ a : Fin 5, a - a = 0 := by decide
@[simp] theorem f5_sub_zero : ∀ a : Fin 5, a - 0 = a := by decide
@[simp] theorem f5_add_neg_cancel : ∀ a : Fin 5, a + -a = 0 := by decide

theorem f5_add_comm : ∀ a b : Fin 5, a + b = b + a := by decide
theorem f5_add_assoc : ∀ a b c : Fin 5, (a + b) + c = a + (b + c) := by decide
theorem f5_mul_comm : ∀ a b : Fin 5, a * b = b * a := by decide
theorem f5_mul_assoc : ∀ a b c : Fin 5, (a * b) * c = a * (b * c) := by decide
theorem f5_mul_add : ∀ a b c : Fin 5, a * (b + c) = a * b + a * c := by decide
theorem f5_add_mul : ∀ a b c : Fin 5, (a + b) * c = a * c + b * c := by decide
theorem f5_sub_eq_add_neg : ∀ a b : Fin 5, a - b = a + -b := by decide

/-- Axiom-free boolean equality on `Fin 5` via `Nat.beq`. -/
@[inline] def eqF5 (a b : Fin 5) : Bool := a.val == b.val

theorem eqF5_iff {a b : Fin 5} : eqF5 a b = true ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (Nat.eq_of_beq_eq_true h)
  · intro h
    subst h
    exact Nat.beq_refl a.val

/-! ## Part 2: Trimmed Polynomials over F_5 -/

/-- Polynomials over `F_5` in little-endian coefficient order `[a_0, a_1, ..., a_d]`. -/
abbrev PolyF5 := List (Fin 5)

/-- Axiom-free boolean equality on `PolyF5`. -/
def polyEqB : PolyF5 → PolyF5 → Bool
  | [], [] => true
  | a :: p, b :: q => eqF5 a b && polyEqB p q
  | _, _ => false

theorem polyEqB_iff : ∀ (p q : PolyF5), polyEqB p q = true ↔ p = q := by
  intro p
  induction p with
  | nil =>
    intro q
    cases q with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons _ _ => constructor <;> intro h <;> cases h
  | cons a p ih =>
    intro q
    cases q with
    | nil => constructor <;> intro h <;> cases h
    | cons b q =>
      simp only [polyEqB, Bool.and_eq_true]
      constructor
      · intro ⟨hab, hpq⟩
        rw [eqF5_iff.mp hab, (ih q).mp hpq]
      · intro h
        injection h with ha hp
        exact ⟨eqF5_iff.mpr ha, (ih q).mpr hp⟩

/-- Canonicalize a polynomial over `F_5` by stripping trailing zeros. -/
def trim : List (Fin 5) → PolyF5
  | [] => []
  | a :: p =>
    match trim p with
    | [] => if a.val == 0 then [] else [a]
    | b :: p' => a :: b :: p'

/-- Computable predicate checking that a coefficient list has no trailing zero. -/
def isTrimmedB : List (Fin 5) → Bool
  | [] => true
  | [a] => !(a.val == 0)
  | _ :: b :: p => isTrimmedB (b :: p)

/-- Coefficient at degree `i`. -/
def coeff : List (Fin 5) → Nat → Fin 5
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, i + 1 => coeff p i

/-- Leading coefficient (`0` for the zero polynomial `[]`). -/
def leadCoeff (p : List (Fin 5)) : Fin 5 :=
  p.getLastD 0

/-- Monicity predicate on trimmed polynomials. -/
def isMonic (p : PolyF5) : Bool :=
  !p.isEmpty && (leadCoeff p).val == 1

theorem isEmpty_true : ∀ {α : Type} {xs : List α}, xs.isEmpty = true → xs = []
  | _, [], _ => rfl
  | _, _ :: _, h => by cases h

theorem isEmpty_false : ∀ {α : Type} {xs : List α}, xs.isEmpty = false → xs ≠ []
  | _, [], h => by cases h
  | _, _ :: _, _ => by simp

theorem isEmpty_of_ne_nil : ∀ {α : Type} {xs : List α}, xs ≠ [] → xs.isEmpty = false
  | _, [], h => False.elim (h rfl)
  | _, _ :: _, _ => rfl

theorem list_length_pos_of_ne_nil : ∀ {α : Type} {xs : List α}, xs ≠ [] → 0 < xs.length
  | _, [], h => False.elim (h rfl)
  | _, _ :: _, _ => Nat.zero_lt_succ _

theorem f5_eq_zero_iff_val {a : Fin 5} : (a.val == 0) = true ↔ a = 0 :=
  ⟨fun h => Fin.ext (Nat.eq_of_beq_eq_true h), fun h => by subst h; exact Nat.beq_refl 0⟩

theorem f5_val_eq_zero_of_beq {a : Fin 5} (h : (a.val == 0) = true) : a = 0 :=
  eqF5_iff.mp h

theorem f5_ne_zero_of_beq_false {a : Fin 5} (h : (a.val == 0) = false) : a ≠ 0 := by
  intro ha
  subst ha
  cases h

theorem isTrimmedB_tail {a : Fin 5} {p : List (Fin 5)}
    (h : isTrimmedB (a :: p) = true) : isTrimmedB p = true := by
  cases p with
  | nil => rfl
  | cons _ _ => exact h

theorem isTrimmedB_trim (p : List (Fin 5)) : isTrimmedB (trim p) = true := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [trim]
    cases htp : trim p with
    | nil =>
      cases h0 : (a.val == 0)
      · simp [isTrimmedB, h0]
      · rfl
    | cons b p' =>
      rw [htp] at ih
      exact ih

theorem trim_of_isTrimmedB {p : List (Fin 5)} (h : isTrimmedB p = true) : trim p = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil =>
      simp only [isTrimmedB, Bool.not_eq_true'] at h
      simp [trim, h]
    | cons b p' =>
      have ht : trim (b :: p') = b :: p' := ih h
      change (match trim (b :: p') with | [] => _ | c :: q => a :: c :: q) = a :: b :: p'
      rw [ht]

theorem trim_idempotent (p : List (Fin 5)) : trim (trim p) = trim p :=
  trim_of_isTrimmedB (isTrimmedB_trim p)

theorem leadCoeff_eq_coeff : ∀ (p : List (Fin 5)), p ≠ [] → leadCoeff p = coeff p (p.length - 1)
  | [], h => False.elim (h rfl)
  | [_], _ => rfl
  | _ :: b :: p, _ => by
    change leadCoeff (b :: p) = coeff (b :: p) p.length
    exact leadCoeff_eq_coeff (b :: p) (by simp)

theorem leadCoeff_ne_zero_of_isTrimmedB :
    ∀ (p : List (Fin 5)), isTrimmedB p = true → p ≠ [] → leadCoeff p ≠ 0
  | [], _, hne => False.elim (hne rfl)
  | [_], ht, _ => by
    simp only [isTrimmedB, Bool.not_eq_true'] at ht
    exact f5_ne_zero_of_beq_false ht
  | _ :: b :: p, ht, _ => leadCoeff_ne_zero_of_isTrimmedB (b :: p) ht (by simp)

theorem lastCoeff_ne_zero_of_isTrimmedB {p : List (Fin 5)}
    (ht : isTrimmedB p = true) (hne : p ≠ []) : coeff p (p.length - 1) ≠ 0 := by
  rw [← leadCoeff_eq_coeff p hne]
  exact leadCoeff_ne_zero_of_isTrimmedB p ht hne

theorem coeff_ge_len_zero : ∀ (p : List (Fin 5)) (i : Nat), p.length ≤ i → coeff p i = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: p, i + 1, h => coeff_ge_len_zero p i (Nat.le_of_succ_le_succ h)

theorem len_le_of_isTrimmedB_coeff_zero {p : List (Fin 5)}
    (ht : isTrimmedB p = true) {k : Nat} (hz : ∀ i, k ≤ i → coeff p i = 0) : p.length ≤ k := by
  cases Nat.lt_or_ge k p.length with
  | inr hge => exact hge
  | inl hlt =>
    have hne : p ≠ [] := by
      intro hp
      rw [hp] at hlt
      simp at hlt
    have hk : k ≤ p.length - 1 := Nat.le_pred_of_lt hlt
    exact False.elim (lastCoeff_ne_zero_of_isTrimmedB ht hne (hz (p.length - 1) hk))

theorem coeff_trim (p : List (Fin 5)) (i : Nat) : coeff (trim p) i = coeff p i := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
    simp only [trim]
    cases htp : trim p with
    | nil =>
      cases h0 : (a.val == 0)
      · cases i with
        | zero => simp [coeff]
        | succ j =>
          have hcz : coeff p j = 0 := by
            rw [← ih j, htp]
            rfl
          simp [coeff, hcz]
      · have ha : a = 0 := f5_val_eq_zero_of_beq h0
        cases i with
        | zero => simp [coeff, ha]
        | succ j =>
          have hcz : coeff p j = 0 := by
            rw [← ih j, htp]
            rfl
          simp [coeff, hcz]
    | cons b p' =>
      cases i with
      | zero => rfl
      | succ j =>
        change coeff (b :: p') j = coeff p j
        rw [← htp]
        exact ih j

theorem eq_of_isTrimmedB_coeff :
    ∀ (p q : List (Fin 5)), isTrimmedB p = true → isTrimmedB q = true →
      (∀ i, coeff p i = coeff q i) → p = q
  | [], [], _, _, _ => rfl
  | [], b :: q', _, hq, hcoeff =>
    False.elim (lastCoeff_ne_zero_of_isTrimmedB hq (by simp) (hcoeff ((b :: q').length - 1)).symm)
  | a :: p', [], hp, _, hcoeff =>
    False.elim (lastCoeff_ne_zero_of_isTrimmedB hp (by simp) (hcoeff ((a :: p').length - 1)))
  | a :: p', b :: q', hp, hq, hcoeff => by
    have ha : a = b := hcoeff 0
    have htail : p' = q' :=
      eq_of_isTrimmedB_coeff p' q' (isTrimmedB_tail hp) (isTrimmedB_tail hq)
        (fun i => hcoeff (i + 1))
    rw [ha, htail]

theorem trim_eq_iff_coeff (p q : List (Fin 5)) :
    trim p = trim q ↔ ∀ i, coeff p i = coeff q i := by
  constructor
  · intro h i
    rw [← coeff_trim p i, ← coeff_trim q i, h]
  · intro h
    refine eq_of_isTrimmedB_coeff (trim p) (trim q) (isTrimmedB_trim p) (isTrimmedB_trim q) ?_
    intro i
    rw [coeff_trim, coeff_trim]
    exact h i

/-! ## Part 3: Raw and Trimmed Polynomial Ring Operations over F_5 -/

def addRaw : List (Fin 5) → List (Fin 5) → List (Fin 5)
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addRaw p q

def negRaw (p : List (Fin 5)) : List (Fin 5) :=
  p.map (fun a => -a)

def scaleRaw (c : Fin 5) : List (Fin 5) → List (Fin 5)
  | [] => []
  | a :: p => (c * a) :: scaleRaw c p

def mulRaw : List (Fin 5) → List (Fin 5) → List (Fin 5)
  | [], _ => []
  | a :: p, q => addRaw (scaleRaw a q) (0 :: mulRaw p q)

def polyZero : PolyF5 := []
def polyOne : PolyF5 := [1]
def polyX : PolyF5 := [0, 1]
def polyAdd (p q : PolyF5) : PolyF5 := trim (addRaw p q)
def polyNeg (p : PolyF5) : PolyF5 := trim (negRaw p)
def polySub (p q : PolyF5) : PolyF5 := polyAdd p (polyNeg q)
def polyScale (c : Fin 5) (p : PolyF5) : PolyF5 := trim (scaleRaw c p)
def polyMul (p q : PolyF5) : PolyF5 := trim (mulRaw p q)

def polyMonic (p : PolyF5) : PolyF5 :=
  let p' := trim p
  if p'.isEmpty then [] else polyScale (invF5 (leadCoeff p')) p'

def polyXpowMul (c : Fin 5) (k : Nat) : PolyF5 :=
  if c.val == 0 then [] else List.replicate k 0 ++ [c]

theorem coeff_addRaw : ∀ (p q : List (Fin 5)) (i : Nat),
    coeff (addRaw p q) i = coeff p i + coeff q i
  | [], _, _ => by simp [addRaw, coeff]
  | _ :: _, [], _ => by simp [addRaw, coeff]
  | _ :: _, _ :: _, 0 => rfl
  | _ :: p, _ :: q, i + 1 => coeff_addRaw p q i

theorem coeff_negRaw : ∀ (p : List (Fin 5)) (i : Nat),
    coeff (negRaw p) i = -coeff p i
  | [], _ => by simp [negRaw, coeff]
  | _ :: _, 0 => rfl
  | _ :: p, i + 1 => coeff_negRaw p i

theorem coeff_scaleRaw : ∀ (c : Fin 5) (p : List (Fin 5)) (i : Nat),
    coeff (scaleRaw c p) i = c * coeff p i
  | _, [], _ => by simp [scaleRaw, coeff]
  | _, _ :: _, 0 => rfl
  | c, _ :: p, i + 1 => coeff_scaleRaw c p i

theorem coeff_polyAdd (p q : PolyF5) (i : Nat) :
    coeff (polyAdd p q) i = coeff p i + coeff q i := by
  rw [polyAdd, coeff_trim, coeff_addRaw]

theorem coeff_polyNeg (p : PolyF5) (i : Nat) :
    coeff (polyNeg p) i = -coeff p i := by
  rw [polyNeg, coeff_trim, coeff_negRaw]

theorem coeff_polySub (p q : PolyF5) (i : Nat) :
    coeff (polySub p q) i = coeff p i - coeff q i := by
  rw [polySub, coeff_polyAdd, coeff_polyNeg, f5_sub_eq_add_neg]

theorem coeff_polyScale (c : Fin 5) (p : PolyF5) (i : Nat) :
    coeff (polyScale c p) i = c * coeff p i := by
  rw [polyScale, coeff_trim, coeff_scaleRaw]

theorem coeff_polyMul (p q : PolyF5) (i : Nat) :
    coeff (polyMul p q) i = coeff (mulRaw p q) i := by
  rw [polyMul, coeff_trim]

theorem coeff_mulRaw_cons_zero (a : Fin 5) (p q : List (Fin 5)) :
    coeff (mulRaw (a :: p) q) 0 = a * coeff q 0 := by
  simp [mulRaw, coeff_addRaw, coeff_scaleRaw, coeff]

theorem coeff_mulRaw_cons_succ (a : Fin 5) (p q : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (a :: p) q) (i + 1) = a * coeff q (i + 1) + coeff (mulRaw p q) i := by
  simp [mulRaw, coeff_addRaw, coeff_scaleRaw, coeff]

theorem coeff_mulRaw_nil_right (p : List (Fin 5)) (i : Nat) :
    coeff (mulRaw p []) i = 0 := by
  induction p generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => simp [coeff_mulRaw_cons_zero, coeff]
    | succ j => simp [coeff_mulRaw_cons_succ, coeff, ih j]

theorem coeff_mulRaw_congr_right (p : List (Fin 5)) {q1 q2 : List (Fin 5)}
    (hq : ∀ i, coeff q1 i = coeff q2 i) (i : Nat) :
    coeff (mulRaw p q1) i = coeff (mulRaw p q2) i := by
  induction p generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => simp [coeff_mulRaw_cons_zero, hq 0]
    | succ j => simp [coeff_mulRaw_cons_succ, hq (j + 1), ih j]

theorem coeff_mulRaw_zero_coeff {p : List (Fin 5)} (q : List (Fin 5))
    (hp : ∀ k, coeff p k = 0) (j : Nat) : coeff (mulRaw p q) j = 0 := by
  induction p generalizing j with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = 0 := hp 0
    have htail : ∀ k, coeff xs k = 0 := fun k => hp (k + 1)
    cases j with
    | zero => simp [coeff_mulRaw_cons_zero, hx]
    | succ j' => simp [coeff_mulRaw_cons_succ, hx, ih htail j']

theorem coeff_mulRaw_congr_left {p1 p2 : List (Fin 5)} (q : List (Fin 5))
    (hp : ∀ i, coeff p1 i = coeff p2 i) (i : Nat) :
    coeff (mulRaw p1 q) i = coeff (mulRaw p2 q) i := by
  induction p1 generalizing p2 i with
  | nil =>
    have hp2 : ∀ j, coeff p2 j = 0 := fun j => (hp j).symm
    exact (coeff_mulRaw_zero_coeff q hp2 i).symm
  | cons a p1 ih1 =>
    cases p2 with
    | nil =>
      exact coeff_mulRaw_zero_coeff q hp i
    | cons b p2 =>
      have hab : a = b := hp 0
      have htail : ∀ k, coeff p1 k = coeff p2 k := fun k => hp (k + 1)
      cases i with
      | zero => simp [coeff_mulRaw_cons_zero, hab]
      | succ j => simp [coeff_mulRaw_cons_succ, hab, ih1 htail j]

theorem coeff_mulRaw_add_left (p1 p2 q : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (addRaw p1 p2) q) i = coeff (mulRaw p1 q) i + coeff (mulRaw p2 q) i := by
  induction p1 generalizing p2 i with
  | nil => simp [addRaw, mulRaw, coeff]
  | cons a p1 ih =>
    cases p2 with
    | nil => simp [addRaw, mulRaw, coeff]
    | cons b p2 =>
      cases i with
      | zero =>
        simp only [addRaw, coeff_mulRaw_cons_zero]
        exact f5_add_mul a b (coeff q 0)
      | succ j =>
        simp only [addRaw, coeff_mulRaw_cons_succ, ih p2 j]
        rw [f5_add_mul]
        rw [f5_add_assoc, f5_add_assoc,
            ← f5_add_assoc (coeff (mulRaw p1 q) j) (b * coeff q (j + 1)),
            f5_add_comm (coeff (mulRaw p1 q) j) (b * coeff q (j + 1)),
            f5_add_assoc (b * coeff q (j + 1)), ← f5_add_assoc]

theorem coeff_mulRaw_scale_left (c : Fin 5) (p q : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (scaleRaw c p) q) i = c * coeff (mulRaw p q) i := by
  induction p generalizing i with
  | nil => simp [scaleRaw, mulRaw, coeff]
  | cons a p ih =>
    cases i with
    | zero =>
      simp only [scaleRaw, coeff_mulRaw_cons_zero]
      exact f5_mul_assoc c a (coeff q 0)
    | succ j =>
      simp only [scaleRaw, coeff_mulRaw_cons_succ, ih j, f5_mul_assoc, f5_mul_add]

theorem coeff_mulRaw_shift_left (p q : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (0 :: p) q) i = match i with | 0 => 0 | j + 1 => coeff (mulRaw p q) j := by
  cases i with
  | zero => simp [coeff_mulRaw_cons_zero]
  | succ j => simp [coeff_mulRaw_cons_succ]

theorem coeff_mulRaw_comm (p q : List (Fin 5)) (i : Nat) :
    coeff (mulRaw p q) i = coeff (mulRaw q p) i := by
  induction p generalizing q i with
  | nil =>
    simp [mulRaw, coeff, coeff_mulRaw_nil_right]
  | cons a p ihp =>
    induction q generalizing i with
    | nil =>
      rw [coeff_mulRaw_nil_right]
      rfl
    | cons b q ihq =>
      cases i with
      | zero =>
        simp only [coeff_mulRaw_cons_zero, coeff]
        exact f5_mul_comm a b
      | succ j =>
        rw [coeff_mulRaw_cons_succ, coeff_mulRaw_cons_succ, ← ihq j]
        cases j with
        | zero =>
          change a * coeff q 0 + coeff (mulRaw p (b :: q)) 0 =
            b * coeff p 0 + coeff (mulRaw (a :: p) q) 0
          rw [ihp (b :: q) 0, coeff_mulRaw_cons_zero, coeff_mulRaw_cons_zero]
          exact f5_add_comm _ _
        | succ k =>
          change a * coeff q (k + 1) + coeff (mulRaw p (b :: q)) (k + 1) =
            b * coeff p (k + 1) + coeff (mulRaw (a :: p) q) (k + 1)
          rw [ihp (b :: q) (k + 1), coeff_mulRaw_cons_succ, coeff_mulRaw_cons_succ, ihp q k]
          rw [← f5_add_assoc, f5_add_comm (a * coeff q (k + 1)), f5_add_assoc]

theorem coeff_mulRaw_assoc (p q r : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (mulRaw p q) r) i = coeff (mulRaw p (mulRaw q r)) i := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
    change coeff (mulRaw (addRaw (scaleRaw a q) (0 :: mulRaw p q)) r) i =
      coeff (mulRaw (a :: p) (mulRaw q r)) i
    rw [coeff_mulRaw_add_left, coeff_mulRaw_scale_left, coeff_mulRaw_shift_left]
    cases i with
    | zero =>
      rw [coeff_mulRaw_cons_zero, f5_add_zero]
    | succ j =>
      dsimp only
      rw [coeff_mulRaw_cons_succ, ih j]

theorem polyAdd_comm (p q : PolyF5) : polyAdd p q = polyAdd q p := by
  rw [polyAdd, polyAdd, trim_eq_iff_coeff]
  intro i
  rw [coeff_addRaw, coeff_addRaw, f5_add_comm]

theorem polyAdd_assoc (p q r : PolyF5) :
    polyAdd (polyAdd p q) r = polyAdd p (polyAdd q r) := by
  simp only [polyAdd, trim_eq_iff_coeff]
  intro i
  simp only [coeff_addRaw, coeff_trim, f5_add_assoc]

theorem polyAdd_zero (p : PolyF5) : polyAdd p polyZero = trim p := by
  rw [polyAdd, trim_eq_iff_coeff]
  intro i
  simp [coeff_addRaw, polyZero, coeff]

theorem polyZero_add (p : PolyF5) : polyAdd polyZero p = trim p := by
  rw [polyAdd_comm, polyAdd_zero]

theorem polySub_add_cancel (p q : PolyF5) : polyAdd (polySub p q) q = trim p := by
  rw [polySub, polyAdd_assoc]
  simp only [polyAdd, trim_eq_iff_coeff]
  intro i
  rw [coeff_addRaw, coeff_trim, coeff_addRaw, coeff_polyNeg]
  have hf : ∀ x y : Fin 5, x + (-y + y) = x := by decide
  exact hf (coeff p i) (coeff q i)

theorem polyMul_trim_left (p q : PolyF5) : polyMul (trim p) q = polyMul p q := by
  rw [polyMul, polyMul, trim_eq_iff_coeff]
  exact coeff_mulRaw_congr_left q (fun i => coeff_trim p i)

theorem polyMul_trim_right (p q : PolyF5) : polyMul p (trim q) = polyMul p q := by
  rw [polyMul, polyMul, trim_eq_iff_coeff]
  exact coeff_mulRaw_congr_right p (fun i => coeff_trim q i)

theorem polyMul_comm (p q : PolyF5) : polyMul p q = polyMul q p := by
  rw [polyMul, polyMul, trim_eq_iff_coeff]
  exact coeff_mulRaw_comm p q

theorem polyMul_assoc (p q r : PolyF5) :
    polyMul (polyMul p q) r = polyMul p (polyMul q r) := by
  simp only [polyMul, trim_eq_iff_coeff]
  intro i
  have h1 := coeff_mulRaw_congr_left r (fun j => coeff_trim (mulRaw p q) j) i
  have h2 := coeff_mulRaw_congr_right p (fun j => coeff_trim (mulRaw q r) j) i
  rw [h1, h2]
  exact coeff_mulRaw_assoc p q r i

theorem polyMul_add_right (p1 p2 q : PolyF5) :
    polyMul (polyAdd p1 p2) q = polyAdd (polyMul p1 q) (polyMul p2 q) := by
  rw [polyAdd, polyMul_trim_left, polyMul, polyAdd, trim_eq_iff_coeff]
  intro i
  rw [coeff_addRaw, coeff_polyMul, coeff_polyMul, coeff_mulRaw_add_left]

theorem polyMul_add_left (p q1 q2 : PolyF5) :
    polyMul p (polyAdd q1 q2) = polyAdd (polyMul p q1) (polyMul p q2) := by
  rw [polyMul_comm p, polyMul_add_right, polyMul_comm q1, polyMul_comm q2]

theorem polyMul_neg_right (p q : PolyF5) :
    polyMul (polyNeg p) q = polyNeg (polyMul p q) := by
  rw [polyNeg, polyMul_trim_left, polyMul, polyNeg, trim_eq_iff_coeff]
  intro i
  rw [coeff_negRaw, coeff_polyMul]
  have hneg : ∀ x : Fin 5, -x = (4 : Fin 5) * x := by decide
  have h1 : ∀ j, coeff (negRaw p) j = coeff (scaleRaw (4 : Fin 5) p) j := by
    intro j
    rw [coeff_negRaw, coeff_scaleRaw, hneg (coeff p j)]
  rw [coeff_mulRaw_congr_left q h1 i, coeff_mulRaw_scale_left, ← hneg]

theorem polyScale_add (c : Fin 5) (p q : PolyF5) :
    polyScale c (polyAdd p q) = polyAdd (polyScale c p) (polyScale c q) := by
  simp only [polyScale, polyAdd, trim_eq_iff_coeff]
  intro i
  simp only [coeff_scaleRaw, coeff_trim, coeff_addRaw, f5_mul_add]

theorem polyMul_scale_left (c : Fin 5) (p q : PolyF5) :
    polyMul (polyScale c p) q = polyScale c (polyMul p q) := by
  rw [polyScale, polyMul_trim_left, polyMul, polyScale, trim_eq_iff_coeff]
  intro i
  rw [coeff_scaleRaw, coeff_polyMul, coeff_mulRaw_scale_left]

theorem polyMul_one_left (p : PolyF5) : polyMul polyOne p = trim p := by
  rw [polyMul, trim_eq_iff_coeff]
  intro i
  cases i with
  | zero => simp [polyOne, coeff_mulRaw_cons_zero]
  | succ j =>
    simp [polyOne, mulRaw, coeff_addRaw, coeff_scaleRaw, coeff]

theorem polyMul_zero_left (p : PolyF5) : polyMul polyZero p = polyZero := by
  rfl

theorem polyAdd_sub_cancel (p q : PolyF5) : polyAdd p (polySub q p) = trim q := by
  rw [polyAdd_comm, polySub_add_cancel]

theorem polySub_sub_distrib (a b c d : PolyF5) :
    polyAdd (polySub a b) (polySub c d) = polySub (polyAdd a c) (polyAdd b d) := by
  rw [polySub, polySub, polySub, polyAdd_assoc, polyAdd_comm (polyNeg b), polyAdd_assoc,
      polyAdd_comm (polyNeg d), ← polyAdd_assoc a c]
  have hneg : polyAdd (polyNeg b) (polyNeg d) = polyNeg (polyAdd b d) := by
    simp only [polyNeg, polyAdd, trim_eq_iff_coeff]
    intro i
    simp only [coeff_addRaw, coeff_trim, coeff_negRaw]
    have hf : ∀ x y : Fin 5, -x + -y = -(x + y) := by decide
    exact hf (coeff b i) (coeff d i)
  rw [← hneg, polyAdd_assoc]

/-! ## Part 4: Euclidean Division and Extended GCD over F_5 -/

def divModAux (b : PolyF5) (invLb : Fin 5) : Nat → PolyF5 → PolyF5 × PolyF5
  | 0, r => ([], r)
  | fuel + 1, r =>
    if r.length < b.length then
      ([], r)
    else
      let shift := r.length - b.length
      let c := leadCoeff r * invLb
      let term := polyXpowMul c shift
      let r' := polySub r (polyMul term b)
      let (q', rem) := divModAux b invLb fuel r'
      (polyAdd term q', rem)

def polyDivMod (a b : PolyF5) : PolyF5 × PolyF5 :=
  let a' := trim a
  let b' := trim b
  if b'.isEmpty then ([], a')
  else divModAux b' (invF5 (leadCoeff b')) a'.length a'

def polyDiv (a b : PolyF5) : PolyF5 := (polyDivMod a b).1
def polyMod (a b : PolyF5) : PolyF5 := (polyDivMod a b).2

theorem coeff_mulRaw_shift_singleton (c : Fin 5) (k : Nat) (b : List (Fin 5)) (i : Nat) :
    coeff (mulRaw (List.replicate k 0 ++ [c]) b) i =
      if i < k then 0 else c * coeff b (i - k) := by
  induction k generalizing i with
  | zero =>
    simp only [List.replicate, List.nil_append, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases i with
    | zero => simp [coeff_mulRaw_cons_zero]
    | succ j => simp [mulRaw, coeff_addRaw, coeff_scaleRaw, coeff]
  | succ k ih =>
    simp only [List.replicate, List.cons_append]
    cases i with
    | zero =>
      simp [coeff_mulRaw_cons_zero]
    | succ j =>
      rw [coeff_mulRaw_cons_succ, ih j]
      simp only [f5_zero_mul, f5_zero_add]
      cases Nat.lt_or_ge j k with
      | inl hlt =>
        have hlt' : j + 1 < k + 1 := Nat.succ_lt_succ hlt
        simp [hlt, hlt']
      | inr hge =>
        have hn1 : ¬ (j < k) := Nat.not_lt_of_ge hge
        have hn2 : ¬ (j + 1 < k + 1) := Nat.not_lt_of_ge (Nat.succ_le_succ hge)
        simp [hn1, hn2, Nat.succ_sub_succ_eq_sub]

theorem coeff_polyMul_polyXpowMul (c : Fin 5) (k : Nat) (b : PolyF5) (i : Nat) :
    coeff (polyMul (polyXpowMul c k) b) i = if i < k then 0 else c * coeff b (i - k) := by
  rw [polyXpowMul, coeff_polyMul]
  cases hc : (c.val == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact coeff_mulRaw_shift_singleton c k b i
  · have hc0 : c = 0 := f5_val_eq_zero_of_beq hc
    subst hc0
    cases Nat.lt_or_ge i k with
    | inl hlt => simp [mulRaw, coeff, hlt]
    | inr hge =>
      have hn : ¬ (i < k) := Nat.not_lt_of_ge hge
      simp [mulRaw, coeff, hn]

theorem divMod_step_len_lt {r b : PolyF5}
    (_hr : isTrimmedB r = true) (hb : isTrimmedB b = true) (hbne : b ≠ [])
    (hlen : b.length ≤ r.length) :
    (polySub r (polyMul (polyXpowMul (leadCoeff r * invF5 (leadCoeff b))
      (r.length - b.length)) b)).length < r.length := by
  have hrne : r ≠ [] := by
    intro h0
    rw [h0] at hlen
    exact hbne (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen))
  have hrpos : 0 < r.length := list_length_pos_of_ne_nil hrne
  have hbpos : 0 < b.length := list_length_pos_of_ne_nil hbne
  let shift := r.length - b.length
  let invLb := invF5 (leadCoeff b)
  let c := leadCoeff r * invLb
  let r' := polySub r (polyMul (polyXpowMul c shift) b)
  have htr' : isTrimmedB r' = true := isTrimmedB_trim _
  have hzero : ∀ i, r.length - 1 ≤ i → coeff r' i = 0 := by
    intro i hi
    change coeff (polySub r (polyMul (polyXpowMul c shift) b)) i = 0
    rw [coeff_polySub, coeff_polyMul_polyXpowMul]
    have hshift : shift ≤ i := by
      have h1 : r.length - b.length ≤ r.length - 1 := Nat.sub_le_sub_left hbpos r.length
      exact Nat.le_trans h1 hi
    have hnot : ¬ (i < shift) := Nat.not_lt_of_ge hshift
    simp only [hnot, ↓reduceIte]
    cases Nat.eq_or_lt_of_le hi with
    | inl heq =>
      subst heq
      have hsub : r.length - 1 - shift = b.length - 1 := by
        have hh := Nat.sub_add_cancel hlen
        have hbsub : (b.length - 1) + 1 = b.length := Nat.sub_add_cancel hbpos
        have hrsub : (r.length - 1) + 1 = r.length := Nat.sub_add_cancel hrpos
        have hsum : shift + (b.length - 1) = r.length - 1 := by
          apply Nat.succ.inj
          calc (shift + (b.length - 1)) + 1
              = shift + ((b.length - 1) + 1) := Nat.add_assoc _ _ _
            _ = shift + b.length := by rw [hbsub]
            _ = r.length := hh
            _ = (r.length - 1) + 1 := hrsub.symm
        rw [← hsum, Nat.add_sub_cancel_left]
      rw [hsub, ← leadCoeff_eq_coeff r hrne, ← leadCoeff_eq_coeff b hbne]
      have hne0 : leadCoeff b ≠ 0 := leadCoeff_ne_zero_of_isTrimmedB b hb hbne
      have hinv : invLb * leadCoeff b = 1 := mul_invF5 (leadCoeff b) hne0
      have hmul : c * leadCoeff b = leadCoeff r := by
        calc c * leadCoeff b = (leadCoeff r * invLb) * leadCoeff b := rfl
          _ = leadCoeff r * (invLb * leadCoeff b) := f5_mul_assoc _ _ _
          _ = leadCoeff r * 1 := by rw [hinv]
          _ = leadCoeff r := f5_mul_one _
      rw [hmul, f5_sub_self]
    | inr hgt =>
      have hge_r : r.length ≤ i := by
        have h1 : (r.length - 1) + 1 ≤ i := hgt
        rwa [Nat.sub_add_cancel hrpos] at h1
      have hge_b : b.length ≤ i - shift := by
        have hrb : r.length - shift = b.length := by
          have := Nat.sub_add_cancel hlen
          calc r.length - shift = (shift + b.length) - shift := by rw [this]
            _ = b.length := Nat.add_sub_cancel_left _ _
        rw [← hrb]
        exact Nat.sub_le_sub_right hge_r shift
      rw [coeff_ge_len_zero r i hge_r, coeff_ge_len_zero b (i - shift) hge_b,
          f5_mul_zero, f5_sub_self]
  have hle := len_le_of_isTrimmedB_coeff_zero htr' hzero
  exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hrpos Nat.zero_lt_one)

theorem divModAux_sound (b : PolyF5) (hb : isTrimmedB b = true) (hbne : b ≠ [])
    (fuel : Nat) (r : PolyF5) (hr : isTrimmedB r = true) (hf : r.length ≤ fuel) :
    let (q, rem) := divModAux b (invF5 (leadCoeff b)) fuel r
    isTrimmedB q = true ∧ isTrimmedB rem = true ∧
    polyAdd (polyMul q b) rem = r ∧ rem.length < b.length := by
  induction fuel generalizing r with
  | zero =>
    have hr0 : r = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hf)
    subst hr0
    simp only [divModAux]
    exact ⟨rfl, rfl, by
      change polyAdd (polyMul polyZero b) [] = []
      rw [polyMul_zero_left, polyZero_add]
      rfl, list_length_pos_of_ne_nil hbne⟩
  | succ fuel ih =>
    simp only [divModAux]
    split
    · rename_i hlt
      exact ⟨rfl, hr, by
        change polyAdd (polyMul polyZero b) r = r
        rw [polyMul_zero_left, polyZero_add]
        exact trim_of_isTrimmedB hr, hlt⟩
    · rename_i hnotlt
      have hle : b.length ≤ r.length := Nat.le_of_not_lt hnotlt
      let invLb := invF5 (leadCoeff b)
      let c := leadCoeff r * invLb
      let term := polyXpowMul c (r.length - b.length)
      let r' := polySub r (polyMul term b)
      have htr' : isTrimmedB r' = true := isTrimmedB_trim _
      have hr'lt : r'.length < r.length := divMod_step_len_lt hr hb hbne hle
      have hr'le : r'.length ≤ fuel := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr'lt hf)
      have ihstep := ih r' htr' hr'le
      rcases hrec : divModAux b invLb fuel r' with ⟨q', rem⟩
      rw [hrec] at ihstep
      rcases ihstep with ⟨htq', htrem, heq, hrem_lt⟩
      refine ⟨isTrimmedB_trim _, htrem, ?_, hrem_lt⟩
      calc polyAdd (polyMul (polyAdd term q') b) rem
          = polyAdd (polyAdd (polyMul term b) (polyMul q' b)) rem := by rw [polyMul_add_right]
        _ = polyAdd (polyMul term b) (polyAdd (polyMul q' b) rem) := polyAdd_assoc _ _ _
        _ = polyAdd (polyMul term b) r' := by rw [heq]
        _ = trim r := polyAdd_sub_cancel (polyMul term b) r
        _ = r := trim_of_isTrimmedB hr

theorem polyDivMod_sound (a b : PolyF5) (hb : trim b ≠ []) :
    let (q, r) := polyDivMod a b
    isTrimmedB q = true ∧ isTrimmedB r = true ∧
    polyAdd (polyMul q (trim b)) r = trim a ∧ r.length < (trim b).length := by
  simp only [polyDivMod]
  have hbis : (trim b).isEmpty = false := isEmpty_of_ne_nil hb
  rw [hbis]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact divModAux_sound (trim b) (isTrimmedB_trim b) hb (trim a).length (trim a)
    (isTrimmedB_trim a) (Nat.le_refl _)

theorem polyDivMod_sound_trimmed {a b : PolyF5}
    (ha : isTrimmedB a = true) (hb : isTrimmedB b = true) (hbne : b ≠ []) :
    let (q, r) := polyDivMod a b
    isTrimmedB q = true ∧ isTrimmedB r = true ∧
    polyAdd (polyMul q b) r = a ∧ r.length < b.length := by
  have htb : trim b = b := trim_of_isTrimmedB hb
  have hta : trim a = a := trim_of_isTrimmedB ha
  have hs := polyDivMod_sound a b (by rw [htb]; exact hbne)
  rw [htb, hta] at hs
  exact hs

def xgcdAux :
    Nat → (PolyF5 × PolyF5 × PolyF5) → (PolyF5 × PolyF5 × PolyF5) →
      (PolyF5 × PolyF5 × PolyF5)
  | 0, (r0, s0, t0), _ =>
    if r0.isEmpty then ([], [], [])
    else
      let inv := invF5 (leadCoeff r0)
      (polyScale inv r0, polyScale inv s0, polyScale inv t0)
  | fuel + 1, (r0, s0, t0), (r1, s1, t1) =>
    if r1.isEmpty then
      if r0.isEmpty then ([], [], [])
      else
        let inv := invF5 (leadCoeff r0)
        (polyScale inv r0, polyScale inv s0, polyScale inv t0)
    else
      let (q, r2) := polyDivMod r0 r1
      let s2 := polySub s0 (polyMul q s1)
      let t2 := polySub t0 (polyMul q t1)
      xgcdAux fuel (r1, s1, t1) (r2, s2, t2)

def polyXgcd (a b : PolyF5) : PolyF5 × PolyF5 × PolyF5 :=
  let a' := trim a
  let b' := trim b
  xgcdAux b'.length (a', polyOne, polyZero) (b', polyZero, polyOne)

def polyGcd (a b : PolyF5) : PolyF5 := (polyXgcd a b).1

theorem isMonic_polyScale_inv {r : PolyF5} (ht : isTrimmedB r = true) (hne : r ≠ []) :
    isMonic (polyScale (invF5 (leadCoeff r)) r) = true := by
  let inv := invF5 (leadCoeff r)
  let p := polyScale inv r
  have htp : isTrimmedB p = true := isTrimmedB_trim _
  have hinv_mul : inv * leadCoeff r = 1 :=
    mul_invF5 (leadCoeff r) (leadCoeff_ne_zero_of_isTrimmedB r ht hne)
  have hlast : coeff p (r.length - 1) = 1 := by
    change coeff (polyScale inv r) (r.length - 1) = 1
    rw [coeff_polyScale, ← leadCoeff_eq_coeff r hne, hinv_mul]
  have hpne : p ≠ [] := by
    intro h0
    rw [h0] at hlast
    cases hlast
  have hlen_le : p.length ≤ r.length := by
    refine len_le_of_isTrimmedB_coeff_zero htp ?_
    intro i hi
    change coeff (polyScale inv r) i = 0
    rw [coeff_polyScale, coeff_ge_len_zero r i hi, f5_mul_zero]
  have hge_len : r.length ≤ p.length := by
    cases Nat.lt_or_ge p.length r.length with
    | inr hge => exact hge
    | inl hlt =>
      have h0 : coeff p (r.length - 1) = 0 :=
        coeff_ge_len_zero p (r.length - 1) (Nat.le_pred_of_lt hlt)
      rw [hlast] at h0
      cases h0
  have hlen_eq : p.length = r.length := Nat.le_antisymm hlen_le hge_len
  have hlead : leadCoeff p = 1 := by
    rw [leadCoeff_eq_coeff p hpne, hlen_eq, hlast]
  have hpis : p.isEmpty = false := isEmpty_of_ne_nil hpne
  change (!p.isEmpty && (leadCoeff p).val == 1) = true
  rw [hpis, hlead]
  rfl

theorem xgcdAux_bezout (a b : PolyF5) (_ha : isTrimmedB a = true) (_hb : isTrimmedB b = true)
    (fuel : Nat) (r0 s0 t0 r1 s1 t1 : PolyF5)
    (hr0 : isTrimmedB r0 = true) (hs0 : isTrimmedB s0 = true) (ht0 : isTrimmedB t0 = true)
    (hr1 : isTrimmedB r1 = true) (hs1 : isTrimmedB s1 = true) (ht1 : isTrimmedB t1 = true)
    (hbez0 : polyAdd (polyMul s0 a) (polyMul t0 b) = r0)
    (hbez1 : polyAdd (polyMul s1 a) (polyMul t1 b) = r1)
    (hlen : r1.length ≤ fuel) :
    let (g, s, t) := xgcdAux fuel (r0, s0, t0) (r1, s1, t1)
    isTrimmedB g = true ∧ isTrimmedB s = true ∧ isTrimmedB t = true ∧
    polyAdd (polyMul s a) (polyMul t b) = g ∧
    (r0 ≠ [] ∨ r1 ≠ [] → isMonic g = true) := by
  induction fuel generalizing r0 s0 t0 r1 s1 t1 with
  | zero =>
    have hr1nil : r1 = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    simp only [xgcdAux]
    cases hr0is : r0.isEmpty with
    | true =>
      have hr0nil : r0 = [] := isEmpty_true hr0is
      simp only [↓reduceIte]
      refine ⟨rfl, rfl, rfl, ?_, fun h => ?_⟩
      · change polyAdd (polyMul polyZero a) (polyMul polyZero b) = []
        rw [polyMul_zero_left, polyZero_add]
        rfl
      · cases h with
        | inl h0 => exact False.elim (h0 hr0nil)
        | inr h1 => exact False.elim (h1 hr1nil)
    | false =>
      have hr0ne : r0 ≠ [] := isEmpty_false hr0is
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨isTrimmedB_trim _, isTrimmedB_trim _, isTrimmedB_trim _, ?_, ?_⟩
      · rw [polyMul_scale_left, polyMul_scale_left, ← polyScale_add, hbez0]
      · intro _; exact isMonic_polyScale_inv hr0 hr0ne
  | succ fuel ih =>
    simp only [xgcdAux]
    cases hr1is : r1.isEmpty with
    | true =>
      have hr1nil : r1 = [] := isEmpty_true hr1is
      simp only [↓reduceIte]
      cases hr0is : r0.isEmpty with
      | true =>
        have hr0nil : r0 = [] := isEmpty_true hr0is
        simp only [↓reduceIte]
        refine ⟨rfl, rfl, rfl, ?_, fun h => ?_⟩
        · change polyAdd (polyMul polyZero a) (polyMul polyZero b) = []
          rw [polyMul_zero_left, polyZero_add]
          rfl
        · cases h with
          | inl h0 => exact False.elim (h0 hr0nil)
          | inr h1 => exact False.elim (h1 hr1nil)
      | false =>
        have hr0ne : r0 ≠ [] := isEmpty_false hr0is
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨isTrimmedB_trim _, isTrimmedB_trim _, isTrimmedB_trim _, ?_, ?_⟩
        · rw [polyMul_scale_left, polyMul_scale_left, ← polyScale_add, hbez0]
        · intro _; exact isMonic_polyScale_inv hr0 hr0ne
    | false =>
      have hr1ne : r1 ≠ [] := isEmpty_false hr1is
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hdm : polyDivMod r0 r1 with ⟨q, r2⟩
      have hdm_sound := polyDivMod_sound_trimmed hr0 hr1 hr1ne
      rw [hdm] at hdm_sound
      rcases hdm_sound with ⟨hq, hr2, hqr2, hr2lt⟩
      let s2 := polySub s0 (polyMul q s1)
      let t2 := polySub t0 (polyMul q t1)
      have hbez2 : polyAdd (polyMul s2 a) (polyMul t2 b) = r2 := by
        have hstep : polyAdd (polyMul s2 a) (polyMul t2 b) =
            polySub r0 (polyMul q r1) := by
          dsimp [s2, t2]
          rw [polySub, polyMul_add_right, polyMul_neg_right, polyMul_assoc]
          rw [polySub, polyMul_add_right, polyMul_neg_right, polyMul_assoc]
          change polyAdd (polySub (polyMul s0 a) (polyMul q (polyMul s1 a)))
              (polySub (polyMul t0 b) (polyMul q (polyMul t1 b))) = _
          rw [polySub_sub_distrib, hbez0, ← polyMul_add_left, hbez1]
        rw [hstep, ← hqr2, polyAdd_comm (polyMul q r1) r2, polySub, polyAdd_assoc]
        have hcancel : polyAdd (polyMul q r1) (polyNeg (polyMul q r1)) = polyZero := by
          change trim (addRaw (polyMul q r1) (polyNeg (polyMul q r1))) = trim []
          rw [trim_eq_iff_coeff]
          intro i
          rw [coeff_addRaw, coeff_polyNeg, f5_add_neg_cancel]
          rfl
        rw [hcancel, polyAdd_zero]
        exact trim_of_isTrimmedB hr2
      have hr2le : r2.length ≤ fuel := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr2lt hlen)
      have ihstep := ih r1 s1 t1 r2 s2 t2 hr1 hs1 ht1 hr2 (isTrimmedB_trim _) (isTrimmedB_trim _)
        hbez1 hbez2 hr2le
      have hnorm : r0 ≠ [] ∨ r1 ≠ [] → r1 ≠ [] ∨ r2 ≠ [] := fun _ => Or.inl hr1ne
      rcases hrec : xgcdAux fuel (r1, s1, t1) (r2, s2, t2) with ⟨g, s, t⟩
      rw [hrec] at ihstep
      rcases ihstep with ⟨hg, hs, ht, hbez, hmonic⟩
      exact ⟨hg, hs, ht, hbez, fun h => hmonic (hnorm h)⟩

theorem polyXgcd_bezout (a b : PolyF5) :
    let (g, s, t) := polyXgcd a b
    isTrimmedB g = true ∧ isTrimmedB s = true ∧ isTrimmedB t = true ∧
    polyAdd (polyMul s (trim a)) (polyMul t (trim b)) = g ∧
    (trim a ≠ [] ∨ trim b ≠ [] → isMonic g = true) := by
  simp only [polyXgcd]
  exact xgcdAux_bezout (trim a) (trim b) (isTrimmedB_trim a) (isTrimmedB_trim b)
    (trim b).length (trim a) polyOne polyZero (trim b) polyZero polyOne
    (isTrimmedB_trim a) rfl rfl (isTrimmedB_trim b) rfl rfl
    (by simp only [polyMul_one_left, polyMul_zero_left, polyAdd_zero, trim_idempotent])
    (by simp only [polyMul_zero_left, polyMul_one_left, polyZero_add, trim_idempotent])
    (Nat.le_refl _)

theorem polyXgcd_bezout_trimmed {a b : PolyF5}
    (ha : isTrimmedB a = true) (hb : isTrimmedB b = true) :
    let (g, s, t) := polyXgcd a b
    isTrimmedB g = true ∧ isTrimmedB s = true ∧ isTrimmedB t = true ∧
    polyAdd (polyMul s a) (polyMul t b) = g ∧
    (a ≠ [] ∨ b ≠ [] → isMonic g = true) := by
  have hta : trim a = a := trim_of_isTrimmedB ha
  have htb : trim b = b := trim_of_isTrimmedB hb
  have hs := polyXgcd_bezout a b
  rw [hta, htb] at hs
  exact hs

/-! ## Part 5: Hyperelliptic Curve C : y^2 = x^5 - x + 1 & Cantor-Mumford Divisors -/

/-- Curve polynomial `f(x) = x^5 - x + 1 = x^5 + 4x + 1` over `F_5`. -/
def curveF5 : PolyF5 := [1, 4, 0, 0, 0, 1]

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

end Genus2Jacobian

-- end of file: leanasm/src/LeanAsm/Genus2Jacobian.lean
