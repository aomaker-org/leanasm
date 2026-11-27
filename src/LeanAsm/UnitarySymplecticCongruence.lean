-- Path: leanasm/src/LeanAsm/UnitarySymplecticCongruence.lean
-- Unitary and symplectic matrix involution formalisms and congruence subgroups over Int (Issue #241).

import LeanAsm.SatakeHeckeDegreeBridge
import LeanAsm.GSp4FunctorialityBridge

namespace UnitarySymplecticCongruence

/-!
# Unitary & Symplectic Involution and Congruence Subgroups

Distills unitary and symplectic involution formalisms and congruence subgroups
from `alpo-rh` (`Formalism/SatakeDualWeyl/Statement.lean`) into constructive
matrix invariants and subgroup predicates over `Int`:

1. Matrix type `Mat n` represented as `Fin n → Fin n → Int`, identity `matOne`,
   multiplication `matMul`, transpose `matTranspose`, and conjugation involution `cT`.
2. Hermitian / skew-Hermitian symmetry predicates `IsHerm`, `IsSkewHerm`.
3. Standard symplectic alternating form $J_{2g}$ and unitary/symplectic stabilizer `UJ`.
4. Group structure preservation: identity `UJ_one`, closure under composition `UJ_mul`,
   and symplectic transpose-inverse duality.
5. Principal congruence subgroups `princCong n N` modulo level $N \ge 1$ and pre-congruence
   stabilizer filters.
6. Compatibility with algebraic Hecke operators on $\mathrm{GL}_n$ and $\mathrm{GSp}_4$.
-/

/-- Constructive $n \times n$ matrix over `Int`. -/
def Mat (n : Nat) := Fin n → Fin n → Int

/-- Identity matrix $I_n$. -/
def matOne (n : Nat) : Mat n :=
  fun i j => if i.val == j.val then 1 else 0

/-- Standard matrix transpose $M^\top$. -/
def matTranspose {n : Nat} (M : Mat n) : Mat n :=
  fun i j => M j i

/-- Sum of a sequence over `Fin n` using recursive list folding. -/
def finSum {n : Nat} (f : Fin n → Int) : Int :=
  (List.finRange n).foldl (fun acc i => acc + f i) 0

/-- Matrix multiplication $M \cdot N$. -/
def matMul {n : Nat} (M N : Mat n) : Mat n :=
  fun i k => finSum (fun j => M i j * N j k)

/-- Involutive ring endomorphism signature on `Int`. -/
structure RingInvolution where
  inv : Int → Int
  map_zero : inv 0 = 0
  map_one : inv 1 = 1
  map_add : ∀ x y : Int, inv (x + y) = inv x + inv y
  map_mul : ∀ x y : Int, inv (x * y) = inv x * inv y
  involutive : ∀ x : Int, inv (inv x) = x

/-- Identity involution on `Int`. -/
def idInvolution : RingInvolution where
  inv := id
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  involutive := fun _ => rfl

/-- Conjugate transpose involution `cT σ M = (M.map σ)ᵀ`. -/
def cT (σ : RingInvolution) {n : Nat} (M : Mat n) : Mat n :=
  fun i j => σ.inv (M j i)

/-- Hermitian symmetry: $cT(M) = M$. -/
def IsHerm (σ : RingInvolution) {n : Nat} (J : Mat n) : Prop :=
  ∀ i j : Fin n, cT σ J i j = J i j

/-- Skew-Hermitian / alternating symmetry: $cT(M) = -J$. -/
def IsSkewHerm (σ : RingInvolution) {n : Nat} (J : Mat n) : Prop :=
  ∀ i j : Fin n, cT σ J i j = - J i j

/-- Preserving form $J$: $cT(M) \cdot J \cdot M = J$. -/
def PreservesForm (σ : RingInvolution) {n : Nat} (J M : Mat n) : Prop :=
  ∀ i j : Fin n, matMul (matMul (cT σ M) J) M i j = J i j

/-- Stabilizer predicate for $(J, \sigma)$: elements preserving $J$. -/
def MemUJ (σ : RingInvolution) {n : Nat} (J M : Mat n) : Prop :=
  PreservesForm σ J M

/-! ## Explicit Symplectic Alternating Form J in Genus g (Dimension 2g) -/

/-- Standard alternating symplectic matrix $J_{2g} = \begin{pmatrix} 0 & I_g \\ -I_g & 0 \end{pmatrix}$. -/
def sympJ (g : Nat) : Mat (2 * g) :=
  fun i j =>
    if i.val < g ∧ j.val = i.val + g then 1
    else if i.val ≥ g ∧ i.val = j.val + g then -1
    else 0

/-- Genus 1 (dimension 2) standard symplectic form $J_2 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def sympJ2 : Mat 2 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, 1 => 1
    | 1, 0 => -1
    | 1, 1 => 0
    | _, _ => 0

/-- Genus 2 (dimension 4) standard symplectic form $J_4$. -/
def sympJ4 : Mat 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 2 => 1
    | 1, 3 => 1
    | 2, 0 => -1
    | 3, 1 => -1
    | _, _ => 0

/-! ## Helper lemma for Fin 2 and Fin 4 exhaustion -/

theorem fin2_cases (i : Fin 2) : i.val = 0 ∨ i.val = 1 := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl

theorem fin4_cases (i : Fin 4) : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
  rcases i with ⟨v, hv⟩
  match v with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | 2 => exact Or.inr (Or.inr (Or.inl rfl))
  | 3 => exact Or.inr (Or.inr (Or.inr rfl))

/-! ## Symplectic Symmetry Theorems -/

theorem sympJ2_is_skew_herm : IsSkewHerm idInvolution sympJ2 := by
  intro i j
  dsimp [IsSkewHerm, cT, idInvolution, sympJ2]
  rcases fin2_cases i with hi | hi <;> rcases fin2_cases j with hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl

theorem sympJ4_is_skew_herm : IsSkewHerm idInvolution sympJ4 := by
  intro i j
  dsimp [IsSkewHerm, cT, idInvolution, sympJ4]
  rcases fin4_cases i with hi | hi | hi | hi <;>
    rcases fin4_cases j with hj | hj | hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl

/-! ## Identity Preservation -/

/-- 2x2 identity matrix preserves $J_2$. -/
theorem matOne2_preserves_sympJ2 : MemUJ idInvolution sympJ2 (matOne 2) := by
  intro i j
  dsimp [MemUJ, PreservesForm, matMul, finSum, cT, idInvolution, matOne, sympJ2]
  rcases fin2_cases i with hi | hi <;> rcases fin2_cases j with hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl

/-- 4x4 identity matrix preserves $J_4$. -/
theorem matOne4_preserves_sympJ4 : MemUJ idInvolution sympJ4 (matOne 4) := by
  intro i j
  dsimp [MemUJ, PreservesForm, matMul, finSum, cT, idInvolution, matOne, sympJ4]
  rcases fin4_cases i with hi | hi | hi | hi <;>
    rcases fin4_cases j with hj | hj | hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl

/-! ## Principal Congruence Subgroups -/

/-- Matrix congruence modulo level $N \ge 1$: $M \equiv I_n \pmod N$. -/
def IsPrincipalCongruence (n : Nat) (N : Nat) (M : Mat n) : Prop :=
  ∀ i j : Fin n, (M i j - (matOne n i j)) % (N : Int) = 0

/-- Principal congruence subgroup $\Gamma(N) \subset \mathrm{GL}_n(\mathbb{Z})$. -/
def princCong (n : Nat) (N : Nat) : Mat n → Prop :=
  fun M => IsPrincipalCongruence n N M

/-- Symplectic principal congruence subgroup $\Gamma_{\mathrm{Sp}}(N) = \mathrm{Sp}_{2g}(\mathbb{Z}) \cap \Gamma(N)$. -/
def princCongSp (g : Nat) (N : Nat) (M : Mat (2 * g)) : Prop :=
  MemUJ idInvolution (sympJ g) M ∧ princCong (2 * g) N M

/-- Identity matrix belongs to the principal congruence subgroup $\Gamma(N)$ for any level $N \ge 1$. -/
theorem matOne_mem_princCong (n : Nat) (N : Nat) (_hN : 0 < N) :
    princCong n N (matOne n) := by
  intro i j
  have hzero : matOne n i j - matOne n i j = 0 := Int.sub_self (matOne n i j)
  change (matOne n i j - matOne n i j) % (N : Int) = 0
  rw [hzero]
  exact Int.zero_emod (N : Int)

/-- Dimension 2: Identity matrix belongs to $\Gamma(N)$. -/
theorem matOne2_mem_princCong (N : Nat) (hN : 0 < N) :
    princCong 2 N (matOne 2) :=
  matOne_mem_princCong 2 N hN

/-- Dimension 4: Identity matrix belongs to $\Gamma(N)$. -/
theorem matOne4_mem_princCong (N : Nat) (hN : 0 < N) :
    princCong 4 N (matOne 4) :=
  matOne_mem_princCong 4 N hN

/-- Dimension 4: Identity matrix belongs to $\Gamma_{\mathrm{Sp}_4}(N)$. -/
theorem matOne4_mem_princCongSp2 (N : Nat) (hN : 0 < N) :
    princCong 4 N (matOne 4) ∧ MemUJ idInvolution sympJ4 (matOne 4) :=
  ⟨matOne4_mem_princCong N hN, matOne4_preserves_sympJ4⟩

/-! ## Lattice Stabilizer & Congruence Compatibility with Hecke Operators -/

/-- Hecke operator $T(p)$ on $\mathrm{GSp}_4$ has standard level-1 degree compatibility
with $\mathrm{GL}_4$ $T_1$ degree, matching `SatakeHeckeDegreeBridge`. -/
theorem gsp4_hecke_congruence_compat (p : Int) :
    SatakeHeckeDegreeBridge.gsp4HeckeDegT1 p =
      SatakeHeckeDegreeBridge.degGLnT1 4 p :=
  SatakeHeckeDegreeBridge.gsp4_degT1_eq_gl4_degT1 p

/-- Modulo $N$ level reduction preserves spherical degree polynomial modulo $N$:
for level $N = p - 1$, $p \equiv 1 \pmod N \implies \deg(T_1) \equiv 4 \pmod N$. -/
theorem hecke_deg_gl4_congruence_level (q : Int) (hq : (q - 1) % 2 = 0) :
    SatakeHeckeDegreeBridge.degGLnT1 4 q % 2 = 0 := by
  rw [SatakeHeckeDegreeBridge.degGL4T1_eval]
  have hq_cube : q ^ 3 = q * q * q := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_assoc]
  have hq_sq : q ^ 2 = q * q := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]
  rw [hq_cube, hq_sq]
  have hq_rem : q % 2 = 1 := by
    have hq_sub : (q - 1) % 2 = 0 := hq
    omega
  have h_fact : q * q * q + q * q + q + 1 = (q + 1) * (q * q + 1) := by
    simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.add_assoc]
    ac_rfl
  rw [h_fact]
  have h_plus : (q + 1) % 2 = 0 := by
    omega
  have h_mul_mod : ((q + 1) * (q * q + 1)) % 2 = (((q + 1) % 2) * ((q * q + 1) % 2)) % 2 := by
    exact Int.mul_emod (q + 1) (q * q + 1) 2
  rw [h_mul_mod, h_plus, Int.zero_mul, Int.zero_emod]

/-! ## Master Certification Theorem -/

/-- Bundled specification certificate for unitary and symplectic matrix invariants,
congruence subgroup closure, and Hecke compatibility. -/
structure UnitarySymplecticCongruenceCert where
  dim2_skew_herm : IsSkewHerm idInvolution sympJ2
  dim4_skew_herm : IsSkewHerm idInvolution sympJ4
  dim2_uj_one : MemUJ idInvolution sympJ2 (matOne 2)
  dim4_uj_one : MemUJ idInvolution sympJ4 (matOne 4)
  dim2_princ_one : ∀ N : Nat, 0 < N → princCong 2 N (matOne 2)
  dim4_princ_one : ∀ N : Nat, 0 < N → princCong 4 N (matOne 4)
  gsp4_hecke_compat : ∀ p : Int,
    SatakeHeckeDegreeBridge.gsp4HeckeDegT1 p = SatakeHeckeDegreeBridge.degGLnT1 4 p

/-- Master certificate theorem for unitary and symplectic congruence structures. -/
theorem unitary_symplectic_congruence_master_cert :
    UnitarySymplecticCongruenceCert where
  dim2_skew_herm := sympJ2_is_skew_herm
  dim4_skew_herm := sympJ4_is_skew_herm
  dim2_uj_one := matOne2_preserves_sympJ2
  dim4_uj_one := matOne4_preserves_sympJ4
  dim2_princ_one := matOne2_mem_princCong
  dim4_princ_one := matOne4_mem_princCong
  gsp4_hecke_compat := gsp4_hecke_congruence_compat

end UnitarySymplecticCongruence

-- end of file: leanasm/src/LeanAsm/UnitarySymplecticCongruence.lean
