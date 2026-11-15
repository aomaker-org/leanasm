-- Path: leanasm/src/LeanAsm/EllipticModularityBridge.lean
-- GL(2) elliptic curve modularity bridge for conductor-11 E_{11a1} and cusp form f_{11}:
-- Eichler-Shimura Hecke-Frobenius trace equality (p <= 97), Hasse-Weil / Ramanujan bounds,
-- cleared-denominator local Euler-factor positivity, and Hecke multiplicativity.
-- Max Column: 120 Columns

import LeanAsm.FiniteFieldRH
import LeanAsm.WeilZetaBridge

namespace EllipticModularityBridge

open FiniteFieldRH
open WeilZetaBridge

-- =============================================================================
-- Part 1: Exact Truncated Power Series for f_{11}(τ) = η(τ)^2 η(11τ)^2
-- =============================================================================

/-- Componentwise polynomial addition over `ℤ`. -/
def polyAdd (xs ys : List Int) : List Int :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' => (x + y) :: polyAdd xs' ys'

/-- Truncated subtraction `xs - ys` preserving the length of `xs`. -/
def zipSub (xs ys : List Int) : List Int :=
  match xs, ys with
  | [], _ => []
  | x :: xs', [] => x :: xs'
  | x :: xs', y :: ys' => (x - y) :: zipSub xs' ys'

/-- Multiply a degree-truncated coefficient list `cs` by `(1 - q^k)`. -/
def mulOneMinusPow (k : Nat) (cs : List Int) : List Int :=
  zipSub cs (List.replicate k 0 ++ cs)

/-- Multiply `cs` sequentially by `∏_{n = lo}^{lo + count - 1} (1 - q^n)^2`. -/
def factorSeq (lo count : Nat) (cs : List Int) : List Int :=
  match count with
  | 0 => cs
  | c + 1 =>
    let cs' := mulOneMinusPow lo (mulOneMinusPow lo cs)
    factorSeq (lo + 1) c cs'

/-- Multiply `cs` sequentially by `∏_{j = m}^{m + count - 1} (1 - q^{11 j})^2`. -/
def factorElev (m count : Nat) (cs : List Int) : List Int :=
  match count with
  | 0 => cs
  | c + 1 =>
    let k := 11 * m
    let cs' := mulOneMinusPow k (mulOneMinusPow k cs)
    factorElev (m + 1) c cs'

/-- Constant unit polynomial `1` truncated to length `100` (degrees `0..99`). -/
def init100 : List Int :=
  1 :: List.replicate 99 0

/-- Stage 1 of `∏_{n=1}^{100} (1 - q^n)^2` (`n = 1..10`) mod `q^100`. -/
def etaStage1 : List Int := factorSeq 1 10 init100
def etaStage2 : List Int := factorSeq 11 10 etaStage1
def etaStage3 : List Int := factorSeq 21 10 etaStage2
def etaStage4 : List Int := factorSeq 31 10 etaStage3
def etaStage5 : List Int := factorSeq 41 10 etaStage4
def etaStage6 : List Int := factorSeq 51 10 etaStage5
def etaStage7 : List Int := factorSeq 61 10 etaStage6
def etaStage8 : List Int := factorSeq 71 10 etaStage7
def etaStage9 : List Int := factorSeq 81 10 etaStage8
def etaStage10 : List Int := factorSeq 91 10 etaStage9

/-- Exact Fourier coefficients `[c_0, c_1, ..., c_100]` of
`f_{11}(τ) = q ∏_{n=1}^{100} (1 - q^n)^2 ∏_{m=1}^{9} (1 - q^{11m})^2` mod `q^101`. -/
def f11Coeffs : List Int :=
  0 :: factorElev 1 9 etaStage10

/-- Explicit literal table `[c_0, c_1, ..., c_100]` certified equal to `f11Coeffs`. -/
def f11TableLit : List Int :=
  [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0,
   2, 2, -2, -1, 0, -4, -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4,
   0, -8, -4, -6, 2, -2, 2, 8, 4, -3, 8, 2, 8, -6, -10, 1, 0, 0, 0, 5,
   -2, 12, -14, 4, -8, 4, 2, -7, -4, 1, 4, -3, 0, 4, -6, 4, 0, -2, 8, -10,
   -4, 1, 16, -6, 4, -2, 12, 0, 0, 15, 4, -8, -2, -7, -16, 0, -8, -7, 6, -2,
   -8]

private theorem etaStage1_eq :
    etaStage1 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 2, -2, -2, 3, 0, 8, 2, 2, -4,
       -8, -4, -1, -8, -5, 2, 3, 14, 9, 18, 6, 0, -8, -4, -24, -24, -15, -14, 5, 8,
       25, 26, 31, 20, 25, -12, -22, -32, -36, -32, -25, -10, 3, 22, 28, 64, 28, 22, 3, -10,
       -25, -32, -36, -32, -22, -12, 25, 20, 31, 26, 25, 8, 5, -14, -15, -24, -24, -4, -8, 0,
       6, 18, 9, 14, 3, 2, -5, -8, -1, -4, -8, -4, 2, 2, 8, 0, 3, -2, -2, 2] := by
  decide

private theorem etaStage2_eq :
    etaStage2 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 2, -2, -6, -1, 2, 8, 4, 0, 0, -5, -2, -4, -2, -2, 4, 4, 6, 4, 6,
       -2, -2, 1, -4, -9, -14, -9, 2, 7, 6, 5, 4, 1, -4, -4, -2, -1, 2, 11, 8,
       19, 6, 9, 6, 5, -8, -20, -30, -20, -20, -13, -8, -3, 2, -5, -4, -1, 4, 7, 28,
       24, 40, 33, 46, 32, 46, 22, 8, -18, -26, -51, -58, -63, -66, -62, -60, -66, -56, -49, -32] := by
  dsimp [etaStage2]; rw [etaStage1_eq]; decide

private theorem etaStage3_eq :
    etaStage3 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 4, -2, -2, -2, 0, 8, 2, 0, -2,
       -10, -4, -4, -4, 1, 4, 2, 6, 8, 6, 4, 0, -1, -4, -6, -6, -6, -4, 0, -6,
       0, 0, 9, 2, 8, 2, -3, 12, 11, 10, 4, -4, -12, -12, -20, -14, -13, -14, -1, 8,
       14, 14, 19, 18, 11, 4, 0, -6, -4, -6, -14, -16, -15, -6, -11, 6, 5, 2, 15, 24] := by
  dsimp [etaStage3]; rw [etaStage2_eq]; decide

private theorem etaStage4_eq :
    etaStage4 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 2, -2, -4, 1, 0, 6, 2, 4, -2, -4, -2, -3, -6, 0, 8, 4, 6, 6, 4,
       2, -4, -2, -4, -4, -8, -12, -4, 0, -6, -1, 4, 6, 8, 10, 6, 2, 4, 8, 6,
       3, -6, -3, -6, -12, -6, -11, -2, -3, 8, -1, -2, -2, -4, -14, -8, -1, 6, 15, 18] := by
  dsimp [etaStage4]; rw [etaStage3_eq]; decide

private theorem etaStage5_eq :
    etaStage5 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 4, -1, -6, 0, 4, 8, 2, 2, -4,
       -6, -6, -4, -6, 2, 6, -2, 6, 6, 4, 1, 0, -2, 0, -6, -8, -8, -6, 2, 0,
       1, 2, 6, 8, 8, 8, 0, 6, 6, 4, 2, -8, -6, -8, -8, -4, -10, -8, -8, -4] := by
  dsimp [etaStage5]; rw [etaStage4_eq]; decide

private theorem etaStage6_eq :
    etaStage6 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 2, 1, -2, 0, 2, 2, 0, 0, -2,
       0, 0, -2, -6, 2, 2, 2, 2, 2, -4, -7, -2, -4, -2, 0, 6, 2, 4, 8, 10,
       3, -2, -2, 0, -8, -6, -10, -4, 0, -2, 0, 0, 6, 4, 8, 6, 0, 6, 6, 2] := by
  dsimp [etaStage6]; rw [etaStage5_eq]; decide

private theorem etaStage7_eq :
    etaStage7 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 2, 1, -2, 0, 2, 2, 0, 0, -2,
       0, -2, 0, -2, 2, 0, -4, 0, 0, -2, -1, 4, -2, -2, 0, 2, 6, 0, 4, 2,
       -5, -4, -4, -2, -2, 8, 0, 6, 6, 8, 2, -4, -2, -4, -8, -8, -10, -4, 0, -4] := by
  dsimp [etaStage7]; rw [etaStage6_eq]; decide

private theorem etaStage8_eq :
    etaStage8 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 2, 1, -2, 0, 2, 2, 0, 0, -2,
       0, -2, 0, -2, 2, 0, -4, 0, 0, -2, -1, 2, 0, 2, 0, 0, 0, -2, 2, 4,
       1, 2, -2, -2, -2, 4, 4, 2, 2, 0, -6, -6, -4, -6, -2, 6, 0, 6, 6, 6] := by
  dsimp [etaStage8]; rw [etaStage7_eq]; decide

private theorem etaStage9_eq :
    etaStage9 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 2, 1, -2, 0, 2, 2, 0, 0, -2,
       0, -2, 0, -2, 2, 0, -4, 0, 0, -2, -1, 2, 0, 2, 0, 0, 0, -2, 2, 4,
       1, 0, 0, 2, -2, 2, -2, 0, 0, 2, 0, 0, -2, -6, -2, 2, 4, 2, 2, -2] := by
  dsimp [etaStage9]; rw [etaStage8_eq]; decide

private theorem etaStage10_eq :
    etaStage10 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0, 0, -2,
       -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -2, 2, 0, -2, 0,
       -4, 0, 0, 0, 1, -2, 0, 0, 2, 0, 2, 2, 1, -2, 0, 2, 2, 0, 0, -2,
       0, -2, 0, -2, 2, 0, -4, 0, 0, -2, -1, 2, 0, 2, 0, 0, 0, -2, 2, 4,
       1, 0, 0, 2, -2, 2, -2, 0, 0, 2, 0, -2, 0, -2, -2, 0, -2, 0, 0, 0] := by
  dsimp [etaStage10]; rw [etaStage9_eq]; decide

/-- Kernel-certified exact expansion of `f11Coeffs` up to `q^100`. -/
theorem f11Coeffs_eq_table : f11Coeffs = f11TableLit := by
  dsimp [f11Coeffs]
  rw [etaStage10_eq]
  decide

/-- The `n`-th Fourier / Hecke coefficient `c_n(f_{11})` of the weight-2 cusp form
`f_{11}(τ) = η(τ)^2 η(11τ)^2 ∈ S_2(Γ_0(11))` (for `0 <= n <= 100`). -/
def heckeCoeff11 (n : Nat) : Int :=
  f11Coeffs.getD n 0

theorem heckeCoeff11_eq_table (n : Nat) :
    heckeCoeff11 n = f11TableLit.getD n 0 := by
  dsimp [heckeCoeff11]
  rw [f11Coeffs_eq_table]

theorem heckeCoeff11_bad_11 : heckeCoeff11 11 = 1 := by
  rw [heckeCoeff11_eq_table]
  decide

-- =============================================================================
-- Part 2: Point Counting & Frobenius Trace for E_{11a1}
-- =============================================================================

/-- Affine Weierstrass congruence for `E_{11a1} : y^2 + y ≡ x^3 - x^2 - 10x - 20 (mod p)`,
expressed purely in nonnegative `Nat` arithmetic by moving negative terms to the LHS. -/
def isPointOnE11a1 (p x y : Nat) : Bool :=
  (y * y + y + x * x + 10 * x + 20) % p == (x * x * x) % p

/-- Signed-integer equivalence showing `isPointOnE11a1 p x y = true` holds iff
`(y^2 + y : Int) % p = (x^3 - x^2 - 10x - 20 : Int) % p` (via `(a - b) % p = 0`). -/
theorem isPointOnE11a1_iff_int_diff (p x y : Nat) :
    isPointOnE11a1 p x y = true ↔
      (((y : Int) * y + y) - ((x : Int) * x * x - x * x - 10 * x - 20)) % (p : Int) = 0 := by
  dsimp [isPointOnE11a1]
  rw [beq_iff_eq]
  have hdiff :
      (((y : Int) * y + y) - ((x : Int) * x * x - x * x - 10 * x - 20)) =
        ((y * y + y + x * x + 10 * x + 20 : Nat) : Int) - ((x * x * x : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    omega
  rw [hdiff]
  constructor
  · intro hmod
    have heq :
        (((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int)) =
          (((x * x * x : Nat) : Int) % (p : Int)) := by
      exact_mod_cast hmod
    rw [Int.sub_emod, heq, Int.sub_self, Int.zero_emod]
  · intro hzero
    by_cases hp : p = 0
    · subst hp
      simp at hzero ⊢
      omega
    · have hppos : (0 : Int) < (p : Int) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hp)
      have ha_nonneg :
          0 ≤ ((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int) :=
        Int.emod_nonneg _ (Int.ne_of_gt hppos)
      have hb_nonneg :
          0 ≤ ((x * x * x : Nat) : Int) % (p : Int) :=
        Int.emod_nonneg _ (Int.ne_of_gt hppos)
      have ha_lt :
          ((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int) < (p : Int) :=
        Int.emod_lt_of_pos _ hppos
      have hb_lt :
          ((x * x * x : Nat) : Int) % (p : Int) < (p : Int) :=
        Int.emod_lt_of_pos _ hppos
      rw [Int.sub_emod] at hzero
      have hsub_eq :
          (((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int) -
            ((x * x * x : Nat) : Int) % (p : Int)) = 0 := by
        by_cases hneg :
            ((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int) -
              ((x * x * x : Nat) : Int) % (p : Int) < 0
        · rw [← Int.add_emod_right _ (p : Int), Int.emod_eq_of_lt (by omega) (by omega)] at hzero
          omega
        · rw [Int.emod_eq_of_lt (by omega) (by omega)] at hzero
          exact hzero
      have hcast :
          (((y * y + y + x * x + 10 * x + 20 : Nat) : Int) % (p : Int)) =
            (((x * x * x : Nat) : Int) % (p : Int)) := by omega
      exact_mod_cast hcast

/-- Balanced binary tree summation over `[lo, lo + len)` avoiding deep linear WHNF chains. -/
def sumTree (lo len fuel : Nat) (f : Nat → Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match len with
    | 0 => 0
    | 1 => f lo
    | _ + 2 =>
      let mid := len / 2
      sumTree lo mid fuel' f + sumTree (lo + mid) (len - mid) fuel' f

private theorem range_foldl_add (f : Nat → Nat) (a b : Nat) :
    (List.range (a + b)).foldl (fun acc k => acc + f k) 0 =
      (List.range a).foldl (fun acc k => acc + f k) 0 +
        (List.range b).foldl (fun acc k => acc + f (a + k)) 0 := by
  induction b with
  | zero => rw [Nat.add_zero, List.range_zero]; rfl
  | succ b' ihb =>
    rw [← Nat.add_assoc, List.range_succ, List.foldl_append, ihb]
    rw [List.range_succ, List.foldl_append]
    dsimp [List.foldl]
    rw [Nat.add_assoc]

/-- Equivalence between balanced `sumTree` and linear `List.range` accumulation. -/
theorem sumTree_eq_range_foldl (lo len fuel : Nat) (f : Nat → Nat) (hlen : len ≤ fuel) :
    sumTree lo len fuel f =
      (List.range len).foldl (fun acc k => acc + f (lo + k)) 0 := by
  induction fuel generalizing lo len with
  | zero =>
    have h0 : len = 0 := Nat.le_zero.mp hlen
    subst h0
    rfl
  | succ fuel' ih =>
    match len with
    | 0 => rfl
    | 1 =>
      show f lo = 0 + f (lo + 0)
      rw [Nat.zero_add, Nat.add_zero]
    | k + 2 =>
      have hmid_le : (k + 2) / 2 ≤ fuel' := by
        have hlt : (k + 2) / 2 < k + 2 := Nat.div_lt_self (Nat.succ_pos _) (by decide)
        exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hlen)
      have hrem_le : (k + 2) - (k + 2) / 2 ≤ fuel' := by
        have hpos : 0 < (k + 2) / 2 := Nat.div_pos (Nat.le_add_left 2 k) (by decide)
        have hlt : (k + 2) - (k + 2) / 2 < k + 2 := Nat.sub_lt (Nat.succ_pos _) hpos
        exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hlen)
      dsimp [sumTree]
      rw [ih lo ((k + 2) / 2) hmid_le, ih (lo + (k + 2) / 2) ((k + 2) - (k + 2) / 2) hrem_le]
      have hfun :
          (fun acc j => acc + f (lo + (k + 2) / 2 + j)) =
            (fun acc j => acc + f (lo + ((k + 2) / 2 + j))) := by
        funext acc j
        rw [Nat.add_assoc]
      have hsplit : (k + 2) / 2 + ((k + 2) - (k + 2) / 2) = k + 2 :=
        Nat.add_sub_cancel' (Nat.div_le_self (k + 2) 2)
      rw [hfun, ← range_foldl_add (fun j => f (lo + j)) ((k + 2) / 2) ((k + 2) - (k + 2) / 2), hsplit]

/-- Number of affine solutions `(x, y) ∈ F_p × F_p` to `y^2 + y ≡ x^3 - x^2 - 10x - 20 (mod p)`
plus `1` for the point at infinity `O`: `#E_{11a1}(F_p)`. -/
def ec11a1PointCount (p : Nat) : Nat :=
  let c2 := p - 1 % p
  let c1 := p - 10 % p
  let c0 := p - 20 % p
  1 + sumTree 0 p p (fun x =>
    let rhs := (x * x * x + c2 * (x * x) + c1 * x + c0) % p
    sumTree 0 p p (fun y => if (y * y + y) % p == rhs then 1 else 0))

/-- For any `p > 0`, the optimized RHS congruence in `ec11a1PointCount p` matches `isPointOnE11a1 p x y`. -/
theorem ec11a1_point_cond_eq (p x y : Nat) (hp : 0 < p) :
    ((y * y + y) % p == (x * x * x + (p - 1 % p) * (x * x) + (p - 10 % p) * x + (p - 20 % p)) % p) =
      isPointOnE11a1 p x y := by
  dsimp [isPointOnE11a1]
  have h1 : 1 % p < p := Nat.mod_lt 1 hp
  have h10 : 10 % p < p := Nat.mod_lt 10 hp
  have h20 : 20 % p < p := Nat.mod_lt 20 hp
  let sub := 1 % p * (x * x) + 10 % p * x + 20 % p
  let csub := (p - 1 % p) * (x * x) + (p - 10 % p) * x + (p - 20 % p)
  have hcsub_add : csub + sub = p * (x * x + x + 1) := by
    have ha : (p - 1 % p) * (x * x) + 1 % p * (x * x) = p * (x * x) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h1)]
    have hb : (p - 10 % p) * x + 10 % p * x = p * x := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h10)]
    have hc : (p - 20 % p) + 20 % p = p := Nat.sub_add_cancel (Nat.le_of_lt h20)
    dsimp [sub, csub]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have hsub_mod : sub % p = (x * x + 10 * x + 20) % p := by
    dsimp [sub]
    rw [Nat.add_mod (1 % p * (x * x) + 10 % p * x) (20 % p)]
    rw [Nat.mod_mod 20 p]
    rw [Nat.add_mod (1 % p * (x * x)) (10 % p * x)]
    rw [Nat.mul_mod (1 % p) (x * x), Nat.mod_mod 1 p, ← Nat.mul_mod 1 (x * x), Nat.one_mul]
    rw [Nat.mul_mod (10 % p) x, Nat.mod_mod 10 p, ← Nat.mul_mod 10 x]
    rw [← Nat.add_mod (x * x) (10 * x) p, ← Nat.add_mod (x * x + 10 * x) 20 p]
  have hzero_mod : (x * x + 10 * x + 20 + csub) % p = 0 := by
    rw [Nat.add_mod (x * x + 10 * x + 20) csub p, ← hsub_mod, ← Nat.add_mod sub csub p]
    rw [Nat.add_comm sub csub, hcsub_add]
    exact Nat.mul_mod_right p _
  have hrhs_cancel :
      (x * x * x + csub + (x * x + 10 * x + 20)) % p = (x * x * x) % p := by
    rw [Nat.add_assoc (x * x * x) csub _, Nat.add_comm csub _, Nat.add_mod]
    rw [hzero_mod, Nat.add_zero, Nat.mod_mod]
  have hrhs_assoc :
      x * x * x + (p - 1 % p) * (x * x) + (p - 10 % p) * x + (p - 20 % p) = x * x * x + csub := by
    dsimp [csub]; omega
  rw [hrhs_assoc]
  have hlhs_assoc : y * y + y + x * x + 10 * x + 20 = y * y + y + (x * x + 10 * x + 20) := by omega
  rw [hlhs_assoc]
  apply Bool.eq_iff_iff.mpr
  constructor <;> intro heq <;> rw [beq_iff_eq] at heq ⊢
  · calc (y * y + y + (x * x + 10 * x + 20)) % p
        = ((y * y + y) % p + (x * x + 10 * x + 20) % p) % p := Nat.add_mod _ _ p
      _ = ((x * x * x + csub) % p + (x * x + 10 * x + 20) % p) % p := by rw [heq]
      _ = (x * x * x + csub + (x * x + 10 * x + 20)) % p := (Nat.add_mod _ _ p).symm
      _ = (x * x * x) % p := hrhs_cancel
  · calc (y * y + y) % p
        = ((y * y + y) % p + 0) % p := by rw [Nat.add_zero, Nat.mod_mod]
      _ = ((y * y + y) % p + (x * x + 10 * x + 20 + csub) % p) % p := by rw [hzero_mod]
      _ = (y * y + y + (x * x + 10 * x + 20 + csub)) % p := (Nat.add_mod _ _ p).symm
      _ = ((y * y + y + (x * x + 10 * x + 20)) + csub) % p := by rw [Nat.add_assoc (y * y + y)]
      _ = ((y * y + y + (x * x + 10 * x + 20)) % p + csub % p) % p := Nat.add_mod _ _ p
      _ = ((x * x * x) % p + csub % p) % p := by rw [heq]
      _ = (x * x * x + csub) % p := (Nat.add_mod _ _ p).symm

/-- Frobenius trace `a_p(E_{11a1}) = p + 1 - #E_{11a1}(F_p)`. -/
def ec11a1FrobTrace (p : Nat) : Int :=
  (p : Int) + 1 - (ec11a1PointCount p : Int)

/-- All `24` good primes `p <= 97` for conductor `11` (`p ≠ 11`). -/
def goodPrimes97 : List Nat :=
  [2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- Exact projective point counts `#E_{11a1}(F_p)` for all `24` good primes `p <= 97`. -/
def ec11a1Counts97Lit : List Nat :=
  [5, 5, 5, 10, 10, 20, 20, 25, 30, 25, 35, 50, 50, 40, 60, 55, 50, 75, 75, 70, 90, 90, 75, 105]

/-- Kernel-certified batch point counts `#E_{11a1}(F_p)` across all `24` good primes `p <= 97`. -/
theorem ec11a1_point_counts_97 :
    goodPrimes97.map ec11a1PointCount = ec11a1Counts97Lit := by
  decide

private theorem forall_mem_of_map_eq {α β : Type} (f : α → β) (P : α → β → Bool) :
    ∀ (ps : List α) (cs : List β), ps.map f = cs →
      (ps.zip cs).all (fun kv => P kv.1 kv.2) = true →
      ∀ x ∈ ps, P x (f x) = true
  | [], _, _, _, _, hx => by cases hx
  | _ :: _, [], hmap, _, _, _ => by cases hmap
  | _ :: as, _ :: cs, hmap, hall, x, hx => by
    rw [List.map_cons] at hmap
    injection hmap with hfa hrest
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    rcases List.mem_cons.mp hx with rfl | hmem
    · rw [hfa]; exact hall.1
    · exact forall_mem_of_map_eq f P as cs hrest hall.2 x hmem

/-- `Z/5Z`-torsion divisibility (`#E_{11a1}(F_p) ≡ 0 (mod 5)`) across all `24` good primes `p <= 97`. -/
theorem ec11a1_five_torsion_97 :
    ∀ p ∈ goodPrimes97, ec11a1PointCount p % 5 = 0 := by
  have hall : (goodPrimes97.zip ec11a1Counts97Lit).all (fun kv => kv.2 % 5 == 0) = true := by
    decide
  intro p hp
  have hb := forall_mem_of_map_eq ec11a1PointCount (fun _ c => c % 5 == 0)
    goodPrimes97 ec11a1Counts97Lit ec11a1_point_counts_97 hall p hp
  exact beq_iff_eq.mp hb

-- =============================================================================
-- Part 3: Eichler-Shimura Hecke-Frobenius Trace Equality (p <= 97)
-- =============================================================================

/-- Eichler-Shimura Hecke-Frobenius trace equality for `E_{11a1}` and `f_{11}` across all `24`
good primes `p <= 97` (`c_p(f_{11}) = p + 1 - #E_{11a1}(F_p)`), plus bad-reduction split
multiplicative coefficient `c_{11}(f_{11}) = 1`. -/
theorem eichler_shimura_trace_eq_11a1 :
    (∀ p ∈ goodPrimes97, heckeCoeff11 p = ec11a1FrobTrace p) ∧ heckeCoeff11 11 = 1 := by
  refine ⟨?_, heckeCoeff11_bad_11⟩
  have hall :
      (goodPrimes97.zip ec11a1Counts97Lit).all
        (fun kv => decide (f11TableLit.getD kv.1 0 = (kv.1 : Int) + 1 - (kv.2 : Int))) = true := by
    decide
  intro p hp
  have hb := forall_mem_of_map_eq ec11a1PointCount
    (fun q c => decide (f11TableLit.getD q 0 = (q : Int) + 1 - (c : Int)))
    goodPrimes97 ec11a1Counts97Lit ec11a1_point_counts_97 hall p hp
  rw [heckeCoeff11_eq_table, ec11a1FrobTrace]
  exact of_decide_eq_true hb

-- =============================================================================
-- Part 4: GL(2) Ramanujan-Petersson Temperedness & Euler-Factor Positivity
-- =============================================================================

/-- Reciprocal `GL(2)` local Euler polynomial `L_p(E, T) = 1 - a_p T + p T^2`. -/
def gl2EulerPoly (p : Int) (ap T : Int) : Int :=
  1 - ap * T + p * T ^ 2

/-- Homogenized `GL(2)` local Euler form evaluating `T = u / v` with cleared denominator `v^2`:
`v^2 L_p(E, u / v) = v^2 - a_p u v + p u^2`. -/
def gl2EulerHomog (p : Int) (ap u v : Int) : Int :=
  v ^ 2 - ap * u * v + p * u ^ 2

private theorem int_pow2_em (x : Int) : x ^ 2 = x * x := by
  simp [Int.pow_succ, Int.pow_zero]

private theorem int_sq_nonneg_em (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem int_sq_pos_of_ne_em (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  by_cases hp : 0 < x
  · exact Int.mul_pos hp hp
  · have hn : x < 0 := by omega
    have hnn : 0 < -x := by omega
    have hm : 0 < (-x) * (-x) := Int.mul_pos hnn hnn
    have heq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    omega

/-- Algebraic square-completion identity for the homogenized `GL(2)` local Euler factor:
`4 (v^2 - a_p u v + p u^2) = (2v - a_p u)^2 + (4p - a_p^2) u^2`. -/
theorem gl2_euler_quad_identity (p ap u v : Int) :
    4 * gl2EulerHomog p ap u v = (2 * v - ap * u) ^ 2 + (4 * p - ap ^ 2) * u ^ 2 := by
  dsimp [gl2EulerHomog]
  rw [int_pow2_em v, int_pow2_em u, int_pow2_em (2 * v - ap * u), int_pow2_em ap]
  have h1 : (2 * v - ap * u) * (2 * v - ap * u) =
      4 * (v * v) - 4 * (ap * u * v) + (ap * ap) * (u * u) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have ha : (ap * u) * (2 * v) = 2 * (ap * u * v) := by ac_rfl
    have hb : (2 * v) * (ap * u) = 2 * (ap * u * v) := by ac_rfl
    have hc : (ap * u) * (ap * u) = (ap * ap) * (u * u) := by ac_rfl
    have hd : (2 * v) * (2 * v) = 4 * (v * v) := by ac_rfl
    omega
  have h2 : (4 * p - ap * ap) * (u * u) = 4 * (p * (u * u)) - (ap * ap) * (u * u) := by
    rw [Int.sub_mul]
    have ha : (4 * p) * (u * u) = 4 * (p * (u * u)) := by ac_rfl
    omega
  rw [h1, h2]
  omega

/-- Any integer trace `a_p` obeying strict Ramanujan temperedness `a_p^2 < 4p` yields strictly
positive cleared-denominator `GL(2)` Euler factors `0 < v^2 - a_p u v + p u^2` for all `v > 0`. -/
theorem gl2_euler_homog_pos_of_ramanujan (p ap u v : Int)
    (hram : ap ^ 2 < 4 * p) (hv : 0 < v) :
    0 < gl2EulerHomog p ap u v := by
  have hid := gl2_euler_quad_identity p ap u v
  have hsq1 : 0 ≤ (2 * v - ap * u) ^ 2 := by
    rw [int_pow2_em]
    exact int_sq_nonneg_em _
  have hdisc : 0 < 4 * p - ap ^ 2 := by omega
  by_cases hu : u = 0
  · subst hu
    have h4v : 0 < 4 * gl2EulerHomog p ap 0 v := by
      rw [hid]
      have h0 : (4 * p - ap ^ 2) * (0 : Int) ^ 2 = 0 := by
        rw [Int.zero_pow (by decide : 2 ≠ 0), Int.mul_zero]
      have hv2 : 0 < (2 * v - ap * 0) ^ 2 := by
        rw [Int.mul_zero, Int.sub_zero, int_pow2_em]
        exact int_sq_pos_of_ne_em (2 * v) (by omega)
      omega
    omega
  · have hu2 : 0 < u ^ 2 := by
      rw [int_pow2_em]
      exact int_sq_pos_of_ne_em u hu
    have hterm2 : 0 < (4 * p - ap ^ 2) * u ^ 2 := Int.mul_pos hdisc hu2
    have h4 : 0 < 4 * gl2EulerHomog p ap u v := by
      rw [hid]
      omega
    omega

/-- Hasse-Weil / Ramanujan-Petersson temperedness (`a_p^2 < 4p` and `a_p^2 <= 4p`) and
cleared-denominator local `GL(2)` Euler-factor positivity across all `24` good primes `p <= 97`
of `E_{11a1}`. -/
theorem hasse_weil_ramanujan_11a1_certs :
    (∀ p ∈ goodPrimes97, ec11a1FrobTrace p ^ 2 ≤ 4 * (p : Int)) ∧
    (∀ p ∈ goodPrimes97, ec11a1FrobTrace p ^ 2 < 4 * (p : Int)) ∧
    (∀ p ∈ goodPrimes97, ∀ u v : Int, 0 < v →
      0 < gl2EulerHomog (p : Int) (ec11a1FrobTrace p) u v) := by
  have hstrict : ∀ p ∈ goodPrimes97, ec11a1FrobTrace p ^ 2 < 4 * (p : Int) := by
    have hall :
        (goodPrimes97.zip ec11a1Counts97Lit).all
          (fun kv => ((kv.1 : Int) + 1 - (kv.2 : Int)) ^ 2 < 4 * (kv.1 : Int)) = true := by
      decide
    intro p hp
    have hb := forall_mem_of_map_eq ec11a1PointCount
      (fun q c => decide (((q : Int) + 1 - (c : Int)) ^ 2 < 4 * (q : Int)))
      goodPrimes97 ec11a1Counts97Lit ec11a1_point_counts_97 hall p hp
    exact of_decide_eq_true hb
  refine ⟨fun p hp => Int.le_of_lt (hstrict p hp), hstrict, ?_⟩
  intro p hp u v hv
  exact gl2_euler_homog_pos_of_ramanujan (p : Int) (ec11a1FrobTrace p) u v (hstrict p hp) hv

-- =============================================================================
-- Part 5: Hecke Algebra Multiplicativity & Prime-Square Relation (n <= 100)
-- =============================================================================

/-- Boolean check verifying `c_{m*n}(f_{11}) = c_m(f_{11}) * c_n(f_{11})` on `f11TableLit`
for all `1 <= m, n` with `m * n <= 100` and `gcd m n = 1`. -/
def checkCoprimeHecke100 (m n : Nat) : Bool :=
  if m * n ≤ 100 ∧ Nat.gcd m n = 1 then
    decide (f11TableLit.getD (m * n) 0 = f11TableLit.getD m 0 * f11TableLit.getD n 0)
  else true

private theorem checkCoprimeHecke100_range :
    (List.range 101).all
      (fun m => (List.range 101).all (fun n => checkCoprimeHecke100 m n)) = true := by
  decide

private theorem mem_range_of_le {k N : Nat} (hk : k ≤ N) : k ∈ List.range (N + 1) :=
  List.mem_range.mpr (Nat.lt_succ_of_le hk)

/-- Good primes `p` whose squares satisfy `p^2 <= 100`: `{2, 3, 5, 7}`. -/
def goodSqPrimes100 : List Nat := [2, 3, 5, 7]

/-- Hecke eigenvalue algebra certificates for `f_{11} ∈ S_2(Γ_0(11))`:
1. Normalization `c_1(f_{11}) = 1`.
2. Coprime multiplicativity `c_{mn}(f_{11}) = c_m(f_{11}) c_n(f_{11})` for all
   `1 <= m, n` with `m * n <= 100` and `gcd(m, n) = 1`.
3. Prime-square Hecke relation `c_{p^2}(f_{11}) = c_p(f_{11})^2 - p` for good primes `p ∈ {2, 3, 5, 7}`. -/
theorem hecke_multiplicativity_11a1_certs :
    heckeCoeff11 1 = 1 ∧
    (∀ m n : Nat, 1 ≤ m → 1 ≤ n → m * n ≤ 100 → Nat.gcd m n = 1 →
      heckeCoeff11 (m * n) = heckeCoeff11 m * heckeCoeff11 n) ∧
    (∀ p ∈ goodSqPrimes100, heckeCoeff11 (p * p) = heckeCoeff11 p ^ 2 - (p : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [heckeCoeff11_eq_table]
    decide
  · intro m n hm hn hmn hgcd
    have hm100 : m ≤ 100 := by
      have : m ≤ m * n := Nat.le_mul_of_pos_right m hn
      omega
    have hn100 : n ≤ 100 := by
      have : n ≤ m * n := Nat.le_mul_of_pos_left n hm
      omega
    have h1 := List.all_eq_true.mp checkCoprimeHecke100_range m (mem_range_of_le hm100)
    have h2 := List.all_eq_true.mp h1 n (mem_range_of_le hn100)
    dsimp [checkCoprimeHecke100] at h2
    simp only [hmn, hgcd, and_self, ↓reduceIte] at h2
    simp only [heckeCoeff11_eq_table]
    exact of_decide_eq_true h2
  · have hall :
        goodSqPrimes100.all
          (fun p => decide (f11TableLit.getD (p * p) 0 = f11TableLit.getD p 0 ^ 2 - (p : Int))) = true := by
      decide
    intro p hp
    have hb := List.all_eq_true.mp hall p hp
    simp only [heckeCoeff11_eq_table]
    exact of_decide_eq_true hb

end EllipticModularityBridge
-- end of file: leanasm/src/LeanAsm/EllipticModularityBridge.lean
