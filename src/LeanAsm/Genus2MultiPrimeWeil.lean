-- Path: leanasm/src/LeanAsm/Genus2MultiPrimeWeil.lean
-- Multi-prime Frobenius and Weil Riemann Hypothesis certificates for genus-2 curve
-- C : y^2 = x^5 - x + 1 across good primes p in {7, 11, 13, 17, 19, 23}.
-- Max Column: 120 Columns

import LeanAsm.GSp4FunctorialityBridge

namespace LeanAsm.Genus2MultiPrimeWeil

open GSp4FunctorialityBridge

/-! ## Part 1: Quadratic Non-Squares and Field Operations -/

/-- Explicit non-square generating the quadratic extension F_{p^2} = F_p[u] / (u^2 - d). -/
def nonSquare (p : Nat) : Nat :=
  match p with
  | 7 => 3
  | 11 => 2
  | 13 => 2
  | 17 => 3
  | 19 => 2
  | 23 => 5
  | _ => 2

/-- Computable test checking whether `val` is a quadratic residue mod `p`. -/
def isSquareFp (p : Nat) (val : Nat) : Bool :=
  (List.range p).any (fun y => (y * y) % p == val)

/-- Number of square roots of `val` in `F_p`. -/
def sqCountFp (p : Nat) (val : Nat) : Nat :=
  if val == 0 then 1
  else if isSquareFp p val then 2
  else 0

/-- Multiplication in `F_{p^2} \cong F_p[u] / (u^2 - d)`. -/
def mulFp2 (p d : Nat) (x y : Nat × Nat) : Nat × Nat :=
  let (x0, x1) := x
  let (y0, y1) := y
  ((x0 * y0 + d * (x1 * y1)) % p, (x0 * y1 + x1 * y0) % p)

/-- Fifth power `x^5` in `F_{p^2}` via repeated squaring. -/
def pow5Fp2 (p d : Nat) (x : Nat × Nat) : Nat × Nat :=
  let x2 := mulFp2 p d x x
  let x4 := mulFp2 p d x2 x2
  mulFp2 p d x4 x

/-- Test whether `(w.1 + w.2 * u)` is a square in `F_{p^2}` via norm `N(w) = w_1^2 - d * w_2^2`. -/
def isSquareFp2 (p d : Nat) (w : Nat × Nat) : Bool :=
  let norm := (w.1 * w.1 + p * d - (d * ((w.2 * w.2) % p)) % p) % p
  isSquareFp p norm

/-- Number of square roots in `F_{p^2}`. -/
def sqCountFp2 (p d : Nat) (w : Nat × Nat) : Nat :=
  if w == (0, 0) then 1
  else if isSquareFp2 p d w then 2
  else 0

/-! ## Part 2: Point Counting on C : y^2 = x^5 - x + 1 -/

/-- Count affine points on `C / F_p`. -/
def countAffineFp (p : Nat) : Nat :=
  (List.range p).foldl (fun acc x =>
    let rhs := (x * x * x * x * x + p - (x % p) + 1) % p
    acc + sqCountFp p rhs) 0

/-- Projective point count `#C(F_p) = 1 + #AffinePoints(F_p)`. -/
def cardC1 (p : Nat) : Nat :=
  1 + countAffineFp p

/-- Count affine points on `C / F_{p^2}`. -/
def countAffineFp2 (p : Nat) : Nat :=
  let d := nonSquare p
  let elements : List (Nat × Nat) :=
    (List.range p).flatMap (fun a => (List.range p).map (fun b => (a, b)))
  elements.foldl (fun acc x =>
    let (x5r, x5i) := pow5Fp2 p d x
    let rhsr := (x5r + p - (x.1 % p) + 1) % p
    let rhsi := (x5i + p - (x.2 % p)) % p
    acc + sqCountFp2 p d (rhsr, rhsi)) 0

/-- Projective point count `#C(F_{p^2}) = 1 + #AffinePoints(F_{p^2})`. -/
def cardC2 (p : Nat) : Nat :=
  1 + countAffineFp2 p

/-! ## Part 3: Frobenius Trace and Degree-2 Trace Extraction -/

/-- Frobenius trace `a_p = p + 1 - #C(F_p)`. -/
def frobeniusTrace (p : Nat) : Int :=
  (p + 1 : Int) - (cardC1 p : Int)

/-- Degree-2 trace `b_p = (1/2) * (a_p^2 - (p^2 + 1 - #C(F_{p^2})))`. -/
def degree2Trace (p : Nat) : Int :=
  let ap := frobeniusTrace p
  let n2 := (cardC2 p : Int)
  (ap * ap - ((p * p + 1 : Int) - n2)) / 2

/-- Degree-4 Frobenius characteristic polynomial:
`P_frob(X) = X^4 - a_p X^3 + b_p X^2 - p a_p X + p^2`. -/
def frobPoly (p : Nat) (X : Int) : Int :=
  let ap := frobeniusTrace p
  let bp := degree2Trace p
  X ^ 4 - ap * X ^ 3 + bp * X ^ 2 - (p : Int) * ap * X + (p : Int) ^ 2

/-- Degree-4 Spin L-polynomial:
`L_spin(T) = 1 - a_p T + b_p T^2 - p a_p T^3 + p^2 T^4`. -/
def spinLPoly (p : Nat) (T : Int) : Int :=
  gsp4SpinEulerPoly (p : Int) (frobeniusTrace p) (degree2Trace p) T

/-- Cleared-denominator degree-5 SO(5) Standard Euler polynomial. -/
def standardEulerPoly (p : Nat) (T : Int) : Int :=
  gsp4StandardEulerPoly (p : Int) (frobeniusTrace p) (degree2Trace p) T

/-! ## Part 4: Bundled Multi-Prime Weil RH Certificate Record -/

/-- Bundled constructive certificate of Weil RH / Hasse-Weil bounds for genus 2. -/
structure Genus2WeilCert (p : Nat) : Prop where
  n1_eq : cardC1 p = match p with | 7 => 7 | 11 => 19 | 13 => 15 | 17 => 21 | 19 => 24 | 23 => 26 | _ => 0
  n2_eq : cardC2 p = match p with | 7 => 49 | 11 => 135 | 13 => 187 | 17 => 313 | 19 => 390 | 23 => 530 | _ => 0
  ap_eq : frobeniusTrace p = match p with | 7 => 1 | 11 => -7 | 13 => -1 | 17 => -3 | 19 => -4 | 23 => -2 | _ => 0
  bp_eq : degree2Trace p = match p with | 7 => 0 | 11 => 31 | 13 => 9 | 17 => 16 | 19 => 22 | 23 => 2 | _ => 0
  ap_weil : frobeniusTrace p * frobeniusTrace p ≤ 16 * (p : Int)
  bp_weil : degree2Trace p * degree2Trace p ≤ 36 * (p : Int) ^ 2
  disc_pos : 0 ≤ frobeniusTrace p * frobeniusTrace p - 4 * degree2Trace p + 8 * (p : Int)
  unit_circle_pos : 0 ≤ 2 * (p : Int) + degree2Trace p
  unit_circle_sq : 4 * (frobeniusTrace p * frobeniusTrace p) * (p : Int) ≤ (2 * (p : Int) + degree2Trace p) ^ 2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Certificate for p = 7. -/
theorem cert_p7 : Genus2WeilCert 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certificate for p = 11. -/
theorem cert_p11 : Genus2WeilCert 11 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certificate for p = 13. -/
theorem cert_p13 : Genus2WeilCert 13 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certificate for p = 17. -/
theorem cert_p17 : Genus2WeilCert 17 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certificate for p = 19. -/
theorem cert_p19 : Genus2WeilCert 19 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Certificate for p = 23. -/
theorem cert_p23 : Genus2WeilCert 23 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The list of good primes under test. -/
def goodPrimesList : List Nat := [7, 11, 13, 17, 19, 23]

/-- Bundled list theorem: all primes in `{7, 11, 13, 17, 19, 23}` satisfy Weil RH. -/
theorem genus2_multiprime_weil_certs :
    ∀ p ∈ goodPrimesList, Genus2WeilCert p := by
  intro p hp
  simp only [goodPrimesList, List.mem_cons, List.not_mem_nil] at hp
  rcases hp with rfl | hp
  · exact cert_p7
  rcases hp with rfl | hp
  · exact cert_p11
  rcases hp with rfl | hp
  · exact cert_p13
  rcases hp with rfl | hp
  · exact cert_p17
  rcases hp with rfl | hp
  · exact cert_p19
  rcases hp with rfl | hp
  · exact cert_p23
  cases hp

/-- Connection to GSp(4) -> SO(5) functoriality: standard Euler polynomial factors. -/
theorem multiprime_gsp4_so5_factorization (p : Nat) (T : Int) :
    standardEulerPoly p T = (1 - T) * gsp4StdQuarticCofactor (p : Int) (frobeniusTrace p) (degree2Trace p) T := by
  exact gsp4StandardEulerPoly_eq_one_sub_mul (p : Int) (frobeniusTrace p) (degree2Trace p) T

end LeanAsm.Genus2MultiPrimeWeil

-- end of file: leanasm/src/LeanAsm/Genus2MultiPrimeWeil.lean
