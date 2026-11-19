-- Path: leanasm/src/LeanAsm/Genus2WeilGSp4Weave.lean
-- Weaves Genus2MultiPrimeWeil (p in {7, 11, 13, 17, 19, 23}) with WeilZetaBridge
-- and GSp4FunctorialityBridge under [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.Genus2MultiPrimeWeil
import LeanAsm.WeilZetaBridge
import LeanAsm.GSp4FunctorialityBridge

namespace LeanAsm.Genus2WeilGSp4Weave

open LeanAsm.Genus2MultiPrimeWeil
open GSp4FunctorialityBridge
open WeilZetaBridge

/-! ## Part 1: Multi-Prime Spin and Homogenized Functional Equation Data -/

/-- Homogenized cleared-denominator degree-4 reciprocal L-polynomial for `(a_p, b_p)`.
Evaluating `(n, d) = (T, 1)` yields `spinLPoly p T`. -/
def spinLPolyHomog (p : Nat) (n d : Int) : Int :=
  let ap := frobeniusTrace p
  let bp := degree2Trace p
  d ^ 4 - ap * n * d ^ 3 + bp * n ^ 2 * d ^ 2 - (p : Int) * ap * n ^ 3 * d + (p : Int) ^ 2 * n ^ 4

/-- Homogenized reciprocal functional equation identity for `spinLPolyHomog`:
evaluating at `(d, p * n)` mirrors the genus-2 Hasse-Weil reciprocal involution
`p^2 * spinLPolyHomog(n, d)`. -/
theorem spinLPolyHomog_recip (p : Nat) (n d : Int) :
    spinLPolyHomog p d ((p : Int) * n) = (p : Int) ^ 2 * spinLPolyHomog p n d := by
  dsimp [spinLPolyHomog]
  have h1 : ((p : Int) * n) ^ 4 = (p : Int) ^ 2 * ((p : Int) ^ 2 * n ^ 4) := by
    simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h2 : frobeniusTrace p * d * ((p : Int) * n) ^ 3 =
      (p : Int) ^ 2 * ((p : Int) * frobeniusTrace p * n ^ 3 * d) := by
    simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h3 : degree2Trace p * d ^ 2 * ((p : Int) * n) ^ 2 =
      (p : Int) ^ 2 * (degree2Trace p * n ^ 2 * d ^ 2) := by
    simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h4 : (p : Int) * frobeniusTrace p * d ^ 3 * ((p : Int) * n) =
      (p : Int) ^ 2 * (frobeniusTrace p * n * d ^ 3) := by
    simp [Int.pow_succ, Int.pow_zero, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h5 : (p : Int) ^ 2 * d ^ 4 = (p : Int) ^ 2 * (d ^ 4) := rfl
  rw [h1, h2, h3, h4, h5]
  rw [← Int.mul_sub, ← Int.mul_add, ← Int.mul_sub, ← Int.mul_add]
  congr 1
  omega

/-- Univariate specialization `(n, d) = (T, 1)` matches `spinLPoly p T`. -/
theorem spinLPolyHomog_one (p : Nat) (T : Int) :
    spinLPolyHomog p T 1 = spinLPoly p T := by
  dsimp [spinLPolyHomog, spinLPoly, gsp4SpinEulerPoly]
  simp only [Int.mul_one]

/-! ## Part 2: Multi-Prime SO(5) Lift & Langlands Functoriality Data -/

/-- Homogenized degree-5 PGSp(4) ≅ SO(5) Standard Euler factor for prime `p`. -/
def standardEulerHomogP (p : Nat) (n d : Int) : Int :=
  gsp4StandardEulerHomog (p : Int) (frobeniusTrace p) (degree2Trace p) n d

/-- Anti-palindromic functional equation for the multi-prime SO(5) Standard factor. -/
theorem standardEulerHomogP_anti_palindromic (p : Nat) (n d : Int) :
    standardEulerHomogP p d n = -standardEulerHomogP p n d := by
  exact gsp4StandardEulerHomog_anti_palindromic (p : Int) (frobeniusTrace p) (degree2Trace p) n d

/-- Factorization of multi-prime degree-5 SO(5) Standard Euler polynomial into
`(1 - T) * Q_p(T)` where `Q_p` is the quartic Ramanujan-Petersson cofactor. -/
theorem standardEulerPoly_factorization (p : Nat) (T : Int) :
    standardEulerPoly p T =
      (1 - T) * gsp4StdQuarticCofactor (p : Int) (frobeniusTrace p) (degree2Trace p) T := by
  exact multiprime_gsp4_so5_factorization p T

/-- Evaluation at the simple pole `T = 1` vanishes for all primes. -/
theorem standardEulerPoly_eval_one (p : Nat) :
    standardEulerPoly p 1 = 0 := by
  rw [standardEulerPoly_factorization p 1]
  simp

/-! ## Part 3: Bundled Weave Certificate and Bridge Theorems -/

/-- Structure bundling the constructive weave for a given prime `p`:
1. Genus-2 Weil certificate (point counts, traces, Hasse-Weil discriminant bounds),
2. Spin L-polynomial homogenized reciprocal functional equation,
3. SO(5) degree-5 lift factorization `(1 - T) * Q_p(T)`,
4. Anti-palindromic symmetry `L_std(d, n) = -L_std(n, d)`,
5. Pole vanishing at `T = 1`. -/
structure Genus2WeilGSp4PrimeWeaveCert (p : Nat) : Prop where
  weil_cert : Genus2WeilCert p
  spin_recip : ∀ n d : Int,
    spinLPolyHomog p d ((p : Int) * n) = (p : Int) ^ 2 * spinLPolyHomog p n d
  so5_factor : ∀ T : Int,
    standardEulerPoly p T =
      (1 - T) * gsp4StdQuarticCofactor (p : Int) (frobeniusTrace p) (degree2Trace p) T
  so5_anti_pal : ∀ n d : Int, standardEulerHomogP p d n = -standardEulerHomogP p n d
  so5_eval_one : standardEulerPoly p 1 = 0

/-- Construction of `Genus2WeilGSp4PrimeWeaveCert` from any valid `Genus2WeilCert`. -/
theorem make_prime_weave_cert {p : Nat} (hcert : Genus2WeilCert p) :
    Genus2WeilGSp4PrimeWeaveCert p :=
  ⟨hcert, spinLPolyHomog_recip p, standardEulerPoly_factorization p,
   standardEulerHomogP_anti_palindromic p, standardEulerPoly_eval_one p⟩

/-- Concrete bundled certificate for p = 7. -/
theorem cert_weave_p7 : Genus2WeilGSp4PrimeWeaveCert 7 :=
  make_prime_weave_cert cert_p7

/-- Concrete bundled certificate for p = 11. -/
theorem cert_weave_p11 : Genus2WeilGSp4PrimeWeaveCert 11 :=
  make_prime_weave_cert cert_p11

/-- Concrete bundled certificate for p = 13. -/
theorem cert_weave_p13 : Genus2WeilGSp4PrimeWeaveCert 13 :=
  make_prime_weave_cert cert_p13

/-- Concrete bundled certificate for p = 17. -/
theorem cert_weave_p17 : Genus2WeilGSp4PrimeWeaveCert 17 :=
  make_prime_weave_cert cert_p17

/-- Concrete bundled certificate for p = 19. -/
theorem cert_weave_p19 : Genus2WeilGSp4PrimeWeaveCert 19 :=
  make_prime_weave_cert cert_p19

/-- Concrete bundled certificate for p = 23. -/
theorem cert_weave_p23 : Genus2WeilGSp4PrimeWeaveCert 23 :=
  make_prime_weave_cert cert_p23

/-- Universal weave bridge certifying multi-prime local Euler factor / functional-equation symmetry
and GSp(4) -> SO(5) Langlands parameter consistency across all good primes in {7,11,13,17,19,23}. -/
theorem genus2_multiprime_weil_gsp4_weave_bridge :
    (∀ p ∈ goodPrimesList, Genus2WeilGSp4PrimeWeaveCert p) ∧
    (∀ p ∈ goodPrimesList, ∀ n d : Int,
      spinLPolyHomog p d ((p : Int) * n) = (p : Int) ^ 2 * spinLPolyHomog p n d) ∧
    (∀ p ∈ goodPrimesList, ∀ T : Int,
      standardEulerPoly p T =
        (1 - T) * gsp4StdQuarticCofactor (p : Int) (frobeniusTrace p) (degree2Trace p) T) ∧
    (∀ p ∈ goodPrimesList, ∀ n d : Int,
      standardEulerHomogP p d n = -standardEulerHomogP p n d) ∧
    (∀ p ∈ goodPrimesList, standardEulerPoly p 1 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact make_prime_weave_cert (genus2_multiprime_weil_certs p hp)
  · intro p _ n d
    exact spinLPolyHomog_recip p n d
  · intro p _ T
    exact standardEulerPoly_factorization p T
  · intro p _ n d
    exact standardEulerHomogP_anti_palindromic p n d
  · intro p _
    exact standardEulerPoly_eval_one p

end LeanAsm.Genus2WeilGSp4Weave

-- end of file: leanasm/src/LeanAsm/Genus2WeilGSp4Weave.lean
