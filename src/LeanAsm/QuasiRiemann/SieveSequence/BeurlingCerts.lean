-- Path: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/BeurlingCerts.lean
-- Exact rational Beurling Euler products, Mertens sums, and generalized Chebyshev operations.
-- Max Column: 120 Columns

import LeanAsm.QuasiRiemann.SieveSequence.Core
import LeanAsm.QuasiRiemann.Rat

open QuasiRiemann

namespace LeanAsm.QuasiRiemann.SieveSequence

/-- Safe rational reciprocal for natural number `l`. -/
def invRat (l : Nat) : QRat :=
  if h : 0 < l then QRat.mk' 1 l h else QRat.ofInt 0

/-- Repeated rational power `x ^ n` for `QRat`. -/
def qratPow (x : QRat) : Nat → QRat
  | 0 => QRat.ofInt 1
  | n + 1 => x * qratPow x n

instance : HPow QRat Nat QRat where
  hPow x n := qratPow x n

/-- Telescoping survival product `∏_{l ∈ gens} (1 - 1 / l)` in exact rational arithmetic. -/
def survivalProductRat (gens : List Nat) : QRat :=
  gens.foldl (fun acc l => acc * (QRat.ofInt 1 - invRat l)) (QRat.ofInt 1)

/-- Finite Mertens / generalized harmonic sum `∑_{l ∈ gens} 1 / l`. -/
def sequenceHarmonicRat (gens : List Nat) : QRat :=
  gens.foldl (fun acc l => acc + invRat l) (QRat.ofInt 0)

/-- Truncated Beurling Euler factor `(1 - l^{-sigma})^{-1}` at rational abscissa `sigma`
    approximated via `M`-term geometric partial sum `∑_{j=0}^{M} l^{-j * sigma}`. -/
def beurlingEulerPartialFactor (invPowL : QRat) (M : Nat) : QRat :=
  (List.range (M + 1)).foldl (fun acc j => acc + invPowL ^ j) (QRat.ofInt 0)

/-- Count of sequence elements `l <= x` (discrete counting step function `pi_P(x)`). -/
def piPCount (gens : List Nat) (x : Nat) : Nat :=
  (gens.filter (fun l => l <= x)).length

/-- Natural power `base ^ exp`. -/
def natPow (base exp : Nat) : Nat :=
  match exp with
  | 0 => 1
  | e + 1 => base * natPow base e

/-- Prime power check: is `n = l^m` for `l ∈ gens` and `m >= 1`?
    Used to define the generalized Chebyshev step support. -/
def isSequencePrimePower (gens : List Nat) (n : Nat) : Bool :=
  gens.any (fun l =>
    if l <= 1 then false
    else
      let rec checkPow (p : Nat) (fuel : Nat) : Bool :=
        match fuel with
        | 0 => false
        | f + 1 =>
          if p == n then true
          else if p > n then false
          else checkPow (p * l) f
      checkPow l n)

/-- Certificate witness bundling finite-prefix generator counts, rational Mertens bounds,
    and truncated Beurling product positivity/non-vanishing on `[1, N]`. -/
structure SieveSequenceCertificate (N : Nat) where
  countUpToN : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalUpper : QRat
  h_count : (ludicGeneratorsUpTo N).length = countUpToN
  h_harm_lo : harmonicLower ≤ sequenceHarmonicRat (ludicGeneratorsUpTo N)
  h_harm_hi : sequenceHarmonicRat (ludicGeneratorsUpTo N) ≤ harmonicUpper
  h_surv_hi : survivalProductRat (ludicGeneratorsUpTo N) ≤ survivalUpper

/-- Concrete Ludic Beurling certificate at `N = 50` (`14` Ludic numbers `<= 50`).
    Exact values:
    harmonic sum ≈ 1.61676 (bounded by [16/10, 17/10])
    survival product ≈ 0.14524 (bounded by 15/100). -/
def ludicBeurlingCert_50 : SieveSequenceCertificate 50 where
  countUpToN := 14
  harmonicLower := QRat.mk' 16 10
  harmonicUpper := QRat.mk' 17 10
  survivalUpper := QRat.mk' 15 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

/-- Exact non-vanishing of finite Ludic Beurling survival product at N = 50. -/
theorem ludic_survival_product_50_pos :
    QRat.ofInt 0 < survivalProductRat (ludicGeneratorsUpTo 50) := by
  decide

/-- Exact non-vanishing of finite Ludic harmonic sum at N = 50. -/
theorem ludic_harmonic_50_pos :
    QRat.ofInt 0 < sequenceHarmonicRat (ludicGeneratorsUpTo 50) := by
  decide

/-- Concrete Josephus certificate structure at `N`. -/
structure JosephusBeurlingCertificate (N : Nat) where
  countUpToN : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalUpper : QRat
  h_count : (josephusGeneratorsUpTo N).length = countUpToN
  h_harm_lo : harmonicLower ≤ sequenceHarmonicRat (josephusGeneratorsUpTo N)
  h_harm_hi : sequenceHarmonicRat (josephusGeneratorsUpTo N) ≤ harmonicUpper
  h_surv_hi : survivalProductRat (josephusGeneratorsUpTo N) ≤ survivalUpper

/-- Concrete Josephus Beurling certificate at `N = 50` (`7` Josephus generators `<= 50`).
    Exact values:
    harmonic sum ≈ 0.68883 (bounded by [68/100, 70/100])
    survival product ≈ 0.45930 (bounded by 46/100). -/
def josephusBeurlingCert_50 : JosephusBeurlingCertificate 50 where
  countUpToN := 7
  harmonicLower := QRat.mk' 68 100
  harmonicUpper := QRat.mk' 70 100
  survivalUpper := QRat.mk' 46 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

/-- Exact non-vanishing of finite Josephus Beurling survival product at N = 50. -/
theorem josephus_survival_product_50_pos :
    QRat.ofInt 0 < survivalProductRat (josephusGeneratorsUpTo 50) := by
  decide

/-- Exact non-vanishing of finite Josephus harmonic sum at N = 50. -/
theorem josephus_harmonic_50_pos :
    QRat.ofInt 0 < sequenceHarmonicRat (josephusGeneratorsUpTo 50) := by
  decide

/-- Concrete Ulam certificate structure at `N`. -/
structure UlamBeurlingCertificate (N : Nat) where
  countUpToN : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalUpper : QRat
  h_count : (ulamGeneratorsUpTo N).length = countUpToN
  h_harm_lo : harmonicLower ≤ sequenceHarmonicRat (ulamGeneratorsUpTo N)
  h_harm_hi : sequenceHarmonicRat (ulamGeneratorsUpTo N) ≤ harmonicUpper
  h_surv_hi : survivalProductRat (ulamGeneratorsUpTo N) ≤ survivalUpper

set_option maxRecDepth 200000 in
/-- Concrete Ulam Beurling certificate at `N = 50` (`15` Ulam generators `<= 50`).
    Exact values:
    harmonic sum ≈ 1.83127 (bounded by [18/10, 19/10])
    survival product ≈ 0.11393 (bounded by 12/100). -/
def ulamBeurlingCert_50 : UlamBeurlingCertificate 50 where
  countUpToN := 15
  harmonicLower := QRat.mk' 18 10
  harmonicUpper := QRat.mk' 19 10
  survivalUpper := QRat.mk' 12 100
  h_count := by decide
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

set_option maxRecDepth 200000 in
/-- Exact non-vanishing of finite Ulam Beurling survival product at N = 50. -/
theorem ulam_survival_product_50_pos :
    QRat.ofInt 0 < survivalProductRat (ulamGeneratorsUpTo 50) := by
  decide

set_option maxRecDepth 200000 in
/-- Exact non-vanishing of finite Ulam harmonic sum at N = 50. -/
theorem ulam_harmonic_50_pos :
    QRat.ofInt 0 < sequenceHarmonicRat (ulamGeneratorsUpTo 50) := by
  decide

/-- Arithmetic Mobius function `μ(n)` taking values in `{-1, 0, 1}`. -/
def mobius (n : Nat) : Int :=
  match n with
  | 0 => 0
  | 1 => 1
  | _ =>
    let rec factorize (temp p : Nat) (factors : Nat) (fuel : Nat) : Int :=
      match fuel with
      | 0 => 0
      | f + 1 =>
        if p * p > temp then
          let totalFactors := if temp > 1 then factors + 1 else factors
          if totalFactors % 2 = 1 then -1 else 1
        else if temp % p = 0 then
          let temp1 := temp / p
          if temp1 % p = 0 then 0
          else factorize temp1 (p + 1) (factors + 1) f
        else
          factorize temp (p + 1) factors f
    factorize n 2 0 n

/-- Prime power multiplicity: returns `m` if `n = l^m` for `m >= 1`, else `0`. -/
def primePowerMultiplicity (l n : Nat) : Nat :=
  if l ≤ 1 ∨ n = 0 then 0
  else
    let rec go (val m : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => 0
      | f + 1 =>
        if val = n then m
        else if val > n then 0
        else go (val * l) (m + 1) f
    go l 1 n

/-- Rational Riemann prime-power counting function `Π_P(x) = ∑_{l^m ≤ x} 1/m`. -/
def riemannPrimePowerPiRat (gens : List Nat) (x : Nat) : QRat :=
  let rec sumUpTo (n : Nat) (fuel : Nat) : QRat :=
    match fuel with
    | 0 => QRat.ofInt 0
    | f + 1 =>
      if n = 0 then QRat.ofInt 0
      else
        let term := gens.foldl (fun acc l =>
          let m := primePowerMultiplicity l n
          if m > 0 then acc + invRat m else acc) (QRat.ofInt 0)
        term + sumUpTo (n - 1) f
  sumUpTo x x

/-- Discrete integer `m`-th root `⌊n^{1/m}⌋`. -/
def natRoot (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ =>
    if m ≤ 1 then n
    else
      let rec bsearch (low high ans : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => ans
        | f + 1 =>
          if low > high then ans
          else
            let mid := (low + high) / 2
            if mid ^ m ≤ n then
              bsearch (mid + 1) high mid f
            else
              match mid with
              | 0 => ans
              | _ => bsearch low (mid - 1) ans f
      bsearch 0 n 0 (n + 1)

/-- Maximum power exponent `m` such that `l_1^m ≤ x`. -/
def maxPowerM (l1 x : Nat) : Nat :=
  if l1 ≤ 1 ∨ x < l1 then 0
  else
    let rec go (pow m : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => m
      | f + 1 =>
        if pow * l1 ≤ x then go (pow * l1) (m + 1) f
        else m
    go l1 1 x

/-- Mobius-inverted rational prime counting evaluator:
    `π_P(x) = ∑_{m=1}^{⌊log_{l_1} x⌋} (μ(m)/m) Π_P(⌊x^{1/m}⌋)`. -/
def mobiusInvertedPiRat (gens : List Nat) (x : Nat) : QRat :=
  match gens with
  | [] => QRat.ofInt 0
  | l1 :: _ =>
    let maxM := maxPowerM l1 x
    (List.range maxM).foldl (fun acc idx =>
      let m := idx + 1
      match mobius m with
      | 0 => acc
      | mu =>
        let xm := natRoot x m
        let piVal := riemannPrimePowerPiRat gens xm
        let weight := QRat.ofInt mu * invRat m
        acc + weight * piVal) (QRat.ofInt 0)

set_option maxRecDepth 200000 in
theorem ulam_riemann_pi_10 :
    QRat.eqv (riemannPrimePowerPiRat [2, 3, 4, 6, 8] 10) (QRat.mk' 19 3 (by decide)) := by
  decide

set_option maxRecDepth 200000 in
theorem ulam_mobius_bridge_10 :
    QRat.eqv (mobiusInvertedPiRat [2, 3, 4, 6, 8] 10) (QRat.ofInt (piPCount [2, 3, 4, 6, 8] 10)) := by
  decide

end LeanAsm.QuasiRiemann.SieveSequence

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/BeurlingCerts.lean
