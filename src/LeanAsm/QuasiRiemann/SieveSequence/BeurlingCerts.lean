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

end LeanAsm.QuasiRiemann.SieveSequence

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/BeurlingCerts.lean
