-- Path: leanasm/src/LeanAsm/QuasiRiemann/LuckySieve/BeurlingCerts.lean
-- Exact rational Beurling Euler products, Lucky harmonic sums, and finite certificates.
-- Max Column: 120 Columns

import LeanAsm.QuasiRiemann.LuckySieve.Core
import LeanAsm.QuasiRiemann.Rat

open QuasiRiemann

namespace LeanAsm.QuasiRiemann.LuckySieve

open LeanAsm.QuasiRiemann.LuckySieve

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

/-- Finite Lucky harmonic / Mertens sum `∑_{l ∈ gens} 1 / l`. -/
def luckyHarmonicRat (gens : List Nat) : QRat :=
  gens.foldl (fun acc l => acc + invRat l) (QRat.ofInt 0)

/-- Truncated Beurling Euler factor `(1 - l^{-sigma})^{-1}` at rational abscissa `sigma`
    approximated via `M`-term geometric partial sum `∑_{j=0}^{M} l^{-j * sigma}`. -/
def beurlingEulerPartialFactor (invPowL : QRat) (M : Nat) : QRat :=
  (List.range (M + 1)).foldl (fun acc j => acc + invPowL ^ j) (QRat.ofInt 0)

/-- Certificate witness bundling finite-prefix Lucky counts, rational Mertens bounds,
    and truncated Beurling product positivity/non-vanishing on `[1, N]`. -/
structure LuckyBeurlingCertificate (N : Nat) where
  countUpToN : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalUpper : QRat
  h_count : (luckyPrefixUpTo N).length = countUpToN
  h_harm_lo : harmonicLower ≤ luckyHarmonicRat (luckyGeneratorsUpTo N)
  h_harm_hi : luckyHarmonicRat (luckyGeneratorsUpTo N) ≤ harmonicUpper
  h_surv_hi : survivalProductRat (luckyGeneratorsUpTo N) ≤ survivalUpper

/-- Concrete constructive certificate at `N = 50` (`13` Lucky numbers `<= 50`).
    Exact values:
    luckyHarmonicRat ≈ 0.95176 (bounded by [95/100, 96/100])
    survivalProductRat ≈ 0.34953 (bounded by 35/100). -/
def luckyBeurlingCert_50 : LuckyBeurlingCertificate 50 where
  countUpToN := 13
  harmonicLower := QRat.mk' 95 100
  harmonicUpper := QRat.mk' 96 100
  survivalUpper := QRat.mk' 35 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

/-- Exact non-vanishing of finite Lucky Beurling survival product at N = 50. -/
theorem lucky_survival_product_50_pos :
    QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo 50) := by
  decide

/-- Exact non-vanishing of finite Lucky harmonic sum at N = 50. -/
theorem lucky_harmonic_50_pos :
    QRat.ofInt 0 < luckyHarmonicRat (luckyGeneratorsUpTo 50) := by
  decide

/-- Concrete constructive certificate at `N = 200` (`39` Lucky numbers `<= 200`).
    Exact values:
    luckyHarmonicRat ≈ 1.19998 (bounded by [119/100, 121/100])
    survivalProductRat ≈ 0.27232 (bounded by 28/100). -/
def luckyBeurlingCert_200 : LuckyBeurlingCertificate 200 where
  countUpToN := 39
  harmonicLower := QRat.mk' 119 100
  harmonicUpper := QRat.mk' 121 100
  survivalUpper := QRat.mk' 28 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

/-- Exact non-vanishing of finite Lucky Beurling survival product at N = 200. -/
theorem lucky_survival_product_200_pos :
    QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo 200) := by
  decide

/-- Exact non-vanishing of finite Lucky harmonic sum at N = 200. -/
theorem lucky_harmonic_200_pos :
    QRat.ofInt 0 < luckyHarmonicRat (luckyGeneratorsUpTo 200) := by
  decide

end LeanAsm.QuasiRiemann.LuckySieve

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/LuckySieve/BeurlingCerts.lean
