-- Path: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/LuckyGenerators500.lean
-- Chunked N = 500 prefix evaluation and exact QRat Beurling certificates for Lucky generators.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.SieveSequence.Core
import LeanAsm.QuasiRiemann.SieveSequence.BeurlingCerts
import LeanAsm.QuasiRiemann.Rat

open QuasiRiemann

namespace LeanAsm.QuasiRiemann.SieveSequence

/-- First chunk (21 generators) of Lucky generators up to 500. -/
def luckyGenerators500Chunk1 : List Nat :=
  [3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49, 51, 63, 67, 69, 73, 75, 79, 87, 93]

/-- Second chunk (21 generators) of Lucky generators up to 500. -/
def luckyGenerators500Chunk2 : List Nat :=
  [99, 105, 111, 115, 127, 129, 133, 135, 141, 151, 159, 163, 169, 171, 189, 193, 195,
   201, 205, 211, 219]

/-- Third chunk (21 generators) of Lucky generators up to 500. -/
def luckyGenerators500Chunk3 : List Nat :=
  [223, 231, 235, 237, 241, 259, 261, 267, 273, 283, 285, 289, 297, 303, 307, 319, 321,
   327, 331, 339, 349]

/-- Fourth chunk (21 generators) of Lucky generators up to 500. -/
def luckyGenerators500Chunk4 : List Nat :=
  [357, 361, 367, 385, 391, 393, 399, 409, 415, 421, 427, 429, 433, 451, 463, 475, 477,
   483, 487, 489, 495]

/-- Certificate for an individual chunk of sieve sequence generators. -/
structure SieveChunkCertificate (chunk : List Nat) where
  count : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalLower : QRat
  survivalUpper : QRat
  h_count : chunk.length = count
  h_harm_lo : harmonicLower ≤ sequenceHarmonicRat chunk
  h_harm_hi : sequenceHarmonicRat chunk ≤ harmonicUpper
  h_surv_lo : survivalLower ≤ survivalProductRat chunk
  h_surv_hi : survivalProductRat chunk ≤ survivalUpper
  h_surv_pos : QRat.ofInt 0 < survivalProductRat chunk

/-- Certificate for Chunk 1:
    count = 21, harmonic ≈ 1.07860 ∈ [107/100, 108/100], survival ≈ 0.30761 ∈ [30/100, 31/100]. -/
def luckyChunkCert1 : SieveChunkCertificate luckyGenerators500Chunk1 where
  count := 21
  harmonicLower := QRat.mk' 107 100
  harmonicUpper := QRat.mk' 108 100
  survivalLower := QRat.mk' 30 100
  survivalUpper := QRat.mk' 31 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_lo := by decide
  h_surv_hi := by decide
  h_surv_pos := by decide

/-- Certificate for Chunk 2:
    count = 21, harmonic ≈ 0.14055 ∈ [14/100, 15/100], survival ≈ 0.86845 ∈ [86/100, 87/100]. -/
def luckyChunkCert2 : SieveChunkCertificate luckyGenerators500Chunk2 where
  count := 21
  harmonicLower := QRat.mk' 14 100
  harmonicUpper := QRat.mk' 15 100
  survivalLower := QRat.mk' 86 100
  survivalUpper := QRat.mk' 87 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_lo := by decide
  h_surv_hi := by decide
  h_surv_pos := by decide

/-- Certificate for Chunk 3:
    count = 21, harmonic ≈ 0.07511 ∈ [7/100, 8/100], survival ≈ 0.92751 ∈ [92/100, 93/100]. -/
def luckyChunkCert3 : SieveChunkCertificate luckyGenerators500Chunk3 where
  count := 21
  harmonicLower := QRat.mk' 7 100
  harmonicUpper := QRat.mk' 8 100
  survivalLower := QRat.mk' 92 100
  survivalUpper := QRat.mk' 93 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_lo := by decide
  h_surv_hi := by decide
  h_surv_pos := by decide

/-- Certificate for Chunk 4:
    count = 21, harmonic ≈ 0.04948 ∈ [4/100, 5/100], survival ≈ 0.95167 ∈ [95/100, 96/100]. -/
def luckyChunkCert4 : SieveChunkCertificate luckyGenerators500Chunk4 where
  count := 21
  harmonicLower := QRat.mk' 4 100
  harmonicUpper := QRat.mk' 5 100
  survivalLower := QRat.mk' 95 100
  survivalUpper := QRat.mk' 96 100
  h_count := by rfl
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_lo := by decide
  h_surv_hi := by decide
  h_surv_pos := by decide

set_option maxRecDepth 500000 in
/-- Exact decomposition of `luckyGeneratorsUpTo 500` into the 4 chunks of length 21. -/
theorem luckyGenerators500_chunks_eq :
    luckyGeneratorsUpTo 500 =
      luckyGenerators500Chunk1 ++ luckyGenerators500Chunk2 ++
      luckyGenerators500Chunk3 ++ luckyGenerators500Chunk4 := by
  decide

set_option maxRecDepth 500000 in
/-- Total count of Lucky generators <= 500 is 84. -/
theorem luckyGeneratorsUpTo_500_length :
    (luckyGeneratorsUpTo 500).length = 84 := by
  decide

set_option maxRecDepth 500000 in
/-- Total count of Lucky prefix elements <= 500 (including 1) is 85. -/
theorem luckyPrefixUpTo_500_length :
    (luckyPrefixUpTo 500).length = 85 := by
  decide

/-- Certificate structure for Lucky Beurling generators up to bound `N`. -/
structure LuckyBeurlingCert (N : Nat) where
  countUpToN : Nat
  harmonicLower : QRat
  harmonicUpper : QRat
  survivalLower : QRat
  survivalUpper : QRat
  h_count : (luckyGeneratorsUpTo N).length = countUpToN
  h_harm_lo : harmonicLower ≤ sequenceHarmonicRat (luckyGeneratorsUpTo N)
  h_harm_hi : sequenceHarmonicRat (luckyGeneratorsUpTo N) ≤ harmonicUpper
  h_surv_lo : survivalLower ≤ survivalProductRat (luckyGeneratorsUpTo N)
  h_surv_hi : survivalProductRat (luckyGeneratorsUpTo N) ≤ survivalUpper
  h_surv_pos : QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo N)

set_option maxRecDepth 500000 in
/-- Concrete certified Beurling bounds at `N = 500`:
    Exact values:
    harmonic sum ≈ 1.34374 (bounded by [134/100, 135/100])
    survival product ≈ 0.23580 (bounded by [23/100, 24/100]). -/
def luckyBeurlingCert_500 : LuckyBeurlingCert 500 where
  countUpToN := 84
  harmonicLower := QRat.mk' 134 100
  harmonicUpper := QRat.mk' 135 100
  survivalLower := QRat.mk' 23 100
  survivalUpper := QRat.mk' 24 100
  h_count := by decide
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_lo := by decide
  h_surv_hi := by decide
  h_surv_pos := by decide

set_option maxRecDepth 500000 in
/-- Exact non-vanishing / strict positivity of the Lucky Beurling survival product at N = 500. -/
theorem lucky_survival_product_500_pos :
    QRat.ofInt 0 < survivalProductRat (luckyGeneratorsUpTo 500) := by
  decide

set_option maxRecDepth 500000 in
/-- Exact non-vanishing / strict positivity of the Lucky Beurling harmonic sum at N = 500. -/
theorem lucky_harmonic_500_pos :
    QRat.ofInt 0 < sequenceHarmonicRat (luckyGeneratorsUpTo 500) := by
  decide

end LeanAsm.QuasiRiemann.SieveSequence

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/LuckyGenerators500.lean
