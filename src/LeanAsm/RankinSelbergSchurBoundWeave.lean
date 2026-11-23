-- Path: leanasm/src/LeanAsm/RankinSelbergSchurBoundWeave.lean
-- Rankin-Selberg Schur and Euler factor bounds woven with Langlands & GSp(4) (Issue #224).
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound] or [].
-- Max Column: 120 Columns

import LeanAsm.LanglandsRankinSelbergBridge
import LeanAsm.QuasiRiemann.RankinSelbergGSp4Sub78Bridge

namespace RankinSelbergSchurBoundWeave

open LanglandsRankinSelbergBridge
open LeanAsm.QuasiRiemann.RankinSelbergGSp4Sub78Bridge

/-!
# Rankin-Selberg Schur and Euler Factor Bound Weave

Distills local Rankin-Selberg Schur and Euler factor bounds (as in `alpo-rh`'s
`EulerProductRankinSelbergGLnGLmDirichletSeries.lean`, specifically `norm_rsTermNM_le`)
into constructive integer arithmetic bounds without complex analysis or measure theory,
under zero Mathlib and zero `Classical.choice`.

Key components:
1. AM-GM / quadratic bounding:
   - For any integers `a` and `b`, `2 * (a * b) ≤ a^2 + b^2`.
   - In absolute values: `2 * |a * b| ≤ a^2 + b^2`.
2. Ramanujan bound preservation for Rankin-Selberg convolutions:
   - Denominator-cleared local quadratic form bounds: if `a_p^2 < 4 * p` and `b_p^2 < 4 * p`,
     then `|a_p * b_p| < 4 * p` and `2 * |a_p * b_p| < 8 * p`.
3. Weaving with existing Rankin-Selberg / GSp(4) modules:
   - Bundles Schur and Euler factor bounds with `rsClearedEuler` positivity and GSp(4) spinor
     factorization theorems from `LanglandsRankinSelbergBridge.lean` and `RankinSelbergGSp4Sub78Bridge.lean`.
-/

/-- Helper identity for squaring an integer. -/
private theorem sq_eq_mul (x : Int) : x ^ 2 = x * x := by
  simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- The classical AM-GM inequality over integers: `2 * (a * b) ≤ a^2 + b^2`,
proven via the nonnegativity of `(a - b)^2`. -/
theorem two_mul_le_sq_add_sq (a b : Int) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rw [sq_eq_mul a, sq_eq_mul b]
  have hsq : 0 ≤ (a - b) * (a - b) := by
    cases Int.le_total 0 (a - b) with
    | inl hpos => exact Int.mul_nonneg hpos hpos
    | inr hneg =>
      have hpos' : 0 ≤ -(a - b) := by omega
      have hmul : 0 ≤ (-(a - b)) * (-(a - b)) := Int.mul_nonneg hpos' hpos'
      have heq : (-(a - b)) * (-(a - b)) = (a - b) * (a - b) := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [← heq]
      exact hmul
  have hexp : (a - b) * (a - b) = a * a + b * b - 2 * (a * b) := by
    calc (a - b) * (a - b)
      _ = a * (a - b) - b * (a - b) := by rw [Int.sub_mul]
      _ = (a * a - a * b) - (b * a - b * b) := by rw [Int.mul_sub, Int.mul_sub]
      _ = a * a + b * b - 2 * (a * b) := by
        have : b * a = a * b := Int.mul_comm b a
        rw [this]
        omega
  omega

/-- Squaring preserves integer absolute value: `a^2 = |a|^2`. -/
theorem sq_eq_sq_natAbs (a : Int) : a ^ 2 = (a.natAbs : Int) ^ 2 := by
  rw [sq_eq_mul a, sq_eq_mul (a.natAbs : Int)]
  cases Int.le_total 0 a with
  | inl hpos =>
    have : (a.natAbs : Int) = a := Int.natAbs_of_nonneg hpos
    rw [this]
  | inr hneg =>
    have : (a.natAbs : Int) = -a := Int.ofNat_natAbs_of_nonpos hneg
    rw [this]
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- Absolute value bound: `2 * |a * b| ≤ a^2 + b^2`.
Direct algebraic counterpart of `norm_rsTermNM_le` in `alpo-rh`. -/
theorem two_mul_natAbs_le_sq_add_sq (a b : Int) :
    2 * (a.natAbs * b.natAbs : Int) ≤ a ^ 2 + b ^ 2 := by
  have ha := sq_eq_sq_natAbs a
  have hb := sq_eq_sq_natAbs b
  rw [ha, hb]
  exact two_mul_le_sq_add_sq (a.natAbs : Int) (b.natAbs : Int)

/-- Rankin-Selberg product bound under Ramanujan bounds `a^2 < 4 * p` and `b^2 < 4 * p`. -/
theorem rs_ramanujan_product_bound (p : Nat) (a b : Int)
    (ha : a ^ 2 < 4 * (p : Int)) (hb : b ^ 2 < 4 * (p : Int)) :
    2 * (a.natAbs * b.natAbs : Int) < 8 * (p : Int) := by
  have hamgm := two_mul_natAbs_le_sq_add_sq a b
  omega

/-- Strict bound on the product: `|a * b| < 4 * p` under Ramanujan bounds. -/
theorem rs_ramanujan_abs_mul_bound (p : Nat) (a b : Int)
    (ha : a ^ 2 < 4 * (p : Int)) (hb : b ^ 2 < 4 * (p : Int)) :
    (a.natAbs * b.natAbs : Int) < 4 * (p : Int) := by
  have h2 := rs_ramanujan_product_bound p a b ha hb
  omega

/-- Bundled specification weaving Rankin-Selberg Schur arithmetic bounds
with GSp(4) and sub-7/8 strip bridge certificates. -/
structure RankinSelbergSchurBoundWeaveSpec where
  rsSpec : RankinSelbergGSp4Sub78BridgeSpec

/-- Master theorem weaving Rankin-Selberg Schur arithmetic inequalities with
Rankin-Selberg / GSp(4) / sub-7/8 bridge properties. -/
theorem rankin_selberg_schur_bound_weave (spec : RankinSelbergSchurBoundWeaveSpec) :
    -- 1. Constructive integer arithmetic Schur / AM-GM inequalities
    (∀ a b : Int, 2 * (a * b) ≤ a ^ 2 + b ^ 2) ∧
    (∀ a b : Int, 2 * (a.natAbs * b.natAbs : Int) ≤ a ^ 2 + b ^ 2) ∧
    (∀ (p : Nat) (a b : Int),
      a ^ 2 < 4 * (p : Int) → b ^ 2 < 4 * (p : Int) →
      (a.natAbs * b.natAbs : Int) < 4 * (p : Int) ∧
      2 * (a.natAbs * b.natAbs : Int) < 8 * (p : Int)) ∧
    -- 2. Rankin-Selberg & GSp(4) Euler factor theorems from sub78 bridge
    (((∀ p ∈ spec.rsSpec.goodPrimes, LeanAsm.Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
        LeanAsm.Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
          (p : Int) ^ 2 * LeanAsm.Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ T : Int,
        LeanAsm.Genus2MultiPrimeWeil.standardEulerPoly p T =
          (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor (p : Int)
            (LeanAsm.Genus2MultiPrimeWeil.frobeniusTrace p) (LeanAsm.Genus2MultiPrimeWeil.degree2Trace p) T) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
        LeanAsm.Genus2WeilGSp4Weave.standardEulerHomogP p d n =
          -LeanAsm.Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, LeanAsm.Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
     ((∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
        0 < LanglandsRankinSelbergBridge.rsClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
        0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ al1 al2 lam T : Int,
        GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
          (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2)))) := by
  have hBridge := rankin_selberg_gsp4_sub78_bridge spec.rsSpec
  refine ⟨two_mul_le_sq_add_sq, two_mul_natAbs_le_sq_add_sq, ?_, hBridge.1, hBridge.2.1⟩
  intro p a b ha hb
  exact ⟨rs_ramanujan_abs_mul_bound p a b ha hb, rs_ramanujan_product_bound p a b ha hb⟩

end RankinSelbergSchurBoundWeave

-- end of file: leanasm/src/LeanAsm/RankinSelbergSchurBoundWeave.lean
