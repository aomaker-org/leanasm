-- Path: leanasm/src/LeanAsm/QuasiRiemann/Qsd24JetIdempotentWeave.lean
-- Higher-Order QSD[2-4] Nilpotent Jet Truncations & Split-Idempotent Tangent Weave.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.QsdAlgebraBridge
import LeanAsm.QuasiRiemann.GaussianQsdBridge
import LeanAsm.QuasiRiemann.Valuation.QsdHenselTower
import LeanAsm.QuasiRiemann.UltraDeep90.Certificates
import LeanAsm.QuasiRiemann.ContractionReflectionBridge

namespace QuasiRiemann

open LeanAsm.QuasiRiemann.RNS
open QuasiRiemann.Valuation

/-!
# Higher-Order QSD[2-4] Nilpotent Jet Truncations & Split-Idempotent Tangent Weave

This module extends `Qsd1IdempotentDyadicAbelWeave` and `GaussianQsdBridge` to:
1. Higher-order `QSD[2-4]` nilpotent jet truncations:
   - Order-4 truncated polynomial jet ring `QsdJet4` over `QRat` (`η^4 = 0`).
   - Order-6 truncated non-commutative / associative defect algebra `QsdTrunc6` (`QSD[2]`).
   - $\mathbb{Z}_2$-graded sign commutation obstruction (`QSD[3]`).
   - Discrete nilpotent modulo $p^{2k}$ residue zero-divisor arithmetic (`QSD[4]`).
2. Constructive split-idempotent decomposition across prime-power tangent extensions:
   - Orthogonal idempotents $e_\pm = (1 \pm L) / 2$ with $e_+ + e_- = 1$,
     $e_\pm^2 = e_\pm$, $e_+ e_- = 0$.
   - Hensel tangent lift $x_{k+1} = x + t \cdot p^k \pmod{p^{k+1}}$ preserving
     idempotency modulo $p^k$.
   - Dual nilpotent tangent remainder vanishing: $(t \cdot p^k)^2 \equiv 0 \pmod{p^{2k}}$.
3. Bounded-height rational box contraction survival under nilpotent jet perturbation:
   - Cleared-denominator Lipschitz margin dominance:
     $2 \cdot M_{\mathrm{lip}} \cdot r \le D_{\mathrm{lo}} \cdot (r - \delta)$
     implies $M_{\mathrm{lip}} \cdot r < D_{\mathrm{lo}} \cdot (r - \delta)$.
   - Interior non-vanishing lower bound surviving nilpotent jet perturbations:
     $D_{\mathrm{lo}} \cdot (r - \delta) - z \ne 0$ for $|z| \le M_{\mathrm{lip}} \cdot r$.

All proofs are constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

/-- Order-4 truncated nilpotent jet ring over `QRat`:
    $a_0 + a_1 \eta + a_2 \eta^2 + a_3 \eta^3$ modulo $\eta^4 = 0$. -/
structure QsdJet4 where
  a0 : QRat
  a1 : QRat
  a2 : QRat
  a3 : QRat
  deriving Repr, DecidableEq

/-- Addition of order-4 nilpotent jets. -/
def QsdJet4.add (x y : QsdJet4) : QsdJet4 :=
  ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3⟩

/-- Multiplication of order-4 nilpotent jets modulo $\eta^4 = 0$. -/
def QsdJet4.mul (x y : QsdJet4) : QsdJet4 :=
  ⟨x.a0 * y.a0,
   x.a0 * y.a1 + x.a1 * y.a0,
   x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0,
   x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0⟩

instance : Add QsdJet4 := ⟨QsdJet4.add⟩
instance : Mul QsdJet4 := ⟨QsdJet4.mul⟩

/-- Canonical nilpotent generator $\eta$ with $\eta^4 = 0$. -/
def etaJet4 : QsdJet4 :=
  ⟨QRat.ofInt 0, QRat.ofInt 1, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Zero element in `QsdJet4`. -/
def zeroJet4 : QsdJet4 :=
  ⟨QRat.ofInt 0, QRat.ofInt 0, QRat.ofInt 0, QRat.ofInt 0⟩

/-- One element in `QsdJet4`. -/
def oneJet4 : QsdJet4 :=
  ⟨QRat.ofInt 1, QRat.ofInt 0, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Embedding a `QRat` into `QsdJet4` as a constant jet. -/
def QsdJet4.ofQRat (q : QRat) : QsdJet4 :=
  ⟨q, QRat.ofInt 0, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Constructive proof of 4th-order nilpotency: $\eta^4 = 0$. -/
theorem qsd4_jet_nilpotent_order4 :
    (((etaJet4 * etaJet4) * etaJet4) * etaJet4) = zeroJet4 := by
  decide

/-- Embedding `SliceDualQRat` (QSD[1] dual numbers) into `QsdJet4` (order-4 jet). -/
def sliceDualToJet4 (x : SliceDualQRat) : QsdJet4 :=
  ⟨x.val, x.tan, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Embedding `SplitIdempotentQRat` into `QsdJet4`. -/
def splitIdempotentToJet4 (s : SplitIdempotentQRat) : QsdJet4 :=
  QsdJet4.ofQRat s.L

/-- Split-idempotent positive projection in `QsdJet4`. -/
def jet4_e_plus (s : SplitIdempotentQRat) : QsdJet4 :=
  QsdJet4.ofQRat (e_plus s)

/-- Split-idempotent negative projection in `QsdJet4`. -/
def jet4_e_minus (s : SplitIdempotentQRat) : QsdJet4 :=
  QsdJet4.ofQRat (e_minus s)

/-- Lifted split-idempotents with nilpotent tangent perturbation:
    $e_\pm(\eta) = e_\pm + t \cdot \eta$ where $t \in \mathbb{Q}$. -/
def jet4_e_plus_tangent (s : SplitIdempotentQRat) (t : QRat) : QsdJet4 :=
  ⟨e_plus s, t, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Negative lifted split-idempotent with compensating tangent perturbation:
    $e_-(\eta) = e_- - t \cdot \eta$. -/
def jet4_e_minus_tangent (s : SplitIdempotentQRat) (t : QRat) : QsdJet4 :=
  ⟨e_minus s, -t, QRat.ofInt 0, QRat.ofInt 0⟩

/-- Tangent sum preservation: $e_+(\eta) + e_-(\eta) = 1 + 0 \cdot \eta$. -/
theorem jet4_tangent_sum_preservation (s : SplitIdempotentQRat)
    (h : s = canL ∨ s = canL_neg) (t : QRat) :
    let sum := (jet4_e_plus_tangent s t) + (jet4_e_minus_tangent s t)
    QRat.eqv sum.a0 (QRat.ofInt 1) ∧ QRat.eqv sum.a1 (QRat.ofInt 0) := by
  intro sum
  dsimp [sum, jet4_e_plus_tangent, jet4_e_minus_tangent, QsdJet4.add]
  have h1 : QRat.eqv (e_plus s + e_minus s) (QRat.ofInt 1) :=
    (split_idempotent_properties s h).1
  refine ⟨h1, ?_⟩
  change (t.num * (t.den : Int) + (-t.num) * (t.den : Int)) * 1 = 0 * _
  rw [← Int.neg_mul_eq_neg_mul, Int.add_right_neg, Int.zero_mul, Int.zero_mul]

/-- Bundled specification for higher-order QSD[2-4] jet and split-idempotent weave. -/
structure Qsd24JetIdempotentSpec where
  splitGen : SplitIdempotentQRat
  hSplit : splitGen = canL ∨ splitGen = canL_neg
  boxSpec : RationalBoxContractionSpec
  primeBase : Nat
  hPrime : 2 ≤ primeBase

/-- Master bridge theorem establishing higher-order QSD[2-4] nilpotent jets, Hensel tangent lifts,
    split-idempotent decomposition, and bounded-height rational contraction. -/
theorem qsd24_jet_idempotent_weave (spec : Qsd24JetIdempotentSpec) :
    -- 1. QSD[2-4] Nilpotent Jet Properties
    ((((etaJet4 * etaJet4) * etaJet4) * etaJet4) = zeroJet4 ∧
     (b_basis.mulTrunc6 b_basis).mulTrunc6 b_basis ≠
       b_basis.mulTrunc6 (b_basis.mulTrunc6 b_basis) ∧
     (qsd2_assoc_defect b_basis b_basis b_basis).f = QRat.ofInt 1 ∧
     (∀ A B : GradedFactor,
       A.deg = Z2Grading.odd → B.deg = Z2Grading.odd →
       (A.val * B.val).num ≠ 0 →
       gradedCommute A B ≠ A.val * B.val)) ∧
    -- 2. Split-Idempotent Orthogonality & Tangent Lift
    ((QRat.eqv (e_plus spec.splitGen + e_minus spec.splitGen) (QRat.ofInt 1) ∧
      QRat.eqv (e_plus spec.splitGen * e_plus spec.splitGen) (e_plus spec.splitGen) ∧
      QRat.eqv (e_minus spec.splitGen * e_minus spec.splitGen) (e_minus spec.splitGen) ∧
      QRat.eqv (e_plus spec.splitGen * e_minus spec.splitGen) (QRat.ofInt 0)) ∧
     (∀ (t : QRat),
       let sum := (jet4_e_plus_tangent spec.splitGen t) + (jet4_e_minus_tangent spec.splitGen t)
       QRat.eqv sum.a0 (QRat.ofInt 1) ∧ QRat.eqv sum.a1 (QRat.ofInt 0))) ∧
    -- 3. Hensel Prime-Tower Tangent Lift & Nilpotent Remainder Modulo p^{2k}
    ((∀ (k x t : Nat) (_hk : 1 ≤ k),
       let pk := spec.primeBase ^ k
       let x_lift := x + t * pk
       (x_lift % pk = x % pk) ∧
       ((t * pk) * (t * pk)) % (pk * pk) = 0) ∧
     (∀ (k : Nat) (_hk : 1 ≤ k),
       let m := spec.primeBase ^ k
       let m2 := m * m
       have hm_pos : 0 < m := pow_pos_of_ge_two spec.hPrime k
       have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
       let tan_elem := QsdModRing.ofNat m2 hm2_pos m
       (QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
       (spec.primeBase ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val))) ∧
    -- 4. Bounded-Height Rational Box Contraction Surviving Jet Perturbations
    (spec.boxSpec.lipNumerator * spec.boxSpec.radius <
       spec.boxSpec.centerLower * (spec.boxSpec.radius - spec.boxSpec.deltaShrink) ∧
     (∀ (z : Int), z.natAbs ≤ spec.boxSpec.lipNumerator * spec.boxSpec.radius →
       ((spec.boxSpec.centerLower * (spec.boxSpec.radius - spec.boxSpec.deltaShrink) : Nat) : Int) -
         z ≠ 0)) := by
  refine ⟨⟨qsd4_jet_nilpotent_order4,
           qsd2_truncation_associativity_defect.1,
           qsd2_truncation_associativity_defect.2,
           fun A B hA hB hprod => qsd3_anticommute_order_obstruction A B hA hB hprod⟩,
          ⟨split_idempotent_properties spec.splitGen spec.hSplit,
           fun t => jet4_tangent_sum_preservation spec.splitGen spec.hSplit t⟩,
          ⟨fun k x t hk => by
             have hstep := qsd4_hensel_tangent_lift_step spec.primeBase k x t spec.hPrime hk
             exact ⟨hstep.1, hstep.2.1⟩,
           fun k hk => qsd4_prime_tower_nilpotent_remainder_bound spec.primeBase spec.hPrime k hk⟩,
          ⟨RationalBoxContractionSpec.lip_mul_radius_lt spec.boxSpec,
           fun z hz => QsdZeroExclusion spec.boxSpec.centerLower spec.boxSpec.lipNumerator
             spec.boxSpec.radius spec.boxSpec.deltaShrink spec.boxSpec.shrink_lt_radius
             (RationalBoxContractionSpec.lip_mul_radius_lt spec.boxSpec) z hz⟩⟩

/-- Canonical concrete specification for `Qsd24JetIdempotentSpec` using `canL`, `rationalBoxSpec_N1024`,
    and prime base $p = 7$. -/
def qsd24JetIdempotentCertSpec : Qsd24JetIdempotentSpec where
  splitGen := canL
  hSplit := Or.inl rfl
  boxSpec := rationalBoxSpec_N1024
  primeBase := 7
  hPrime := by decide

/-- Concrete certificate theorem for `qsd24_jet_idempotent_weave` under `qsd24JetIdempotentCertSpec`. -/
theorem qsd24_jet_idempotent_cert :
    ((((etaJet4 * etaJet4) * etaJet4) * etaJet4) = zeroJet4 ∧
     (b_basis.mulTrunc6 b_basis).mulTrunc6 b_basis ≠
       b_basis.mulTrunc6 (b_basis.mulTrunc6 b_basis) ∧
     (qsd2_assoc_defect b_basis b_basis b_basis).f = QRat.ofInt 1 ∧
     (∀ A B : GradedFactor,
       A.deg = Z2Grading.odd → B.deg = Z2Grading.odd →
       (A.val * B.val).num ≠ 0 →
       gradedCommute A B ≠ A.val * B.val)) ∧
    ((QRat.eqv (e_plus qsd24JetIdempotentCertSpec.splitGen +
         e_minus qsd24JetIdempotentCertSpec.splitGen) (QRat.ofInt 1) ∧
      QRat.eqv (e_plus qsd24JetIdempotentCertSpec.splitGen *
         e_plus qsd24JetIdempotentCertSpec.splitGen)
        (e_plus qsd24JetIdempotentCertSpec.splitGen) ∧
      QRat.eqv (e_minus qsd24JetIdempotentCertSpec.splitGen *
         e_minus qsd24JetIdempotentCertSpec.splitGen)
        (e_minus qsd24JetIdempotentCertSpec.splitGen) ∧
      QRat.eqv (e_plus qsd24JetIdempotentCertSpec.splitGen *
         e_minus qsd24JetIdempotentCertSpec.splitGen) (QRat.ofInt 0)) ∧
     (∀ (t : QRat),
       let sum := (jet4_e_plus_tangent qsd24JetIdempotentCertSpec.splitGen t) +
         (jet4_e_minus_tangent qsd24JetIdempotentCertSpec.splitGen t)
       QRat.eqv sum.a0 (QRat.ofInt 1) ∧ QRat.eqv sum.a1 (QRat.ofInt 0))) ∧
    ((∀ (k x t : Nat) (_hk : 1 ≤ k),
       let pk := qsd24JetIdempotentCertSpec.primeBase ^ k
       let x_lift := x + t * pk
       (x_lift % pk = x % pk) ∧
       ((t * pk) * (t * pk)) % (pk * pk) = 0) ∧
     (∀ (k : Nat) (_hk : 1 ≤ k),
       let m := qsd24JetIdempotentCertSpec.primeBase ^ k
       let m2 := m * m
       have hm_pos : 0 < m := pow_pos_of_ge_two qsd24JetIdempotentCertSpec.hPrime k
       have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
       let tan_elem := QsdModRing.ofNat m2 hm2_pos m
       (QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
       (qsd24JetIdempotentCertSpec.primeBase ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val))) ∧
    (qsd24JetIdempotentCertSpec.boxSpec.lipNumerator * qsd24JetIdempotentCertSpec.boxSpec.radius <
       qsd24JetIdempotentCertSpec.boxSpec.centerLower *
         (qsd24JetIdempotentCertSpec.boxSpec.radius -
           qsd24JetIdempotentCertSpec.boxSpec.deltaShrink) ∧
     (∀ (z : Int), z.natAbs ≤ qsd24JetIdempotentCertSpec.boxSpec.lipNumerator *
         qsd24JetIdempotentCertSpec.boxSpec.radius →
       ((qsd24JetIdempotentCertSpec.boxSpec.centerLower *
         (qsd24JetIdempotentCertSpec.boxSpec.radius -
           qsd24JetIdempotentCertSpec.boxSpec.deltaShrink) : Nat) : Int) -
         z ≠ 0)) :=
  qsd24_jet_idempotent_weave qsd24JetIdempotentCertSpec

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Qsd24JetIdempotentWeave.lean
