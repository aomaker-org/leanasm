-- Path: leanasm/src/LeanAsm/QuasiRiemann/JacobianRankinSelbergWeave.lean
-- Weaves split Genus2Jacobian (Core, GroupLaw) with RankinSelbergGSp4Sub78Bridge.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.Genus2Jacobian.Core
import LeanAsm.Genus2Jacobian.GroupLaw
import LeanAsm.QuasiRiemann.RankinSelbergGSp4Sub78Bridge

open LeanAsm.Genus2MultiPrimeWeil
open LeanAsm.Genus2Jacobian.Core
open LeanAsm.Genus2Jacobian.GroupLaw
open LeanAsm.QuasiRiemann.RankinSelbergGSp4Sub78Bridge

namespace LeanAsm.QuasiRiemann.JacobianRankinSelbergWeave

/-!
# Split Genus2Jacobian and Rankin-Selberg / GSp(4) / Sub-7/8 Weave Bridge

This module constructively weaves:
1. Modularized genus-2 Jacobian divisor foundations and Cantor group-law certificates on
   $J(C)(\mathbb{F}_5)$ (`Genus2Jacobian.Core`, `Genus2Jacobian.GroupLaw`), establishing:
   - $71 \cdot [P_0 - \infty] = 0$,
   - Primitivity of $[P_0 - \infty]$ (order 71),
   - 71x71 Cayley group-law verification on the orbit,
   - Reduced Mumford divisor closure and identity properties.
2. Rankin-Selberg, multi-prime $\mathrm{GSp}(4)$ Weil bounds across
   $p \in \{7, 11, 13, 17, 19, 23\}$, and sub-7/8 non-vanishing strip certificates
   (`RankinSelbergGSp4Sub78Bridge`).

All proofs are constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

/-- Bundled specification weaving modularized genus-2 Jacobian certificates
    with Rankin-Selberg / GSp(4) / sub-7/8 strip certificate bridge. -/
structure JacobianRankinSelbergWeaveSpec where
  rsSpec : RankinSelbergGSp4Sub78BridgeSpec

/-- Constructive bridge theorem connecting modularized genus-2 Jacobian group law
    and order certificates with the Rankin-Selberg / GSp(4) / sub-7/8 strip bridge. -/
theorem jacobian_split_rankin_selberg_weave (spec : JacobianRankinSelbergWeaveSpec) :
    -- 1. Genus2Jacobian Core & GroupLaw certificates
    (cantorSmul 71 D0 = MumfordDivisor.zero ∧
     (∀ k : Nat, 1 ≤ k → k ≤ 70 → cantorSmul k D0 ≠ MumfordDivisor.zero) ∧
     isReducedMumford D0.u D0.v = true ∧
     ((∀ A B C, inD0Orbit A → inD0Orbit B → inD0Orbit C →
         cantorAdd (cantorAdd A B) C = cantorAdd A (cantorAdd B C)) ∧
      (∀ A B, inD0Orbit A → inD0Orbit B → cantorAdd A B = cantorAdd B A) ∧
      (∀ A, inD0Orbit A →
         cantorAdd A MumfordDivisor.zero = A ∧ cantorAdd MumfordDivisor.zero A = A) ∧
      (∀ A, inD0Orbit A →
         inD0Orbit (cantorNeg A) ∧
         cantorAdd A (cantorNeg A) = MumfordDivisor.zero ∧
         cantorAdd (cantorNeg A) A = MumfordDivisor.zero))) ∧
    -- 2. Rankin-Selberg, GSp(4) and sub-7/8 strip bridge
    (((∀ p ∈ spec.rsSpec.goodPrimes, Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
        Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
          (p : Int) ^ 2 * Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ T : Int,
        Genus2MultiPrimeWeil.standardEulerPoly p T =
          (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor (p : Int)
            (Genus2MultiPrimeWeil.frobeniusTrace p) (Genus2MultiPrimeWeil.degree2Trace p) T) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
        Genus2WeilGSp4Weave.standardEulerHomogP p d n =
          -Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
      (∀ p ∈ spec.rsSpec.goodPrimes, Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
     ((∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
        0 < LanglandsRankinSelbergBridge.rsClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
        0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ al1 al2 lam T : Int,
        GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
          (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2))) ∧
     ((2 * spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
         spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
       spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
         (spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius -
           spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
       spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
         spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius <
       spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
         (spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius -
           spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
      (QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen2 ≤
         2 * QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum2
           spec.rsSpec.stripBridgeSpec.vDen2 ∧
       QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum2
           spec.rsSpec.stripBridgeSpec.vDen2 *
         QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen1 <
       QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum1
           spec.rsSpec.stripBridgeSpec.vDen1 *
         QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen2 ∧
       8 * QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum1
           spec.rsSpec.stripBridgeSpec.vDen1 ≤
         7 * QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen1) ∧
      (0 < spec.rsSpec.stripBridgeSpec.weaveSpec.margin ∧
       spec.rsSpec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
      (QuasiRiemann.QRat.mk' 1 2 < spec.rsSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
       spec.rsSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.qrhThresholdSevenEighths))) := by
  have hJac :
      cantorSmul 71 D0 = MumfordDivisor.zero ∧
      (∀ k : Nat, 1 ≤ k → k ≤ 70 → cantorSmul k D0 ≠ MumfordDivisor.zero) ∧
      isReducedMumford D0.u D0.v = true ∧
      ((∀ A B C, inD0Orbit A → inD0Orbit B → inD0Orbit C →
          cantorAdd (cantorAdd A B) C = cantorAdd A (cantorAdd B C)) ∧
       (∀ A B, inD0Orbit A → inD0Orbit B → cantorAdd A B = cantorAdd B A) ∧
       (∀ A, inD0Orbit A →
          cantorAdd A MumfordDivisor.zero = A ∧ cantorAdd MumfordDivisor.zero A = A) ∧
       (∀ A, inD0Orbit A →
          inD0Orbit (cantorNeg A) ∧
          cantorAdd A (cantorNeg A) = MumfordDivisor.zero ∧
          cantorAdd (cantorNeg A) A = MumfordDivisor.zero)) :=
    ⟨jacobian_D0_order_71, jacobian_D0_primitive, D0_is_reduced, jacobian_group_axioms_on_orbit⟩
  have hRS := rankin_selberg_gsp4_sub78_bridge spec.rsSpec
  exact ⟨hJac, hRS⟩

/-- Concrete bridge specification for the Rung 32000 sub-7/8 strip certificate. -/
def jacobianRankinSelbergRung32000Spec : JacobianRankinSelbergWeaveSpec where
  rsSpec := rankinSelbergGSp4Rung32000Spec

/-- Concrete certificate theorem weaving split Genus2Jacobian and Rankin-Selberg
    GSp(4) sub-7/8 strip certificates at Rung 32000. -/
theorem jacobian_split_rankin_selberg_cert :
    -- Genus2Jacobian order & group law certificates
    (cantorSmul 71 D0 = MumfordDivisor.zero ∧
     (∀ k : Nat, 1 ≤ k → k ≤ 70 → cantorSmul k D0 ≠ MumfordDivisor.zero) ∧
     isReducedMumford D0.u D0.v = true ∧
     ((∀ A B C, inD0Orbit A → inD0Orbit B → inD0Orbit C →
         cantorAdd (cantorAdd A B) C = cantorAdd A (cantorAdd B C)) ∧
      (∀ A B, inD0Orbit A → inD0Orbit B → cantorAdd A B = cantorAdd B A) ∧
      (∀ A, inD0Orbit A →
         cantorAdd A MumfordDivisor.zero = A ∧ cantorAdd MumfordDivisor.zero A = A) ∧
      (∀ A, inD0Orbit A →
         inD0Orbit (cantorNeg A) ∧
         cantorAdd A (cantorNeg A) = MumfordDivisor.zero ∧
         cantorAdd (cantorNeg A) A = MumfordDivisor.zero))) ∧
    -- Concrete Rankin-Selberg GSp(4) Rung 32000 certificate
    (((∀ p ∈ goodPrimesList, Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
      (∀ p ∈ goodPrimesList, ∀ n d : Int,
        Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
          (p : Int) ^ 2 * Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
      (∀ p ∈ goodPrimesList, ∀ T : Int,
        Genus2MultiPrimeWeil.standardEulerPoly p T =
          (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor (p : Int)
            (Genus2MultiPrimeWeil.frobeniusTrace p) (Genus2MultiPrimeWeil.degree2Trace p) T) ∧
      (∀ p ∈ goodPrimesList, ∀ n d : Int,
        Genus2WeilGSp4Weave.standardEulerHomogP p d n =
          -Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
      (∀ p ∈ goodPrimesList, Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
     ((∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
        0 < LanglandsRankinSelbergBridge.rsClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
        0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p
          (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
      (∀ al1 al2 lam T : Int,
        GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
          (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2))) ∧
     ((2 * rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
         rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
         (rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius -
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
         rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius <
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
         (rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.radius -
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
      (QuasiRiemann.mollifierThetaDen rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen2 ≤
         2 * QuasiRiemann.mollifierThetaNum rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vNum2
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen2 ∧
       QuasiRiemann.mollifierThetaNum rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vNum2
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen2 *
         QuasiRiemann.mollifierThetaDen rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen1 <
       QuasiRiemann.mollifierThetaNum rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vNum1
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen1 *
         QuasiRiemann.mollifierThetaDen rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen2 ∧
       8 * QuasiRiemann.mollifierThetaNum rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vNum1
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen1 ≤
         7 * QuasiRiemann.mollifierThetaDen rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.vDen1) ∧
      (rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.margin = 2682997 ∧
       (4 * rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.scaleN) *
           (rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.tailBound *
             rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.tailBound) ≤
         ((2 * rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.denomM) *
           (2 * rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.denomM)) *
           (rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.tailNum *
             rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.gate.tailNum) ∧
       QuasiRiemann.QRat.mk' 1 2 <
         rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.QRat.mk' 3 4 ∧
       rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.qrhThresholdSevenEighths ∧
       QuasiRiemann.zdGuthMaynard.exponent
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 1 2) ∧
       QuasiRiemann.zdHuxley.exponent
           rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
         QuasiRiemann.zdHuxley.exponent (QuasiRiemann.QRat.mk' 1 2) ∧
       let rect := rankinSelbergGSp4Rung32000Spec.stripBridgeSpec.weaveSpec.strip.rectSpec
       rect.HasCertifiedNonVanishing ∧
       (QuasiRiemann.highTruncTiles_1e30_N2048.length = 4 ∧
         (∀ t ∈ QuasiRiemann.highTruncTiles_1e30_N2048, QuasiRiemann.IsValidLipTile2D t))))) := by
  have hBridge := jacobian_split_rankin_selberg_weave jacobianRankinSelbergRung32000Spec
  have hCert := rankin_selberg_gsp4_rung32000_cert
  exact ⟨hBridge.1, hCert⟩

end LeanAsm.QuasiRiemann.JacobianRankinSelbergWeave

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/JacobianRankinSelbergWeave.lean
