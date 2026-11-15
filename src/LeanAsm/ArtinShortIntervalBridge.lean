-- Path: leanasm/src/LeanAsm/ArtinShortIntervalBridge.lean
-- GL(1) Artin character-twisted short-interval prime bounds over Fermat primes via MiniVM NTT.
-- Max Column: 120 Columns

import LeanAsm.ArtinFermatBridge
import LeanAsm.MiniVMNttBridge
import LeanAsm.EulerFactorNonVanishing
import LeanAsm.QuasiRiemann.ShortIntervalPrimes
import LeanAsm.QuasiRiemann.ParametricQrhLadder

namespace ArtinShortIntervalBridge

open ArtinFermatBridge
open MiniVM
open MiniVMNttBridge
open NttArithmetic
open EulerFactorNonVanishing
open QuasiRiemann

-- =============================================================================
-- Part 1: Exact Z[i] Order-4 Artin Character Orthogonality & MiniVM NTT Bridge
-- =============================================================================

/-- Real part of the order-4 Gaussian character `i^(r * m)` (`1, i, -1, -i`). -/
def artinCharGaussRe (r m : Nat) : Int :=
  match (r * m) % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

/-- Imaginary part of the order-4 Gaussian character `i^(r * m)`. -/
def artinCharGaussIm (r m : Nat) : Int :=
  match (r * m) % 4 with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => -1

/-- Real part of the `r`-th GL(1) order-4 character-twisted sum `∑_{m=0}^3 χ_r(m) * v(m)`. -/
def artinTwistedSumRe (v : Fin 4 → Int) (r : Nat) : Int :=
  artinCharGaussRe r 0 * v 0 + artinCharGaussRe r 1 * v 1 +
  artinCharGaussRe r 2 * v 2 + artinCharGaussRe r 3 * v 3

/-- Imaginary part of the `r`-th GL(1) order-4 character-twisted sum `∑_{m=0}^3 χ_r(m) * v(m)`. -/
def artinTwistedSumIm (v : Fin 4 → Int) (r : Nat) : Int :=
  artinCharGaussIm r 0 * v 0 + artinCharGaussIm r 1 * v 1 +
  artinCharGaussIm r 2 * v 2 + artinCharGaussIm r 3 * v 3

/-- Real part of the inverse orthogonality sum `∑_{r=0}^3 conj(χ_r(m)) * T_r`. -/
def artinInverseSumRe (TRe TIm : Nat → Int) (m : Fin 4) : Int :=
  (artinCharGaussRe 0 m.val * TRe 0 + artinCharGaussIm 0 m.val * TIm 0) +
  (artinCharGaussRe 1 m.val * TRe 1 + artinCharGaussIm 1 m.val * TIm 1) +
  (artinCharGaussRe 2 m.val * TRe 2 + artinCharGaussIm 2 m.val * TIm 2) +
  (artinCharGaussRe 3 m.val * TRe 3 + artinCharGaussIm 3 m.val * TIm 3)

/-- Imaginary part of the inverse orthogonality sum `∑_{r=0}^3 conj(χ_r(m)) * T_r`. -/
def artinInverseSumIm (TRe TIm : Nat → Int) (m : Fin 4) : Int :=
  (artinCharGaussRe 0 m.val * TIm 0 - artinCharGaussIm 0 m.val * TRe 0) +
  (artinCharGaussRe 1 m.val * TIm 1 - artinCharGaussIm 1 m.val * TRe 1) +
  (artinCharGaussRe 2 m.val * TIm 2 - artinCharGaussIm 2 m.val * TRe 2) +
  (artinCharGaussRe 3 m.val * TIm 3 - artinCharGaussIm 3 m.val * TRe 3)

/-- Exact integer orthogonality identity in `ℤ[i]`:
`∑_{r=0}^3 conj(χ_r(m)) * (∑_n χ_r(n) * v(n)) = 4 * v(m)` with zero imaginary residual. -/
theorem artin_gaussian_char_orthogonality (v : Fin 4 → Int) (m : Fin 4) :
    artinInverseSumRe (artinTwistedSumRe v) (artinTwistedSumIm v) m = 4 * v m ∧
    artinInverseSumIm (artinTwistedSumRe v) (artinTwistedSumIm v) m = 0 := by
  rcases m with ⟨m, hm⟩
  match m with
  | 0 =>
    simp [artinInverseSumRe, artinInverseSumIm, artinTwistedSumRe, artinTwistedSumIm,
      artinCharGaussRe, artinCharGaussIm]
    exact ⟨by omega, by omega⟩
  | 1 =>
    simp [artinInverseSumRe, artinInverseSumIm, artinTwistedSumRe, artinTwistedSumIm,
      artinCharGaussRe, artinCharGaussIm]
    exact ⟨by omega, by omega⟩
  | 2 =>
    simp [artinInverseSumRe, artinInverseSumIm, artinTwistedSumRe, artinTwistedSumIm,
      artinCharGaussRe, artinCharGaussIm]
    exact ⟨by omega, by omega⟩
  | 3 =>
    simp [artinInverseSumRe, artinInverseSumIm, artinTwistedSumRe, artinTwistedSumIm,
      artinCharGaussRe, artinCharGaussIm]
    exact ⟨by omega, by omega⟩
  | _ + 4 => exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 4 _) hm)

private def fin4OfVec4 (v : Vec4) (i : Fin 4) : Int :=
  match i.val with
  | 0 => (v.x0 : Int)
  | 1 => (v.x1 : Int)
  | 2 => (v.x2 : Int)
  | _ => (v.x3 : Int)

private theorem artinTwistedGauss_mod_eq_charTransform (p w : Nat) (hp : 0 < p)
    (hsq : (w * w + 1) % p = 0) (v : Vec4) :
    let vf := fin4OfVec4 v
    let X := artinCharTransform4 p w v
    ((artinTwistedSumRe vf 0 +
        (w : Int) * artinTwistedSumIm vf 0) % (p : Int) = (X.x0 : Int) % p) ∧
    ((artinTwistedSumRe vf 1 +
        (w : Int) * artinTwistedSumIm vf 1) % (p : Int) = (X.x1 : Int) % p) ∧
    ((artinTwistedSumRe vf 2 +
        (w : Int) * artinTwistedSumIm vf 2) % (p : Int) = (X.x2 : Int) % p) ∧
    ((artinTwistedSumRe vf 3 +
        (w : Int) * artinTwistedSumIm vf 3) % (p : Int) = (X.x3 : Int) % p) := by
  have hntt : artinCharTransform4 p w v = ntt4 p w v :=
    artinCharTransform4_eq_ntt4_generic p w hp hsq v
  rw [hntt]
  rcases v with ⟨a, b, c, d⟩
  have hlt (u : Nat) : u % p < p := Nat.mod_lt u hp
  have hsub (u y : Nat) :
      (((u + p - y % p) % p : Nat) : Int) % (p : Int) = ((u : Int) - (y : Int)) % p := by
    have hle : y % p ≤ u + p := by
      have := hlt y
      omega
    rw [Int.natCast_emod, Int.emod_emod, Int.ofNat_sub hle]
    have ha : ((u + p : Nat) : Int) = (u : Int) + p := rfl
    rw [ha, Int.natCast_emod, Int.sub_emod, Int.add_emod, Int.emod_self, Int.add_zero,
        Int.emod_emod, Int.emod_emod, ← Int.sub_emod]
  have hadd0 : (((a + c) % p : Nat) : Int) % p = ((a : Int) + c) % p := by
    rw [Int.natCast_emod, Int.emod_emod]; rfl
  have hadd1 : (((b + d) % p % p : Nat) : Int) % p = ((b : Int) + d) % p := by
    rw [Int.natCast_emod, Int.natCast_emod, Int.emod_emod, Int.emod_emod]; rfl
  have hsub0 : (((a + p - c % p) % p : Nat) : Int) % p = ((a : Int) - c) % p := hsub a c
  have hsub1 : (((b + p - d % p) % p * w % p : Nat) : Int) % p = (((b : Int) - d) * w) % p := by
    rw [Int.natCast_emod, Int.emod_emod, Int.natCast_mul, Int.mul_emod, hsub b d, ← Int.mul_emod]
  simp only [ntt4, nttButterfly2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hlhs : artinTwistedSumRe (fin4OfVec4 ⟨a, b, c, d⟩) 0 +
        (w : Int) * artinTwistedSumIm (fin4OfVec4 ⟨a, b, c, d⟩) 0 =
        ((a : Int) + c) + ((b : Int) + d) := by
      simp [fin4OfVec4, artinTwistedSumRe, artinTwistedSumIm,
        artinCharGaussRe, artinCharGaussIm]
      omega
    have hr : (((((a + c) % p + (b + d) % p % p) % p : Nat) : Int) % p) =
        (((a : Int) + c) + ((b : Int) + d)) % p := by
      rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add, Int.add_emod, hadd0, hadd1,
          ← Int.add_emod]
    rw [hlhs, hr]
  · have hlhs : artinTwistedSumRe (fin4OfVec4 ⟨a, b, c, d⟩) 1 +
        (w : Int) * artinTwistedSumIm (fin4OfVec4 ⟨a, b, c, d⟩) 1 =
        ((a : Int) - c) + (((b : Int) - d) * w) := by
      simp [fin4OfVec4, artinTwistedSumRe, artinTwistedSumIm,
        artinCharGaussRe, artinCharGaussIm, Int.sub_mul, Int.mul_add, Int.mul_neg]
      have hc1 : (w : Int) * (b : Int) = (b : Int) * (w : Int) := Int.mul_comm _ _
      have hc2 : (w : Int) * (d : Int) = (d : Int) * (w : Int) := Int.mul_comm _ _
      rw [hc1, hc2]
      omega
    have hr : (((((a + p - c % p) % p + (b + p - d % p) % p * w % p) % p : Nat) : Int) % p) =
        (((a : Int) - c) + (((b : Int) - d) * w)) % p := by
      rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add, Int.add_emod, hsub0, hsub1,
          ← Int.add_emod]
    rw [hlhs, hr]
  · have hlhs : artinTwistedSumRe (fin4OfVec4 ⟨a, b, c, d⟩) 2 +
        (w : Int) * artinTwistedSumIm (fin4OfVec4 ⟨a, b, c, d⟩) 2 =
        ((a : Int) + c) - ((b : Int) + d) := by
      simp [fin4OfVec4, artinTwistedSumRe, artinTwistedSumIm,
        artinCharGaussRe, artinCharGaussIm]
      omega
    have hr : ((((((a + c) % p + p - (b + d) % p % p % p) % p : Nat) : Int) % p)) =
        (((a : Int) + c) - ((b : Int) + d)) % p := by
      have hs := hsub ((a + c) % p) ((b + d) % p % p)
      rw [hs, Int.sub_emod, hadd0, hadd1, ← Int.sub_emod]
    rw [hlhs, hr]
  · have hlhs : artinTwistedSumRe (fin4OfVec4 ⟨a, b, c, d⟩) 3 +
        (w : Int) * artinTwistedSumIm (fin4OfVec4 ⟨a, b, c, d⟩) 3 =
        ((a : Int) - c) - (((b : Int) - d) * w) := by
      simp [fin4OfVec4, artinTwistedSumRe, artinTwistedSumIm,
        artinCharGaussRe, artinCharGaussIm, Int.sub_mul, Int.mul_add, Int.mul_neg]
      have hc1 : (w : Int) * (b : Int) = (b : Int) * (w : Int) := Int.mul_comm _ _
      have hc2 : (w : Int) * (d : Int) = (d : Int) * (w : Int) := Int.mul_comm _ _
      rw [hc1, hc2]
      omega
    have hr : ((((((a + p - c % p) % p + p - (b + p - d % p) % p * w % p % p) % p : Nat) : Int) %
        p)) = (((a : Int) - c) - (((b : Int) - d) * w)) % p := by
      have hs := hsub ((a + p - c % p) % p) ((b + p - d % p) % p * w % p)
      rw [hs, Int.sub_emod, hsub0, hsub1, ← Int.sub_emod]
    rw [hlhs, hr]

/-- Theorem (`MiniVM` 4-Point NTT Residue-Class Character Recovery):
Composes `ArtinFermatBridge.artin_char_transform_eq_ntt4`, `artin_char_orthogonality_minivm`,
and `artin_gaussian_char_orthogonality` across all Fermat-tower primes `{5, 17, 257, 65537}`:
1. Executing `ntt4AsmFermat` computes both `artinCharTransform4` and the `ℤ[i] → ℤ/F_kℤ`
   character-twisted image `Re(T_r) + ω₄ Im(T_r) mod F_k`.
2. Executing `intt4AsmFermat` inverts `ntt4AsmFermat` back to the residue-class coset vector
   `v` in `MiniVM` registers `r0..r3`, matching `4 * v(m)` via cleared Gaussian orthogonality.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem artin_ntt4_residue_class_recovery :
    ∀ spec ∈ artinFermatTowerSpecs,
      ∀ (s : State) (v : Vec4),
        v.x0 < spec.primeMod → v.x1 < spec.primeMod →
        v.x2 < spec.primeMod → v.x3 < spec.primeMod →
        s.r0 = v.x0 → s.r1 = v.x1 → s.r2 = v.x2 → s.r3 = v.x3 →
        let s1 := runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)
        let s2 := runProgram s1 (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
        let vf := fin4OfVec4 v
        let X := artinCharTransform4 spec.primeMod spec.omega4 v
        (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : Vec4) = X ∧
        X = ntt4 spec.primeMod spec.omega4 v ∧
        ((artinTwistedSumRe vf 0 +
            (spec.omega4 : Int) * artinTwistedSumIm vf 0) % (spec.primeMod : Int) =
          (s1.r0 : Int) % spec.primeMod) ∧
        ((artinTwistedSumRe vf 1 +
            (spec.omega4 : Int) * artinTwistedSumIm vf 1) % (spec.primeMod : Int) =
          (s1.r1 : Int) % spec.primeMod) ∧
        ((artinTwistedSumRe vf 2 +
            (spec.omega4 : Int) * artinTwistedSumIm vf 2) % (spec.primeMod : Int) =
          (s1.r2 : Int) % spec.primeMod) ∧
        ((artinTwistedSumRe vf 3 +
            (spec.omega4 : Int) * artinTwistedSumIm vf 3) % (spec.primeMod : Int) =
          (s1.r3 : Int) % spec.primeMod) ∧
        (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : Vec4) = v ∧
        ((4 * s2.r0) % spec.primeMod = (4 * v.x0) % spec.primeMod ∧
         (4 * s2.r1) % spec.primeMod = (4 * v.x1) % spec.primeMod ∧
         (4 * s2.r2) % spec.primeMod = (4 * v.x2) % spec.primeMod ∧
         (4 * s2.r3) % spec.primeMod = (4 * v.x3) % spec.primeMod) ∧
        (∀ m : Fin 4,
          artinInverseSumRe (artinTwistedSumRe vf) (artinTwistedSumIm vf) m = 4 * vf m) := by
  intro spec hmem s v h0 h1 h2 h3 hr0 hr1 hr2 hr3
  have hval := artinFermatTowerSpecs_valid spec hmem
  have hp0 : 0 < spec.primeMod := Nat.lt_trans Nat.zero_lt_one hval.2.2.1
  have hsq : (spec.omega4 * spec.omega4 + 1) % spec.primeMod = 0 := hval.2.2.2.2.2.2.1
  rcases artin_char_orthogonality_minivm.1 spec hmem s v h0 h1 h2 h3 hr0 hr1 hr2 hr3 with
    ⟨hs1, hs2⟩
  have hntt : artinCharTransform4 spec.primeMod spec.omega4 v =
      ntt4 spec.primeMod spec.omega4 v :=
    artin_char_transform_eq_ntt4.1 spec hmem v
  rcases artinTwistedGauss_mod_eq_charTransform spec.primeMod spec.omega4 hp0 hsq v with
    ⟨hm0, hm1, hm2, hm3⟩
  have hr0Eq : (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r0 =
      (artinCharTransform4 spec.primeMod spec.omega4 v).x0 := congrArg Vec4.x0 hs1
  have hr1Eq : (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r1 =
      (artinCharTransform4 spec.primeMod spec.omega4 v).x1 := congrArg Vec4.x1 hs1
  have hr2Eq : (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r2 =
      (artinCharTransform4 spec.primeMod spec.omega4 v).x2 := congrArg Vec4.x2 hs1
  have hr3Eq : (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4)).r3 =
      (artinCharTransform4 spec.primeMod spec.omega4 v).x3 := congrArg Vec4.x3 hs1
  have hs2_0 : (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
      (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r0 = v.x0 := congrArg Vec4.x0 hs2
  have hs2_1 : (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
      (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r1 = v.x1 := congrArg Vec4.x1 hs2
  have hs2_2 : (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
      (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r2 = v.x2 := congrArg Vec4.x2 hs2
  have hs2_3 : (runProgram (runProgram s (ntt4AsmFermat spec.primeMod spec.omega4))
      (intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)).r3 = v.x3 := congrArg Vec4.x3 hs2
  refine ⟨hs1, hntt, ?_, ?_, ?_, ?_, hs2, ?_, ?_⟩
  · simpa [hr0Eq] using hm0
  · simpa [hr1Eq] using hm1
  · simpa [hr2Eq] using hm2
  · simpa [hr3Eq] using hm3
  · rw [hs2_0, hs2_1, hs2_2, hs2_3]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro m
    exact (artin_gaussian_char_orthogonality (fin4OfVec4 v) m).1

-- =============================================================================
-- Part 2: Character-Twisted Short-Interval Envelope & Positivity Bridge
-- =============================================================================

/-- GL(1) Artin character-twisted short-interval specification pairing an order-4
Fermat character spec `F_k ∈ {5, 17, 257, 65537}` with an `ApShortIntervalSpec`
bounded on the beyond-`7/8` parametric QRH ladder `qrhShortExponent rungK`. -/
structure ArtinTwistedShortIntervalSpec where
  artinSpec : ArtinFermatCharacterSpec
  apSpec : ApShortIntervalSpec
  rungK : Nat
  rungK_pos : 1 ≤ rungK
  artinValid : artinSpec.Valid
  primeMod_eq : apSpec.q = artinSpec.primeMod
  phiQ_eq : apSpec.phiQ = artinSpec.galoisOrder
  theta_le_rung : apSpec.base.thetaQRat ≤ qrhShortExponent rungK
  has_ap_prime : apSpec.HasGuaranteedApPrime

private theorem four_abs_le_imp_abs_le (a b : Int) (h : Int.natAbs (4 * a) ≤ 4 * Int.natAbs b) :
    Int.natAbs a ≤ Int.natAbs b := by
  have hmul : Int.natAbs (4 * a) = 4 * Int.natAbs a := by
    rw [Int.natAbs_mul]
    rfl
  rw [hmul] at h
  omega

/-- Constructive Artin character-twisted to AP short-interval prime positivity bridge:
If `4 * ψ(x; q, a)` decomposes into four order-4 character-twisted components
`(re0X, re1X, re2X, re3X)` (where trivial character `re0X` carries main term `4 * x`,
and non-trivial characters `re1X, re2X, re3X` satisfy character-twisted Chebyshev error
bounds summing to at most `4 * errUpper`), and similarly at `x + h`, then `tw.apSpec`
satisfies the hypotheses of `ap_short_interval_psi_diff_bound` and guarantees
`(0 : Int) < thetaApXH - thetaApX` across every reduced residue class mod `F_k`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem artin_twisted_ap_short_interval_pos
    (tw : ArtinTwistedShortIntervalSpec)
    (psiApX psiApXH thetaApX thetaApXH : Int)
    (re0X re1X re2X re3X re0XH re1XH re2XH re3XH : Int)
    (e0 e1 e2 e3 : Nat)
    (hDecompX : 4 * psiApX = re0X + re1X + re2X + re3X)
    (hDecompXH : 4 * psiApXH = re0XH + re1XH + re2XH + re3XH)
    (hTrivX : Int.natAbs ((tw.apSpec.phiQ : Int) * re0X -
        4 * ((10 ^ tw.apSpec.base.xScaleExp : Nat) : Int)) ≤ tw.apSpec.phiQ * e0)
    (hTw1X : Int.natAbs ((tw.apSpec.phiQ : Int) * re1X) ≤ tw.apSpec.phiQ * e1)
    (hTw2X : Int.natAbs ((tw.apSpec.phiQ : Int) * re2X) ≤ tw.apSpec.phiQ * e2)
    (hTw3X : Int.natAbs ((tw.apSpec.phiQ : Int) * re3X) ≤ tw.apSpec.phiQ * e3)
    (hTrivXH : Int.natAbs ((tw.apSpec.phiQ : Int) * re0XH -
        4 * ((10 ^ tw.apSpec.base.xScaleExp + 10 ^ tw.apSpec.base.hScaleExp : Nat) : Int)) ≤
        tw.apSpec.phiQ * e0)
    (hTw1XH : Int.natAbs ((tw.apSpec.phiQ : Int) * re1XH) ≤ tw.apSpec.phiQ * e1)
    (hTw2XH : Int.natAbs ((tw.apSpec.phiQ : Int) * re2XH) ≤ tw.apSpec.phiQ * e2)
    (hTw3XH : Int.natAbs ((tw.apSpec.phiQ : Int) * re3XH) ≤ tw.apSpec.phiQ * e3)
    (hErrSum : e0 + e1 + e2 + e3 ≤ 4 * tw.apSpec.base.errUpper)
    (hCorr : (psiApXH - psiApX) - (thetaApXH - thetaApX) ≤
        (tw.apSpec.base.primePowerCorr : Int)) :
    Int.natAbs ((tw.apSpec.phiQ : Int) * psiApX -
        ((10 ^ tw.apSpec.base.xScaleExp : Nat) : Int)) ≤
      tw.apSpec.phiQ * tw.apSpec.base.errUpper ∧
    Int.natAbs ((tw.apSpec.phiQ : Int) * psiApXH -
        ((10 ^ tw.apSpec.base.xScaleExp + 10 ^ tw.apSpec.base.hScaleExp : Nat) : Int)) ≤
      tw.apSpec.phiQ * tw.apSpec.base.errUpper ∧
    (0 : Int) < thetaApXH - thetaApX := by
  let phiZ : Int := (tw.apSpec.phiQ : Int)
  have hCombine : ∀ (psi re0 re1 re2 re3 tgt : Int),
      4 * psi = re0 + re1 + re2 + re3 →
      Int.natAbs (phiZ * re0 - 4 * tgt) ≤ tw.apSpec.phiQ * e0 →
      Int.natAbs (phiZ * re1) ≤ tw.apSpec.phiQ * e1 →
      Int.natAbs (phiZ * re2) ≤ tw.apSpec.phiQ * e2 →
      Int.natAbs (phiZ * re3) ≤ tw.apSpec.phiQ * e3 →
      Int.natAbs (phiZ * psi - tgt) ≤ tw.apSpec.phiQ * tw.apSpec.base.errUpper := by
    intro psi re0 re1 re2 re3 tgt hDec ht0 ht1 ht2 ht3
    have h4eq : 4 * (phiZ * psi - tgt) =
        (phiZ * re0 - 4 * tgt) + phiZ * re1 + phiZ * re2 + phiZ * re3 := by
      have hMul4 : 4 * (phiZ * psi) = phiZ * (4 * psi) := by ac_rfl
      rw [Int.mul_sub, hMul4, hDec]
      simp only [Int.mul_add]
      omega
    have hTri : Int.natAbs (4 * (phiZ * psi - tgt)) ≤
        Int.natAbs (phiZ * re0 - 4 * tgt) + Int.natAbs (phiZ * re1) +
        Int.natAbs (phiZ * re2) + Int.natAbs (phiZ * re3) := by
      rw [h4eq]
      have ha := Int.natAbs_add_le
        ((phiZ * re0 - 4 * tgt) + phiZ * re1 + phiZ * re2) (phiZ * re3)
      have hb := Int.natAbs_add_le
        ((phiZ * re0 - 4 * tgt) + phiZ * re1) (phiZ * re2)
      have hc := Int.natAbs_add_le (phiZ * re0 - 4 * tgt) (phiZ * re1)
      omega
    have hSumBound :
        Int.natAbs (phiZ * re0 - 4 * tgt) + Int.natAbs (phiZ * re1) +
        Int.natAbs (phiZ * re2) + Int.natAbs (phiZ * re3) ≤
        4 * (tw.apSpec.phiQ * tw.apSpec.base.errUpper) := by
      have hMulSum : tw.apSpec.phiQ * (e0 + e1 + e2 + e3) =
          tw.apSpec.phiQ * e0 + tw.apSpec.phiQ * e1 +
          tw.apSpec.phiQ * e2 + tw.apSpec.phiQ * e3 := by
        simp only [Nat.mul_add]
      have hLe4 : tw.apSpec.phiQ * (e0 + e1 + e2 + e3) ≤
          4 * (tw.apSpec.phiQ * tw.apSpec.base.errUpper) := by
        have h1 := Nat.mul_le_mul_left tw.apSpec.phiQ hErrSum
        have hcomm : tw.apSpec.phiQ * (4 * tw.apSpec.base.errUpper) =
            4 * (tw.apSpec.phiQ * tw.apSpec.base.errUpper) := by ac_rfl
        omega
      omega
    have hAbs4 : Int.natAbs (4 * (phiZ * psi - tgt)) ≤
        4 * Int.natAbs ((tw.apSpec.phiQ * tw.apSpec.base.errUpper : Nat) : Int) := by
      rw [Int.natAbs_natCast]
      exact Nat.le_trans hTri hSumBound
    have hFinal := four_abs_le_imp_abs_le (phiZ * psi - tgt)
      ((tw.apSpec.phiQ * tw.apSpec.base.errUpper : Nat) : Int) hAbs4
    rw [Int.natAbs_natCast] at hFinal
    exact hFinal
  have hBX := hCombine psiApX re0X re1X re2X re3X
    ((10 ^ tw.apSpec.base.xScaleExp : Nat) : Int) hDecompX hTrivX hTw1X hTw2X hTw3X
  have hBXH := hCombine psiApXH re0XH re1XH re2XH re3XH
    ((10 ^ tw.apSpec.base.xScaleExp + 10 ^ tw.apSpec.base.hScaleExp : Nat) : Int)
    hDecompXH hTrivXH hTw1XH hTw2XH hTw3XH
  have hPos := ap_short_interval_psi_diff_bound tw.apSpec psiApX psiApXH thetaApX thetaApXH
    hBX hBXH hCorr tw.has_ap_prime
  exact ⟨hBX, hBXH, hPos⟩

/-- Direct coset short-interval positivity theorem via exact `ℤ[i]` orthogonality:
given 4 coset short-interval differences `c0..c3` whose character transforms
`(T_0..T_3)` invert via `artin_gaussian_char_orthogonality`, bounds on `T_0 - x` and
`|T_r|` (`r = 1, 2, 3`) directly certify positivity `0 < 4 * c_m - primeCorr` on each coset. -/
private theorem artin_coset_pos_core (t0 t1r t1i t2 t3r t3i c1r c1i c2r c3r c3i : Int)
    (mainTerm e0 e1 e2 e3 primeCorr : Nat)
    (hTriv : Int.natAbs (t0 - (mainTerm : Int)) ≤ e0)
    (hTw1 : Int.natAbs t1r + Int.natAbs t1i ≤ e1)
    (hTw2 : Int.natAbs t2 ≤ e2)
    (hTw3 : Int.natAbs t3r + Int.natAbs t3i ≤ e3)
    (hGap : e0 + e1 + e2 + e3 + primeCorr < mainTerm)
    (h1r : -(Int.natAbs t1r : Int) ≤ c1r * t1r)
    (h1i : -(Int.natAbs t1i : Int) ≤ c1i * t1i)
    (h2r : -(Int.natAbs t2 : Int) ≤ c2r * t2)
    (h3r : -(Int.natAbs t3r : Int) ≤ c3r * t3r)
    (h3i : -(Int.natAbs t3i : Int) ≤ c3i * t3i) :
    (0 : Int) < (t0 + (c1r * t1r + c1i * t1i) + c2r * t2 + (c3r * t3r + c3i * t3i)) -
      (primeCorr : Int) := by
  omega

theorem artin_twisted_coset_short_interval_pos
    (cDiff : Fin 4 → Int) (mainTerm : Nat) (e0 e1 e2 e3 primeCorr : Nat)
    (hTriv : Int.natAbs (artinTwistedSumRe cDiff 0 - (mainTerm : Int)) ≤ e0)
    (hTw1 : Int.natAbs (artinTwistedSumRe cDiff 1) +
        Int.natAbs (artinTwistedSumIm cDiff 1) ≤ e1)
    (hTw2 : Int.natAbs (artinTwistedSumRe cDiff 2) ≤ e2)
    (hTw3 : Int.natAbs (artinTwistedSumRe cDiff 3) +
        Int.natAbs (artinTwistedSumIm cDiff 3) ≤ e3)
    (hGap : e0 + e1 + e2 + e3 + primeCorr < mainTerm) :
    ∀ m : Fin 4, (0 : Int) < 4 * cDiff m - (primeCorr : Int) := by
  intro m
  have hOrtho := (artin_gaussian_char_orthogonality cDiff m).1
  rw [← hOrtho]
  dsimp [artinInverseSumRe]
  have hcg0 : artinCharGaussRe 0 m.val = 1 ∧ artinCharGaussIm 0 m.val = 0 := by
    rcases m with ⟨m, hm⟩
    match m with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 4 _) hm)
  have hcg1 : Int.natAbs (artinCharGaussRe 1 m.val) ≤ 1 ∧
      Int.natAbs (artinCharGaussIm 1 m.val) ≤ 1 := by
    rcases m with ⟨m, hm⟩
    match m with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 4 _) hm)
  have hcg2 : Int.natAbs (artinCharGaussRe 2 m.val) ≤ 1 ∧
      artinCharGaussIm 2 m.val = 0 := by
    rcases m with ⟨m, hm⟩
    match m with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 4 _) hm)
  have hcg3 : Int.natAbs (artinCharGaussRe 3 m.val) ≤ 1 ∧
      Int.natAbs (artinCharGaussIm 3 m.val) ≤ 1 := by
    rcases m with ⟨m, hm⟩
    match m with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 4 _) hm)
  have hMulBound : ∀ (a b : Int), Int.natAbs a ≤ 1 → -(Int.natAbs b : Int) ≤ a * b := by
    intro a b ha
    have hmul : Int.natAbs (a * b) ≤ Int.natAbs b := by
      rw [Int.natAbs_mul]
      exact Nat.le_trans (Nat.mul_le_mul_right _ ha) (Nat.le_of_eq (Nat.one_mul _))
    omega
  rw [hcg0.1, hcg0.2, hcg2.2]
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero]
  exact artin_coset_pos_core
    (artinTwistedSumRe cDiff 0) (artinTwistedSumRe cDiff 1) (artinTwistedSumIm cDiff 1)
    (artinTwistedSumRe cDiff 2) (artinTwistedSumRe cDiff 3) (artinTwistedSumIm cDiff 3)
    (artinCharGaussRe 1 m.val) (artinCharGaussIm 1 m.val) (artinCharGaussRe 2 m.val)
    (artinCharGaussRe 3 m.val) (artinCharGaussIm 3 m.val)
    mainTerm e0 e1 e2 e3 primeCorr hTriv hTw1 hTw2 hTw3 hGap
    (hMulBound _ _ hcg1.1) (hMulBound _ _ hcg1.2) (hMulBound _ _ hcg2.1)
    (hMulBound _ _ hcg3.1) (hMulBound _ _ hcg3.2)

-- =============================================================================
-- Part 3: Concrete Beyond-7/8 Fermat-Tower {5, 17, 257, 65537} Certificates
-- =============================================================================

/-- QRH exponent `θ = 39/64` amplified by Kim-Sarnak `Sym^4` (`7/64`). -/
def qrhThresholdKimSarnak : QRat := QRat.mk' 39 64 (by decide)

/-- Chebyshev remainder spec at `x = 10^48` (`k = 4`) for `θ = 5/8`. -/
def chebyshevSpec48_58 : ChebyshevRemainderSpec :=
  ⟨4, by decide, 1, by decide, qrhThresholdFiveEighths, by decide, by decide⟩

/-- Chebyshev remainder spec at `x = 10^48` (`k = 4`) for `θ = 2/3`. -/
def chebyshevSpec48_23 : ChebyshevRemainderSpec :=
  ⟨4, by decide, 1, by decide, qrhThresholdTwoThirds, by decide, by decide⟩

/-- Chebyshev remainder spec at `x = 10^192` (`k = 16`) for `θ = 39/64 < 5/8`. -/
def chebyshevSpec192_3964 : ChebyshevRemainderSpec :=
  ⟨16, by decide, 1, by decide, qrhThresholdKimSarnak, by decide, by decide⟩

/-- Base Chebyshev short-interval spec at `(x = 10^48, h = 10^42)` for `θ = 2/3`. -/
def shortIntervalQrh48_23Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 2
    thetaDen := 3
    xScaleExp := 48
    hScaleExp := 42
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec48_23
    primePowerCorr := 10 ^ 32
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Base Chebyshev short-interval spec at `(x = 10^48, h = 10^40)` for `θ = 5/8`. -/
def shortIntervalQrh48_58Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 5
    thetaDen := 8
    xScaleExp := 48
    hScaleExp := 40
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec48_58
    primePowerCorr := 10 ^ 30
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Base Chebyshev short-interval spec at `(x = 10^192, h = 10^128)` for `θ = 39/64 < 5/8`. -/
def shortIntervalQrh192_3964Spec : ShortIntervalChebyshevSpec :=
  { thetaNum := 39
    thetaDen := 64
    xScaleExp := 192
    hScaleExp := 128
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec192_3964
    primePowerCorr := 10 ^ 117
    thetaDen_pos := by decide
    theta_lt_one := by decide }

/-- Base Chebyshev short-interval spec at `(x = 10^96, h = 10^62)` for `θ = 17/32`. -/
def shortIntervalQrh96_1732ApBaseSpec : ShortIntervalChebyshevSpec :=
  { thetaNum := 17
    thetaDen := 32
    xScaleExp := 96
    hScaleExp := 62
    errUpper := qrhRemainderBoundAtTwoTenPow chebyshevSpec96_1732
    primePowerCorr := 10 ^ 51
    thetaDen_pos := by decide
    theta_lt_one := by decide }

private theorem ap_ten_factor_lt_fermat (phiQ e c gap coeff hExp : Nat)
    (hPhi : phiQ < 10 ^ 5)
    (hc : e + gap = hExp)
    (hCoeff : 2 * c + 1 < coeff)
    (hGap : 10 ^ 5 * coeff < 10 ^ gap) :
    phiQ * (2 * (c * 10 ^ e) + 10 ^ e) < 10 ^ hExp := by
  have hInner : 2 * (c * 10 ^ e) + 10 ^ e < coeff * 10 ^ e := by
    have hmul : 2 * (c * 10 ^ e) + 10 ^ e = (2 * c + 1) * 10 ^ e := by
      rw [Nat.add_mul, Nat.one_mul]
      ac_rfl
    rw [hmul]
    exact Nat.mul_lt_mul_of_pos_right hCoeff (Nat.pow_pos (by decide))
  have hScaled : phiQ * (2 * (c * 10 ^ e) + 10 ^ e) < 10 ^ 5 * (coeff * 10 ^ e) :=
    Nat.mul_lt_mul_of_lt_of_le' hPhi (Nat.le_of_lt hInner)
      (Nat.add_pos_right _ (Nat.pow_pos (by decide)))
  have hGapMul : 10 ^ 5 * (coeff * 10 ^ e) < 10 ^ gap * 10 ^ e := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hGap (Nat.pow_pos (by decide))
  have hExpEq : 10 ^ gap * 10 ^ e = 10 ^ hExp := by
    rw [← Nat.pow_add, Nat.add_comm gap e, hc]
  exact hExpEq ▸ Nat.lt_trans hScaled hGapMul

private def fermatApSpecOf (base : ShortIntervalChebyshevSpec)
    (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid) : ApShortIntervalSpec :=
  { base := base
    q := spec.primeMod
    phiQ := spec.galoisOrder
    phiQ_pos := by
      rcases hspec with ⟨_, _, hp1, hgal, _, _, _, _, _⟩
      rw [hgal]
      exact Nat.sub_pos_of_lt hp1
    phiQ_lt_q := by
      rcases hspec with ⟨_, _, hp1, hgal, _, _, _, _, _⟩
      rw [hgal]
      exact Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one hp1) Nat.zero_lt_one }

/-- Builder turning any valid `ArtinFermatCharacterSpec` into `ArtinTwistedShortIntervalSpec`
once `HasGuaranteedApPrime` and `thetaQRat ≤ qrhShortExponent rungK` are certified. -/
def mkArtinTwistedSpec (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (base : ShortIntervalChebyshevSpec) (rungK : Nat) (hrung : 1 ≤ rungK)
    (hle : base.thetaQRat ≤ qrhShortExponent rungK)
    (hPrime : (fermatApSpecOf base spec hspec).HasGuaranteedApPrime) :
    ArtinTwistedShortIntervalSpec :=
  { artinSpec := spec
    apSpec := fermatApSpecOf base spec hspec
    rungK := rungK
    rungK_pos := hrung
    artinValid := hspec
    primeMod_eq := rfl
    phiQ_eq := rfl
    theta_le_rung := hle
    has_ap_prime := hPrime }

set_option exponentiation.threshold 2000 in
private theorem ap48_23_has_prime (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (hPhi : spec.galoisOrder < 10 ^ 5) :
    (fermatApSpecOf shortIntervalQrh48_23Spec spec hspec).HasGuaranteedApPrime := by
  dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatApSpecOf, shortIntervalQrh48_23Spec,
    qrhRemainderBoundAtTwoTenPow, chebyshevSpec48_23]
  have hceil : tenPowThetaCeilExp 4 qrhThresholdTwoThirds = 32 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 4) * (29 * 4)) = 26912 := by decide
  have hEq : 2 * 1 * 10 ^ 32 * ((29 * 4) * (29 * 4)) = 26912 * 10 ^ 32 := by
    calc 2 * 1 * 10 ^ 32 * ((29 * 4) * (29 * 4))
        = (2 * 1 * ((29 * 4) * (29 * 4))) * 10 ^ 32 := by ac_rfl
      _ = 26912 * 10 ^ 32 := by rw [hmul]
  rw [hEq]
  exact ap_ten_factor_lt_fermat spec.galoisOrder 32 26912 10 60000 42
    hPhi (by decide) (by decide) (by decide)

set_option exponentiation.threshold 2000 in
private theorem ap48_58_has_prime (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (hPhi : spec.galoisOrder < 10 ^ 5) :
    (fermatApSpecOf shortIntervalQrh48_58Spec spec hspec).HasGuaranteedApPrime := by
  dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatApSpecOf, shortIntervalQrh48_58Spec,
    qrhRemainderBoundAtTwoTenPow, chebyshevSpec48_58]
  have hceil : tenPowThetaCeilExp 4 qrhThresholdFiveEighths = 30 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 4) * (29 * 4)) = 26912 := by decide
  have hEq : 2 * 1 * 10 ^ 30 * ((29 * 4) * (29 * 4)) = 26912 * 10 ^ 30 := by
    calc 2 * 1 * 10 ^ 30 * ((29 * 4) * (29 * 4))
        = (2 * 1 * ((29 * 4) * (29 * 4))) * 10 ^ 30 := by ac_rfl
      _ = 26912 * 10 ^ 30 := by rw [hmul]
  rw [hEq]
  exact ap_ten_factor_lt_fermat spec.galoisOrder 30 26912 10 60000 40
    hPhi (by decide) (by decide) (by decide)

set_option exponentiation.threshold 2000 in
private theorem ap192_3964_has_prime (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (hPhi : spec.galoisOrder < 10 ^ 5) :
    (fermatApSpecOf shortIntervalQrh192_3964Spec spec hspec).HasGuaranteedApPrime := by
  dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatApSpecOf, shortIntervalQrh192_3964Spec,
    qrhRemainderBoundAtTwoTenPow, chebyshevSpec192_3964]
  have hceil : tenPowThetaCeilExp 16 qrhThresholdKimSarnak = 117 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 16) * (29 * 16)) = 430592 := by decide
  have hEq : 2 * 1 * 10 ^ 117 * ((29 * 16) * (29 * 16)) = 430592 * 10 ^ 117 := by
    calc 2 * 1 * 10 ^ 117 * ((29 * 16) * (29 * 16))
        = (2 * 1 * ((29 * 16) * (29 * 16))) * 10 ^ 117 := by ac_rfl
      _ = 430592 * 10 ^ 117 := by rw [hmul]
  rw [hEq]
  exact ap_ten_factor_lt_fermat spec.galoisOrder 117 430592 11 900000 128
    hPhi (by decide) (by decide) (by decide)

set_option exponentiation.threshold 2000 in
private theorem ap96_1732_has_prime (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (hPhi : spec.galoisOrder < 10 ^ 5) :
    (fermatApSpecOf shortIntervalQrh96_1732ApBaseSpec spec hspec).HasGuaranteedApPrime := by
  dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatApSpecOf,
    shortIntervalQrh96_1732ApBaseSpec, qrhRemainderBoundAtTwoTenPow, chebyshevSpec96_1732]
  have hceil : tenPowThetaCeilExp 8 (qrhShortExponent 4) = 51 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 8) * (29 * 8)) = 107648 := by decide
  have hEq : 2 * 1 * 10 ^ 51 * ((29 * 8) * (29 * 8)) = 107648 * 10 ^ 51 := by
    calc 2 * 1 * 10 ^ 51 * ((29 * 8) * (29 * 8))
        = (2 * 1 * ((29 * 8) * (29 * 8))) * 10 ^ 51 := by ac_rfl
      _ = 107648 * 10 ^ 51 := by rw [hmul]
  rw [hEq]
  exact ap_ten_factor_lt_fermat spec.galoisOrder 51 107648 11 300000 62
    hPhi (by decide) (by decide) (by decide)

set_option exponentiation.threshold 2000 in
private theorem ap168_34_has_prime (spec : ArtinFermatCharacterSpec) (hspec : spec.Valid)
    (hPhi : spec.galoisOrder < 10 ^ 5) :
    (fermatApSpecOf shortIntervalQrh34Spec spec hspec).HasGuaranteedApPrime := by
  dsimp [ApShortIntervalSpec.HasGuaranteedApPrime, fermatApSpecOf, shortIntervalQrh34Spec,
    qrhRemainderBoundAtTwoTenPow, chebyshevSpec168_34]
  have hceil : tenPowThetaCeilExp 14 qrhThresholdThreeQuarters = 126 := by decide
  rw [hceil]
  have hmul : 2 * 1 * ((29 * 14) * (29 * 14)) = 329672 := by decide
  have hEq : 2 * 1 * 10 ^ 126 * ((29 * 14) * (29 * 14)) = 329672 * 10 ^ 126 := by
    calc 2 * 1 * 10 ^ 126 * ((29 * 14) * (29 * 14))
        = (2 * 1 * ((29 * 14) * (29 * 14))) * 10 ^ 126 := by ac_rfl
      _ = 329672 * 10 ^ 126 := by rw [hmul]
  rw [hEq]
  have hBase : 2 * (329672 * 10 ^ 126) + 10 ^ 89 < 2 * (329672 * 10 ^ 126) + 10 ^ 126 :=
    Nat.add_lt_add_left (by decide) _
  have hMul : spec.galoisOrder * (2 * (329672 * 10 ^ 126) + 10 ^ 89) ≤
      spec.galoisOrder * (2 * (329672 * 10 ^ 126) + 10 ^ 126) :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt hBase)
  have hFac := ap_ten_factor_lt_fermat spec.galoisOrder 126 329672 14 700000 140
    hPhi (by decide) (by decide) (by decide)
  exact Nat.lt_of_le_of_lt hMul hFac

private theorem fermat_spec_phi_lt (spec : ArtinFermatCharacterSpec)
    (hmem : spec ∈ artinFermatTowerSpecs) : spec.galoisOrder < 10 ^ 5 := by
  dsimp [artinFermatTowerSpecs] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · decide
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · decide
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · decide
        · cases List.not_mem_nil hmem

set_option exponentiation.threshold 2000 in
/-- Theorem (Fermat-Tower `{5, 17, 257, 65537}` Artin Character-Twisted Short-Interval Bounds):
Couples `EulerFactorNonVanishing.FermatTowerStripCert` (`fermat_tower_euler_product_strip_certs`)
with `ArtinTwistedShortIntervalSpec` across every Fermat-tower prime `{5, 17, 257, 65537}` and
beyond-`7/8` ladder exponents `17/32 < 39/64 < 5/8 < 2/3 < 3/4 < 7/8`:
1. Certifies `FermatTowerStripCert` (`σ ∈ {1/2, 3/4, 1}`) and tower moduli `[5, 17, 257, 65537]`.
2. Instantiates valid `ArtinTwistedShortIntervalSpec` certificates for every `spec ∈ artinFermatTowerSpecs`
   at `θ = 3/4` (`(10^168, 10^140)`), `θ = 2/3` (`(10^48, 10^42)`), `θ = 5/8` (`(10^48, 10^40)`),
   `θ = 39/64 < 5/8` (`(10^192, 10^128)`, Kim-Sarnak `7/64` coupling), and
   `θ = 17/32 < 39/64` (`(10^96, 10^62)`, `qrhShortExponent 4`).
3. Delivers constructive residue-class prime positivity `0 < θ(x + h; F_k, a) - θ(x; F_k, a)`
   from character-twisted error envelopes at both `39/64` and `17/32` across all four primes.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermat_tower_artin_short_interval_certs :
    FermatTowerStripCert ∧
    artinFermatTowerSpecs.map (·.primeMod) = [5, 17, 257, 65537] ∧
    (qrhShortExponent 4 = QRat.mk' 17 32 (by decide) ∧
     QRat.mk' 17 32 (by decide) < qrhThresholdKimSarnak ∧
     qrhThresholdKimSarnak < qrhThresholdFiveEighths ∧
     qrhThresholdFiveEighths < qrhThresholdTwoThirds ∧
     qrhThresholdTwoThirds < qrhThresholdThreeQuarters ∧
     qrhThresholdThreeQuarters < qrhThresholdSevenEighths) ∧
    (∀ spec : ArtinFermatCharacterSpec, spec ∈ artinFermatTowerSpecs →
      ∃ hval : spec.Valid,
        (fermatApSpecOf shortIntervalQrh34Spec spec hval).HasGuaranteedApPrime ∧
        (fermatApSpecOf shortIntervalQrh48_23Spec spec hval).HasGuaranteedApPrime ∧
        (fermatApSpecOf shortIntervalQrh48_58Spec spec hval).HasGuaranteedApPrime ∧
        (fermatApSpecOf shortIntervalQrh192_3964Spec spec hval).HasGuaranteedApPrime ∧
        (fermatApSpecOf shortIntervalQrh96_1732ApBaseSpec spec hval).HasGuaranteedApPrime) ∧
    (∀ spec ∈ artinFermatTowerSpecs,
      ∃ tw : ArtinTwistedShortIntervalSpec,
        tw.artinSpec = spec ∧
        tw.apSpec.base.thetaQRat = qrhThresholdKimSarnak ∧
        tw.apSpec.base.thetaQRat < qrhThresholdFiveEighths ∧
        tw.apSpec.HasGuaranteedApPrime) ∧
    (∀ spec ∈ artinFermatTowerSpecs,
      ∃ tw : ArtinTwistedShortIntervalSpec,
        tw.artinSpec = spec ∧
        tw.apSpec.base.thetaQRat = qrhShortExponent 4 ∧
        tw.apSpec.HasGuaranteedApPrime) := by
  refine ⟨fermat_tower_euler_product_strip_certs, rfl, by decide, ?_, ?_, ?_⟩
  · intro spec hmem
    have hval := artinFermatTowerSpecs_valid spec hmem
    have hPhi := fermat_spec_phi_lt spec hmem
    exact ⟨hval,
           ap168_34_has_prime spec hval hPhi,
           ap48_23_has_prime spec hval hPhi,
           ap48_58_has_prime spec hval hPhi,
           ap192_3964_has_prime spec hval hPhi,
           ap96_1732_has_prime spec hval hPhi⟩
  · intro spec hmem
    have hval := artinFermatTowerSpecs_valid spec hmem
    have hPhi := fermat_spec_phi_lt spec hmem
    refine ⟨mkArtinTwistedSpec spec hval shortIntervalQrh192_3964Spec 2 (by decide)
        (by decide) (ap192_3964_has_prime spec hval hPhi),
      rfl, rfl, ?_, ap192_3964_has_prime spec hval hPhi⟩
    dsimp [mkArtinTwistedSpec, fermatApSpecOf]
    decide
  · intro spec hmem
    have hval := artinFermatTowerSpecs_valid spec hmem
    have hPhi := fermat_spec_phi_lt spec hmem
    refine ⟨mkArtinTwistedSpec spec hval shortIntervalQrh96_1732ApBaseSpec 4 (by decide)
        (by decide) (ap96_1732_has_prime spec hval hPhi),
      rfl, ?_, ap96_1732_has_prime spec hval hPhi⟩
    dsimp [mkArtinTwistedSpec, fermatApSpecOf]
    decide

end ArtinShortIntervalBridge

-- end of file: leanasm/src/LeanAsm/ArtinShortIntervalBridge.lean
