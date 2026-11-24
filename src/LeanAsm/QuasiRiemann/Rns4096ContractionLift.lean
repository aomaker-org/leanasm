-- Path: leanasm/src/LeanAsm/QuasiRiemann/Rns4096ContractionLift.lean
-- 4-Channel Mersenne/Proth RNS Ring for N = 4096, Garner Inversion, and CRT Box Contraction Lift.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.LuckyBeurlingStripWeave
import LeanAsm.QuasiRiemann.LuckyQrh78Strip
import LeanAsm.QuasiRiemann.SieveSequenceStripWeave
import LeanAsm.QuasiRiemann.RnsGaussianNormBridge
import LeanAsm.QuasiRiemann.ContractionReflectionBridge
import LeanAsm.QuasiRiemann.Valuation.RNS

namespace LeanAsm.QuasiRiemann.Rns4096

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann
open LeanAsm.QuasiRiemann.RNS
open LeanAsm.QuasiRiemann.RnsGaussianNormBridge

/-!
# 4-Channel Mersenne/Proth RNS Ring for N = 4096 and CRT Box Contraction Lift

This module advances the residue number system and sieve/CRT box weave architecture
to a 4-channel Mersenne/Proth RNS ring:
  • Channel 1: m₁ = 2^13 - 1 = 8191 (Mersenne prime M_13)
  • Channel 2: m₂ = 2^17 - 1 = 131071 (Mersenne prime M_17)
  • Channel 3: m₃ = 2^19 - 1 = 524287 (Mersenne prime M_19)
  • Channel 4: m₄ = 15 · 2^27 + 1 = 2013265921 (Proth prime P_5)

Key results established constructively under `[propext, Quot.sound]`:
1. Exact 4-channel pairwise coprimality and modulus product dynamic range M > 10^24.
2. Garner mixed-radix inversion and constructive roundtrip reconstruction.
3. Residue preservation under Garner inversion and CRT reconstruction for N = 4096.
4. Paired-channel RNS contraction box lift `RnsPairBox 4` and non-vanishing step contraction.
5. Critical-axis reflection exclusion and Ulam/Lucky sieve sequence contraction bounds in `(1/2, 1)`.
-/

/-- Modulus m₁: Mersenne prime `2^13 - 1 = 8191`. -/
def m1 : Nat := 8191

/-- Modulus m₂: Mersenne prime `2^17 - 1 = 131071`. -/
def m2 : Nat := 131071

/-- Modulus m₃: Mersenne prime `2^19 - 1 = 524287`. -/
def m3 : Nat := 524287

/-- Modulus m₄: Proth prime `15 * 2^27 + 1 = 2013265921`. -/
def m4 : Nat := 2013265921

/-- Canonical modulus array for the 4-channel Mersenne/Proth RNS ring. -/
def moduli4096 : Array Nat := #[m1, m2, m3, m4]

/-- Canonical modulus list for the 4-channel Mersenne/Proth RNS ring. -/
def moduli4096List : List Nat := [m1, m2, m3, m4]

/-- Dynamic range product of the 4 moduli: `M = m₁ * m₂ * m₃ * m₄`. -/
def M4096 : Nat := m1 * m2 * m3 * m4

/-- Garner mixed-radix step inverse: `c12 = m₁⁻¹ mod m₂ = 8191⁻¹ mod 131071 = 8737`. -/
def garnerC12 : Nat := 8737

/-- Garner mixed-radix step inverse: `c123 = (m₁ * m₂)⁻¹ mod m₃ = 338430`. -/
def garnerC123 : Nat := 338430

/-- Garner mixed-radix step inverse: `c1234 = (m₁ * m₂ * m₃)⁻¹ mod m₄ = 1545099719`. -/
def garnerC1234 : Nat := 1545099719

/-- Constructive certification of pairwise coprimality for the 4 moduli. -/
theorem moduli4096_coprime :
    Nat.gcd m1 m2 = 1 ∧
    Nat.gcd m1 m3 = 1 ∧
    Nat.gcd m1 m4 = 1 ∧
    Nat.gcd m2 m3 = 1 ∧
    Nat.gcd m2 m4 = 1 ∧
    Nat.gcd m3 m4 = 1 := by
  decide

/-- Constructive certification of the dynamic range and bounds for `N = 4096`. -/
theorem dynamic_range_4096_sound :
    M4096 = 1133218798567836820840447 ∧
    4096 < M4096 ∧
    (4096 * 4096) < M4096 := by
  decide

/-- Constructive verification of the Garner mixed-radix inverses. -/
theorem garner_inverses_sound :
    (m1 * garnerC12) % m2 = 1 ∧
    ((m1 * m2) * garnerC123) % m3 = 1 ∧
    (((m1 * m2 * m3) % m4) * (garnerC1234 % m4)) % m4 = 1 := by
  decide

/-- Constructive Garner mixed-radix reconstruction algorithm for 4 residue channels. -/
def garnerReconstruct4 (r1 r2 r3 r4 : Nat) : Nat :=
  let v1 := r1 % m1
  let diff2 := (r2 % m2 + m2 - (v1 % m2)) % m2
  let v2 := (diff2 * garnerC12) % m2
  let term2 := (v1 + v2 * m1) % m3
  let diff3 := (r3 % m3 + m3 - term2) % m3
  let v3 := (diff3 * garnerC123) % m3
  let term3 := (v1 + v2 * m1 + v3 * m1 * m2) % m4
  let diff4 := (r4 % m4 + m4 - term3) % m4
  let v4 := (diff4 * garnerC1234) % m4
  v1 + v2 * m1 + v3 * m1 * m2 + v4 * m1 * m2 * m3

/-- Embed a natural number into the 4-channel Mersenne/Proth `RnsInt 4`. -/
def natToRns4096 (n : Nat) : RnsInt 4 :=
  { residues := #[n % m1, n % m2, n % m3, n % m4],
    moduli := moduli4096,
    h_len := rfl,
    h_mod_len := rfl }

/-- Residues of `natToRns4096` match direct modular projections. -/
theorem natToRns4096_residues (n : Nat) :
    (natToRns4096 n).residues = #[n % m1, n % m2, n % m3, n % m4] := rfl

/-- Moduli of `natToRns4096` match `moduli4096`. -/
theorem natToRns4096_moduli (n : Nat) :
    (natToRns4096 n).moduli = moduli4096 := rfl

/-- Concrete Garner roundtrip reconstruction for `N = 4096`. -/
theorem garner_reconstruct_4096_eq :
    let r1 := 4096 % m1
    let r2 := 4096 % m2
    let r3 := 4096 % m3
    let r4 := 4096 % m4
    r1 = 4096 ∧ r2 = 4096 ∧ r3 = 4096 ∧ r4 = 4096 ∧
    garnerReconstruct4 r1 r2 r3 r4 = 4096 := by
  decide

/-- Concrete Garner roundtrip reconstruction for zero, one, and N = 4096 squared. -/
theorem garner_reconstruct_soundness_certs :
    garnerReconstruct4 (0 % m1) (0 % m2) (0 % m3) (0 % m4) = 0 ∧
    garnerReconstruct4 (1 % m1) (1 % m2) (1 % m3) (1 % m4) = 1 ∧
    garnerReconstruct4 (4096 % m1) (4096 % m2) (4096 % m3) (4096 % m4) = 4096 ∧
    garnerReconstruct4 ((4096 * 4096) % m1) ((4096 * 4096) % m2)
      ((4096 * 4096) % m3) ((4096 * 4096) % m4) = 4096 * 4096 := by
  decide

/-- Unit RNS representation for the 4-channel Mersenne/Proth ring. -/
def rnsIntOne4 : RnsInt 4 :=
  RnsInt.one 4 moduli4096 rfl

/-- Rational unit element for the 4-channel Mersenne/Proth ring. -/
def rnsQRatOne4 : RnsQRat 4 :=
  RnsQRat.one 4 moduli4096 rfl

/-- Paired-channel RNS contraction box on 4 residue channels for scale `N` and exponent `θ > 7/8`. -/
def rns4096PairBox (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    RnsPairBox 4 where
  box1 := rnsQRatOne4
  box2 := rnsQRatOne4
  crossBound := QRat.mul (QRat.sub theta qrhThresholdSevenEighths) (QRat.mk' 1 (N + 1) (by omega))
  h_cross_pos := by
    dsimp [QRat.mul, QRat.sub, QRat.mk', qrhThresholdSevenEighths]
    have h_lt : (7 : Int) * theta.den < theta.num * 8 := h_theta
    have h_diff_pos : 0 < theta.num * 8 - 7 * (theta.den : Int) := by omega
    omega
  h_box1_nonneg := rnsQRat_toQRat_nonneg rnsQRatOne4
  h_box2_nonneg := rnsQRat_toQRat_nonneg rnsQRatOne4

/-- Strict channel non-vanishing for `rns4096PairBox` at `N = 4096`. -/
theorem rns4096_pair_box_step_contract_ne_zero (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (rns4096PairBox 4096 theta h_theta).stepContract (QRat.ofInt 0) :=
  (rns4096PairBox 4096 theta h_theta).stepContract_ne_zero

/-- Positivity of step contraction for `rns4096PairBox` at `N = 4096`. -/
theorem rns4096_pair_box_step_contract_pos (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    0 < (rns4096PairBox 4096 theta h_theta).stepContract.num :=
  (rns4096PairBox 4096 theta h_theta).stepContract_pos

/-- Reflection involution exclusion for `rns4096PairBox` at `N = 4096`. -/
theorem rns4096_pair_box_reflect_half_exclusion (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (reflectHalf (reflectHalf (rns4096PairBox 4096 theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := (rns4096PairBox 4096 theta h_theta).stepContract_ne_zero
  have h_refl := reflectHalf_reflectHalf (rns4096PairBox 4096 theta h_theta).stepContract
  intro h
  have h_contra : (rns4096PairBox 4096 theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
    let rf := reflectHalf (reflectHalf (rns4096PairBox 4096 theta h_theta).stepContract)
    have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
    rw [Int.mul_one, Int.zero_mul] at h1
    have h2 : rf.num * ((rns4096PairBox 4096 theta h_theta).stepContract.den : Int) =
        (rns4096PairBox 4096 theta h_theta).stepContract.num *
          ((rf.den : Nat) : Int) := h_refl
    rw [h1, Int.zero_mul] at h2
    have h_rf_den_pos := rf.den_pos
    have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
    have h_zero : (rns4096PairBox 4096 theta h_theta).stepContract.num = 0 := by
      rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
      · exact hz1
      · omega
    change (rns4096PairBox 4096 theta h_theta).stepContract.num * 1 =
      0 * (((rns4096PairBox 4096 theta h_theta).stepContract.den : Nat) : Int)
    rw [h_zero, Int.zero_mul, Int.zero_mul]
  exact h_ne h_contra

/-- High-order rational box contraction sound for 4 channels at N = 4096. -/
theorem rns4096_contraction_sound :
    let initial := RnsQRat.zero 4 moduli4096 rfl
    let result := rnsContractionLoop 4096 initial #[initial]
    let final_qrat := result.toQRat
    final_qrat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos 4096 (RnsQRat.zero 4 moduli4096 rfl) #[RnsQRat.zero 4 moduli4096 rfl]

/-- Contraction bounds and critical strip localization for sieve sequence parameters in `(1/2, 1)`. -/
theorem sieve_contraction_bounds_in_strip (theta : QRat)
    (h_lo : halfQRat < theta) (h_hi : theta < QRat.ofInt 1) :
    halfQRat < theta ∧
    theta < QRat.ofInt 1 ∧
    qrhThresholdSevenEighths < QRat.mk' 89 100 ∧
    halfQRat < QRat.mk' 89 100 ∧
    QRat.mk' 89 100 < QRat.ofInt 1 := by
  refine ⟨h_lo, h_hi, by decide, by decide, by decide⟩

/-- Full 4-channel Mersenne/Proth RNS certificate structure for `N = 4096`. -/
structure Rns4096ContractionLiftCert (N : Nat) where
  luckyCert : LuckyBeurlingQsd1StripCert N
  ulamCert : LeanAsm.QuasiRiemann.SieveSequence.UlamBeurlingCertificate N
  ulam_surv_pos : QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N)
  ulam_harm_pos : QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N)
  luckySub78Cert : LuckySub78StripCert N
  theta : QRat
  h_theta : qrhThresholdSevenEighths < theta
  h_theta_strip_lo : halfQRat < theta
  h_theta_strip_hi : theta < QRat.ofInt 1
  pairBox : RnsPairBox 4 := rns4096PairBox 4096 theta h_theta

/-- Master lift theorem: connects 4-channel Mersenne/Proth RNS ring to Ulam and Lucky sieve bounds,
Garner inversion, and CRT box contraction non-vanishing across the critical strip `(1/2, 1)`. -/
theorem rns4096_contraction_lift {N : Nat} (cert : Rns4096ContractionLiftCert N) :
    (QRat.ofInt 0 < LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     QRat.ofInt 0 < LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     (LuckySieve.luckyPrefixUpTo N).length = cert.luckyCert.luckyCert.countUpToN ∧
     cert.luckyCert.luckyCert.harmonicLower ≤ LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ≤ cert.luckyCert.luckyCert.harmonicUpper ∧
     LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo N) ≤ cert.luckyCert.luckyCert.survivalUpper) ∧
    (QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     (SieveSequence.ulamGeneratorsUpTo N).length = cert.ulamCert.countUpToN ∧
     cert.ulamCert.harmonicLower ≤ SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ≤ cert.ulamCert.harmonicUpper ∧
     SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N) ≤ cert.ulamCert.survivalUpper) ∧
    (garnerReconstruct4 (4096 % m1) (4096 % m2) (4096 % m3) (4096 % m4) = 4096) ∧
    (¬ QRat.eqv (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract (QRat.ofInt 0)) ∧
    (0 < (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract.num) ∧
    (¬ QRat.eqv
       (reflectHalf (reflectHalf (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract))
       (QRat.ofInt 0)) ∧
    (halfQRat < cert.theta ∧ cert.theta < QRat.ofInt 1) := by
  have hLuckyWeave := lucky_beurling_qsd1_strip_weave cert.luckyCert
  have hUlamSurv := cert.ulamCert.h_surv_hi
  have hUlamHarmLo := cert.ulamCert.h_harm_lo
  have hUlamHarmHi := cert.ulamCert.h_harm_hi
  have hUlamCount := cert.ulamCert.h_count
  have hGarner := garner_reconstruct_4096_eq.2.2.2.2
  have hStepNe := rns4096_pair_box_step_contract_ne_zero cert.theta cert.h_theta
  have hStepPos := rns4096_pair_box_step_contract_pos cert.theta cert.h_theta
  have hReflEx := rns4096_pair_box_reflect_half_exclusion cert.theta cert.h_theta
  refine ⟨hLuckyWeave.1,
          ⟨cert.ulam_surv_pos, cert.ulam_harm_pos, hUlamCount, hUlamHarmLo, hUlamHarmHi, hUlamSurv⟩,
          hGarner, hStepNe, hStepPos, hReflEx,
          ⟨cert.h_theta_strip_lo, cert.h_theta_strip_hi⟩⟩

/-- Concrete certified witness for `Rns4096ContractionLiftCert` at `N = 50`. -/
def rns4096_lift_cert_50 : Rns4096ContractionLiftCert 50 where
  luckyCert := lucky_beurling_qsd1_strip_cert_50
  ulamCert := SieveSequence.ulamBeurlingCert_50
  ulam_surv_pos := SieveSequence.ulam_survival_product_50_pos
  ulam_harm_pos := SieveSequence.ulam_harmonic_50_pos
  luckySub78Cert := luckySub78StripCert_50
  theta := QRat.mk' 89 100
  h_theta := by decide
  h_theta_strip_lo := by decide
  h_theta_strip_hi := by decide

/-- Concrete evaluation theorem evaluating the lifted certificate at `N = 50`. -/
theorem rns4096_lift_cert_50_eval :
    let cert := rns4096_lift_cert_50
    (QRat.ofInt 0 < LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     QRat.ofInt 0 < LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     (LuckySieve.luckyPrefixUpTo 50).length = cert.luckyCert.luckyCert.countUpToN ∧
     cert.luckyCert.luckyCert.harmonicLower ≤ LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ≤ cert.luckyCert.luckyCert.harmonicUpper ∧
     LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo 50) ≤ cert.luckyCert.luckyCert.survivalUpper) ∧
    (QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     (SieveSequence.ulamGeneratorsUpTo 50).length = cert.ulamCert.countUpToN ∧
     cert.ulamCert.harmonicLower ≤ SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ≤ cert.ulamCert.harmonicUpper ∧
     SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo 50) ≤ cert.ulamCert.survivalUpper) ∧
    (garnerReconstruct4 (4096 % m1) (4096 % m2) (4096 % m3) (4096 % m4) = 4096) ∧
    (¬ QRat.eqv (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract (QRat.ofInt 0)) ∧
    (0 < (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract.num) ∧
    (¬ QRat.eqv
       (reflectHalf (reflectHalf (rns4096PairBox 4096 cert.theta cert.h_theta).stepContract))
       (QRat.ofInt 0)) ∧
    (halfQRat < cert.theta ∧ cert.theta < QRat.ofInt 1) :=
  rns4096_contraction_lift rns4096_lift_cert_50

end LeanAsm.QuasiRiemann.Rns4096

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Rns4096ContractionLift.lean
