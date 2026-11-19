-- Path: leanasm/src/LeanAsm/MiniVMRnsHenselWeave.lean
-- MiniVM NTT, RnsInt CRT and QSD[4] Hensel prime-tower weave bridge.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.MiniVMNttBridge
import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.Valuation.QsdHenselTower

open LeanAsm.QuasiRiemann.RNS
open QuasiRiemann.Valuation
open MiniVMNttBridge
open MiniVM

namespace LeanAsm.MiniVMRnsHenselWeave

/-!
# MiniVM NTT + RnsInt CRT + QSD[4] Hensel Prime-Tower Weave

This module weaves:
1. `MiniVMNttBridge`: Symbolic execution semantics for modular NTT / INTT and compiled 4-channel
   Garner CRT reconstruction over `(5, 17, 257, 65537)`.
2. `QuasiRiemann.Valuation.RNS`: Coprime residue channel decomposition, element-wise arithmetic,
   and exact CRT reconstruction for `RnsInt` and `RnsQRat`.
3. `QuasiRiemann.Valuation.QsdHenselTower`: Constructive `QSD[4]` Hensel prime-tower tangent lifts
   (`mod p^k` and nilpotent `m^2 = 0`) certifying stationary and quadratic lift steps.

All proofs are constructive on `[propext, Quot.sound]`, with zero Mathlib, zero `Classical.choice`,
and zero `sorryAx`.
-/

/-- Bundled certificate for the weave between `MiniVM` NTT, `RnsInt` CRT, and `QSD[4]` Hensel
tangent tower lifts. -/
structure MiniVMRnsHenselWeaveCert : Prop where
  /-- Hensel quadratic tangent lift steps and projection invariants for $p = 7$. -/
  hensel_cert_p7 :
    (qsd4_hensel_tower_cert_p7.x1 * qsd4_hensel_tower_cert_p7.x1) % 7 = 2 % 7 ∧
    (qsd4_hensel_tower_cert_p7.x2 * qsd4_hensel_tower_cert_p7.x2) % (7 ^ 2) = 2 % (7 ^ 2) ∧
    (qsd4_hensel_tower_cert_p7.x3 * qsd4_hensel_tower_cert_p7.x3) % (7 ^ 3) = 2 % (7 ^ 3) ∧
    qsd4_hensel_tower_cert_p7.x2 % 7 = qsd4_hensel_tower_cert_p7.x1 % 7 ∧
    qsd4_hensel_tower_cert_p7.x3 % (7 ^ 2) = qsd4_hensel_tower_cert_p7.x2 % (7 ^ 2)
  /-- Nilpotent zero-divisor remainder bound for dual tangent lifts $m^2 = 0$ along prime towers. -/
  nilpotent_tan_bound :
    ∀ (p : Nat) (hp : 2 ≤ p) (k : Nat) (_hk : 1 ≤ k),
      let m := p ^ k
      let m2 := m * m
      have hm_pos : 0 < m := QuasiRiemann.Valuation.pow_pos_of_ge_two hp k
      have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
      let tan_elem := QuasiRiemann.QsdModRing.ofNat m2 hm2_pos m
      (QuasiRiemann.QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
      (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val)
  /-- RNS Mersenne-channel CRT reconstruction and residue preservation for tower states. -/
  rns_channel_consistency :
    let rnsVal : RnsInt 3 := {
      residues := #[qsd4_hensel_tower_cert_p7.x1 % 7,
                    qsd4_hensel_tower_cert_p7.x2 % 31,
                    qsd4_hensel_tower_cert_p7.x3 % 127]
      moduli := #[7, 31, 127]
      h_len := rfl
      h_mod_len := rfl
    }
    rnsVal.reconstruct = 14332 ∧
    rnsVal.reconstruct % 7 = 3 ∧
    rnsVal.reconstruct % 31 = 10 ∧
    rnsVal.reconstruct % 127 = 108
  /-- MiniVM compiled 4-channel Garner CRT evaluation reconstructing tower-lifted residue state. -/
  minivm_garner_reconstruct :
    let sInit : State := {
      r0 := 1,
      r1 := qsd4_hensel_tower_cert_p7.x1,
      r2 := qsd4_hensel_tower_cert_p7.x2,
      r3 := qsd4_hensel_tower_cert_p7.x3,
      pc := 0
    }
    (runProgram sInit garnerReconstruct4Asm).r0 = 1327386506 ∧
    1327386506 < CrtNtt.fermatTowerMod4 ∧
    1327386506 % 5 = 1 ∧
    1327386506 % 17 = 3 ∧
    1327386506 % 257 = 10 ∧
    1327386506 % 65537 = 108
  /-- MiniVM 4-point NTT / INTT roundtrip compatibility on Fermat configuration cfg17. -/
  minivm_ntt4_roundtrip :
    ∀ (s : State) (a b c d : Nat),
      a < 17 → b < 17 → c < 17 → d < 17 →
      s.r0 = a → s.r1 = b → s.r2 = c → s.r3 = d →
      let s1 := runProgram s ntt4AsmF17
      let s2 := runProgram s1 intt4AsmF17
      (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : NttArithmetic.Vec4) = ⟨a, b, c, d⟩

/-- Concrete Mersenne RNS witness embedding the $p = 7$ Hensel prime-tower roots. -/
def rnsTowerMersenneCert : RnsInt 3 := {
  residues := #[qsd4_hensel_tower_cert_p7.x1 % 7,
                qsd4_hensel_tower_cert_p7.x2 % 31,
                qsd4_hensel_tower_cert_p7.x3 % 127]
  moduli := #[7, 31, 127]
  h_len := rfl
  h_mod_len := rfl
}

/-- Unit RNS witness for the Mersenne modulus vector `#[7, 31, 127]`. -/
def oneMersenne : RnsInt 3 := {
  residues := #[1, 1, 1]
  moduli := #[7, 31, 127]
  h_len := rfl
  h_mod_len := rfl
}

/-- Rational RNS witness pairing the tower root numerator with a cleared denominator. -/
def rnsTowerMersenneQRat : RnsQRat 3 :=
  ⟨rnsTowerMersenneCert, oneMersenne⟩

/-- Initial register state loading tower roots into `MiniVM` registers `(r0, r1, r2, r3)`. -/
def sInitHenselWeave : State := {
  r0 := 1
  r1 := qsd4_hensel_tower_cert_p7.x1
  r2 := qsd4_hensel_tower_cert_p7.x2
  r3 := qsd4_hensel_tower_cert_p7.x3
  pc := 0
}

/-- Certified residue-channel consistency for `rnsTowerMersenneCert`. -/
theorem rns_tower_mersenne_channel_consistency :
    rnsTowerMersenneCert.reconstruct = 14332 ∧
    rnsTowerMersenneCert.reconstruct % 7 = 3 ∧
    rnsTowerMersenneCert.reconstruct % 31 = 10 ∧
    rnsTowerMersenneCert.reconstruct % 127 = 108 := by
  have hrec : rnsTowerMersenneCert.reconstruct = 14332 := by
    have h := rnsInt_reconstruct_mersenne_eq
      (qsd4_hensel_tower_cert_p7.x1 % 7)
      (qsd4_hensel_tower_cert_p7.x2 % 31)
      (qsd4_hensel_tower_cert_p7.x3 % 127)
      rnsTowerMersenneCert rfl rfl
    rw [h]; decide
  have hcons := rnsInt_reconstruct_mod_eq
    (qsd4_hensel_tower_cert_p7.x1 % 7)
    (qsd4_hensel_tower_cert_p7.x2 % 31)
    (qsd4_hensel_tower_cert_p7.x3 % 127)
    rnsTowerMersenneCert rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨hrec, hcons.1, hcons.2.1, hcons.2.2⟩

/-- Certified MiniVM 4-channel Garner CRT reconstruction of the tower residue state. -/
theorem minivm_garner_hensel_weave_sound :
    (runProgram sInitHenselWeave garnerReconstruct4Asm).r0 = 1327386506 ∧
    1327386506 < CrtNtt.fermatTowerMod4 ∧
    1327386506 % 5 = 1 ∧
    1327386506 % 17 = 3 ∧
    1327386506 % 257 = 10 ∧
    1327386506 % 65537 = 108 := by
  have hsound := garnerReconstruct4Asm_sound
    sInitHenselWeave 1327386506 (by decide) rfl rfl rfl rfl
  refine ⟨hsound, by decide, by decide, by decide, by decide, by decide⟩

/-- Concrete certificate theorem validating `MiniVMRnsHenselWeaveCert`. -/
theorem minivm_rns_hensel_weave_cert_hold : MiniVMRnsHenselWeaveCert := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨qsd4_hensel_tower_cert_p7.h_step1_res,
           qsd4_hensel_tower_cert_p7.h_step2_res,
           qsd4_hensel_tower_cert_p7.h_step3_res,
           qsd4_hensel_tower_cert_p7.h_step1_proj,
           qsd4_hensel_tower_cert_p7.h_step2_proj⟩
  · intro p hp k hk
    exact qsd4_prime_tower_nilpotent_remainder_bound p hp k hk
  · exact rns_tower_mersenne_channel_consistency
  · exact minivm_garner_hensel_weave_sound
  · intro s a b c d ha hb hc hd hr0 hr1 hr2 hr3
    exact intt4_ntt4_asm_F17_roundtrip s a b c d ha hb hc hd hr0 hr1 hr2 hr3

/-- Theorem (`MiniVMNttBridge` + `RnsInt` CRT + `QsdHenselTower` Weave Bridge):
Constructively bridges `MiniVM` modular NTT/Garner execution, coprime `RnsInt` CRT residue
decomposition, and `QSD[4]` prime-tower tangent lifts with cleared-denominator rational
evaluations under `[propext, Quot.sound]`. -/
theorem minivm_ntt_rns_hensel_weave_bridge :
    MiniVMRnsHenselWeaveCert ∧
    rnsTowerMersenneQRat.num.reconstruct = 14332 ∧
    rnsTowerMersenneQRat.den.reconstruct = 1 ∧
    rnsTowerMersenneQRat.toQRat.num = 14332 ∧
    rnsTowerMersenneQRat.toQRat.den = 1 ∧
    rnsTowerMersenneQRat.toQRat.num * 1 = 14332 * (rnsTowerMersenneQRat.toQRat.den : Int) := by
  have hnum : rnsTowerMersenneQRat.num.reconstruct = 14332 := by
    dsimp [rnsTowerMersenneQRat]
    have h := rnsInt_reconstruct_mersenne_eq
      (qsd4_hensel_tower_cert_p7.x1 % 7)
      (qsd4_hensel_tower_cert_p7.x2 % 31)
      (qsd4_hensel_tower_cert_p7.x3 % 127)
      rnsTowerMersenneCert rfl rfl
    rw [h]; decide
  have hden : rnsTowerMersenneQRat.den.reconstruct = 1 := by
    dsimp [rnsTowerMersenneQRat]
    have h := rnsInt_reconstruct_mersenne_eq 1 1 1 oneMersenne rfl rfl
    rw [h]; decide
  have htoq : rnsTowerMersenneQRat.toQRat = QuasiRiemann.QRat.mk' 14332 1 (by decide) := by
    dsimp [RnsQRat.toQRat]
    rw [hnum, hden]
    decide
  refine ⟨minivm_rns_hensel_weave_cert_hold, hnum, hden, ?_, ?_, ?_⟩
  · rw [htoq]; rfl
  · rw [htoq]; rfl
  · rw [htoq]; decide

end LeanAsm.MiniVMRnsHenselWeave

-- end of file: leanasm/src/LeanAsm/MiniVMRnsHenselWeave.lean
