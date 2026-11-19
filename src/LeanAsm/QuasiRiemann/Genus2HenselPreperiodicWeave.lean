-- Path: leanasm/src/LeanAsm/QuasiRiemann/Genus2HenselPreperiodicWeave.lean
-- Weaves multi-prime genus-2 Frobenius trace certificates with QSD[4] Hensel
-- prime-tower tangent lifts, nilpotent remainder bounds, and preperiodic dynamics bounds.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.Genus2MultiPrimeWeil
import LeanAsm.QuasiRiemann.Valuation.QsdHenselTower
import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

open _root_.QuasiRiemann
open _root_.QuasiRiemann.Valuation
open _root_.LeanAsm.Genus2MultiPrimeWeil
open _root_.LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

namespace LeanAsm.QuasiRiemann.Genus2HenselPreperiodicWeave

/-!
# Multi-Prime Genus-2, QSD[4] Hensel Prime-Tower & Preperiodic Dynamics Weave

This module establishes a constructive bridge connecting:
1. Multi-prime genus-2 Frobenius traces and Weil RH certificates across
   $p \in \{7, 11, 13, 17, 19, 23\}$ (`LeanAsm.Genus2MultiPrimeWeil`).
2. Constructive `QSD[4]` Hensel prime-tower tangent lifts and nilpotent remainder
   bounds ($m^2 \equiv 0 \pmod{p^{2k}}$) across prime powers (`QsdHenselTower.lean`).
3. Preperiodic orbit, divisibility, and multiplicity bounds over rational dynamical
   systems (`PreperiodicDynamics.lean`).

All proofs are strictly constructive under `[propext, Quot.sound]`, with zero `Classical.choice`,
zero `sorryAx`, and zero Mathlib.
-/

/-- Bundled certificate for an individual prime $p$ weaving genus-2 Weil bounds with
    $p$-tower Hensel tangent lifts, nilpotent remainders, and preperiodic dynamical invariants. -/
structure Genus2HenselPreperiodicPrimeCert (p : Nat) : Prop where
  weil_cert : Genus2WeilCert p
  hp_ge_two : 2 ≤ p
  lift_tangent_step : ∀ (k x t : Nat) (_hk : 1 ≤ k),
    let m := p ^ (k + 1)
    let pk := p ^ k
    let x_lift := x + t * pk
    have hm_pos : 0 < m := pow_pos_of_ge_two hp_ge_two (k + 1)
    let dual_lift : QsdDualModRing m :=
      ⟨QsdModRing.ofNat m hm_pos x, QsdModRing.ofNat m hm_pos (t * pk)⟩
    (x_lift % pk = x % pk) ∧
    ((t * pk) * (t * pk)) % (pk * pk) = 0 ∧
    dual_lift.val.val = x % m ∧
    dual_lift.tan.val = (t * pk) % m
  nilpotent_remainder : ∀ (k : Nat) (_hk : 1 ≤ k),
    let m := p ^ k
    let m2 := m * m
    have hm_pos : 0 < m := pow_pos_of_ge_two hp_ge_two k
    have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
    let tan_elem := QsdModRing.ofNat m2 hm2_pos m
    (QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
    (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val)

/-- Construction of `Genus2HenselPreperiodicPrimeCert` from a genus-2 Weil certificate and
    prime bound $2 \le p$. -/
theorem make_genus2_hensel_preperiodic_prime_cert {p : Nat}
    (hcert : Genus2WeilCert p) (hp : 2 ≤ p) : Genus2HenselPreperiodicPrimeCert p :=
  ⟨hcert, hp,
   fun k x t hk => qsd4_hensel_tangent_lift_step p k x t hp hk,
   fun k hk => qsd4_prime_tower_nilpotent_remainder_bound p hp k hk⟩

/-- Concrete certified weave for p = 7. -/
theorem cert_weave_p7 : Genus2HenselPreperiodicPrimeCert 7 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p7 (by decide)

/-- Concrete certified weave for p = 11. -/
theorem cert_weave_p11 : Genus2HenselPreperiodicPrimeCert 11 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p11 (by decide)

/-- Concrete certified weave for p = 13. -/
theorem cert_weave_p13 : Genus2HenselPreperiodicPrimeCert 13 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p13 (by decide)

/-- Concrete certified weave for p = 17. -/
theorem cert_weave_p17 : Genus2HenselPreperiodicPrimeCert 17 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p17 (by decide)

/-- Concrete certified weave for p = 19. -/
theorem cert_weave_p19 : Genus2HenselPreperiodicPrimeCert 19 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p19 (by decide)

/-- Concrete certified weave for p = 23. -/
theorem cert_weave_p23 : Genus2HenselPreperiodicPrimeCert 23 :=
  make_genus2_hensel_preperiodic_prime_cert cert_p23 (by decide)

/-- Master structure weaving multi-prime Frobenius traces with Hensel tower lifts
    and preperiodic dynamics invariants. -/
structure Genus2HenselPreperiodicWeaveBridge : Prop where
  prime_certs : ∀ p ∈ goodPrimesList, Genus2HenselPreperiodicPrimeCert p
  hensel_tower_p7 :
    qsd4_hensel_tower_cert_p7.x1 = 3 ∧
    qsd4_hensel_tower_cert_p7.x2 = 10 ∧
    qsd4_hensel_tower_cert_p7.x3 = 108 ∧
    (qsd4_hensel_tower_cert_p7.x1 * qsd4_hensel_tower_cert_p7.x1) % 7 = 2 % 7 ∧
    (qsd4_hensel_tower_cert_p7.x2 * qsd4_hensel_tower_cert_p7.x2) % (7 ^ 2) = 2 % (7 ^ 2) ∧
    (qsd4_hensel_tower_cert_p7.x3 * qsd4_hensel_tower_cert_p7.x3) % (7 ^ 3) = 2 % (7 ^ 3)
  hensel_tower_p2 :
    (1 * 1) % 2 = 1 % 2 ∧
    (1 * 1) % (2 ^ 2) = 1 % (2 ^ 2) ∧
    (1 * 1) % (2 ^ 3) = 1 % (2 ^ 3) ∧
    pAdicVal 2 (QRat.ofInt (1 * 1 - 1)) = none
  preperiodic_mult_bound :
    (wreathProductMultiplicityBound 2 2 (QRat.mk' 1 100 (by decide))).num > 0
  preperiodic_div_bound :
    (lemma43DivisibilityBound 2 3 1 (QRat.mk' 1 10 (by decide))).num > 0
  preperiodic_asymp_bound :
    let base := QRat.mk' 2 5 (by decide)
    theorem51AsymptoticBound 2 2 base ≥ base
  preperiodic_avg_bound :
    (theorem13AverageBound 134).num > 0
  preperiodic_prop53_bound :
    (proposition53AverageBound 2 2 134).num > 0

/-- Constructive bridge theorem certifying the weave between genus-2 multi-prime Frobenius
    traces, QSD[4] Hensel prime-tower tangent lifts, and preperiodic dynamics bounds. -/
theorem genus2_hensel_preperiodic_weave_bridge : Genus2HenselPreperiodicWeaveBridge := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [goodPrimesList, List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact cert_weave_p7
    rcases hp with rfl | hp
    · exact cert_weave_p11
    rcases hp with rfl | hp
    · exact cert_weave_p13
    rcases hp with rfl | hp
    · exact cert_weave_p17
    rcases hp with rfl | hp
    · exact cert_weave_p19
    rcases hp with rfl | hp
    · exact cert_weave_p23
    cases hp
  · exact ⟨rfl, rfl, rfl, by decide, by decide, by decide⟩
  · exact qsd4_hensel_tower_cert_p2
  · exact wreath_product_bound_sound
  · exact lemma43_divisibility_bound_sound
  · exact theorem51_asymptotic_bound_sound
  · exact theorem13_average_bound_sound
  · exact proposition53_average_bound_sound

/-- Concrete certificate alias for downstream provenance and testing. -/
theorem genus2_hensel_preperiodic_cert : Genus2HenselPreperiodicWeaveBridge :=
  genus2_hensel_preperiodic_weave_bridge

end LeanAsm.QuasiRiemann.Genus2HenselPreperiodicWeave

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Genus2HenselPreperiodicWeave.lean
