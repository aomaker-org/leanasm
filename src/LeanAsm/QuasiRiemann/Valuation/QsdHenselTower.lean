-- Path: leanasm/src/LeanAsm/QuasiRiemann/Valuation/QsdHenselTower.lean
-- Constructive QSD[4] Hensel prime-tower tangent lifts (mod p^k and m^2 = 0).
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.Valuation.Ultrametric
import LeanAsm.QuasiRiemann.Valuation.Hensel
import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
import LeanAsm.QuasiRiemann.QsdAlgebraBridge

open QuasiRiemann
open QuasiRiemann.Valuation

namespace QuasiRiemann.Valuation

/-!
# QSD[4] Hensel Prime-Tower Tangent Lifts

Constructive formalization of `QSD[4]` residue rings carrying prime-power modulus steps
`p^k → p^(k+1)` alongside the nilpotent tangent element `m` (`m^2 = 0`).

This module connects:
1. `QsdModRing` from `QsdAlgebraBridge.lean` (residue ring and nilpotent zero-divisor arithmetic).
2. Stationary and quadratic Hensel lifting from `Valuation/Hensel.lean`.
3. Preperiodic dynamics and $p$-adic valuation / divisibility invariants from
   `Valuation/PreperiodicDynamics.lean` and `Valuation/Ultrametric.lean`.

All proofs are constructive, using zero Mathlib, zero `Classical.choice`, and zero `sorryAx`
(reducing strictly to `[propext, Quot.sound]`).
-/

/-- Dual residue-ring element over `QsdModRing m` representing `val + tan * ε` with `ε^2 = 0`. -/
structure QsdDualModRing (m : Nat) where
  val : QsdModRing m
  tan : QsdModRing m
  deriving Repr, DecidableEq

/-- Addition in `QsdDualModRing m`. -/
def QsdDualModRing.add {m : Nat} (hm : 0 < m) (x y : QsdDualModRing m) : QsdDualModRing m :=
  ⟨QsdModRing.add hm x.val y.val, QsdModRing.add hm x.tan y.tan⟩

/-- First-order dual multiplication in `QsdDualModRing m` enforcing `ε^2 = 0`:
    `(v₁ + t₁ ε)(v₂ + t₂ ε) = v₁ v₂ + (v₁ t₂ + t₁ v₂) ε`. -/
def QsdDualModRing.mul {m : Nat} (hm : 0 < m) (x y : QsdDualModRing m) : QsdDualModRing m :=
  let v := QsdModRing.mul hm x.val y.val
  let t1 := QsdModRing.mul hm x.val y.tan
  let t2 := QsdModRing.mul hm x.tan y.val
  let t := QsdModRing.add hm t1 t2
  ⟨v, t⟩

/-- Helper: 0 < p^k for any base p ≥ 2 and exponent k. -/
theorem pow_pos_of_ge_two {p : Nat} (hp : 2 ≤ p) (k : Nat) : 0 < p ^ k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k' ih =>
    have hp0 : 0 < p := by omega
    simp only [Nat.pow_succ]
    exact Nat.mul_pos ih hp0

/-- Helper: p ≤ p^k for any base p ≥ 2 and exponent k ≥ 1. -/
theorem pow_ge_self_of_ge_two {p : Nat} (hp : 2 ≤ p) (k : Nat) (hk : 1 ≤ k) : p ≤ p ^ k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    cases k' with
    | zero => simp
    | succ k'' =>
      simp only [Nat.pow_succ]
      have ih' := ih (by omega)
      have hp0 : 0 < p := by omega
      calc p ≤ p ^ (k'' + 1) := ih'
      _ ≤ p ^ (k'' + 1) * p := Nat.le_mul_of_pos_right (p ^ (k'' + 1)) hp0

private theorem mul_assoc_comm (a b : Nat) : (a * b) * (a * b) = (a * a) * (b * b) := by
  calc (a * b) * (a * b) = a * (b * (a * b)) := Nat.mul_assoc a b (a * b)
  _ = a * (b * a * b) := by rw [Nat.mul_assoc b a b]
  _ = a * (a * b * b) := by rw [Nat.mul_comm b a]
  _ = a * (a * (b * b)) := by rw [Nat.mul_assoc a b b]
  _ = (a * a) * (b * b) := by rw [← Nat.mul_assoc a a (b * b)]

private theorem mul_mod_self_left (a b : Nat) : (a * b) % b = 0 := by
  rw [Nat.mul_comm a b, Nat.mul_mod_right]

/-- **QSD[4] Hensel Tangent Lift Step Theorem:**
    Given a residue root $x \pmod{p^k}$, a Hensel tangent lift $x_{k+1} = x + t \cdot p^k$
    projects back to $x \pmod{p^k}$, while the squared tangent remainder vanishes modulo
    $p^{2k}$, establishing nilpotent dual-tangent boundary $m^2 \equiv 0 \pmod{p^{2k}}$. -/
theorem qsd4_hensel_tangent_lift_step
    (p k x t : Nat) (hp : 2 ≤ p) (_hk : 1 ≤ k) :
    let m := p ^ (k + 1)
    let pk := p ^ k
    let x_lift := x + t * pk
    have hm_pos : 0 < m := pow_pos_of_ge_two hp (k + 1)
    let dual_lift : QsdDualModRing m :=
      ⟨QsdModRing.ofNat m hm_pos x, QsdModRing.ofNat m hm_pos (t * pk)⟩
    (x_lift % pk = x % pk) ∧
    ((t * pk) * (t * pk)) % (pk * pk) = 0 ∧
    dual_lift.val.val = x % m ∧
    dual_lift.tan.val = (t * pk) % m := by
  intro m pk x_lift hm_pos dual_lift
  refine ⟨?_, ?_, rfl, rfl⟩
  · dsimp [x_lift]
    rw [Nat.add_mul_mod_self_right]
  · rw [mul_assoc_comm t pk]
    exact mul_mod_self_left (t * t) (pk * pk)

/-- **QSD[4] Prime-Tower Nilpotent Remainder Bound:**
    In the residue ring $\mathbb{Z} / (p^k)^2 \mathbb{Z} = \mathbb{Z} / p^{2k} \mathbb{Z}$,
    the tangent carrier element $m = p^k$ satisfies $m^2 \equiv 0 \pmod{p^{2k}}$ exactly,
    providing the discrete residue analog of the dual tangent parameter $m^2 = 0$, with
    its square divisible by $p^{2k}$. -/
theorem qsd4_prime_tower_nilpotent_remainder_bound
    (p : Nat) (hp : 2 ≤ p) (k : Nat) (hk : 1 ≤ k) :
    let m := p ^ k
    let m2 := m * m
    have hm_pos : 0 < m := pow_pos_of_ge_two hp k
    have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
    let tan_elem := QsdModRing.ofNat m2 hm2_pos m
    (QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
    (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val) := by
  intro m m2 hm_pos hm2_pos tan_elem
  have h1 : 1 < m := by
    have hpk : p ≤ p ^ k := pow_ge_self_of_ge_two hp k hk
    omega
  have hlt : m < m * m := by
    calc m = m * 1 := by rw [Nat.mul_one]
    _ < m * m := Nat.mul_lt_mul_of_pos_left h1 hm_pos
  have hx : m % (m * m) = m := Nat.mod_eq_of_lt hlt
  have hmul : (m * m) % (m * m) = 0 := Nat.mod_self (m * m)
  dsimp [tan_elem, QsdModRing.ofNat, QsdModRing.mul, m2, m]
  rw [hx]
  have hpow2 : (p ^ k) * (p ^ k) = p ^ (2 * k) := by
    rw [← Nat.pow_add, Nat.two_mul]
  refine ⟨hmul, ?_⟩
  rw [hpow2]
  exact Nat.dvd_refl (p ^ (2 * k))

/-- Prime-tower tangent lift certificate for $p = 7$ solving $x^2 \equiv 2 \pmod{7^k}$
    across tower rungs $k = 1, 2, 3$:
    - Rung 1: $x_1 = 3$, $3^2 \equiv 2 \pmod 7$, valuation $\nu_7(3^2 - 2) = 1$.
    - Rung 2: $x_2 = 10 = 3 + 1 \cdot 7$, $10^2 \equiv 2 \pmod{49}$, $\nu_7(10^2 - 2) = 2$.
    - Rung 3: $x_3 = 108 = 10 + 2 \cdot 49$, $108^2 \equiv 2 \pmod{343}$, $\nu_7(108^2 - 2) = 3$. -/
structure QsdPrimeTowerCert (p : Nat) where
  x1 : Nat
  x2 : Nat
  x3 : Nat
  h_step1_res : (x1 * x1) % p = 2 % p
  h_step2_res : (x2 * x2) % (p ^ 2) = 2 % (p ^ 2)
  h_step3_res : (x3 * x3) % (p ^ 3) = 2 % (p ^ 3)
  h_step1_proj : x2 % p = x1 % p
  h_step2_proj : x3 % (p ^ 2) = x2 % (p ^ 2)
  h_step1_val : pAdicVal p (QRat.ofInt (x1 * x1 - 2)) = some 1
  h_step2_val : pAdicVal p (QRat.ofInt (x2 * x2 - 2)) = some 2
  h_step3_val : pAdicVal p (QRat.ofInt (x3 * x3 - 2)) = some 3

/-- Concrete certified prime-tower Hensel tangent lift instance for $p = 7$ across $k = 1..3$. -/
def qsd4_hensel_tower_cert_p7 : QsdPrimeTowerCert 7 := {
  x1 := 3
  x2 := 10
  x3 := 108
  h_step1_res := by decide
  h_step2_res := by decide
  h_step3_res := by decide
  h_step1_proj := by decide
  h_step2_proj := by decide
  h_step1_val := by decide
  h_step2_val := by decide
  h_step3_val := by decide
}

/-- Prime-tower tangent lift certificate for $p = 2$ solving $x \equiv 1 \pmod{2^k}$
    for idempotent/unital square-free root dynamics $x^2 \equiv x \pmod{2^k}$ across $k = 1..3$:
    $x_1 = 1$, $x_2 = 1$, $x_3 = 1$. -/
theorem qsd4_hensel_tower_cert_p2 :
    (1 * 1) % 2 = 1 % 2 ∧
    (1 * 1) % (2 ^ 2) = 1 % (2 ^ 2) ∧
    (1 * 1) % (2 ^ 3) = 1 % (2 ^ 3) ∧
    pAdicVal 2 (QRat.ofInt (1 * 1 - 1)) = none :=
  ⟨by decide, by decide, by decide, rfl⟩

end QuasiRiemann.Valuation

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Valuation/QsdHenselTower.lean
