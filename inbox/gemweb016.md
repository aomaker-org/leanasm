Here is a self-contained implementation prompt for AGY to bridge `QuasiRiemann.lean` and `RnsArithmetic.lean` by proving local prime-tower Euler factor non-vanishing bounds ($1 - p^{-\sigma} > 0$) across your RNS prime tower $p \in \{7, 11, 13\}$ with zero axioms.

---

### AGY Implementation Prompt: Local Prime-Tower Euler Factor Non-Vanishing (`EulerFactorNonVanishing`)

```text
Task: Bridge `QuasiRiemann.lean` and `RnsArithmetic.lean` in `leanasm` by proving constructive, zero-axiom local Euler factor non-vanishing bounds (`1 - p^(-σ) > 0` and finite partial Euler product positivity) over the RNS prime tower `p ∈ {7, 11, 13}` for positive real parts `σ > 0`.

Context & Constraints:
- Inspect `RnsArithmetic.lean`, `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions match existing module imports, naming conventions, and formatting.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (no `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, or `trustCompiler`), verified via `#print axioms` in `TestAxioms.lean`.
- Avoid `Float` inside `Prop` definitions and avoid classical real-analysis imports. Model rational real parts `σ = num / den` with `num > 0, den > 0` using exact integer/rational power comparison (`p^num > 1^den`, i.e., `1 < p^num`), so every inequality reduces constructively via `Nat.pow`, `decide`, and `omega`.

Mathematical Model (Exact Rational Power Encoding):
For a prime modulus `p ≥ 2` and a positive rational real part `σ = num / den` (`num ≥ 1`, `den ≥ 1`):
- Because `x ↦ x^den` is strictly increasing on positive rationals, `p^(-num/den) < 1` holds if and only if `1 < p^num`, which holds for every `p ≥ 2` and `num ≥ 1`.
- Define the exact `den`-th power lower-bound numerator for the local Euler factor `1 - p^(-num/den)`:
  Since `1 - p^(-num/den) > 0 ⟺ p^(num/den) > 1 ⟺ p^num > 1`, define:
  `eulerFactorMargin (p num : Nat) : Nat := p ^ num - 1`
  and the exact rational lower bound for the integer-exponent case `σ = k` (`den = 1`):
  `eulerLocalFactorAtInt (p k : Nat) : Rat := 1 - (1 : Rat) / ((p ^ k : Nat) : Rat)`
  (or represent numerator/denominator pairs `(p^k - 1, p^k)` directly over `Nat` so zero `Rat` axioms are needed if `Rat` introduces any quotient/propext dependencies—verify with `#print axioms`!).

Deliverables:

1. Add Local Euler Factor Definitions & Theorems (in `QuasiRiemann.lean` or a dedicated `EulerFactorNonVanishing.lean` imported by `Main.lean` and `TestAxioms.lean`):
   - Reference the RNS prime-tower moduli `m₁ = 7, m₂ = 11, m₃ = 13` from `RnsArithmetic.lean`.
   - Define `eulerFactorMargin (p num : Nat) : Nat := p ^ num - 1` and `partialEulerProductMargin (num : Nat) : Nat := (7 ^ num - 1) * (11 ^ num - 1) * (13 ^ num - 1)`.
   - Prove constructively (with ZERO axioms):
     a. `prime_power_gt_one`: `∀ (p num : Nat), 2 ≤ p → 1 ≤ num → 1 < p ^ num`
     b. `local_euler_factor_nonvanishing`: `∀ (p num : Nat), 2 ≤ p → 1 ≤ num → 0 < eulerFactorMargin p num` (establishing `1 - p^(-σ) > 0` for any positive rational `σ = num / den`).
     c. `rns_prime_tower_euler_nonvanishing`: `∀ (num : Nat), 1 ≤ num → 0 < eulerFactorMargin 7 num ∧ 0 < eulerFactorMargin 11 num ∧ 0 < eulerFactorMargin 13 num`
     d. `partial_euler_product_nonvanishing`: `∀ (num : Nat), 1 ≤ num → 0 < partialEulerProductMargin num` (proving the finite product `∏_{p ∈ {7,11,13}} (1 - p^(-σ)) > 0` never vanishes anywhere in the right half-plane `σ > 0`, including across the entire critical strip `0 < σ ≤ 7/8`).
     e. `qrh_seven_eighths_euler_margins`: Concrete verified margins at the QRH threshold `σ = 7/8` (`num = 7, den = 8`), showing `7^7 - 1 = 823542 > 0`, `11^7 - 1 = 19487170 > 0`, `13^7 - 1 = 62748516 > 0`, and their product margin `> 0`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `prime_power_gt_one`, `local_euler_factor_nonvanishing`, `rns_prime_tower_euler_nonvanishing`, `partial_euler_product_nonvanishing`, and `qrh_seven_eighths_euler_margins`, confirming every theorem prints `does not depend on any axioms`.
   - Add `[+] Part 8: Prime-Tower Local Euler Factor Non-Vanishing (RNS ↔ QRH)` to `Main.lean` displaying the local Euler factor margins for `p ∈ {7, 11, 13}` at `σ = 1/2` (RH) and `σ = 7/8` (QRH), demonstrating that zeros of `ζ(s)` cannot originate from individual RNS prime channels.
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why This Encoding Guarantees Zero Axioms

* **Avoiding Quotient/Classical Dependencies:** By formulating the positivity of $1 - p^{-a/b}$ via its exact $b$-th power algebraic equivalent $p^a - 1 > 0$ over `Nat`, every theorem is proved using `Nat.one_lt_pow` / structural induction on `num` and `omega` / `decide`—guaranteeing that `propext`, `Classical.choice`, and `Quot.sound` never enter the proof term.
* **Conceptual Bridge:** It makes explicit inside `leanasm` why finite RNS prime towers $\{7, 11, 13\}$ are strictly non-vanishing for all $\operatorname{Re}(s) > 0$, isolating non-trivial zeros of $\zeta(s)$ as an emergent global phenomenon of infinite analytic continuation rather than a local channel defect.
