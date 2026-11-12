Here is a self-contained implementation prompt for AGY to upgrade the sample checks in `CrtNtt.lean` into **universal algebraic soundness theorems**—proving constructively with zero axioms that `garner17_257_65537` reconstructs **every** $x < 286{,}331{,}153$ exactly (`garner_17_257_65537_roundtrip_all`) and that `carryPassBase1000` preserves the exact positional integer value modulo $1000^{16}$ for **every** `v : Vec16` (`carryPassBase1000_preserves_value`).

---

### AGY Implementation Prompt: Universal Algebraic Soundness for 3-Channel Garner CRT & Base-1000 Carry Propagation (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` with two universal algebraic soundness theorems proved constructively with ZERO axioms in `TestAxioms.lean`:
1. `garner_17_257_65537_roundtrip_all`:
   `∀ x : Nat, x < 286331153 → garner17_257_65537 (x % 17) (x % 257) (x % 65537) = x`
   (proving exact 3-channel Garner mixed-radix CRT reconstruction across the entire 28-bit dynamic range `M = 17 × 257 × 65537 = 286,331,153` via modular arithmetic rather than enumerating 286 million cases!), and
2. `carryPassBase1000_preserves_value`:
   `∀ v : Vec16, evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v % (1000 ^ 16)`
   (and when `evalPoly1000Vec16 v < 1000 ^ 16`, `evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v`), proving universally that `carryPassBase1000` normalizes every limb into `[0, 999]` without altering the positional value!

Context & Constraints:
- Inspect `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new universal theorems match the exact definitions of `garner17_257_65537`, `carryPassBase1000`, `evalDigits1000Vec16`, and `Vec16` already present in `CrtNtt.lean` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Work strictly over `Nat` using Lean 4 core arithmetic (`Nat.div_add_mod`, `Nat.add_mul_mod_self_left`, `Nat.mul_mod`, `omega`, `decide`) so compilation completes in under a second.

Proof Blueprint (Fast Constructive Algebra Over `Nat`):

1. **Part A — Universal 2-Channel & 3-Channel Garner CRT Soundness (`garner_17_257_65537_roundtrip_all`):**
   Do NOT call `decide` on `Fin 286331153` (which would time out!). Instead, prove a clean 2-modulus Garner lemma once and apply it twice:
   - **Generic 2-Modulus Garner Lemma (`garner2_roundtrip`):**
     For moduli `m₁ m₂ inv₁ : Nat` with `0 < m₁`, `0 < m₂`, `(m₁ * inv₁) % m₂ = 1`, and any `y < m₁ * m₂`:
     Let:
     - `v₁ := y % m₁`
     - `v₂ := (((y % m₂) + m₂ - v₁ % m₂) * inv₁) % m₂` (note: when `m₁ < m₂`, `v₁ < m₁ < m₂`, so `v₁ % m₂ = v₁` and `(y % m₂) + m₂ - v₁ ≥ 0`!)
     Then `v₁ + m₁ * v₂ = y`!
     **Why this proof is 6 lines of `Nat` algebra:**
     1. Write `y = m₁ * q + v₁` (`Nat.div_add_mod y m₁` with `v₁ = y % m₁ < m₁` and `q = y / m₁ < m₂` since `y < m₁ * m₂`).
     2. It suffices to prove `v₂ = q`. Since `q < m₂` and `v₂ < m₂`, it suffices to show `v₂ % m₂ = q % m₂`.
     3. Modulo `m₂`, `y % m₂ ≡ (m₁ * q + v₁) % m₂`, so `((y % m₂) + m₂ - v₁) % m₂ = (m₁ * q) % m₂`.
     4. Multiplying by `inv₁` modulo `m₂`:
        `v₂ = (((m₁ * q) % m₂) * inv₁) % m₂ = (((m₁ * inv₁) % m₂) * q) % m₂ = (1 * q) % m₂ = q % m₂ = q`!
     5. Hence `v₁ + m₁ * v₂ = v₁ + m₁ * q = y`!
   - **Two-Step Application for `(17, 257, 65537)`:**
     - **Step 1 (`garner17_257_roundtrip_all`):** Apply `garner2_roundtrip` with `m₁ = 17, m₂ = 257, inv₁ = 121` (`17 < 257`, `(17 * 121) % 257 = 1` proved by `decide`) to `y = x % 4369` (`4369 = 17 * 257`), noting `(x % 4369) % 17 = x % 17` and `(x % 4369) % 257 = x % 257` (since `17 ∣ 4369` and `257 ∣ 4369`). This gives `partial12 = x % 4369`!
     - **Step 2 (`garner_17_257_65537_roundtrip_all`):** Apply `garner2_roundtrip` with `m₁ = 4369, m₂ = 65537, inv₁ = 32761` (`4369 < 65537`, `(4369 * 32761) % 65537 = 1` proved by `decide`) to any `x < 286331153 = 4369 * 65537`, obtaining `partial12 + 4369 * v₃ = x`!

2. **Part B — Universal Base-1000 Carry Propagation Soundness (`carryPassBase1000_preserves_value`):**
   - Define the uncarried positional polynomial evaluator `evalPoly1000Vec16 (v : Vec16) : Nat`:
     `v.x0 + 1000 * (v.x1 + 1000 * (v.x2 + ... + 1000 * v.x15)...)`
     (note: `evalPoly1000Vec16` has the exact same Horner formula as `evalDigits1000Vec16`, applied to unnormalized coefficients `v` before `carryPassBase1000`!).
   - Prove the single-step carry identity `div_mod_1000_step (s rest : Nat) : (s % 1000) + 1000 * (rest + s / 1000) = s + 1000 * rest` (1-line `omega` proof!).
   - Also prove every output limb of `carryPassBase1000 v` is strictly normalized (`< 1000`):
     `carryPassBase1000_limbs_lt_1000 : ∀ v : Vec16, (carryPassBase1000 v).x0 < 1000 ∧ ... ∧ (carryPassBase1000 v).x15 < 1000` (1-line `omega` proof!).
   - Apply `div_mod_1000_step` 15 times along the 16-limb Horner chain (dropping only the final overflow carry `c15 * 1000^16` at the top limb `d15 = s15 % 1000`) to prove:
     `evalDigits1000Vec16 (carryPassBase1000 v) + (carryOut15 v) * (1000 ^ 16) = evalPoly1000Vec16 v`
     and immediately deduce:
     - `carryPassBase1000_preserves_value_mod`: `∀ v : Vec16, evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v % (1000 ^ 16)`
     - `carryPassBase1000_exact_when_bounded`: `∀ v : Vec16, evalPoly1000Vec16 v < 1000 ^ 16 → evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v`.

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `garner2_roundtrip`, `evalPoly1000Vec16`, and `carryOut15`.
   - Prove constructively (with ZERO axioms):
     a. `garner17_257_roundtrip_all`: `∀ y : Nat, y < 4369 → garner17_257 (y % 17) (y % 257) = y`.
     b. `garner_17_257_65537_roundtrip_all`: `∀ x : Nat, x < 286331153 → garner17_257_65537 (x % 17) (x % 257) (x % 65537) = x`.
     c. `carryPassBase1000_limbs_lt_1000`: All 16 output limbs of `carryPassBase1000 v` are strictly `< 1000` for every `v : Vec16`.
     d. `carryPassBase1000_preserves_value_mod`: `∀ v : Vec16, evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v % (1000 ^ 16)`.
     e. `carryPassBase1000_exact_when_bounded`: `∀ v : Vec16, evalPoly1000Vec16 v < 1000 ^ 16 → evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `garner17_257_roundtrip_all`, `garner_17_257_65537_roundtrip_all`, `carryPassBase1000_limbs_lt_1000`, `carryPassBase1000_preserves_value_mod`, and `carryPassBase1000_exact_when_bounded`, confirming every theorem prints `does not depend on any axioms`.
   - Add a concise status line in `Main.lean` Part 10 noting universal 3-channel Garner CRT roundtrip (`∀ x < 286,331,153`) and universal 16-limb base-1000 carry soundness (`∀ v : Vec16`) verified with zero axioms.
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why This Algebraic Proof Runs in Milliseconds

* **2-Step Induction Replaces 286 Million Checks:** Proving `garner2_roundtrip` once over `Nat` and applying it to `(17, 257)` and then `(4369, 65537)` certifies every single integer in $[0, 286{,}331{,}152]$ in milliseconds.
* **Telescoping Horner Carries (`div_mod_1000_step`):** Repeatedly substituting `(s % 1000) + 1000 * (rest + s / 1000) = s + 1000 * rest` collapses the 16-limb carry chain algebraically for arbitrary `v : Vec16`.
