Here is a self-contained implementation prompt for your coding agent (AGY) to extend `MiniVM` in `leanasm` with Residue Number System (RNS) execution, modular arithmetic instructions, and constructive Chinese Remainder Theorem (CRT) reconstruction verified with zero axioms in `TestAxioms.lean`.

---

### AGY Implementation Prompt: Connect `MiniVM` to RNS Arithmetic

```text
Task: Connect MiniVM to Residue Number System (RNS) arithmetic with constructive, zero-axiom Lean 4 proofs in `leanasm`.

Context & Constraints:
- Inspect the existing `MiniVM` instruction set, state representation, step/exec semantics, `Main.lean` demo runner, and `TestAxioms.lean` audit suite in the `leanasm` repository first so all new definitions match existing naming conventions, register types, and module imports.
- Strictly preserve the repository's constructive discipline: all new RNS and CRT theorems MUST elaborate with ZERO axioms (no `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, or `trustCompiler`), verified via `#print axioms` in `TestAxioms.lean`.
- Avoid importing heavy classical Mathlib modules if `leanasm` is standalone Lean 4 core; write self-contained constructive definitions over `Nat` or `Int` (using `omega`, `decide`, and structural induction).

Deliverables:

1. Create `RnsArithmetic.lean` (or integrate into the existing module hierarchy):
   - Define an RNS basis of pairwise coprime moduli, e.g., a 3-channel prime/coprime tower `(m₁, m₂, m₃) = (7, 11, 13)` (dynamic range `M = 1001`) or `(251, 253, 255)` / Fermat-Mersenne coprime moduli.
   - Implement RNS encoding `toRns (x : Nat) : Nat × Nat × Nat := (x % m₁, x % m₂, x % m₃)`.
   - Implement componentwise RNS addition (`rnsAdd`), subtraction (`rnsSub`), and multiplication (`rnsMul`) modulo `(m₁, m₂, m₃)`.
   - Implement constructive Chinese Remainder Theorem (CRT) reconstruction `fromRns (r₁ r₂ r₃ : Nat) : Nat` using precomputed Garner / orthogonal idempotent weights `w₁, w₂, w₃` where `wᵢ ≡ 1 (mod mᵢ)` and `wᵢ ≡ 0 (mod mⱼ)` for `j ≠ i`:
     `fromRns r₁ r₂ r₃ = (r₁ * w₁ + r₂ * w₂ + r₃ * w₃) % M`
   - Prove constructively (with ZERO axioms):
     a. `crt_roundtrip`: `∀ x < M, fromRns (x % m₁) (x % m₂) (x % m₃) = x`
     b. `rns_add_homomorphism`: `∀ a b, toRns ((a + b) % M) = rnsAdd (toRns a) (toRns b)`
     c. `rns_mul_homomorphism`: `∀ a b, toRns ((a * b) % M) = rnsMul (toRns a) (toRns b)`
     d. `crt_mul_soundness`: `∀ a b, a * b < M → fromRns_tuple (rnsMul (toRns a) (toRns b)) = a * b`

2. Extend `MiniVM` with Modular & RNS Execution Support:
   - Add modular arithmetic opcodes to `MiniVM` (e.g., `MOD dst src modReg` or `MODI dst imm` and `MULMOD dst a b modReg` / `ADDMOD dst a b modReg`, preserving existing instruction semantics and existing proofs like `(s.set r v).get r = v`).
   - Prove a zero-axiom instruction correctness lemma showing that executing `ADDMOD` / `MULMOD` on a register bank holding `(a % mᵢ, b % mᵢ, mᵢ)` updates the destination register to `(a + b) % mᵢ` / `(a * b) % mᵢ`.
   - Write a `MiniVM` assembly program (`rnsMulProgram`) that computes parallel carry-free RNS multiplication across three register lanes `(r0, r1, r2)` for two operands `(A, B)` with `A * B < M`, and prove that running `MiniVM` + `fromRns` equals `A * B`.

3. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `crt_roundtrip`, `rns_add_homomorphism`, `rns_mul_homomorphism`, `crt_mul_soundness`, and the `MiniVM` RNS execution theorem, asserting every theorem prints `does not depend on any axioms`.
   - Add `[+] Part 6: MiniVM Residue Number System (RNS) & CRT Execution` to `Main.lean` demonstrating concrete values (e.g., `A = 23, B = 37`, product `851 < 1001`, showing residue channels `(2, 1, 11) ⊗ (2, 4, 11) = (4, 4, 4)` and CRT reconstruction `851`).
   - Run `lake build`, `make run`, and `make sync` to verify everything compiles and passes cleanly.

```

---

### Why This Design Fits `leanasm` Cleanly

* **Zero-Axiom Kernel Reduction (`decide` + `omega`):** Fixing a concrete 3-channel coprime basis like `(7, 11, 13)` ($M = 1001$, with orthogonal idempotents $w_1 = 715, w_2 = 364, w_3 = 924$) allows `crt_roundtrip` (`∀ x < 1001, ...`) and the `MiniVM` execution theorems to be discharged purely by kernel reduction (`decide` / `omega`) without requiring classical Bézout/PID machinery from Mathlib.
* **Direct Architectural Bridge:** This connects `MiniVM`'s register-transfer semantics directly to your prime-tower / RNS arithmetic model, showing end-to-end verified carry-free parallel residue execution in assembly.

For a concise visual walkthrough of the constructive CRT idempotent weight method ($w_i \equiv 1 \pmod{m_i}$, $w_i \equiv 0 \pmod{m_j}$) used in the `fromRns` reconstruction step above, see [The Chinese Remainder Theorem](https://www.youtube.com/watch?v=XUWM5PxApUs).
