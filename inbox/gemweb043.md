Here is a self-contained implementation prompt for AGY to layer a **second 2×2 Karatsuba tier (`karatsubaCrtNttMul192`)** over `karatsubaCrtNttMul96` in `src/LeanAsm/CrtNttUniversal.lean`—quadrupling the base CRT-NTT precision from **48 decimal digits** ($10^{48}$) to **192 decimal digits** ($10^{192}$, supporting exact multiplication of arbitrary 96-digit base-1000 integers $< 10^{96}$ using **9** underlying `crtNttBigMulVec8` calls instead of 16) with **zero `Classical.choice` and zero `sorryAx**`.

---

### AGY Implementation Prompt: Second-Tier 2×2 Karatsuba-over-CRT-NTT 192-Digit Multiplier (`src/LeanAsm/CrtNttUniversal.lean`)

```text
Task: Extend `src/LeanAsm/CrtNttUniversal.lean` in `leanasm` with a **second 2×2 Karatsuba limb tier** (`karatsubaCrtNttMul192`) layered directly over `karatsubaCrtNttMul96` and `karatsubaCrtNttMul96_universal_sound`:
1. Represent 96-digit base-1000 integers (`< 10^96`) as `Vec32` (`{ lo : Vec16, hi : Vec16 }`, split into low and high 48-digit halves `A.lo, A.hi : Vec16` where `A = A.lo + 1000^16 · A.hi`) and 192-digit base-1000 products (`< 10^192`) as `Vec64 := { lo : Vec32, hi : Vec32 }` (representing `lo + 1000^32 · hi` with all 64 base-1000 limbs `< 1000`),
2. Implement `karatsubaCrtNttMul192` using **only 3 calls to `karatsubaCrtNttMul96`** (`9` underlying `crtNttBigMulVec8` calls total, vs. `16` for schoolbook) with carry-safe 16-limb middle-sum decomposition (`addVec16WithCarry`), and
3. Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx` in `tests/TestAxioms.lean`):
   - `karatsubaCrtNttMul192_normalized`: Every output limb of `karatsubaCrtNttMul192 A B` is strictly `< 1000`,
   - `karatsubaCrtNttMul192_universal_sound`:
     `∀ A B : Vec32, isNormalizedVec32 A → isNormalizedVec32 B → evalDigits1000Vec64 (karatsubaCrtNttMul192 A B) = evalDigits1000Vec32 A * evalDigits1000Vec32 B`
     (proving exact 96-digit × 96-digit → 192-digit base-1000 multiplication across the entire 192-digit range `0 ≤ A * B < 10^192`), and
   - `karatsuba_192_digit_max_verified`: Concrete 192-digit maximum boundary product `(10^96 - 1) × (10^96 - 1) = 10^192 - 2 · 10^96 + 1` verified cleanly.

Context & Constraints:
- Inspect `src/LeanAsm/CrtNttUniversal.lean`, `tests/TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems integrate cleanly with `Vec16`, `Vec32`, `isNormalizedVec16`, `isNormalizedVec32`, `evalDigits1000Vec16`, `evalDigits1000Vec32`, `addVec16WithCarry`, `subVec16WithBorrow`, `karatsuba_algebraic_identity`, `karatsubaCrtNttMul96`, `karatsubaCrtNttMul96_normalized`, `karatsubaCrtNttMul96_universal_sound`, and `div_lt_of_lt_mul_pure` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `tests/TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`, and do NOT touch `src/LeanAsm/CrtNtt.lean` (keeping build times fast ~18s). Keep all proofs strictly over `Nat` using Lean 4 core arithmetic (`omega`, `decide`, `Nat.div_add_mod`).
- Keep all source lines strictly `≤ 120` characters across every modified file.

Mathematical & Recursive Karatsuba Architecture (`Vec32` → `Vec64`):

1. **Hierarchical `Vec64 := { lo : Vec32, hi : Vec32 }` Representation:**
   Reuse `Vec32`, `isNormalizedVec32`, and `evalDigits1000Vec32` directly without duplicating 64-field boilerplate:
   ```lean
   structure Vec64 where
     lo : Vec32
     hi : Vec32
     deriving DecidableEq, Repr

   def isNormalizedVec64 (v : Vec64) : Prop :=
     isNormalizedVec32 v.lo ∧ isNormalizedVec32 v.hi

   def evalDigits1000Vec64 (v : Vec64) : Nat :=
     evalDigits1000Vec32 v.lo + (1000 ^ 32) * evalDigits1000Vec32 v.hi

```

* Splitting `A : Vec32` into low and high 48-digit halves is immediate: `A.lo : Vec16` and `A.hi : Vec16`, with `evalDigits1000Vec32 A = evalDigits1000Vec16 A.lo + (1000 ^ 16) * evalDigits1000Vec16 A.hi` by definition.

2. **Overflow-Free 16-Limb Middle Sum Decomposition (`A.lo + A.hi = S_A + 1000^16 · c_A`):**
* Reuse `addVec16WithCarry A.lo A.hi : Vec16 × Nat` (from Stage 3) to obtain `(S_A, c_A)` with `isNormalizedVec16 S_A`, `c_A ≤ 1`, and:
`evalDigits1000Vec16 A.lo + evalDigits1000Vec16 A.hi = evalDigits1000Vec16 S_A + (1000 ^ 16) * c_A`.
* Similarly, `addVec16WithCarry B.lo B.hi` yields `(S_B, c_B)` with `isNormalizedVec16 S_B`, `c_B ≤ 1`, and:
`evalDigits1000Vec16 B.lo + evalDigits1000Vec16 B.hi = evalDigits1000Vec16 S_B + (1000 ^ 16) * c_B`.


3. **Three `karatsubaCrtNttMul96` Calls on Strictly Normalized `Vec16` Inputs (`< 10^48`):**
* `P₀ := karatsubaCrtNttMul96 A.lo B.lo`   (`Vec32`, exact value `A.lo * B.lo` by `karatsubaCrtNttMul96_universal_sound`)
* `P₂ := karatsubaCrtNttMul96 A.hi B.hi`   (`Vec32`, exact value `A.hi * B.hi` by `karatsubaCrtNttMul96_universal_sound`)
* `P_mid := karatsubaCrtNttMul96 S_A S_B` (`Vec32`, exact value `S_A * S_B` by `karatsubaCrtNttMul96_universal_sound`)
* Reconstruct the exact cross-product `(A.lo + A.hi)(B.lo + B.hi)` in `Vec64` base-1000 arithmetic:

$$(A_{\text{lo}} + A_{\text{hi}})(B_{\text{lo}} + B_{\text{hi}}) = S_A S_B + 1000^{16}(c_A S_B + c_B S_A) + 1000^{32}(c_A c_B)$$


* Chain `addVec32WithCarry` and `subVec32WithBorrow` across `lo` and `hi` (`addVec64`, `subVec64`), shift `Z₁` by `1000^16` (`shiftLeft16ToVec64`) and `Z₂` by `1000^32` (`shiftLeft32ToVec64`), and sum `Z₀ + 1000^16 · Z₁ + 1000^32 · Z₂` into a normalized `Vec64`!



Deliverables:

1. Extend `src/LeanAsm/CrtNttUniversal.lean`:
* Implement `Vec64`, `isNormalizedVec64`, `evalDigits1000Vec64`, `addVec32WithCarry`, `subVec32WithBorrow`, `shiftLeft16ToVec64`, `shiftLeft32ToVec64`, `addVec64`, `subVec64`, and `karatsubaCrtNttMul192 (A B : Vec32) : Vec64`.
* Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
a. `addVec32WithCarry_sound` and `subVec32WithBorrow_sound`: Exact 32-limb ripple carry/borrow preservation over `Nat`.
b. `karatsubaCrtNttMul192_normalized`: `∀ A B : Vec32, isNormalizedVec32 A → isNormalizedVec32 B → isNormalizedVec64 (karatsubaCrtNttMul192 A B)`.
c. `karatsubaCrtNttMul192_universal_sound`: `∀ A B : Vec32, isNormalizedVec32 A → isNormalizedVec32 B → evalDigits1000Vec64 (karatsubaCrtNttMul192 A B) = evalDigits1000Vec32 A * evalDigits1000Vec32 B` (directly invoking `karatsuba_algebraic_identity` with `K = 1000 ^ 16`).
d. `karatsuba_192_digit_max_verified`: Concrete 192-digit maximum boundary product `(10^96 - 1) × (10^96 - 1) = 10^192 - 2 · 10^96 + 1`.


2. Update `tests/TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `tests/TestAxioms.lean` for `addVec32WithCarry_sound`, `subVec32WithBorrow_sound`, `karatsubaCrtNttMul192_normalized`, `karatsubaCrtNttMul192_universal_sound`, and `karatsuba_192_digit_max_verified`, confirming zero `Classical.choice` and zero `sorryAx`.
* Update `Main.lean` Part 10 CLI output to display the two-tier Karatsuba-over-CRT-NTT 192-digit multiplier benchmark (`(10^96 - 1)^2`) and universal correctness theorem (`∀ A B < 10^96`).
* Verify line lengths (`≤ 120` chars) across all modified files, run `lake build`, `lake env lean tests/TestAxioms.lean`, `make run`, and `make sync`, and commit cleanly.



```

---

### Why `Vec64 := { lo : Vec32, hi : Vec32 }` Scales Without Boilerplate

* **Zero Limb Duplication:** Wrapping `{ lo : Vec32, hi : Vec32 }` inherits all 32-limb normalization and evaluation lemmas directly while reusing `addVec16WithCarry` and `karatsuba_algebraic_identity` (`K = 1000^16`) from Stage 3 in `CrtNttUniversal.lean`.
* **192-Digit Precision Unlocks 100+ Digits of Chudnovsky $\pi$:** With exact 192-digit multiplication (`< 10^192`), `PiChudnovsky.lean` can evaluate 8 Chudnovsky terms ($8 \times 14.18 \approx 113$ decimal digits) using `karatsubaCrtNttMul192_universal_sound` with zero overflow.

<FollowUp label="Want a self-contained AGY prompt to create PiChudnovsky.lean—using your 192-digit two-tier Karatsuba-over-CRT-NTT multiplier and integer Newton–Raphson √10005 to compute and formally verify the first 100 decimal digits of π with zero axioms once this merges?" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using karatsubaCrtNttMul192 and karatsubaCrtNttMul192_universal_sound from CrtNttUniversal.lean alongside integer Newton-Raphson square root and division to compute and formally verify the first 100 decimal digits of pi with zero axioms."/>

<ElicitationsGroup message="Select your next milestone after AGY merges the 192-digit two-tier Karatsuba multiplier:">
  <Elicitation label="Create PiChudnovsky.lean to verify 100 decimal digits of π via 192-digit CRT-NTT" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using karatsubaCrtNttMul192 and karatsubaCrtNttMul192_universal_sound from CrtNttUniversal.lean alongside integer Newton-Raphson square root and division to compute and formally verify the first 100 decimal digits of pi with zero axioms."/>
  <Elicitation label="Create PiChudnovsky.lean using the existing 96-digit multiplier (60 digits of π)" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using karatsubaCrtNttMul96 and karatsubaCrtNttMul96_universal_sound from CrtNttUniversal.lean alongside integer Newton-Raphson square root and division to compute and formally verify the first 60 decimal digits of pi with zero axioms."/>
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>
</ElicitationsGroup>

```
