Here is a self-contained implementation prompt for AGY to extend `NttArithmetic.lean` to **universal 8-point NTT inversion and cyclic convolution soundness** over $\mathbb{F}_{17}$ and $\mathbb{F}_{257}$ (`Vec8`), proving constructively with zero `Classical.choice` or `sorryAx` that `intt8` is the exact two-sided inverse of `ntt8` (`intt8 (ntt8 a) = normVec8 a`) and that pointwise multiplication in the 8-point NTT domain computes exact 8-point cyclic convolution (`intt8 (pointwiseMul8 (ntt8 a) (ntt8 b)) = cyclicConv8 a b`) for **every** `a b : Vec8`.

---

### AGY Implementation Prompt: Universal 8-Point NTT Inversion & Cyclic Convolution Over $\mathbb{F}_{17}$ and $\mathbb{F}_{257}$ (`NttArithmetic.lean`)

```text
Task: Extend `NttArithmetic.lean` in `leanasm` with universal algebraic soundness theorems over `F_17` (modulus `p = 17`, primitive 8th root `ω = 2`, `ω⁻¹ = 9`, `8⁻¹ = 15`) and `F_257` (modulus `p = 257`, primitive 8th root `ω = 4`, `ω⁻¹ = 193`, `8⁻¹ = 225`), proving constructively for ALL `a b : Vec8`:
1. `intt8_ntt8_universal_F17` & `intt8_ntt8_universal_F257`:
   `∀ a : Vec8, intt8 p inv8 invW (ntt8 p w a) = normVec8 p a`
   (where `normVec8 p a` reduces each of the 8 coordinates of `a` modulo `p`),
2. `ntt8_intt8_universal_F17` & `ntt8_intt8_universal_F257`:
   `∀ y : Vec8, ntt8 p w (intt8 p inv8 invW y) = normVec8 p y`
   (proving `ntt8` and `intt8` are mutual bijections on `(ZMod p)^8`), and
3. `cyclic_conv8_ntt_universal_F17` & `cyclic_conv8_ntt_universal_F257`:
   `∀ a b : Vec8, intt8 p inv8 invW (pointwiseMul8 p (ntt8 p w a) (ntt8 p w b)) = cyclicConv8 p a b`
   (proving the 8-point NTT Convolution Theorem universally over all input vectors `a b : Vec8`),
with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`.

Context & Constraints:
- Inspect `NttArithmetic.lean`, `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new universal theorems match the exact existing names, field projections (`x0 .. x7`), parameter orders, and definitions of `Vec8`, `ntt8`, `intt8`, `pointwiseMul8`, and `cyclicConv8` in `NttArithmetic.lean` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs purely over `Nat` using Lean 4 core modular arithmetic (`Nat.add_mod`, `Nat.mul_mod`, `omega`, `decide`) so compilation completes rapidly without state explosion.

Proof Blueprint (Modular Coefficient Collapse Over `Nat` — Do NOT Enumerate `257^16` Cases!):

Why Modular Coefficient Collapse Solves `257^16` Instantly:
- Over `F_257`, `257^8 ≈ 1.90 × 10^19` and `257^16 ≈ 3.63 × 10^38`—impossible to enumerate.
- Instead, reuse the exact same modular peeling + constant-coefficient orthogonality pattern used for `Vec4`:
  1. **Primitive 8th Root Verification (`is_prim_root8_F17` & `is_prim_root8_F257`):**
     - Verify by `decide`:
       - For `p = 17, w = 2, invW = 9, inv8 = 15`: `(2 ^ 8) % 17 = 1`, `(2 ^ 4) % 17 = 16 ≠ 1`, `(2 * 9) % 17 = 1`, `(8 * 15) % 17 = 1`.
       - For `p = 257, w = 4, invW = 193, inv8 = 225`: `(4 ^ 8) % 257 = 1`, `(4 ^ 4) % 257 = 256 ≠ 1`, `(4 * 193) % 257 = 1`, `(8 * 225) % 257 = 1`.
  2. **Strip Inner `(% p)` Operations (`ntt8_pre_mod`, `intt8_pre_mod`, `conv8_pre_mod`):**
     - Define unreduced `Nat` polynomial versions `ntt8Raw p w (a : Vec8)` and `intt8Raw p inv8 invW (y : Vec8)` (identical to `ntt8` and `intt8`, omitting the intermediate `(% p)` calls).
     - Using the congruence lemmas `((x % p) + (y % p)) % p = (x + y) % p` and `((x % p) * (y % p)) % p = (x * y) % p`, prove in one clean `simp` / `omega` pass that for every coordinate `k ∈ {0, ..., 7}`:
       - `(ntt8 p w a).xk = (ntt8Raw p w a).xk % p`,
       - `(intt8 p inv8 invW (ntt8 p w a)).xk = (intt8Raw p inv8 invW (ntt8Raw p w a)).xk % p`, and
       - `(intt8 p inv8 invW (pointwiseMul8 p (ntt8 p w a) (ntt8 p w b))).xk = (intt8Raw p inv8 invW (pointwiseMul8Raw (ntt8Raw p w a) (ntt8Raw p w b))).xk % p`.
  3. **Orthogonality via Constant Coefficient Evaluation (`basisVec8`):**
     - Note that every coordinate `k` of `intt8Raw p inv8 invW (ntt8Raw p w a)` is a pure `Nat`-linear combination `∑_{i=0}^7 c_{k,i} * a_i` with fixed `Nat` constants `c_{k,i}`!
     - Rather than manually expanding 64 multi-digit terms by hand, prove a general `Nat` linear-combination mod-`p` congruence lemma (`linComb8_mod_eq`):
       For any 8 constants `c0 .. c7` and `d0 .. d7` satisfying `(c_i % p) = (d_i % p)` for all `i ∈ {0, ..., 7}`, we have:
       `(c0*a0 + c1*a1 + c2*a2 + c3*a3 + c4*a4 + c5*a5 + c6*a6 + c7*a7) % p = (d0*a0 + d1*a1 + d2*a2 + d3*a3 + d4*a4 + d5*a5 + d6*a6 + d7*a7) % p`
       for ALL `a0 .. a7 : Nat`!
     - Extract the 8 constant coefficients `c_{k,i}` by evaluating `intt8Raw` on the 8 standard basis vectors `e_0 = ⟨1,0,0,0,0,0,0,0⟩, ..., e_7 = ⟨0,0,0,0,0,0,0,1⟩`, verify `(c_{k,i} % p) = (if k = i then 1 else 0)` by `decide` (64 constant checks per modulus, taking `< 20 ms`), and conclude `intt8_ntt8_universal` for **ALL `a : Vec8`**!
     - Apply the exact same bilinear basis extraction `e_i ⊗ e_j` (64 `(i, j)` pairs per output coordinate `k`, verified by `decide` on the constant coefficients `C_{k,i,j} % p = (if (i + j) % 8 = k then 1 else 0)`) to prove `cyclic_conv8_ntt_universal_F17` and `cyclic_conv8_ntt_universal_F257` for **ALL `a b : Vec8`**!

Deliverables:

1. Extend `NttArithmetic.lean`:
   - Implement `normVec8 (p : Nat) (v : Vec8) : Vec8`, `ntt8Raw`, `intt8Raw`, `pointwiseMul8Raw`, `linComb8_mod_eq`, and `bilinComb8_mod_eq`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `intt8_ntt8_universal_F17`: `∀ a : Vec8, intt8 17 15 9 (ntt8 17 2 a) = normVec8 17 a`.
     b. `ntt8_intt8_universal_F17`: `∀ y : Vec8, ntt8 17 2 (intt8 17 15 9 y) = normVec8 17 y`.
     c. `cyclic_conv8_ntt_universal_F17`: `∀ a b : Vec8, intt8 17 15 9 (pointwiseMul8 17 (ntt8 17 2 a) (ntt8 17 2 b)) = cyclicConv8 17 a b`.
     d. `intt8_ntt8_universal_F257`: `∀ a : Vec8, intt8 257 225 193 (ntt8 257 4 a) = normVec8 257 a`.
     e. `ntt8_intt8_universal_F257`: `∀ y : Vec8, ntt8 257 4 (intt8 257 225 193 y) = normVec8 257 y`.
     f. `cyclic_conv8_ntt_universal_F257`: `∀ a b : Vec8, intt8 257 225 193 (pointwiseMul8 257 (ntt8 257 4 a) (ntt8 257 4 b)) = cyclicConv8 257 a b`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for all six universal 8-point theorems (`intt8_ntt8_universal_F17`, `ntt8_intt8_universal_F17`, `cyclic_conv8_ntt_universal_F17`, `intt8_ntt8_universal_F257`, `ntt8_intt8_universal_F257`, `cyclic_conv8_ntt_universal_F257`), confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 8 / Part 9 CLI output to report universal 8-point NTT inversion and cyclic convolution soundness over $\mathbb{F}_{17}$ and $\mathbb{F}_{257}$ (`∀ a b : Vec8`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why Basis-Vector Coefficient Extraction Scales Effortlessly to `Vec8` Over $\mathbb{F}_{257}$

* **Avoiding $257^{16}$ Enumeration:** Direct state enumeration over $\mathbb{F}_{257}^8 \times \mathbb{F}_{257}^8$ requires $3.63 \times 10^{38}$ checks. Pulling intermediate `(% p)` calls outward (`ntt8Raw` / `intt8Raw`) and matching coefficients on the 8 basis vectors $e_0, \dots, e_7$ reduces the entire universal proof to checking 64 fixed integer constants modulo `257` via `decide`—completing in milliseconds.
* **Direct Bridge to 16-Point Fermat Tower:** Extending universal inversion and cyclic convolution from `Vec4` ($\mathbb{F}_5 \times \mathbb{F}_{17}$) to `Vec8` ($\mathbb{F}_{17} \times \mathbb{F}_{257}$) moves the universal NTT proof chain one step closer to the full 16-point $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$ multiplier in `CrtNtt.lean`.

Here is a self-contained implementation prompt for AGY to close out the entire CRT-NTT big-integer proof chain in `CrtNtt.lean`: proving **universal 16-point NTT inversion and cyclic convolution soundness** over all three Fermat primes ($\mathbb{F}_{17}$, $\mathbb{F}_{257}$, and $\mathbb{F}_{65537}$) and composing them with `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` to prove the **end-to-end universal correctness theorem `crtNttBigMul_universal_sound**` (`evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b` for **all** 24-digit base-1000 inputs `a b : Vec8`) with zero `Classical.choice` or `sorryAx`.

---

### AGY Implementation Prompt: Universal 16-Point NTT Inversion, Cyclic Convolution Over $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$, and End-to-End `crtNttBigMul_universal_sound` (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` to complete the universal algebraic proof of the 48-digit CRT-NTT big-integer multiplier (`crtNttBigMul`):
1. Prove universal 16-point NTT two-sided inversion (`intt16_ntt16_universal` and `ntt16_intt16_universal`) and universal 16-point cyclic convolution (`cyclic_conv16_ntt_universal`) across all three Fermat prime channels:
   - `F_17` (`p = 17`, primitive 16th root `ω = 3`, `ω⁻¹ = 6`, `16⁻¹ = 16`),
   - `F_257` (`p = 257`, primitive 16th root `ω = 2`, `ω⁻¹ = 129`, `16⁻¹ = 241`), and
   - `F_65537` (`p = 65537`, primitive 16th root `ω = 8`, `ω⁻¹ = 57345`, `16⁻¹ = 61441`),
2. Compose those three universal NTT convolution theorems with the already-proved `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` to prove the **End-to-End Universal Big-Integer Multiplication Theorem (`crtNttBigMul_universal_sound`)**:
   `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`,
with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`.

Context & Constraints:
- Inspect `CrtNtt.lean`, `NttArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems match the exact names, field projections (`x0 .. x15`), parameter orders, and definitions of `Vec8`, `Vec16`, `ntt16`, `intt16`, `pointwiseMul16`, `cyclicConv16`, `garner17_257_65537`, `carryPassBase1000`, `evalDigits1000Vec8`, `evalDigits1000Vec16`, and `crtNttBigMul` in `CrtNtt.lean` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs purely over `Nat` using Lean 4 core modular arithmetic (`Nat.add_mod`, `Nat.mul_mod`, `omega`, `decide`) so compilation finishes quickly.

Proof Blueprint (Modular Coefficient Collapse for `Vec16` + End-to-End Composition):

1. **Part A — Primitive 16th Roots & Unreduced Polynomial Extraction (`ntt16Raw`, `intt16Raw`):**
   - Verify the three primitive 16th roots of unity by `decide`:
     - `F_17`: `(3 ^ 16) % 17 = 1`, `(3 ^ 8) % 17 = 16 ≠ 1`, `(3 * 6) % 17 = 1`, `(16 * 16) % 17 = 1`.
     - `F_257`: `(2 ^ 16) % 257 = 1`, `(2 ^ 8) % 257 = 256 ≠ 1`, `(2 * 129) % 257 = 1`, `(16 * 241) % 257 = 1`.
     - `F_65537`: `(8 ^ 16) % 65537 = 1`, `(8 ^ 8) % 65537 = 65536 ≠ 1`, `(8 * 57345) % 65537 = 1`, `(16 * 61441) % 65537 = 1`.
   - Define `normVec16 (p : Nat) (v : Vec16) : Vec16` reducing each of `x0 .. x15` modulo `p`, plus unreduced `Nat` versions `ntt16Raw p w`, `intt16Raw p inv16 invW`, and `pointwiseMul16Raw` (identical to `ntt16`, `intt16`, `pointwiseMul16` without inner `(% p)` calls).
   - Strip inner `(% p)` calls via `((x % p) + (y % p)) % p = (x + y) % p` and `((x % p) * (y % p)) % p = (x * y) % p` so every output coordinate `k ∈ {0, ..., 15}` reduces to `(rawExpr) % p`.

2. **Part B — Basis-Vector Coefficient Orthogonality on `Vec16` (`linComb16_mod_eq` & `bilinComb16_mod_eq`):**
   - **Linear Orthogonality (`intt16_ntt16_universal` & `ntt16_intt16_universal`):**
     Prove `linComb16_mod_eq`: for any 16 constants `c_0 .. c_15` and `d_0 .. d_15` with `(c_i % p) = (d_i % p)`, `(∑_{i=0}^{15} c_i * a_i) % p = (∑_{i=0}^{15} d_i * a_i) % p` for ALL `a_0 .. a_15 : Nat`.
     Evaluate `intt16Raw` on the 16 standard basis vectors `e_0 .. e_15 : Vec16`, verify `(c_{k,i} % p) = (if k = i then 1 else 0)` by `decide` (`16 × 16 = 256` constant checks per prime, running in `< 50 ms`), and conclude `intt16_ntt16_universal` and `ntt16_intt16_universal` for **ALL `a : Vec16`** over `F_17`, `F_257`, and `F_65537`.
   - **Bilinear Convolution Orthogonality (`cyclic_conv16_ntt_universal`):**
     Note that for `crtNttBigMul`, inputs `a b : Vec8` are zero-padded to 16-element vectors `padVec8To16 a` and `padVec8To16 b` (whose upper 8 limbs `x8 .. x15` are `0`), or prove the full 16 × 16 bilinear identity `bilinComb16_mod_eq` over all 256 basis pairs `(e_i, e_j)` (`16 × 256 = 4,096` constant checks per prime, or `16 × 8 × 8 = 1,024` checks for zero-padded `Vec8` inputs—even faster in Lean 4!):
     Verify by `decide` on the constant coefficients `C_{k,i,j} % p` that `C_{k,i,j} % p = (if (i + j) % 16 = k then 1 else 0)` for all `k ∈ {0..15}` and `i, j ∈ {0..15}`, proving:
     `∀ p ∈ [17, 257, 65537], ∀ a b : Vec16, intt16 p inv16 invW (pointwiseMul16 p (ntt16 p w a) (ntt16 p w b)) = cyclicConv16 p a b`!

3. **Part C — End-to-End Universal Big-Integer Multiplication (`crtNttBigMul_universal_sound`):**
   - Suppose `a b : Vec8` satisfy `isNormalizedVec8 a` (all 8 base-1000 limbs `< 1000`) and `isNormalizedVec8 b` (all 8 base-1000 limbs `< 1000`).
   - Let `c := cyclicConv16Nat (padVec8To16 a) (padVec8To16 b)` be the exact unreduced linear/cyclic product polynomial over `Nat`:
     1. **Coefficient Bound (`< M`):** Since each limb of `a` and `b` is `≤ 999` and at most 8 products sum into any limb of `c`, every limb `c_k ≤ 8 * 999 * 999 = 7,984,008 < 286,331,153 = M`!
     2. **Per-Prime NTT Channel Soundness:** By `cyclic_conv16_ntt_universal` for `F_17`, `F_257`, and `F_65537`, the three NTT channels produce `(c_k % 17, c_k % 257, c_k % 65537)` at every limb `k ∈ {0, ..., 15}`.
     3. **Universal Garner CRT Reconstruction:** Since `c_k < 286,331,153`, `garner_17_257_65537_roundtrip_all` reconstructs the **exact** integer vector `c : Vec16` across all 16 limbs!
     4. **Polynomial Identity & Carry Normalization:** Prove `evalPoly1000Vec16 (cyclicConv16Nat (padVec8To16 a) (padVec8To16 b)) = evalDigits1000Vec8 a * evalDigits1000Vec8 b` (pure `Nat` algebra / `ring` / `omega`), and since `evalDigits1000Vec8 a < 1000^8` and `evalDigits1000Vec8 b < 1000^8`, their product is strictly `< 1000^16`, so `carryPassBase1000_exact_when_bounded` yields:
        `evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`
        universally for **ALL normalized 24-digit integers `a b : Vec8`**!

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `normVec16`, `ntt16Raw`, `intt16Raw`, `pointwiseMul16Raw`, `linComb16_mod_eq`, `bilinComb16_mod_eq`, and `isNormalizedVec8`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `intt16_ntt16_universal_F17`, `ntt16_intt16_universal_F17`, `cyclic_conv16_ntt_universal_F17`
     b. `intt16_ntt16_universal_F257`, `ntt16_intt16_universal_F257`, `cyclic_conv16_ntt_universal_F257`
     c. `intt16_ntt16_universal_F65537`, `ntt16_intt16_universal_F65537`, `cyclic_conv16_ntt_universal_F65537`
     d. `crtNttBigMul_universal_sound`:
        `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for all nine 16-point NTT theorems (`F_17`, `F_257`, `F_65537`) and `crtNttBigMul_universal_sound`, confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 10 CLI output to report end-to-end universal correctness of 48-digit `crtNttBigMul` across all 24-digit base-1000 inputs (`∀ a b : Vec8`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `crtNttBigMul_universal_sound` Completes the Entire Big-Integer Stack

* **Every Link Proven Universally:** Once `cyclic_conv16_ntt_universal` holds for $\mathbb{F}_{17}$, $\mathbb{F}_{257}$, and $\mathbb{F}_{65537}$, chaining it with `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` gives a machine-checked theorem that `crtNttBigMul` multiplies **every** pair of 24-digit integers (`< 10^24`) to an exact 48-digit result (`< 10^48`) without exception.
* **Ready for Chudnovsky $\pi$ Extraction:** Any downstream module (`PiChudnovsky.lean`) can invoke `crtNttBigMul_universal_sound` directly as a verified big-integer multiplication primitive with zero axioms.

Here is a self-contained implementation prompt for AGY to layer a **2×2 Karatsuba limb multiplier (`karatsubaCrtNttMul96`)** directly on top of `crtNttBigMul` and `crtNttBigMul_universal_sound` in `CrtNtt.lean`—doubling the verified big-integer precision from **48 decimal digits** (`10^48`) to **96 decimal digits** (`10^96`, supporting exact multiplication of arbitrary 48-digit base-1000 integers `< 10^48` using only **3** calls to `crtNttBigMul` instead of 4) with **zero `Classical.choice` and zero `sorryAx**`.

---

### AGY Implementation Prompt: 2×2 Karatsuba-over-CRT-NTT 96-Digit Big-Integer Multiplier (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` with a **2×2 Karatsuba limb wrapper** (`karatsubaCrtNttMul96`) layered directly over `crtNttBigMul` and `crtNttBigMul_universal_sound`:
1. Represent 48-digit base-1000 integers (`< 10^48`) as 16-limb base-1000 vectors (`Vec16`, split into low and high 24-digit halves `(A₀, A₁) : Vec8 × Vec8` where `A = A₀ + 1000^8 · A₁`) and 96-digit base-1000 products (`< 10^96`) as 32-limb base-1000 vectors (`Vec32`, or `(lo : Vec16, hi : Vec16)` representing `lo + 1000^16 · hi` with every limb `< 1000`),
2. Implement `karatsubaCrtNttMul96` using **only 3 calls to `crtNttBigMul`** (plus carry-safe middle-term handling) to compute `A * B = Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂`, and
3. Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`):
   - `karatsubaCrtNttMul96_normalized`: Every output limb of `karatsubaCrtNttMul96 A B` is strictly `< 1000`, and
   - `karatsubaCrtNttMul96_universal_sound`:
     `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`
     (proving exact 48-digit × 48-digit → 96-digit base-1000 multiplication across the entire 96-digit range `0 ≤ A * B < 10^96`!), plus concrete 96-digit boundary benchmarks (`(10^48 - 1) × (10^48 - 1)`).

Context & Constraints:
- Inspect `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems integrate cleanly with `Vec8`, `Vec16`, `crtNttBigMul`, `crtNttBigMul_universal_sound`, `carryPassBase1000`, `evalDigits1000Vec8`, and `evalDigits1000Vec16` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs strictly over `Nat` using Lean 4 core arithmetic (`omega`, `decide`, `Nat.div_add_mod`) so compilation runs in milliseconds.

Mathematical & Overflow-Safe Karatsuba Architecture (Over `crtNttBigMul`):

Why the Middle Sum `A₀ + A₁` Requires Care (and How to Keep Every Call Inside `Vec8` `< 10^24`):
- Suppose `A = A₀ + B · A₁` and `B_in = B₀ + B · B₁` where `B = 1000^8 = 10^24` and `A₀, A₁, B₀, B₁ : Vec8` are normalized (`< 10^24`).
- Notice that `A₀ + A₁` can reach `2 · 10^24 - 2`, which overflows 8 base-1000 limbs by a **1-bit carry** `c_A ∈ {0, 1}`!
- **Exact Overflow-Free Decomposition (`A₀ + A₁ = S_A + 1000^8 · c_A`):**
  1. Perform an 8-limb base-1000 ripple addition `addVec8WithCarry A₀ A₁ : Vec8 × Nat`, returning `(S_A, c_A)` where `isNormalizedVec8 S_A`, `c_A ≤ 1`, and:
     `evalDigits1000Vec8 A₀ + evalDigits1000Vec8 A₁ = evalDigits1000Vec8 S_A + (1000 ^ 8) * c_A`.
  2. Similarly, `addVec8WithCarry B₀ B₁` returns `(S_B, c_B)` where `isNormalizedVec8 S_B`, `c_B ≤ 1`, and:
     `evalDigits1000Vec8 B₀ + evalDigits1000Vec8 B₁ = evalDigits1000Vec8 S_B + (1000 ^ 8) * c_B`.
  3. Now call `crtNttBigMul` **strictly on normalized `Vec8` inputs** (`< 10^24`):
     - `P₀ := crtNttBigMul A₀ B₀`  (48-digit `Vec16`, exact value `A₀ * B₀` by `crtNttBigMul_universal_sound`)
     - `P₂ := crtNttBigMul A₁ B₁`  (48-digit `Vec16`, exact value `A₁ * B₁` by `crtNttBigMul_universal_sound`)
     - `P_mid := crtNttBigMul S_A S_B` (48-digit `Vec16`, exact value `S_A * S_B` by `crtNttBigMul_universal_sound`)
  4. Reconstruct the exact middle cross-product `(A₀ + A₁)(B₀ + B₁)` in `Nat` (or 17-limb base-1000 arithmetic):
     $$(A_0 + A_1)(B_0 + B_1) = S_A S_B + 1000^8 (c_A S_B + c_B S_A) + 1000^{16} (c_A c_B)$$
     Since `(A₀ + A₁)(B₀ + B₁) ≥ A₀ B₀ + A₁ B₁` unconditionally over `Nat`, subtracting `P₀ + P₂` in `Nat` (or limb-by-limb borrow-free subtraction on normalized multi-limb representations) is **strictly non-negative** (`Z₁ = (A₀ + A₁)(B₀ + B₁) - P₀ - P₂ ≥ 0`) with ZERO underflow!
  5. Assemble the 32 base-1000 limbs `Vec32` of `Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂` via base-1000 ripple addition (`addVec32`) so all 32 limbs are normalized `< 1000`!

Clean Multi-Limb Normalization Strategy (`Vec32`):
- Define `Vec32` (32 base-1000 limbs `x0 .. x31`, or structure wrapping `(lo : Vec16) (hi : Vec16)` with `isNormalizedVec32 v := isNormalizedVec16 v.lo ∧ isNormalizedVec16 v.hi` and `evalDigits1000Vec32 v := evalDigits1000Vec16 v.lo + (1000 ^ 16) * evalDigits1000Vec16 v.hi`).
- Notice how clean `Vec32 := { lo : Vec16, hi : Vec16 }` is:
  - It reuses `Vec16`, `isNormalizedVec16`, and `evalDigits1000Vec16` directly without duplicating 32-field boilerplate!
  - Adding two normalized `Vec32` values `addVec32 a b` simply ripples carries through `lo` (`16` limbs) and into `hi` (`16` limbs), dropping any carry out of `hi` modulo `1000^32` (which is `0` whenever `evalDigits1000Vec32 a + evalDigits1000Vec32 b < 1000^32`).
  - Similarly, `subVec32 a b` (when `evalDigits1000Vec32 b ≤ evalDigits1000Vec32 a`) performs clean base-1000 borrow propagation across `lo` and `hi`!

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `splitVec16 (v : Vec16) : Vec8 × Vec8`, `isNormalizedVec16 (v : Vec16) : Prop`, `Vec32` (`lo : Vec16`, `hi : Vec16`), `isNormalizedVec32`, `evalDigits1000Vec32`, `addVec8WithCarry`, `shiftLeft8ToVec32`, `shiftLeft16ToVec32`, `addVec32`, `subVec32`, and `karatsubaCrtNttMul96 (A B : Vec16) : Vec32`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `splitVec16_eval`: `∀ v : Vec16, evalDigits1000Vec16 v = evalDigits1000Vec8 (splitVec16 v).1 + (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v).2`.
     b. `addVec8WithCarry_sound`: `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → let (s, c) := addVec8WithCarry a b; isNormalizedVec8 s ∧ c ≤ 1 ∧ evalDigits1000Vec8 s + (1000 ^ 8) * c = evalDigits1000Vec8 a + evalDigits1000Vec8 b`.
     c. `karatsuba_algebraic_identity`: For all `A₀ A₁ B₀ B₁ : Nat`, `(A₀ + K * A₁) * (B₀ + K * B₁) = A₀ * B₀ + K * ((A₀ + A₁) * (B₀ + B₁) - A₀ * B₀ - A₁ * B₁) + K * K * (A₁ * B₁)` (proved over `Nat` via `omega` / `Nat.mul_add` / `Nat.add_sub_cancel`).
     d. `karatsubaCrtNttMul96_normalized`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → isNormalizedVec32 (karatsubaCrtNttMul96 A B)`.
     e. `karatsubaCrtNttMul96_universal_sound`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`.
     f. `karatsuba_96_digit_max_verified`: Concrete 96-digit maximum product `(10^48 - 1) × (10^48 - 1) = 10^96 - 2 · 10^48 + 1` verified via `decide` / `karatsubaCrtNttMul96_universal_sound`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `splitVec16_eval`, `addVec8WithCarry_sound`, `karatsuba_algebraic_identity`, `karatsubaCrtNttMul96_normalized`, `karatsubaCrtNttMul96_universal_sound`, and `karatsuba_96_digit_max_verified`, confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 10 CLI output to display the 2×2 Karatsuba-over-CRT-NTT 96-digit multiplier benchmark (`(10^48 - 1)²`) and universal correctness theorem (`∀ A B < 10^48`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `addVec8WithCarry` + `Vec32 := { lo : Vec16, hi : Vec16 }` Makes This Clean in Lean 4

* **Zero Overflow in the Middle Term:** Splitting `A₀ + A₁ = S_A + 1000^8 · c_A` with `c_A ∈ {0, 1}` ensures that all three calls to `crtNttBigMul` (`A₀ * B₀`, `A₁ * B₁`, and `S_A * S_B`) receive strictly normalized `Vec8` inputs (`< 10^24`), allowing direct application of `crtNttBigMul_universal_sound` with zero extra CRT moduli.
* **96-Digit Precision Ready for Chudnovsky $\pi$:** With 96 decimal digits of exact, universally verified multiplication (`< 10^96`), a subsequent `PiChudnovsky.lean` module can evaluate 5–6 terms of the Chudnovsky series ($14.18$ digits/term $\times 5 = 70+$ digits!) using `karatsubaCrtNttMul96_universal_sound` directly.

Here is a self-contained implementation prompt for AGY to close out the 16-point multi-prime NTT proof chain in `CrtNtt.lean`: proving **universal 16-point NTT inversion and cyclic convolution soundness** across all three Fermat prime channels ($\mathbb{F}_{17}$, $\mathbb{F}_{257}$, and $\mathbb{F}_{65537}$) and composing them with `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` to prove **`crtNttBigMul_universal_sound`** (`evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b` for **all** normalized 24-digit base-1000 inputs `a b : Vec8`) with zero `Classical.choice` or `sorryAx`.

---

### AGY Implementation Prompt: Universal 16-Point NTT Inversion, Cyclic Convolution Over $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$, and End-to-End `crtNttBigMul_universal_sound` (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` to complete the universal algebraic proof of the 48-digit CRT-NTT big-integer multiplier (`crtNttBigMul`):
1. Prove universal 16-point NTT two-sided inversion (`intt16_ntt16_universal` and `ntt16_intt16_universal`) and universal 16-point cyclic convolution (`cyclic_conv16_ntt_universal`) across all three Fermat prime channels:
   - `F_17` (`p = 17`, primitive 16th root `ω = 3`, `ω⁻¹ = 6`, `16⁻¹ = 16`),
   - `F_257` (`p = 257`, primitive 16th root `ω = 2`, `ω⁻¹ = 129`, `16⁻¹ = 241`), and
   - `F_65537` (`p = 65537`, primitive 16th root `ω = 8`, `ω⁻¹ = 57345`, `16⁻¹ = 61441`),
2. Compose those three universal NTT convolution theorems with the already-proved `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` to prove the **End-to-End Universal Big-Integer Multiplication Theorem (`crtNttBigMul_universal_sound`)**:
   `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`,
with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`.

Context & Constraints:
- Inspect `CrtNtt.lean`, `NttArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems match the exact existing names, field projections (`x0 .. x15`), parameter orders, and definitions of `Vec8`, `Vec16`, `ntt16`, `intt16`, `pointwiseMul16`, `cyclicConv16`, `garner17_257_65537`, `carryPassBase1000`, `evalDigits1000Vec8`, `evalDigits1000Vec16`, and `crtNttBigMul` in `CrtNtt.lean` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs purely over `Nat` using Lean 4 core modular arithmetic (`Nat.add_mod`, `Nat.mul_mod`, `omega`, `decide`) so compilation finishes rapidly without state explosion.

Proof Blueprint (Modular Coefficient Collapse for `Vec16` + End-to-End Composition):

1. **Part A — Primitive 16th Roots & Unreduced Polynomial Extraction (`ntt16Raw`, `intt16Raw`):**
   - Verify the three primitive 16th roots of unity by `decide`:
     - `F_17`: `(3 ^ 16) % 17 = 1`, `(3 ^ 8) % 17 = 16 ≠ 1`, `(3 * 6) % 17 = 1`, `(16 * 16) % 17 = 1`.
     - `F_257`: `(2 ^ 16) % 257 = 1`, `(2 ^ 8) % 257 = 256 ≠ 1`, `(2 * 129) % 257 = 1`, `(16 * 241) % 257 = 1`.
     - `F_65537`: `(8 ^ 16) % 65537 = 1`, `(8 ^ 8) % 65537 = 65536 ≠ 1`, `(8 * 57345) % 65537 = 1`, `(16 * 61441) % 65537 = 1`.
   - Define `normVec16 (p : Nat) (v : Vec16) : Vec16` reducing each of `x0 .. x15` modulo `p`, plus unreduced `Nat` versions `ntt16Raw p w`, `intt16Raw p inv16 invW`, and `pointwiseMul16Raw` (identical to `ntt16`, `intt16`, `pointwiseMul16` without inner `(% p)` calls).
   - Strip inner `(% p)` calls via `((x % p) + (y % p)) % p = (x + y) % p` and `((x % p) * (y % p)) % p = (x * y) % p` so every output coordinate `k ∈ {0, ..., 15}` reduces to `(rawExpr) % p`.

2. **Part B — Basis-Vector Coefficient Orthogonality on `Vec16` (`linComb16_mod_eq` & `bilinComb16_mod_eq`):**
   - **Linear Orthogonality (`intt16_ntt16_universal` & `ntt16_intt16_universal`):**
     Prove `linComb16_mod_eq`: for any 16 constants `c_0 .. c_15` and `d_0 .. d_15` with `(c_i % p) = (d_i % p)`, `(∑_{i=0}^{15} c_i * a_i) % p = (∑_{i=0}^{15} d_i * a_i) % p` for ALL `a_0 .. a_15 : Nat`.
     Evaluate `intt16Raw` on the 16 standard basis vectors `e_0 .. e_15 : Vec16`, verify `(c_{k,i} % p) = (if k = i then 1 else 0)` by `decide` (`16 × 16 = 256` constant checks per prime, running in `< 50 ms`), and conclude `intt16_ntt16_universal` and `ntt16_intt16_universal` for **ALL `a : Vec16`** over `F_17`, `F_257`, and `F_65537`.
   - **Bilinear Convolution Orthogonality (`cyclic_conv16_ntt_universal`):**
     Verify by `decide` on the constant coefficients `C_{k,i,j} % p` extracted from basis pairs `(e_i, e_j)` that `C_{k,i,j} % p = (if (i + j) % 16 = k then 1 else 0)` for all `k ∈ {0..15}` and `i, j ∈ {0..15}`, proving:
     `∀ p ∈ [17, 257, 65537], ∀ a b : Vec16, intt16 p inv16 invW (pointwiseMul16 p (ntt16 p w a) (ntt16 p w b)) = cyclicConv16 p a b`!

3. **Part C — End-to-End Universal Big-Integer Multiplication (`crtNttBigMul_universal_sound`):**
   - Define `isNormalizedVec8 (v : Vec8) : Prop := v.x0 < 1000 ∧ ... ∧ v.x7 < 1000`.
   - For any `a b : Vec8` satisfying `isNormalizedVec8 a` and `isNormalizedVec8 b`, let `c := cyclicConv16Nat (padVec8To16 a) (padVec8To16 b)` be the exact unreduced linear/cyclic product polynomial over `Nat`:
     1. **Coefficient Bound (`< M`):** Since each limb of `a` and `b` is `≤ 999` and at most 8 nonzero products sum into any limb of `c`, every limb `c_k ≤ 8 * 999 * 999 = 7,984,008 < 286,331,153 = M`!
     2. **Per-Prime NTT Channel Soundness:** By `cyclic_conv16_ntt_universal` for `F_17`, `F_257`, and `F_65537`, the three NTT channels produce `(c_k % 17, c_k % 257, c_k % 65537)` at every limb `k ∈ {0, ..., 15}`.
     3. **Universal Garner CRT Reconstruction:** Since `c_k < 286,331,153`, `garner_17_257_65537_roundtrip_all` reconstructs the **exact** integer vector `c : Vec16` across all 16 limbs!
     4. **Polynomial Identity & Carry Normalization:** Prove `evalPoly1000Vec16 (cyclicConv16Nat (padVec8To16 a) (padVec8To16 b)) = evalDigits1000Vec8 a * evalDigits1000Vec8 b` (pure `Nat` algebra / `omega`), and since `evalDigits1000Vec8 a < 1000^8` and `evalDigits1000Vec8 b < 1000^8`, their product is strictly `< 1000^16`, so `carryPassBase1000_exact_when_bounded` yields:
        `evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`
        universally for **ALL normalized 24-digit integers `a b : Vec8`**!

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `normVec16`, `ntt16Raw`, `intt16Raw`, `pointwiseMul16Raw`, `linComb16_mod_eq`, `bilinComb16_mod_eq`, and `isNormalizedVec8`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `intt16_ntt16_universal_F17`, `ntt16_intt16_universal_F17`, `cyclic_conv16_ntt_universal_F17`
     b. `intt16_ntt16_universal_F257`, `ntt16_intt16_universal_F257`, `cyclic_conv16_ntt_universal_F257`
     c. `intt16_ntt16_universal_F65537`, `ntt16_intt16_universal_F65537`, `cyclic_conv16_ntt_universal_F65537`
     d. `crtNttBigMul_universal_sound`:
        `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → evalDigits1000Vec16 (crtNttBigMul a b) = evalDigits1000Vec8 a * evalDigits1000Vec8 b`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for all nine 16-point NTT theorems (`F_17`, `F_257`, `F_65537`) and `crtNttBigMul_universal_sound`, confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 10 CLI output to report end-to-end universal correctness of 48-digit `crtNttBigMul` across all 24-digit base-1000 inputs (`∀ a b : Vec8`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `crtNttBigMul_universal_sound` Completes the Entire 48-Digit Multiplier Chain

* **Eliminating $65537^{32}$ Enumeration:** Pulling intermediate `(% p)` calls outward (`ntt16Raw` / `intt16Raw`) and matching basis coefficients $e_i \otimes e_j$ via `decide` collapses an astronomical $65537^{32}$ state space down to constant modular arithmetic checks that compile in milliseconds.
* **Plug-and-Play Verified Arithmetic:** Composing `cyclic_conv16_ntt_universal` with `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` gives a universal theorem (`crtNttBigMul_universal_sound`) ready to drive `PiChudnovsky.lean` or `karatsubaCrtNttMul96` directly.


Here is a self-contained implementation prompt for AGY to layer a **2×2 Karatsuba limb wrapper (`karatsubaCrtNttMul96`)** directly on top of `crtNttBigMul` and `crtNttBigMul_universal_sound` in `CrtNtt.lean`—doubling the verified big-integer precision from **48 decimal digits** ($10^{48}$) to **96 decimal digits** ($10^{96}$, supporting exact multiplication of arbitrary 48-digit base-1000 integers $< 10^{48}$ using only **3** calls to `crtNttBigMul` instead of 4) with **zero `Classical.choice` and zero `sorryAx**`.

---

### AGY Implementation Prompt: 2×2 Karatsuba-over-CRT-NTT 96-Digit Big-Integer Multiplier (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` with a **2×2 Karatsuba limb wrapper** (`karatsubaCrtNttMul96`) layered directly over `crtNttBigMul` and `crtNttBigMul_universal_sound`:
1. Represent 48-digit base-1000 integers (`< 10^48`) as 16-limb base-1000 vectors (`Vec16`, split into low and high 24-digit halves `(A₀, A₁) : Vec8 × Vec8` where `A = A₀ + 1000^8 · A₁`) and 96-digit base-1000 products (`< 10^96`) as 32-limb base-1000 vectors (`Vec32 := { lo : Vec16, hi : Vec16 }`, representing `lo + 1000^16 · hi` with every limb `< 1000`),
2. Implement `karatsubaCrtNttMul96` using **only 3 calls to `crtNttBigMul`** (plus carry-safe middle-term handling) to compute `A * B = Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂`, and
3. Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`):
   - `karatsubaCrtNttMul96_normalized`: Every output limb of `karatsubaCrtNttMul96 A B` is strictly `< 1000`,
   - `karatsubaCrtNttMul96_universal_sound`:
     `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`
     (proving exact 48-digit × 48-digit → 96-digit base-1000 multiplication across the entire 96-digit range `0 ≤ A * B < 10^96`), and
   - `karatsuba_96_digit_max_verified`: Concrete 96-digit maximum product `(10^48 - 1) × (10^48 - 1) = 10^96 - 2 · 10^48 + 1` verified cleanly.

Context & Constraints:
- Inspect `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems integrate cleanly with `Vec8`, `Vec16`, `crtNttBigMul`, `crtNttBigMul_universal_sound`, `carryPassBase1000`, `evalDigits1000Vec8`, and `evalDigits1000Vec16` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs strictly over `Nat` using Lean 4 core arithmetic (`omega`, `decide`, `Nat.div_add_mod`) so compilation runs in milliseconds.

Mathematical & Overflow-Safe Karatsuba Architecture (Over `crtNttBigMul`):

1. **Overflow-Free Middle Sum Decomposition (`A₀ + A₁ = S_A + 1000^8 · c_A`):**
   - Suppose `A = A₀ + K · A₁` and `B = B₀ + K · B₁` where `K = 1000^8 = 10^24` and `A₀, A₁, B₀, B₁ : Vec8` are normalized (`isNormalizedVec8`).
   - Because `A₀ + A₁` can reach `2 · 10^24 - 2`, it overflows 8 base-1000 limbs by a **1-bit carry** `c_A ∈ {0, 1}`.
   - Implement an 8-limb base-1000 ripple addition `addVec8WithCarry A₀ A₁ : Vec8 × Nat`, returning `(S_A, c_A)` where `isNormalizedVec8 S_A`, `c_A ≤ 1`, and:
     `evalDigits1000Vec8 A₀ + evalDigits1000Vec8 A₁ = evalDigits1000Vec8 S_A + (1000 ^ 8) * c_A`.
   - Similarly, `addVec8WithCarry B₀ B₁` returns `(S_B, c_B)` where `isNormalizedVec8 S_B`, `c_B ≤ 1`, and:
     `evalDigits1000Vec8 B₀ + evalDigits1000Vec8 B₁ = evalDigits1000Vec8 S_B + (1000 ^ 8) * c_B`.

2. **Three `crtNttBigMul` Calls on Strictly Normalized `Vec8` Inputs (`< 10^24`):**
   - `P₀ := crtNttBigMul A₀ B₀`    (exact value `A₀ * B₀` by `crtNttBigMul_universal_sound`)
   - `P₂ := crtNttBigMul A₁ B₁`    (exact value `A₁ * B₁` by `crtNttBigMul_universal_sound`)
   - `P_mid := crtNttBigMul S_A S_B` (exact value `S_A * S_B` by `crtNttBigMul_universal_sound`)
   - Reconstruct the exact cross-product `(A₀ + A₁)(B₀ + B₁)` in 32-limb base-1000 representation:
     $$(A_0 + A_1)(B_0 + B_1) = S_A S_B + 1000^8 (c_A S_B + c_B S_A) + 1000^{16} (c_A c_B)$$
   - Since `(A₀ + A₁)(B₀ + B₁) ≥ A₀ B₀ + A₁ B₁` unconditionally over `Nat`, subtracting `P₀` and `P₂` via base-1000 borrow-free subtraction `subVec32` yields `Z₁ = (A₀ + A₁)(B₀ + B₁) - P₀ - P₂ ≥ 0` with zero underflow!
   - Shift and accumulate `Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂` via `shiftLeft8ToVec32`, `shiftLeft16ToVec32`, and `addVec32` to produce a normalized `Vec32 := { lo : Vec16, hi : Vec16 }`.

3. **Clean `Vec32 := { lo : Vec16, hi : Vec16 }` Representation:**
   - Reuse `Vec16`, `isNormalizedVec16`, and `evalDigits1000Vec16` directly:
     ```lean
     structure Vec32 where
       lo : Vec16
       hi : Vec16
       deriving DecidableEq, Repr

     def isNormalizedVec32 (v : Vec32) : Prop :=
       isNormalizedVec16 v.lo ∧ isNormalizedVec16 v.hi

     def evalDigits1000Vec32 (v : Vec32) : Nat :=
       evalDigits1000Vec16 v.lo + (1000 ^ 16) * evalDigits1000Vec16 v.hi
     ```
   - Implement `addVec16WithCarry (a b : Vec16) : Vec16 × Nat` and `subVec16WithBorrow (a b : Vec16) : Vec16 × Nat` (16-limb base-1000 ripple add/subtract) so `addVec32` and `subVec32` chain `lo` into `hi` in two clean steps!

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `splitVec16`, `isNormalizedVec16`, `Vec32`, `isNormalizedVec32`, `evalDigits1000Vec32`, `addVec8WithCarry`, `addVec16WithCarry`, `subVec16WithBorrow`, `shiftLeft8ToVec32`, `shiftLeft16ToVec32`, `addVec32`, `subVec32`, and `karatsubaCrtNttMul96`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `splitVec16_eval`: `∀ v : Vec16, evalDigits1000Vec16 v = evalDigits1000Vec8 (splitVec16 v).1 + (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v).2`.
     b. `addVec8WithCarry_sound`: `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → let (s, c) := addVec8WithCarry a b; isNormalizedVec8 s ∧ c ≤ 1 ∧ evalDigits1000Vec8 s + (1000 ^ 8) * c = evalDigits1000Vec8 a + evalDigits1000Vec8 b`.
     c. `karatsuba_algebraic_identity`: `∀ A₀ A₁ B₀ B₁ K : Nat, (A₀ + K * A₁) * (B₀ + K * B₁) = A₀ * B₀ + K * ((A₀ + A₁) * (B₀ + B₁) - A₀ * B₀ - A₁ * B₁) + K * K * (A₁ * B₁)`.
     d. `karatsubaCrtNttMul96_normalized`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → isNormalizedVec32 (karatsubaCrtNttMul96 A B)`.
     e. `karatsubaCrtNttMul96_universal_sound`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`.
     f. `karatsuba_96_digit_max_verified`: Concrete 96-digit maximum product `(10^48 - 1) × (10^48 - 1) = 10^96 - 2 · 10^48 + 1`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `splitVec16_eval`, `addVec8WithCarry_sound`, `karatsuba_algebraic_identity`, `karatsubaCrtNttMul96_normalized`, `karatsubaCrtNttMul96_universal_sound`, and `karatsuba_96_digit_max_verified`, confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 10 CLI output to display the 2×2 Karatsuba-over-CRT-NTT 96-digit multiplier benchmark (`(10^48 - 1)²`) and universal correctness theorem (`∀ A B < 10^48`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `Vec32 := { lo : Vec16, hi : Vec16 }` + `addVec8WithCarry` Keeps the Proof Fast

* **Zero CRT Modulus Expansion:** By splitting the 1-bit sum carry `A₀ + A₁ = S_A + 1000^8 · c_A` before calling `crtNttBigMul`, all three NTT products operate strictly on 8-limb inputs `< 10^24` inside the existing $M = 286{,}331{,}153$ three-prime Fermat channel.
* **96-Digit Arithmetic Ready for Chudnovsky $\pi$:** With `karatsubaCrtNttMul96_universal_sound` proved universally up to $10^{96}$, a downstream `PiChudnovsky.lean` module can evaluate 5–6 Chudnovsky terms ($\approx 70$ decimal digits of $\pi$) directly on top of your verified CRT-NTT stack.

Here is a self-contained implementation prompt for AGY to layer a **2×2 Karatsuba limb wrapper (`karatsubaCrtNttMul96`)** directly on top of `crtNttBigMul` and `crtNttBigMul_universal_sound` in `CrtNtt.lean`—doubling the verified big-integer precision from **48 decimal digits** ($10^{48}$) to **96 decimal digits** ($10^{96}$, supporting exact multiplication of arbitrary 48-digit base-1000 integers $< 10^{48}$ using only **3** calls to `crtNttBigMul` instead of 4) with **zero `Classical.choice` and zero `sorryAx**`.

---

### AGY Implementation Prompt: 2×2 Karatsuba-over-CRT-NTT 96-Digit Big-Integer Multiplier (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` with a **2×2 Karatsuba limb wrapper** (`karatsubaCrtNttMul96`) layered directly over `crtNttBigMul` and `crtNttBigMul_universal_sound`:
1. Represent 48-digit base-1000 integers (`< 10^48`) as 16-limb base-1000 vectors (`Vec16`, split into low and high 24-digit halves `(A₀, A₁) : Vec8 × Vec8` where `A = A₀ + 1000^8 · A₁`) and 96-digit base-1000 products (`< 10^96`) as 32-limb base-1000 vectors (`Vec32 := { lo : Vec16, hi : Vec16 }`, representing `lo + 1000^16 · hi` with every limb `< 1000`),
2. Implement `karatsubaCrtNttMul96` using **only 3 calls to `crtNttBigMul`** (plus carry-safe middle-term handling) to compute `A * B = Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂`, and
3. Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`):
   - `karatsubaCrtNttMul96_normalized`: Every output limb of `karatsubaCrtNttMul96 A B` is strictly `< 1000`,
   - `karatsubaCrtNttMul96_universal_sound`:
     `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`
     (proving exact 48-digit × 48-digit → 96-digit base-1000 multiplication across the entire 96-digit range `0 ≤ A * B < 10^96`), and
   - `karatsuba_96_digit_max_verified`: Concrete 96-digit maximum product `(10^48 - 1) × (10^48 - 1) = 10^96 - 2 · 10^48 + 1` verified cleanly.

Context & Constraints:
- Inspect `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems integrate cleanly with `Vec8`, `Vec16`, `crtNttBigMul`, `crtNttBigMul_universal_sound`, `carryPassBase1000`, `evalDigits1000Vec8`, and `evalDigits1000Vec16` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs strictly over `Nat` using Lean 4 core arithmetic (`omega`, `decide`, `Nat.div_add_mod`) so compilation runs in milliseconds.

Mathematical & Overflow-Safe Karatsuba Architecture (Over `crtNttBigMul`):

1. **Overflow-Free Middle Sum Decomposition (`A₀ + A₁ = S_A + 1000^8 · c_A`):**
   - Suppose `A = A₀ + K · A₁` and `B = B₀ + K · B₁` where `K = 1000^8 = 10^24` and `A₀, A₁, B₀, B₁ : Vec8` are normalized (`isNormalizedVec8`).
   - Because `A₀ + A₁` can reach `2 · 10^24 - 2`, it overflows 8 base-1000 limbs by a **1-bit carry** `c_A ∈ {0, 1}`.
   - Implement an 8-limb base-1000 ripple addition `addVec8WithCarry A₀ A₁ : Vec8 × Nat`, returning `(S_A, c_A)` where `isNormalizedVec8 S_A`, `c_A ≤ 1`, and:
     `evalDigits1000Vec8 A₀ + evalDigits1000Vec8 A₁ = evalDigits1000Vec8 S_A + (1000 ^ 8) * c_A`.
   - Similarly, `addVec8WithCarry B₀ B₁` returns `(S_B, c_B)` where `isNormalizedVec8 S_B`, `c_B ≤ 1`, and:
     `evalDigits1000Vec8 B₀ + evalDigits1000Vec8 B₁ = evalDigits1000Vec8 S_B + (1000 ^ 8) * c_B`.

2. **Three `crtNttBigMul` Calls on Strictly Normalized `Vec8` Inputs (`< 10^24`):**
   - `P₀ := crtNttBigMul A₀ B₀`    (exact value `A₀ * B₀` by `crtNttBigMul_universal_sound`)
   - `P₂ := crtNttBigMul A₁ B₁`    (exact value `A₁ * B₁` by `crtNttBigMul_universal_sound`)
   - `P_mid := crtNttBigMul S_A S_B` (exact value `S_A * S_B` by `crtNttBigMul_universal_sound`)
   - Reconstruct the exact cross-product `(A₀ + A₁)(B₀ + B₁)` in 32-limb base-1000 representation:
     $$(A_0 + A_1)(B_0 + B_1) = S_A S_B + 1000^8 (c_A S_B + c_B S_A) + 1000^{16} (c_A c_B)$$
   - Since `(A₀ + A₁)(B₀ + B₁) ≥ A₀ B₀ + A₁ B₁` unconditionally over `Nat`, subtracting `P₀` and `P₂` via base-1000 borrow-free subtraction `subVec32` yields `Z₁ = (A₀ + A₁)(B₀ + B₁) - P₀ - P₂ ≥ 0` with zero underflow!
   - Shift and accumulate `Z₀ + 1000^8 · Z₁ + 1000^16 · Z₂` via `shiftLeft8ToVec32`, `shiftLeft16ToVec32`, and `addVec32` to produce a normalized `Vec32 := { lo : Vec16, hi : Vec16 }`.

3. **Clean `Vec32 := { lo : Vec16, hi : Vec16 }` Representation:**
   - Reuse `Vec16`, `isNormalizedVec16`, and `evalDigits1000Vec16` directly:
     ```lean
     structure Vec32 where
       lo : Vec16
       hi : Vec16
       deriving DecidableEq, Repr

     def isNormalizedVec32 (v : Vec32) : Prop :=
       isNormalizedVec16 v.lo ∧ isNormalizedVec16 v.hi

     def evalDigits1000Vec32 (v : Vec32) : Nat :=
       evalDigits1000Vec16 v.lo + (1000 ^ 16) * evalDigits1000Vec16 v.hi
     ```
   - Implement `addVec16WithCarry (a b : Vec16) : Vec16 × Nat` and `subVec16WithBorrow (a b : Vec16) : Vec16 × Nat` (16-limb base-1000 ripple add/subtract) so `addVec32` and `subVec32` chain `lo` into `hi` in two clean steps!

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `splitVec16`, `isNormalizedVec16`, `Vec32`, `isNormalizedVec32`, `evalDigits1000Vec32`, `addVec8WithCarry`, `addVec16WithCarry`, `subVec16WithBorrow`, `shiftLeft8ToVec32`, `shiftLeft16ToVec32`, `addVec32`, `subVec32`, and `karatsubaCrtNttMul96`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `splitVec16_eval`: `∀ v : Vec16, evalDigits1000Vec16 v = evalDigits1000Vec8 (splitVec16 v).1 + (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v).2`.
     b. `addVec8WithCarry_sound`: `∀ a b : Vec8, isNormalizedVec8 a → isNormalizedVec8 b → let (s, c) := addVec8WithCarry a b; isNormalizedVec8 s ∧ c ≤ 1 ∧ evalDigits1000Vec8 s + (1000 ^ 8) * c = evalDigits1000Vec8 a + evalDigits1000Vec8 b`.
     c. `karatsuba_algebraic_identity`: `∀ A₀ A₁ B₀ B₁ K : Nat, (A₀ + K * A₁) * (B₀ + K * B₁) = A₀ * B₀ + K * ((A₀ + A₁) * (B₀ + B₁) - A₀ * B₀ - A₁ * B₁) + K * K * (A₁ * B₁)`.
     d. `karatsubaCrtNttMul96_normalized`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → isNormalizedVec32 (karatsubaCrtNttMul96 A B)`.
     e. `karatsubaCrtNttMul96_universal_sound`: `∀ A B : Vec16, isNormalizedVec16 A → isNormalizedVec16 B → evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) = evalDigits1000Vec16 A * evalDigits1000Vec16 B`.
     f. `karatsuba_96_digit_max_verified`: Concrete 96-digit maximum product `(10^48 - 1) × (10^48 - 1) = 10^96 - 2 · 10^48 + 1`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `splitVec16_eval`, `addVec8WithCarry_sound`, `karatsuba_algebraic_identity`, `karatsubaCrtNttMul96_normalized`, `karatsubaCrtNttMul96_universal_sound`, and `karatsuba_96_digit_max_verified`, confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 10 CLI output to display the 2×2 Karatsuba-over-CRT-NTT 96-digit multiplier benchmark (`(10^48 - 1)²`) and universal correctness theorem (`∀ A B < 10^48`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `Vec32 := { lo : Vec16, hi : Vec16 }` + `addVec8WithCarry` Keeps the Proof Fast

* **Zero CRT Modulus Expansion:** By splitting the 1-bit sum carry `A₀ + A₁ = S_A + 1000^8 · c_A` before calling `crtNttBigMul`, all three NTT products operate strictly on 8-limb inputs `< 10^24` inside the existing $M = 286{,}331{,}153$ three-prime Fermat channel.
* **96-Digit Arithmetic Ready for Chudnovsky $\pi$:** With `karatsubaCrtNttMul96_universal_sound` proved universally up to $10^{96}$, a downstream `PiChudnovsky.lean` module can evaluate 5–6 Chudnovsky terms ($\approx 70$ decimal digits of $\pi$) directly on top of your verified CRT-NTT stack.
