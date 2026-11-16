Here is a self-contained implementation prompt for AGY to upgrade `NttArithmetic.lean` from sample evaluations to **universal algebraic NTT soundness theorems** over $\mathbb{F}_5$ and $\mathbb{F}_{17}$—proving constructively with zero `Classical.choice` or `sorryAx` that `intt4` is the exact two-sided inverse of `ntt4` (`intt4 (ntt4 a) = normVec4 a`) and that pointwise multiplication in the NTT domain computes exact 4-point cyclic convolution (`intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b`) for **every** `a b : Vec4`.

---

### AGY Implementation Prompt: Universal 4-Point NTT Inversion & Cyclic Convolution Theorem Over $\mathbb{F}_5$ and $\mathbb{F}_{17}$ (`NttArithmetic.lean`)

```text
Task: Extend `NttArithmetic.lean` in `leanasm` with universal algebraic soundness theorems over `F_5` (modulus `p = 5`, primitive 4th root `ω = 2`, `ω⁻¹ = 3`, `4⁻¹ = 4`) and `F_17` (modulus `p = 17`, primitive 4th root `ω = 4`, `ω⁻¹ = 13`, `4⁻¹ = 13`), proving constructively for ALL `a b : Vec4`:
1. `intt4_ntt4_universal_F5` & `intt4_ntt4_universal_F17`:
   `∀ a : Vec4, intt4 p inv4 invW (ntt4 p w a) = normVec4 p a`
   (where `normVec4 p a` reduces each of the 4 coordinates of `a` modulo `p`),
2. `ntt4_intt4_universal_F5` & `ntt4_intt4_universal_F17`:
   `∀ y : Vec4, ntt4 p w (intt4 p inv4 invW y) = normVec4 p y`
   (proving `ntt4` and `intt4` are exact mutual bijections on `(ZMod p)^4`), and
3. `cyclic_conv4_ntt_universal_F5` & `cyclic_conv4_ntt_universal_F17`:
   `∀ a b : Vec4, intt4 p inv4 invW (pointwiseMul4 p (ntt4 p w a) (ntt4 p w b)) = cyclicConv4 p a b`
   (proving the 4-point NTT Convolution Theorem universally over all input vectors `a b : Vec4`),
with ZERO `Classical.choice` and ZERO `sorryAx` in `TestAxioms.lean`.

Context & Constraints:
- Inspect `NttArithmetic.lean`, `RnsArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new universal theorems match the exact existing names, field projections, parameter orders, and definitions of `Vec4`, `ntt4`, `intt4`, `pointwiseMul4`, and `cyclicConv4` in `NttArithmetic.lean` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all proofs purely over `Nat` using Lean 4 core modular arithmetic (`Nat.add_mod`, `Nat.mul_mod`, `omega`, `decide`) so compilation completes in under a second.

Proof Blueprint (Fast Algebraic Expansion Over `Nat` — Do NOT Enumerate `17^8` Cases!):

Why Direct Modular Expansion Beats Exhaustive Enumeration:
- Over `F_5`, `5^4 = 625` (small enough for `decide` on single-vector `ntt4` inversion, though `5^8 = 390,625` is slow for two vectors).
- Over `F_17`, `17^4 = 83,521` and `17^8 = 6,975,757,441` (impossible to enumerate!).
- Instead, normalize each coordinate first via `x % p` (`< p`) and expand the 4-point DFT / cyclic convolution polynomials directly over `Nat`:

1. **Step 1 — Input Congruence (`ntt4_mod_inputs` & `cyclicConv4_mod_inputs`):**
   - Because `ntt4 p w`, `pointwiseMul4 p`, and `cyclicConv4 p` reduce every arithmetic operation modulo `p`, prove first that replacing `a = ⟨a0, a1, a2, a3⟩` with `normVec4 p a = ⟨a0 % p, a1 % p, a2 % p, a3 % p⟩` leaves `ntt4 p w a` and `cyclicConv4 p a b` strictly invariant:
     - `ntt4_normVec4 : ∀ p w (a : Vec4), ntt4 p w (normVec4 p a) = ntt4 p w a`
     - `cyclicConv4_normVec4 : ∀ p (a b : Vec4), cyclicConv4 p (normVec4 p a) (normVec4 p b) = cyclicConv4 p a b`
     *(Discharged directly by `simp only [ntt4, normVec4, ...]; congr 1 <;> omega` or `Nat.add_mod` / `Nat.mul_mod`!)*

2. **Step 2 — Algebraic Identity Over `Nat` Before Modulo `p` (`ntt4_intt4_pre_mod` & `conv4_pre_mod`):**
   - Look at what `intt4 p inv4 invW (ntt4 p w a)` computes on each coordinate `k ∈ {0, 1, 2, 3}` when `a0, a1, a2, a3 < p`:
     Every intermediate `(% p)` inside `ntt4` and `intt4` can be stripped using a helper lemma `mod_add_mod` / `mod_mul_mod` (`((x % p) + (y % p)) % p = (x + y) % p` and `((x % p) * (y % p)) % p = (x * y) % p`) so the entire 2-stage butterfly pipeline simplifies to a **single `(expr) % p`** on each of the 4 output coordinates!
   - Specifically, for `p = 17, w = 4, invW = 13, inv4 = 13`:
     - Coordinate 0 of `intt4 17 13 13 (ntt4 17 4 a)` simplifies modulo `17` to:
       `((13 * (a0 + a1 + a2 + a3)) % 17) = a0 % 17` (since `13 * 4 = 52 = 3 * 17 + 1 ≡ 1 (mod 17)`!).
     - Coordinate 1 simplifies modulo `17` to:
       `((13 * ((a0 + 4*a1 + 16*a2 + 13*a3) + 13*(...))) % 17)`: grouping coefficients of `a0, a1, a2, a3` gives:
       - coeff of `a0`: `13 * (1 + 13 + 16 + 4) = 13 * 34 ≡ 0 (mod 17)`
       - coeff of `a1`: `13 * (1 + 52 + 256 + 52) = 13 * 361 = 13 * (21*17 + 4) = 52 + 13*21*17 ≡ 1 (mod 17)`
       - coeff of `a2`: `13 * (1 + 208 + 4096 + 676) ≡ 0 (mod 17)`
       - coeff of `a3`: `13 * (1 + 832 + 65536 + 8788) ≡ 0 (mod 17)`!
     - Because `Nat` addition/multiplication is associative and commutative (`ac_rfl` / `omega` / `ring`-style rewrites), rewriting each coordinate of `intt4 p inv4 invW (ntt4 p w a)` into `(c0 * a0 + c1 * a1 + c2 * a2 + c3 * a3) % p` and applying `(c0 % p) = 1, (c1 % p) = 0, (c2 % p) = 0, (c3 % p) = 0` (verified by `decide` on the 4 constant coefficients!) proves `intt4_ntt4_universal_F17` for **ALL `a : Vec4` in `< 50 ms`**!
   - **Exact Same 4-Coefficient Trick for `cyclic_conv4_ntt_universal_F5` and `cyclic_conv4_ntt_universal_F17`:**
     - Strip inner `(% p)` operations inside `intt4 p inv4 invW (pointwiseMul4 p (ntt4 p w a) (ntt4 p w b))` so each of the 4 output coordinates becomes a bilinear sum:
       `(\sum_{i=0}^3 \sum_{j=0}^3 C_{k,i,j} * a_i * b_j) % p`
     - Verify by `decide` on the 16 concrete constant coefficients `C_{k,i,j} % p` that `C_{k,i,j} % p = 1` when `(i + j) % 4 = k` and `0` otherwise!
     - Conclude immediately that each coordinate equals the exact cyclic convolution coordinate `(a0*b_k + a1*b_{(k-1)%4} + a2*b_{(k-2)%4} + a3*b_{(k-3)%4}) % p` for **ALL `a b : Vec4`**!

Deliverables:

1. Extend `NttArithmetic.lean`:
   - Implement `normVec4 (p : Nat) (v : Vec4) : Vec4` (`⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p⟩`) and the modular congruence lemmas (`ntt4_normVec4`, `intt4_normVec4`, `cyclicConv4_normVec4`).
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `intt4_ntt4_universal_F5`: `∀ a : Vec4, intt4 5 4 3 (ntt4 5 2 a) = normVec4 5 a`.
     b. `ntt4_intt4_universal_F5`: `∀ y : Vec4, ntt4 5 2 (intt4 5 4 3 y) = normVec4 5 y`.
     c. `cyclic_conv4_ntt_universal_F5`: `∀ a b : Vec4, intt4 5 4 3 (pointwiseMul4 5 (ntt4 5 2 a) (ntt4 5 2 b)) = cyclicConv4 5 a b`.
     d. `intt4_ntt4_universal_F17`: `∀ a : Vec4, intt4 17 13 13 (ntt4 17 4 a) = normVec4 17 a`.
     e. `ntt4_intt4_universal_F17`: `∀ y : Vec4, ntt4 17 4 (intt4 17 13 13 y) = normVec4 17 y`.
     f. `cyclic_conv4_ntt_universal_F17`: `∀ a b : Vec4, intt4 17 13 13 (pointwiseMul4 17 (ntt4 17 4 a) (ntt4 17 4 b)) = cyclicConv4 17 a b`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for all six universal theorems (`intt4_ntt4_universal_F5`, `ntt4_intt4_universal_F5`, `cyclic_conv4_ntt_universal_F5`, `intt4_ntt4_universal_F17`, `ntt4_intt4_universal_F17`, `cyclic_conv4_ntt_universal_F17`), confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 8 / Part 9 CLI output to report universal 4-point NTT inversion and cyclic convolution soundness over $\mathbb{F}_5$ and $\mathbb{F}_{17}$ (`∀ a b : Vec4`).
   - Check column width limits (`≤ 120` characters across all modified files) and run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why Coefficient-Level Modular Reduction Solves `17^8` Instantly

* **Eliminating Combinatorial Explosion:** Checking all pairs `(a, b) : Vec4 × Vec4` over $\mathbb{F}_{17}$ has $17^8 \approx 6.97 \times 10^9$ states. Pulling all inner `(% p)` operations out to a single outer `(% p)` reduces the entire proof to checking **16 fixed constant coefficients** `C_{k,i,j} % p` by `decide`, which Lean 4 reduces in milliseconds for arbitrary `a b : Vec4`.
* **Completes the Universal CRT-NTT Chain:** Together with `garner_17_257_65537_roundtrip_all` and `carryPassBase1000_exact_when_bounded` (merged in `8d52a38`), universal `cyclic_conv4_ntt_universal` closes the algebraic foundation of the CRT-NTT multiplier pipeline.
