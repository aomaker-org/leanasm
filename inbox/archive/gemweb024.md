Here is a self-contained implementation prompt for AGY to extend `NttArithmetic.lean` in `leanasm` from a 2-point butterfly to a full 4-point radix-2 Cooley–Tukey NTT over $\mathbb{F}_{17}$ and prove the Cyclic Convolution Theorem with zero axioms.

---

### AGY Implementation Prompt: 4-Point Radix-2 Cooley–Tukey NTT & Cyclic Convolution Theorem (`NttArithmetic.lean`)

```text
Task: Extend `NttArithmetic.lean` in `leanasm` from the existing 2-point butterfly (`nttButterfly2` / `inttButterfly2`) to a full 4-point radix-2 decimation-in-time Cooley–Tukey Number Theoretic Transform (`ntt4`) and inverse NTT (`intt4`) over the Fermat prime field `𝔽₁₇` (`p = 17`), and prove the Cyclic Convolution Theorem (`intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b`) constructively with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `NttArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions reuse the existing modulus `p = 17`, modular arithmetic helpers (`mod17`, `add17`, `sub17`, `mul17`), and naming conventions without breaking existing 2-point butterfly theorems (`ntt_roots_of_unity_sound`, `ntt_butterfly2_roundtrip_5_12`, `ntt_butterfly2_sound_all_pairs`).
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Work strictly over `Nat` (with `Fin 17` or `Nat` reduced modulo `17`) so algebraic identities discharge cleanly via `omega`, `decide`, and elementary modular ring lemmas (`Nat.add_mod`, `Nat.mul_mod`, `Nat.mod_mod`).

Mathematical Specification over `𝔽₁₇` (`p = 17`):
1. **Principal 4th Root of Unity & Modular Inverses in `𝔽₁₇`:**
   - Using the primitive root `g = 3` and principal 8th root `ω₈ = 9` (`9^8 ≡ 1 (mod 17)`), the principal 4th root of unity is:
     `ω₄ = ω₈² mod 17 = 81 mod 17 = 13`
     satisfying:
     - `ω₄⁰ = 1`, `ω₄¹ = 13`, `ω₄² = 16 ≡ -1`, `ω₄³ = 4`, `ω₄⁴ = 1 (mod 17)`
     - Orthogonality sum: `1 + ω₄ + ω₄² + ω₄³ = 1 + 13 + 16 + 4 = 34 ≡ 0 (mod 17)`
     - Inverse 4th root: `ω₄⁻¹ = ω₄³ = 4` (`13 * 4 = 52 ≡ 1 (mod 17)`)
     - Transform length scaling inverse: `4⁻¹ ≡ 13 (mod 17)` (`4 * 13 = 52 ≡ 1 (mod 17)`).

2. **4-Vector Representation (`Vec4`):**
   Define a lightweight 4-element tuple or structure over `Nat`:
   ```lean
   structure Vec4 where
     x0 : Nat
     x1 : Nat
     x2 : Nat
     x3 : Nat
     deriving DecidableEq, Repr

```

with canonical reduction `normVec4 (v : Vec4) : Vec4 := ⟨v.x0 % 17, v.x1 % 17, v.x2 % 17, v.x3 % 17⟩` and componentwise Hadamard product:
`pointwiseMul4 (u v : Vec4) : Vec4 := ⟨(u.x0 * v.x0) % 17, (u.x1 * v.x1) % 17, (u.x2 * v.x2) % 17, (u.x3 * v.x3) % 17⟩`.

3. **Radix-2 Cooley–Tukey Forward `ntt4` & Inverse `intt4`:**
* **Stage 1 (Even/Odd Split + 2-Point Butterflies):**
* Even indices `(x0, x2)`: `(e0, e1) = nttButterfly2 x0 x2` (`((x0 + x2) % 17, (x0 + 17 - x2 % 17) % 17)`)
* Odd indices `(x1, x3)`: `(o0, o1) = nttButterfly2 x1 x3` (`((x1 + x3) % 17, (x1 + 17 - x3 % 17) % 17)`)


* **Stage 2 (Twiddle Multiplication by `ω₄⁰ = 1`, `ω₄¹ = 13` + Combine):**
* `t0 = o0 % 17`
* `t1 = (o1 * 13) % 17`
* `X0 = (e0 + t0) % 17`
* `X1 = (e1 + t1) % 17`
* `X2 = (e0 + 17 - t0) % 17`
* `X3 = (e1 + 17 - t1) % 17`
*(Verify that this matches the direct DFT matrix `X_k = ∑_{j=0}^3 x_j · 13^(j*k) mod 17` for all `k ∈ {0, 1, 2, 3}`!)*


* **Inverse `intt4 (X : Vec4) : Vec4`:**
Apply the conjugate twiddle factor `ω₄⁻¹ = 4` in the two-stage butterfly and scale each output lane by `4⁻¹ ≡ 13 (mod 17)`:
* Stage 1: `(u0, u1) = nttButterfly2 X.x0 X.x2`, `(v0, v1) = nttButterfly2 X.x1 X.x3`
* Stage 2 with `ω₄⁻¹ = 4`: `w0 = v0 % 17`, `w1 = (v1 * 4) % 17`
* Combine & scale by `13`:
`x0 = ((u0 + w0) * 13) % 17`
`x1 = ((u1 + w1) * 13) % 17`
`x2 = ((u0 + 17 - w0) * 13) % 17`
`x3 = ((u1 + 17 - w1) * 13) % 17`




4. **4-Point Cyclic Polynomial Convolution (`cyclicConv4`):**
Represents `(a₀ + a₁x + a₂x² + a₃x³) · (b₀ + b₁x + b₂x² + b₃x³) mod (x⁴ - 1, 17)`:
```lean
def cyclicConv4 (a b : Vec4) : Vec4 where
  x0 := (a.x0 * b.x0 + a.x1 * b.x3 + a.x2 * b.x2 + a.x3 * b.x1) % 17
  x1 := (a.x0 * b.x1 + a.x1 * b.x0 + a.x2 * b.x3 + a.x3 * b.x2) % 17
  x2 := (a.x0 * b.x2 + a.x1 * b.x1 + a.x2 * b.x0 + a.x3 * b.x3) % 17
  x3 := (a.x0 * b.x3 + a.x1 * b.x2 + a.x2 * b.x1 + a.x3 * b.x0) % 17

```



Deliverables:

1. Extend `NttArithmetic.lean`:
* Add `Vec4`, `normVec4`, `pointwiseMul4`, `ntt4`, `intt4`, `dft4Direct`, and `cyclicConv4`.
* Prove constructively (with ZERO axioms):
a. `ntt4_fourth_roots_sound`: `13 ^ 4 % 17 = 1 ∧ 13 ^ 2 % 17 = 16 ∧ (1 + 13 + 16 + 4) % 17 = 0 ∧ (13 * 4) % 17 = 1 ∧ (4 * 13) % 17 = 1`.
b. `ntt4_equals_direct_dft`: `∀ (a0 a1 a2 a3 : Fin 17), let v : Vec4 := ⟨a0.val, a1.val, a2.val, a3.val⟩; ntt4 v = dft4Direct v` (proving the fast Cooley–Tukey butterfly matches the $O(N^2)$ DFT definition across all $17^4 = 83{,}521$ vectors in $\mathbb{F}_{17}^4$ via `decide`!).
c. `ntt4_roundtrip_all_vectors`: `∀ (a0 a1 a2 a3 : Fin 17), let v : Vec4 := ⟨a0.val, a1.val, a2.val, a3.val⟩; intt4 (ntt4 v) = v` (proving exact invertibility across all $83{,}521$ vectors in $\mathbb{F}_{17}^4$ via `decide`, or algebraically via `Nat.add_mod` / `Nat.mul_mod` + `omega` if faster at compile time).
d. `ntt4_cyclic_convolution_concrete`: Concrete fast polynomial multiplication over $\mathbb{F}_{17}[x]/(x^4 - 1)$, e.g., `a = ⟨1, 2, 3, 4⟩` and `b = ⟨5, 6, 7, 8⟩`, proving `intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b` (`⟨15, 2, 10, 6⟩`).
e. `ntt4_cyclic_convolution_theorem`: Universal algebraic proof for ALL `a b : Vec4`:
`intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b`
*(Tip: Note that `ntt4 a` only depends on `a.x0 % 17, ..., a.x3 % 17`, so reducing `a` and `b` via `Nat.mod_lt` into `Fin 17` or expanding the modular arithmetic modulo `17` lets `decide` over `Fin 17`—or algebraic expansion—prove the general `∀ a b : Vec4` theorem cleanly with zero axioms! Keep `decide` dimension small if checking pairs: e.g., prove `ntt4_homomorphism_mul : ∀ (a b : Vec4), ntt4 (cyclicConv4 a b) = pointwiseMul4 (ntt4 a) (ntt4 b)` by expanding the four components modulo `17` or checking `Fin 17` linearity + basis convolutions, then compose with `ntt4_roundtrip_all_vectors`!)*


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `ntt4_fourth_roots_sound`, `ntt4_equals_direct_dft`, `ntt4_roundtrip_all_vectors`, `ntt4_cyclic_convolution_concrete`, and `ntt4_cyclic_convolution_theorem`, confirming every theorem prints `does not depend on any axioms`.
* Update Part 9 of `Main.lean` to execute the 4-point radix-2 Cooley–Tukey NTT (`ntt4 ⟨1, 2, 3, 4⟩`), Hadamard pointwise product, and `intt4` cyclic convolution reconstruction (`⟨15, 2, 10, 6⟩`), reporting zero-axiom verification.
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Fast-Compile Proof Tip Included in the Prompt

* **Factoring Convolution via Linearity (`ntt4_homomorphism_mul`):** Enumerating all $17^8 \approx 6.97 \times 10^9$ pairs `(a, b)` directly in `decide` would time out, whereas proving `ntt4_roundtrip_all_vectors` over `Fin 17 × Fin 17 × Fin 17 × Fin 17` ($17^4 = 83{,}521$ states) and proving `ntt4 (cyclicConv4 a b) = pointwiseMul4 (ntt4 a) (ntt4 b)` by algebraic distributivity modulo `17` (or decomposing `b` into the 4 standard basis vectors $1, x, x^2, x^3$) compiles in under a second with zero axioms.

<FollowUp label="Want an AGY prompt to compile the 4-point NTT butterfly onto MiniVM assembly instructions and verify hardware-level NTT execution with zero axioms once this merges?" query="Write a self-contained AGY prompt to compile the radix-2 NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove execution soundness with zero axioms."/>

<ElicitationsGroup message="Choose your next milestone after AGY merges the 4-point NTT & Cyclic Convolution Theorem:">
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the radix-2 NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove execution soundness with zero axioms."/>
  <Elicitation label="Combine RNS + NTT (CRT-NTT) for multi-prime polynomial multiplication" query="Write a self-contained AGY prompt to combine your (7, 11, 13) RNS basis with Fermat-prime NTT arithmetic in leanasm for carry-free CRT-NTT convolution with zero axioms."/>
  <Elicitation label="Audit another openai/math Comparator challenge (Matrix Multiplication or Hadwiger)" query="Show the exact Lean 4 challenge signatures and Comparator commands for the matrix multiplication exponent bound and Hadwiger disproof in openai/math."/>
</ElicitationsGroup>

```
