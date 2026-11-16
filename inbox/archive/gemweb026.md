Here is a self-contained implementation prompt for AGY to create `CrtNtt.lean` in `leanasm`, combining 4-point radix-2 NTTs over the two Fermat primes $\mathbb{F}_5$ ($2^{2^1} + 1$, $\omega_4 = 2$) and $\mathbb{F}_{17}$ ($2^{2^2} + 1$, $\omega_4 = 13$) with word-bounded Garner CRT reconstruction ($M = 5 \times 17 = 85$) to recover the exact unreduced integer cyclic convolution $\langle 1, 2, 3, 4 \rangle \circledast \langle 5, 6, 7, 8 \rangle = \langle 66, 68, 66, 60 \rangle$ with zero axioms.

---

### AGY Implementation Prompt: Multi-Prime CRT-NTT Exact Integer Convolution (`CrtNtt.lean`)

```text
Task: Create `CrtNtt.lean` in `leanasm` combining 4-point radix-2 Cooley–Tukey Number Theoretic Transforms over the two Fermat primes `𝔽₅` (`p₁ = 5`, `ω₄ = 2`) and `𝔽₁₇` (`p₂ = 17`, `ω₄ = 13`) with word-bounded Garner mixed-radix CRT reconstruction (`M = 5 × 17 = 85`) to recover the exact integer cyclic convolution of `a = ⟨1, 2, 3, 4⟩` and `b = ⟨5, 6, 7, 8⟩`:
`crtNttConv4 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ = ⟨66, 68, 66, 60⟩`
with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `NttArithmetic.lean`, `RnsArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so `CrtNtt.lean` reuses existing `Vec4`, `ntt4`, `intt4`, `pointwiseMul4`, and `cyclicConv4` definitions (or cleanly generalizes/pairs with `NttArithmetic.lean`) without breaking any existing theorems.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Keep all arithmetic over `Nat` so every proof discharges cleanly via `decide` and `omega`.

Mathematical Specification (`𝔽₅ × 𝔽₁₇` CRT-NTT over Dynamic Range `M = 85`):
Notice why single-prime NTT over `𝔽₁₇` wrapped around in `NttArithmetic.lean`:
For `a = ⟨1, 2, 3, 4⟩` and `b = ⟨5, 6, 7, 8⟩`, the exact integer cyclic convolution coefficients are:
- `c₀ = 1·5 + 2·8 + 3·7 + 4·6 = 5 + 16 + 21 + 24 = 66`
- `c₁ = 1·6 + 2·5 + 3·8 + 4·7 = 6 + 10 + 24 + 28 = 68`
- `c₂ = 1·7 + 2·6 + 3·5 + 4·8 = 7 + 12 + 15 + 32 = 66`
- `c₃ = 1·8 + 2·7 + 3·6 + 4·5 = 8 + 14 + 18 + 20 = 60`
Over `𝔽₁₇` alone, `⟨66, 68, 66, 60⟩ mod 17 = ⟨15, 0, 15, 9⟩`. By pairing `𝔽₁₇` with the smaller Fermat prime `𝔽₅` (`p₁ = 5 = 2^{2¹} + 1`, where `4 ∣ 5 - 1`), the combined dynamic range `M = 5 × 17 = 85` exceeds the maximum coefficient `68 < 85`, recovering the exact integer coefficients without overflow!

1. **4-Point Radix-2 NTT over `𝔽₅` (`p₁ = 5`):**
   - Principal 4th root of unity in `𝔽₅`: `ω₄ = 2`
     - `2⁰ = 1`, `2¹ = 2`, `2² = 4 ≡ -1`, `2³ = 3`, `2⁴ = 1 (mod 5)`
     - Orthogonality sum: `1 + 2 + 4 + 3 = 10 ≡ 0 (mod 5)`
     - Inverse 4th root: `ω₄⁻¹ = 2³ = 3` (`2 * 3 = 6 ≡ 1 (mod 5)`)
     - Transform length scaling inverse: `4⁻¹ ≡ 4 (mod 5)` (`4 * 4 = 16 ≡ 1 (mod 5)`)
   - Implement 2-point butterfly `nttButterfly2Mod5 (x y : Nat) : Nat × Nat := ((x + y) % 5, (x + 5 - y % 5) % 5)`, 4-point forward `ntt4Mod5 (v : Vec4) : Vec4` (twiddle `ω₄¹ = 2`), pointwise Hadamard product `pointwiseMul4Mod5`, and inverse `intt4Mod5 (X : Vec4) : Vec4` (inverse twiddle `ω₄⁻¹ = 3`, scaling factor `4⁻¹ ≡ 4 (mod 5)`).
   - For `a = ⟨1, 2, 3, 4⟩` and `b = ⟨5, 6, 7, 8⟩`:
     `intt4Mod5 (pointwiseMul4Mod5 (ntt4Mod5 a) (ntt4Mod5 b)) = ⟨1, 3, 1, 0⟩` (`= ⟨66, 68, 66, 60⟩ mod 5`).

2. **Word-Bounded Garner Mixed-Radix CRT Reconstruction (`M = 5 × 17 = 85`):**
   - Since `5⁻¹ mod 17 = 7` (`5 * 7 = 35 ≡ 1 (mod 17)`), given residue pair `(r₅, r₁₇)` with `r₅ < 5` and `r₁₇ < 17`:
     - `v₁ = r₅ % 5`
     - `v₂ = ((r₁₇ % 17 + 17 - v₁) * 7) % 17`
     - `garner5_17 r₅ r₁₇ = v₁ + 5 * v₂`
     *(Notice all intermediate arithmetic stays strictly `< 22 * 7 = 154 < 169`!)*
   - Apply componentwise across `Vec4` channels:
     `garnerVec4_5_17 (u₅ u₁₇ : Vec4) : Vec4`
   - Define the end-to-end CRT-NTT 4-point convolution pipeline:
     ```lean
     def crtNttConv4 (a b : Vec4) : Vec4 :=
       let conv5  := intt4Mod5 (pointwiseMul4Mod5 (ntt4Mod5 a) (ntt4Mod5 b))
       let conv17 := intt4 (pointwiseMul4 (ntt4 a) (ntt4 b))
       garnerVec4_5_17 conv5 conv17
     ```
   - Also define exact unreduced integer cyclic convolution `exactIntCyclicConv4 (a b : Vec4) : Vec4` (without `% 17`) for comparison.

Deliverables:

1. Create `CrtNtt.lean`:
   - Implement `nttButterfly2Mod5`, `ntt4Mod5`, `intt4Mod5`, `pointwiseMul4Mod5`, `garner5_17`, `garnerVec4_5_17`, `crtNttConv4`, and `exactIntCyclicConv4`.
   - Prove constructively (with ZERO axioms):
     a. `ntt4_mod5_roots_sound`: `2 ^ 4 % 5 = 1 ∧ 2 ^ 2 % 5 = 4 ∧ (1 + 2 + 4 + 3) % 5 = 0 ∧ (2 * 3) % 5 = 1 ∧ (4 * 4) % 5 = 1`.
     b. `garner_5_17_inverse_sound`: `(5 * 7) % 17 = 1 ∧ 5 * 17 = 85`.
     c. `garner_5_17_roundtrip_all`: `∀ (x : Fin 85), garner5_17 (x.val % 5) (x.val % 17) = x.val` (exhaustively proves exact CRT reconstruction across the entire dynamic range `0 ≤ x < 85` via `decide`!).
     d. `ntt4_mod5_roundtrip_all`: `∀ (a0 a1 a2 a3 : Fin 5), let v : Vec4 := ⟨a0.val, a1.val, a2.val, a3.val⟩; intt4Mod5 (ntt4Mod5 v) = v` (exhaustively verifies invertibility across all `5^4 = 625` vectors in `𝔽₅⁴` via `decide`!).
     e. `crt_ntt_exact_integer_convolution`:
        `crtNttConv4 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ = exactIntCyclicConv4 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩`
        and `crtNttConv4 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ = ⟨66, 68, 66, 60⟩`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Import `CrtNtt` in `TestAxioms.lean` and `Main.lean` (and `leanasm.lean` root library if applicable).
   - Add `#print axioms` checks in `TestAxioms.lean` for `ntt4_mod5_roots_sound`, `garner_5_17_inverse_sound`, `garner_5_17_roundtrip_all`, `ntt4_mod5_roundtrip_all`, and `crt_ntt_exact_integer_convolution`, confirming every theorem prints `does not depend on any axioms`.
   - Add `[+] Part 10: Multi-Prime CRT-NTT Exact Integer Convolution (𝔽₅ × 𝔽₁₇, M = 85)` to `Main.lean` displaying:
     - `𝔽₅` NTT convolution channel: `⟨1, 3, 1, 0⟩`
     - `𝔽₁₇` NTT convolution channel: `⟨15, 0, 15, 9⟩`
     - Garner CRT-NTT exact integer product: `⟨66, 68, 66, 60⟩` (`< 85` dynamic range, ZERO axioms).
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why `𝔽₅ × 𝔽₁₇` Fits Your Fermat Prime Tower

* **Consecutive Fermat Primes ($F_1 = 5$, $F_2 = 17$):** Both $5 = 2^{2^1} + 1$ and $17 = 2^{2^2} + 1$ come straight from your Fermat prime tower `[3, 5, 17, 257, 65537]` in `EulerFactorNonVanishing.lean`, and both satisfy $4 \mid p_i - 1$, giving exact rational-free 4th roots of unity ($\omega_4 = 2 \pmod 5$ and $\omega_4 = 13 \pmod{17}$).
* **Zero Wrap-Around Proof (`garner_5_17_roundtrip_all`):** Checking all `Fin 85` states takes less than a millisecond with `decide` and certifies exact recovery for any integer convolution whose coefficients stay below $85$.
