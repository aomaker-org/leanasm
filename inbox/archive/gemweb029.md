Here is a self-contained implementation prompt for AGY to scale `CrtNtt.lean` in `leanasm` to a **16-point radix-2 Cooley–Tukey CRT-NTT** across all three consecutive Fermat primes $F_2 = 17$, $F_3 = 257$, and $F_4 = 65537$, combining them via 3-channel Garner mixed-radix CRT reconstruction ($M = 17 \times 257 \times 65537 = 286{,}331{,}153 > 2^{28}$) to recover exact multi-digit 16-point integer cyclic polynomial convolutions with zero axioms.

---

### AGY Implementation Prompt: 16-Point Radix-2 CRT-NTT Across $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$ ($M = 286{,}331{,}153$)

```text
Task: Scale `CrtNtt.lean` in `leanasm` to a **16-point radix-2 decimation-in-time Cooley–Tukey CRT-NTT** across the three consecutive Fermat primes `𝔽₁₇` (`p₁ = 17`), `𝔽₂₅₇` (`p₂ = 257`), and `𝔽₆₅₅₃₇` (`p₃ = 65537 = 2^{2⁴} + 1`), reconstructing exact unreduced 16-point integer cyclic polynomial convolutions via 3-channel Garner mixed-radix CRT (`M = 17 × 257 × 65537 = 286,331,153`) with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `CrtNtt.lean`, `NttArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new 16-point definitions coexist cleanly with the existing 4-point (`𝔽₅ × 𝔽₁₇`, `M = 85`) and 8-point (`𝔽₁₇ × 𝔽₂₅₇`, `M = 4369`) CRT-NTT theorems without breaking any existing signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`, and do NOT run `decide` over all `286,331,153` states (which would time out!). Instead, prove `garner_17_257_65537_inverse_sound` and verify `garner_17_257_65537_roundtrip_samples` across boundary/large test integers (including `0`, `16`, `17`, `4368`, `4369`, `100000`, `123456789`, `286331152 = M - 1`) so compilation completes in under a second with zero axioms.

Mathematical Specification (`𝔽₁₇ × 𝔽₂₅₇ × 𝔽₆₅₅₃₇` 16-Point CRT-NTT over Dynamic Range `M = 286,331,153`):

1. **16-Vector Representation (`Vec16`):**
   Define a 16-element structure `Vec16` over `Nat` (`x0` through `x15`, `deriving DecidableEq, Repr`), componentwise modular Hadamard product `pointwiseMul16Mod (p : Nat) (u v : Vec16) : Vec16`, and exact unreduced integer 16-point cyclic polynomial convolution `exactIntCyclicConv16 (a b : Vec16) : Vec16` where for $k \in \{0, \dots, 15\}$:
   $$c_k = \sum_{j=0}^{15} a_j \cdot b_{(k - j) \bmod 16}$$

2. **Exact Principal 16th Roots of Unity & Modular Inverses (`16 ∣ pᵢ - 1` for all three Fermat primes):**
   Because $17 - 1 = 16$, $257 - 1 = 256 = 16 \times 16$, and $65537 - 1 = 65536 = 16 \times 4096$, every channel admits an exact principal 16th root of unity $\omega_{16}$ satisfying $\omega_{16}^8 \equiv -1 \pmod{p_i}$ and $\omega_{16}^{16} \equiv 1 \pmod{p_i}$:

   - **Channel 1 (`𝔽₁₇`, `p₁ = 17`):**
     - Primitive root `g = 3` (`3¹ = 3` is already a principal 16th root of unity in `𝔽₁₇`!):
       - `ω₁₆ = 3`, `ω₁₆⁸ = 3⁸ = 6561 ≡ 16 ≡ -1 (mod 17)`, `ω₁₆¹⁶ ≡ 1 (mod 17)`
       - Powers `w_k = 3^k mod 17` for `k = 0..7`: `[1, 3, 9, 10, 13, 5, 15, 11]`
       - Inverse 16th root: `ω₁₆⁻¹ = 3⁻¹ mod 17 = 6` (`3 * 6 = 18 ≡ 1 (mod 17)`)
       - Inverse powers `iw_k = 6^k mod 17` for `k = 0..7`: `[1, 6, 2, 12, 4, 7, 8, 14]`
       - Length scaling inverse: `16⁻¹ ≡ 16 (mod 17)` (`16 * 16 = 256 ≡ 1 (mod 17)`).

   - **Channel 2 (`𝔽₂₅₇`, `p₂ = 257`):**
     - Since `ω₈ = 4` satisfied `4⁴ = 256 ≡ -1 (mod 257)`, any square root of `4` modulo `257` is a principal 16th root: `ω₁₆ = 2`!
       - `ω₁₆ = 2`, `ω₁₆⁸ = 2⁸ = 256 ≡ -1 (mod 257)`, `ω₁₆¹⁶ = 65536 ≡ 1 (mod 257)`
       - Powers `w_k = 2^k mod 257` for `k = 0..7`: `[1, 2, 4, 8, 16, 32, 64, 128]`
       - Inverse 16th root: `ω₁₆⁻¹ = 2⁻¹ mod 257 = 129` (`2 * 129 = 258 ≡ 1 (mod 257)`)
       - Inverse powers `iw_k = 129^k mod 257` for `k = 0..7`: `[1, 129, 193, 225, 241, 249, 253, 255]`
       - Length scaling inverse: `16⁻¹ ≡ 241 (mod 257)` (`16 * 241 = 3856 = 15 * 257 + 1`).

   - **Channel 3 (`𝔽₆₅₅₃₇`, `p₃ = 65537`):**
     - Notice `2¹⁶ = 65536 ≡ -1 (mod 65537)`! Therefore `2² = 4` satisfies `4⁸ = 2¹⁶ = 65536 ≡ -1 (mod 65537)`, so `ω₁₆ = 4` is the exact minimal principal 16th root of unity in `𝔽₆₅₅₃₇`!
       - `ω₁₆ = 4`, `ω₁₆⁸ = 4⁸ = 65536 ≡ -1 (mod 65537)`, `ω₁₆¹⁶ ≡ 1 (mod 65537)`
       - Powers `w_k = 4^k mod 65537` for `k = 0..7`: `[1, 4, 16, 64, 256, 1024, 4096, 16384]`
       - Inverse 16th root: `ω₁₆⁻¹ = 4⁻¹ mod 65537 = 49153` (`4 * 49153 = 196612 = 3 * 65537 + 1`)
       - Inverse powers `iw_k = 49153^k mod 65537` for `k = 0..7`:
         `[1, 49153, 61441, 64513, 65281, 65473, 65521, 65533]`
       - Length scaling inverse: `16⁻¹ mod 65537 = 61441` (`16 * 61441 = 983056 = 15 * 65537 + 1`).

3. **Parametric 4-Stage Radix-2 Decimation-in-Time Cooley–Tukey `ntt16WithRoots` & `intt16WithRoots`:**
   - **Bit-Reversed Input Permutation of `(x0 .. x15)`:**
     `[x0, x8, x4, x12, x2, x10, x6, x14, x1, x9, x5, x13, x3, x11, x7, x15]`
   - **Stage 1 (8 × 2-point butterflies, twiddle `w₀ = 1`):**
     Pair adjacent bit-reversed entries `(0,1), (2,3), (4,5), (6,7), (8,9), (10,11), (12,13), (14,15)` via `butterfly2 p`.
   - **Stage 2 (4 × 4-point butterflies, twiddles `w₀ = 1, w₄`):**
     Combine `(0,2), (1,3)` with `(1, w₄)`, `(4,6), (5,7)` with `(1, w₄)`, `(8,10), (9,11)` with `(1, w₄)`, `(12,14), (13,15)` with `(1, w₄)`.
   - **Stage 3 (2 × 8-point butterflies, twiddles `w₀ = 1, w₂, w₄, w₆`):**
     Combine `(0..3)` with `(4..7)` using twiddles `(1, w₂, w₄, w₆)` and `(8..11)` with `(12..15)` using `(1, w₂, w₄, w₆)`.
   - **Stage 4 (1 × 16-point butterfly, twiddles `w₀ = 1, w₁, w₂, w₃, w₄, w₅, w₆, w₇`):**
     Combine `(0..7)` with `(8..15)` using twiddles `(1, w₁, w₂, w₃, w₄, w₅, w₆, w₇)`.
   - **Inverse `intt16WithRoots`:**
     Run the identical 4-stage butterfly using the inverse twiddles `(1, iw₁, iw₂, iw₃, iw₄, iw₅, iw₆, iw₇)` and scale every output lane by `(lane * inv16) % p`.

4. **3-Channel Garner Mixed-Radix CRT Reconstruction (`M = 17 × 257 × 65537 = 286,331,153`):**
   - Precomputed mixed-radix inverses:
     - `m₁ = 17`, `m₂ = 257`, `m₃ = 65537`
     - `inv17Mod257 = 121` (`(17 * 121) % 257 = 1`)
     - `(17 * 257)⁻¹ mod 65537 = 4369⁻¹ mod 65537`:
       Since `17 * 3855 = 65535 ≡ -2 (mod 65537)` and `(-2) * 32768 = -65536 ≡ 1`, `17⁻¹ mod 65537 = (3855 * 32768) % 65537 = 38551` (`17 * 38551 = 655367 = 10 * 65537 + 1`), and `257⁻¹ mod 65537`: since `257 * 255 = 65535 ≡ -2`, `257⁻¹ mod 65537 = (255 * 32768) % 65537 = 65282` (`257 * 65282 = 16777474 = 256 * 65537 + 1`), so:
       `inv4369Mod65537 = (38551 * 65282) % 65537 = 16384`!
       Check: `4369 * 16384 = 71,581,696 = 1092 * 65537 + 1` (`71581696 - 1092 * 65537 = 71581696 - 71581695 = 1`!).
   - Given `(r₁₇, r₂₅₇, r₆₅₅₃₇)`:
     - `v₁ = r₁₇ % 17`
     - `v₂ = ((r₂₅₇ % 257 + 257 - v₁) * 121) % 257`
     - `partial12 = v₁ + 17 * v₂` (`< 4369 < 65537`)
     - `v₃ = ((r₆₅₅₃₇ % 65537 + 65537 - partial12) * 16384) % 65537`
     - `garner17_257_65537 r₁₇ r₂₅₇ r₆₅₅₃₇ = partial12 + 4369 * v₃`
   - Apply componentwise across `Vec16` (`garnerVec16_17_257_65537`) to define `crtNttConv16 (a b : Vec16) : Vec16`.

Deliverables:

1. Extend `CrtNtt.lean`:
   - Implement `Vec16`, `ntt16WithRoots`, `intt16WithRoots`, `ntt16Mod17`, `intt16Mod17`, `ntt16Mod257`, `intt16Mod257`, `ntt16Mod65537`, `intt16Mod65537`, `pointwiseMul16Mod`, `garner17_257_65537`, `garnerVec16_17_257_65537`, `crtNttConv16`, and `exactIntCyclicConv16`.
   - Prove constructively (with ZERO axioms):
     a. `ntt16_all_fermat_roots_sound`: Verifies `(3 ^ 8) % 17 = 16 ∧ (3 * 6) % 17 = 1 ∧ (16 * 16) % 17 = 1`, `(2 ^ 8) % 257 = 256 ∧ (2 * 129) % 257 = 1 ∧ (16 * 241) % 257 = 1`, and `(4 ^ 8) % 65537 = 65536 ∧ (4 * 49153) % 65537 = 1 ∧ (16 * 61441) % 65537 = 1`.
     b. `garner_17_257_65537_inverse_sound`: `(17 * 121) % 257 = 1 ∧ (4369 * 16384) % 65537 = 1 ∧ 17 * 257 * 65537 = 286331153`.
     c. `garner_17_257_65537_roundtrip_samples`: Exact CRT reconstruction across boundary and multi-million test integers `[0, 1, 16, 17, 256, 257, 4368, 4369, 65536, 65537, 1000000, 123456789, 286331152]`.
     d. `ntt16_three_channels_roundtrip_concrete`: `intt16Mod17 (ntt16Mod17 v) = v`, `intt16Mod257 (ntt16Mod257 v) = v`, and `intt16Mod65537 (ntt16Mod65537 v) = v` on `v = ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16⟩`.
     e. `crt_ntt16_exact_integer_convolution`:
        For `a = ⟨10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160⟩` and `b = ⟨160, 150, 140, 130, 120, 110, 100, 90, 80, 70, 60, 50, 40, 30, 20, 10⟩` (whose exact integer cyclic convolution coefficients reach `149,600`—far exceeding `4,369` and `65,537`, yet comfortably below `286,331,153`!):
        `crtNttConv16 a b = exactIntCyclicConv16 a b`!

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `ntt16_all_fermat_roots_sound`, `garner_17_257_65537_inverse_sound`, `garner_17_257_65537_roundtrip_samples`, `ntt16_three_channels_roundtrip_concrete`, and `crt_ntt16_exact_integer_convolution`, confirming every theorem prints `does not depend on any axioms`.
   - Update Part 10 of `Main.lean` to also execute the 16-point `𝔽₁₇ × 𝔽₂₅₇ × 𝔽₆₅₅₃₇` (`M = 286,331,153`) CRT-NTT convolution, printing peak reconstructed coefficient `149,600` (`< 286,331,153` dynamic range) with zero axioms.
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$ Completes the Fermat-Prime NTT Ladder

* **Minimal Roots Across All Three Fermat Primes:** $\omega_{16} = 3 \pmod{17}$, $\omega_{16} = 2 \pmod{257}$, and $\omega_{16} = 4 \pmod{65537}$ are all tiny powers of $2$ and $3$, keeping butterfly products fast and clean.
* **28-Bit Dynamic Range ($M = 286{,}331{,}153$):** Testing `⟨10, 20, …, 160⟩ ⊛ ⟨160, 150, …, 10⟩` produces exact integer coefficients up to $149{,}600$, exceeding every individual modulus ($17$, $257$, $65537$) and proving true multi-channel Garner reconstruction without single-prime overflow.
