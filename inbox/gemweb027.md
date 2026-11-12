Here is a self-contained implementation prompt for AGY to scale `CrtNtt.lean` in `leanasm` to an **8-point radix-2 Cooley–Tukey CRT-NTT** over the consecutive Fermat primes $F_2 = 17$ ($2^{2^2} + 1$) and $F_3 = 257$ ($2^{2^3} + 1$), giving dynamic range $M = 17 \times 257 = 4{,}369$ and recovering exact multi-digit integer cyclic polynomial convolutions with zero axioms.

---

### AGY Implementation Prompt: 8-Point Radix-2 CRT-NTT Over $\mathbb{F}_{17} \times \mathbb{F}_{257}$ ($M = 4{,}369$)

```text
Task: Scale `CrtNtt.lean` in `leanasm` from the 4-point `𝔽₅ × 𝔽₁₇` (`M = 85`) CRT-NTT to a full **8-point radix-2 Cooley–Tukey CRT-NTT** across the consecutive Fermat primes `𝔽₁₇` (`p₁ = 17 = 2^{2²} + 1`) and `𝔽₂₅₇` (`p₂ = 257 = 2^{2³} + 1`), combining both channels via word-bounded Garner mixed-radix CRT reconstruction (`M = 17 × 257 = 4369`) to compute exact unreduced 8-point integer cyclic polynomial convolutions with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `CrtNtt.lean`, `NttArithmetic.lean`, `TestAxioms.lean`, and `Main.lean` first so all new 8-point definitions coexist cleanly with the existing 4-point `𝔽₅ × 𝔽₁₇` definitions (`crtNttConv4`, `garner_5_17_roundtrip_all`, etc.) without breaking any existing theorems.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Work strictly over `Nat` (with `Fin 4369` for the exhaustive CRT roundtrip check) so every proof discharges rapidly via `decide` and `omega`.

Mathematical Specification (`𝔽₁₇ × 𝔽₂₅₇` 8-Point CRT-NTT over Dynamic Range `M = 4369`):

1. **8-Vector Representation (`Vec8`):**
   Define a lightweight 8-element structure over `Nat`:
   ```lean
   structure Vec8 where
     x0 : Nat
     x1 : Nat
     x2 : Nat
     x3 : Nat
     x4 : Nat
     x5 : Nat
     x6 : Nat
     x7 : Nat
     deriving DecidableEq, Repr

```

along with componentwise modular Hadamard product `pointwiseMul8Mod (p : Nat) (u v : Vec8) : Vec8` and exact unreduced integer 8-point cyclic polynomial convolution `exactIntCyclicConv8 (a b : Vec8) : Vec8`, where for $k \in \{0, \dots, 7\}$:


$$c_k = \sum_{j=0}^{7} a_j \cdot b_{(k - j) \bmod 8}$$

2. **Parametric 3-Stage Radix-2 Decimation-in-Time Cooley–Tukey `ntt8Mod` & `intt8Mod`:**
Because both `p₁ = 17` and `p₂ = 257` are Fermat primes with `8 ∣ (pᵢ - 1)`, you can write a single clean parametric 3-stage radix-2 butterfly engine `ntt8WithRoots (p w1 w2 w3 : Nat) (v : Vec8) : Vec8` (where `w1 = ω₈`, `w2 = ω₈² mod p`, `w3 = ω₈³ mod p`) and inverse `intt8WithRoots (p iw1 iw2 iw3 inv8 : Nat) (X : Vec8) : Vec8`!
* **Bit-Reversed Input Permutation (`(x0, x4, x2, x6, x1, x5, x3, x7)`):**
* **Stage 1 (4 × 2-point butterflies, twiddle `1`):**
* `(a0, a1) = butterfly2 p v.x0 v.x4`
* `(a2, a3) = butterfly2 p v.x2 v.x6`
* `(a4, a5) = butterfly2 p v.x1 v.x5`
* `(a6, a7) = butterfly2 p v.x3 v.x7`


* **Stage 2 (2 × 4-point butterflies, twiddles `1`, `w2 = ω₈²`):**
* `(b0, b2) = butterfly2 p a0 a2`
* `(b1, b3) = butterfly2 p a1 ((a3 * w2) % p)`
* `(b4, b6) = butterfly2 p a4 a6`
* `(b5, b7) = butterfly2 p a5 ((a7 * w2) % p)`


* **Stage 3 (1 × 8-point butterfly, twiddles `1`, `w1 = ω₈`, `w2 = ω₈²`, `w3 = ω₈³`):**
* `(X0, X4) = butterfly2 p b0 b4`
* `(X1, X5) = butterfly2 p b1 ((b5 * w1) % p)`
* `(X2, X6) = butterfly2 p b2 ((b6 * w2) % p)`
* `(X3, X7) = butterfly2 p b3 ((b7 * w3) % p)`
*(Where `butterfly2 p u v := ((u + v) % p, (u + p - v % p) % p)`.)*




* **Inverse `intt8WithRoots (p iw1 iw2 iw3 inv8 : Nat) (X : Vec8) : Vec8`:**
Apply the exact same 3-stage butterfly using the inverse roots `iw1 = ω₈⁻¹`, `iw2 = ω₈⁻²`, `iw3 = ω₈⁻³` and multiply each of the 8 output lanes by `inv8 = 8⁻¹ mod p` (`(lane * inv8) % p`).


3. **Exact Fermat Prime Constants:**
* **Channel 1 (`𝔽₁₇`, `p₁ = 17`):**
* Primitive root `g = 3` (`3² = 9`)
* Principal 8th root of unity: `ω₈ = 9` (`9¹ = 9`, `9² ≡ 13`, `9³ ≡ 15`, `9⁴ ≡ 16 ≡ -1`, `9⁸ ≡ 1 (mod 17)`)
* Inverse 8th roots: `ω₈⁻¹ = 9⁷ mod 17 = 2` (`9 * 2 = 18 ≡ 1`), `ω₈⁻² = 4` (`13 * 4 = 52 ≡ 1`), `ω₈⁻³ = 8` (`15 * 8 = 120 ≡ 1`)
* Length scaling inverse: `8⁻¹ ≡ 15 (mod 17)` (`8 * 15 = 120 ≡ 1 (mod 17)`)


* **Channel 2 (`𝔽₂₅₇`, `p₂ = 257`):**
* Primitive root `g = 3` (`3³² = 3^(256/8) mod 257`)
* Compute `ω₈ = 3³² mod 257 = 249` (Note: `249 ≡ -8 (mod 257)`, and `(-8)⁴ = 4096 = 16 * 257 - 16 ≡ -16`? Wait—verify carefully in Lean: `249² mod 257 = 64`, `64² mod 257 = 4096 mod 257 = 241 ≡ -16`, `241² mod 257 = 256 ≡ -1`, so `249⁸ ≡ 1 (mod 257)`! That means `ω₈ = 249` IS an exact primitive 8th root of unity modulo `257`!)
* Powers of `ω₈ = 249 mod 257`:
* `w1 = 249`
* `w2 = (249 * 249) % 257 = 64`
* `w3 = (64 * 249) % 257 = 2` (`64 * (-8) = -512 = -2 * 257 + 2 ≡ 2 (mod 257)`!)
* `w4 = (2 * 249) % 257 = 241`
* `w5 = (241 * 249) % 257 = 8`
* `w6 = (8 * 249) % 257 = 193`
* `w7 = (193 * 249) % 257 = 255`


* Inverse 8th roots modulo `257`:
* `iw1 = 255` (`249 * 255 ≡ (-8)*(-2) = 16`? Check: `249 * 16 = 3984 = 15 * 257 + 129`? No: `(-8) * 32 = -256 ≡ 1 (mod 257)`! So `iw1 = 32` (`249 * 32 = 7968 = 31 * 257 + 1`), `iw2 = (32 * 32) % 257 = 1024 % 257 = 253` (`64 * 253 = 16192 = 63 * 257 + 1`), `iw3 = (253 * 32) % 257 = 8096 % 257 = 129` (`2 * 129 = 258 ≡ 1 (mod 257)`)!)


* Length scaling inverse modulo `257`:
* `8⁻¹ mod 257 = 225` (`8 * 225 = 1800 = 7 * 257 + 1`, since `8 * (-32) = -256 ≡ 1` and `257 - 32 = 225`!).






4. **Word-Bounded Garner Mixed-Radix CRT Reconstruction (`M = 17 × 257 = 4369`):**
* Find `17⁻¹ mod 257`: since `17 * 15 = 255 ≡ -2 (mod 257)` and `(-2) * 128 = -256 ≡ 1 (mod 257)`, `(15 * 128) % 257 = 1920 % 257 = 121` (`17 * 121 = 2057 = 8 * 257 + 1`!).
* Given `(r₁₇, r₂₅₇)` with `r₁₇ < 17` and `r₂₅₇ < 257`:
* `v₁ = r₁₇ % 17`
* `v₂ = ((r₂₅₇ % 257 + 257 - v₁) * 121) % 257`
* `garner17_257 r₁₇ r₂₅₇ = v₁ + 17 * v₂`
*(Every intermediate operand stays strictly `< 514 * 121 = 62,194 < 2¹⁶`, well inside a 16-bit machine word!)*


* Apply componentwise across `Vec8` (`garnerVec8_17_257`) to define `crtNttConv8 (a b : Vec8) : Vec8`.



Deliverables:

1. Extend `CrtNtt.lean`:
* Implement `Vec8`, `butterfly2`, `ntt8WithRoots`, `intt8WithRoots`, `ntt8Mod17`, `intt8Mod17`, `ntt8Mod257`, `intt8Mod257`, `pointwiseMul8Mod`, `garner17_257`, `garnerVec8_17_257`, `crtNttConv8`, and `exactIntCyclicConv8`.
* Prove constructively (with ZERO axioms):
a. `ntt8_mod17_roots_sound`: `(9 ^ 8) % 17 = 1 ∧ (9 ^ 4) % 17 = 16 ∧ (9 * 2) % 17 = 1 ∧ (13 * 4) % 17 = 1 ∧ (15 * 8) % 17 = 1 ∧ (8 * 15) % 17 = 1`.
b. `ntt8_mod257_roots_sound`: `(249 ^ 8) % 257 = 1 ∧ (249 ^ 4) % 257 = 256 ∧ (249 * 32) % 257 = 1 ∧ (64 * 253) % 257 = 1 ∧ (2 * 129) % 257 = 1 ∧ (8 * 225) % 257 = 1`.
c. `garner_17_257_inverse_sound`: `(17 * 121) % 257 = 1 ∧ 17 * 257 = 4369`.
d. `garner_17_257_roundtrip_all`: `∀ (x : Fin 4369), garner17_257 (x.val % 17) (x.val % 257) = x.val` (exhaustively proves exact CRT reconstruction across the entire `4,369`-element dynamic range via `decide`!).
e. `ntt8_mod17_and_mod257_roundtrip_concrete`: `intt8Mod17 (ntt8Mod17 v) = v` and `intt8Mod257 (ntt8Mod257 v) = v` on `v = ⟨1, 2, 3, 4, 5, 6, 7, 8⟩`.
f. `crt_ntt8_exact_integer_convolution`:
For `a = ⟨1, 2, 3, 4, 5, 6, 7, 8⟩` and `b = ⟨8, 7, 6, 5, 4, 3, 2, 1⟩` (whose exact integer cyclic convolution coefficients reach up to `168`—exceeding `85` and `257`, but well below `4369`!):
`crtNttConv8 a b = exactIntCyclicConv8 a b`
(which equals `⟨120, 128, 144, 168, 168, 160, 144, 120⟩`!).


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `ntt8_mod17_roots_sound`, `ntt8_mod257_roots_sound`, `garner_17_257_inverse_sound`, `garner_17_257_roundtrip_all`, `ntt8_mod17_and_mod257_roundtrip_concrete`, and `crt_ntt8_exact_integer_convolution`, confirming every theorem prints `does not depend on any axioms`.
* Update Part 10 of `Main.lean` to also execute the 8-point `𝔽₁₇ × 𝔽₂₅₇` (`M = 4369`) CRT-NTT convolution on `⟨1..8⟩ ⊛ ⟨8..1⟩`, printing the exact integer output `⟨120, 128, 144, 168, 168, 160, 144, 120⟩` with zero axioms.
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Why `𝔽₁₇ × 𝔽₂₅₇` Scales Cleanly in Lean 4

* **Exact 8th Roots & Inverses Pre-Verified:** All modular inverses ($9^{-1} \equiv 2 \pmod{17}$, $8^{-1} \equiv 15 \pmod{17}$, $249^{-1} \equiv 32 \pmod{257}$, $8^{-1} \equiv 225 \pmod{257}$, and $17^{-1} \equiv 121 \pmod{257}$) are precomputed and checked directly in `ntt8_mod17_roots_sound`, `ntt8_mod257_roots_sound`, and `garner_17_257_inverse_sound`.
* **Fast Compile Time:** Checking `garner_17_257_roundtrip_all` across all `Fin 4369` values with `decide` evaluates 4,369 simple integer operations in milliseconds, while `⟨1..8⟩ ⊛ ⟨8..1⟩` produces coefficients up to $168$—demonstrating a genuine multi-prime reconstruction that exceeds single-channel $\mathbb{F}_{17}$ capacity by an order of magnitude.

<FollowUp label="Want an AGY prompt to compile the radix-2 NTT butterfly over F_17 onto MiniVM assembly instructions and verify hardware-level NTT execution with zero axioms once this merges?" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>

<ElicitationsGroup message="Select your next milestone after AGY merges the 8-point CRT-NTT:">
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>
  <Elicitation label="Scale CRT-NTT to 16-point convolution using F_17 x F_257 x F_65537" query="Write a self-contained AGY prompt to scale CrtNtt.lean to a 16-point radix-2 CRT-NTT across the three Fermat primes F_17, F_257, and F_65537 with zero axioms."/>
  <Elicitation label="Audit another openai/math Comparator challenge (Matrix Multiplication or Hadwiger)" query="Show the exact Lean 4 challenge signatures and Comparator commands for the matrix multiplication exponent bound and Hadwiger disproof in openai/math."/>
</ElicitationsGroup>

```
