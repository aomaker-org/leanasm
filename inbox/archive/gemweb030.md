Here is a self-contained implementation prompt for AGY to add **verified multi-limb base-1000 big-integer multiplication** on top of the 16-point $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$ ($M = 286{,}331{,}153$) CRT-NTT engine in `CrtNtt.lean`—demonstrating end-to-end Schönhage–Strassen / Furer-style FFT big-integer multiplication (base-1000 limb decomposition $\to$ zero-padded `Vec16` $\to$ 3-Fermat-prime CRT-NTT linear convolution $\to$ carry propagation $\to$ exact 48-digit integer product) with zero axioms.

---

### AGY Implementation Prompt: Verified Multi-Limb Base-1000 Big-Integer Multiplication (`CrtNtt.lean`)

```text
Task: Extend `CrtNtt.lean` in `leanasm` to implement **verified multi-limb base-1000 big-integer multiplication** powered by the existing 16-point `𝔽₁₇ × 𝔽₂₅₇ × 𝔽₆₅₅₃₇` (`M = 286,331,153`) CRT-NTT engine (`crtNttConv16`), proving end-to-end exact equality between CRT-NTT big-integer multiplication and native Lean `Nat` multiplication (`crtNttBigMul a b = a * b`) on concrete multi-digit test numbers (including 24-digit × 24-digit → 48-digit integers) with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `CrtNtt.lean`, `TestAxioms.lean`, and `Main.lean` first so all new big-integer limb definitions reuse the existing `Vec16` and `crtNttConv16` declarations without breaking any existing 4-point, 8-point, or 16-point CRT-NTT theorems.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Work strictly over `Nat` so every proof discharges cleanly via `decide` and `omega`.

Mathematical & Algorithmic Specification (Base-1000 Limb Multiplication via 16-Point CRT-NTT):
Why Base-1000 Limbs + 16-Point `𝔽₁₇ × 𝔽₂₅₇ × 𝔽₆₅₅₃₇` CRT-NTT Has Zero Overflow:
- An 8-limb base-1000 integer `X = ∑_{i=0}^7 d_i · 1000^i` (`0 ≤ d_i < 1000`) represents any integer up to `10^24 - 1` (24 decimal digits).
- When two 8-limb base-1000 integers `A` and `B` are zero-padded to length `16` (`Vec16` with `x8 .. x15 = 0`), their 16-point cyclic convolution `crtNttConv16 (toBase1000Vec16 A) (toBase1000Vec16 B)` equals their **acyclic linear polynomial product** (degree `≤ 14 < 16`, so zero cyclic wrap-around!).
- Every uncarried convolution coefficient `c_k` satisfies:
  `c_k ≤ 8 · 999² = 7,984,008 < 286,331,153 = 17 × 257 × 65537`
  guaranteeing zero CRT modular overflow!
- Propagating base-1000 carries across the 16 reconstructed coefficients yields the exact 16-limb (`48`-decimal-digit) product `A * B`.

1. **Base-1000 Limb Encoding & Decoding (`toBase1000Vec16` / `fromBase1000Vec16`):**
   - Extract the 8 low base-1000 limbs of `n : Nat` (zero-padded in slots `x8 .. x15`):
     ```lean
     def limb1000 (n idx : Nat) : Nat := (n / (1000 ^ idx)) % 1000

     def toBase1000Vec16 (n : Nat) : Vec16 where
       x0 := limb1000 n 0
       x1 := limb1000 n 1
       x2 := limb1000 n 2
       x3 := limb1000 n 3
       x4 := limb1000 n 4
       x5 := limb1000 n 5
       x6 := limb1000 n 6
       x7 := limb1000 n 7
       x8 := 0; x9 := 0; x10 := 0; x11 := 0
       x12 := 0; x13 := 0; x14 := 0; x15 := 0
     ```
   - Carry-propagation evaluator `evalCarryBase1000Vec16 (v : Vec16) : Nat`:
     Converts the 16 uncarried convolution coefficients `[v.x0, ..., v.x15]` into a single `Nat` via Horner / positional evaluation (`∑_{k=0}^{15} v_k · 1000^k`, or explicit step-by-step carry propagation `carryPassBase1000 (v : Vec16) : Vec16` followed by positional reconstruction `evalDigits1000Vec16 (digits : Vec16) : Nat`):
     ```lean
     def carryPassBase1000 (v : Vec16) : Vec16 :=
       let d0 := v.x0 % 1000; let c0 := v.x0 / 1000
       let s1 := v.x1 + c0; let d1 := s1 % 1000; let c1 := s1 / 1000
       -- ... propagate carries through s14, c14 ...
       let s15 := v.x15 + c14; let d15 := s15 % 1000
       ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩
     ```
     and `evalDigits1000Vec16 (d : Vec16) : Nat` evaluates `d.x0 + 1000 * (d.x1 + 1000 * (...))` via Horner's rule!

2. **End-to-End CRT-NTT Big-Integer Multiplier (`crtNttBigMul`):**
   ```lean
   def crtNttBigMul (a b : Nat) : Nat :=
     let va := toBase1000Vec16 a
     let vb := toBase1000Vec16 b
     let rawConv := crtNttConv16 va vb
     let normalizedDigits := carryPassBase1000 rawConv
     evalDigits1000Vec16 normalizedDigits

```

Deliverables:

1. Extend `CrtNtt.lean`:
* Implement `limb1000`, `toBase1000Vec16`, `carryPassBase1000`, `evalDigits1000Vec16`, and `crtNttBigMul`.
* Prove constructively (with ZERO axioms):
a. `base1000_limb_capacity_bound`: `8 * 999 ^ 2 < 17 * 257 * 65537` (`7,984,008 < 286,331,153`, proving worst-case 8-limb base-1000 convolution coefficients never overflow the 3-Fermat-prime CRT dynamic range).
b. `base1000_roundtrip_concrete`: `evalDigits1000Vec16 (toBase1000Vec16 123456789012345678901234) = 123456789012345678901234` (proves lossless 24-digit limb decomposition).
c. `crt_ntt_big_mul_12_digit`:
`crtNttBigMul 123456789012 987654321098 = 123456789012 * 987654321098`
(`= 121932631137021795223746`).
d. `crt_ntt_big_mul_24_digit_max`:
Full 24-digit × 24-digit → 48-digit stress test (including maximum limb carry cascade `999999999999999999999999` and asymmetric `123456789012345678901234 * 987654321098765432109876`):
`crtNttBigMul 123456789012345678901234 987654321098765432109876 = 123456789012345678901234 * 987654321098765432109876`
(`= 121932631137021795226185032733622923332237463801114264`)
and `crtNttBigMul 999999999999999999999999 999999999999999999999999 = 999999999999999999999999 * 999999999999999999999999` (`10^48 - 2·10^24 + 1`)!


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `base1000_limb_capacity_bound`, `base1000_roundtrip_concrete`, `crt_ntt_big_mul_12_digit`, and `crt_ntt_big_mul_24_digit_max`, confirming every theorem prints `does not depend on any axioms`.
* Update Part 10 of `Main.lean` to execute `crtNttBigMul 123456789012345678901234 987654321098765432109876`, printing the 24-digit inputs, the 48-digit CRT-NTT reconstructed product, and exact match with `a * b` (ZERO axioms).
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Why This Stress Test Is an Ideal End-to-End Capstone for `CrtNtt.lean`

* **Worst-Case Carry & Overflow Verification:** Evaluating `999999999999999999999999 * 999999999999999999999999` (`(10^24 - 1)^2`) exercises the peak possible uncarried convolution peak $8 \times 999^2 = 7{,}984{,}008 < 286{,}331{,}153$ and the longest possible base-1000 carry cascade across all 16 output limbs (`999...998000...001`), proving both CRT headroom and carry-propagation exactness in a single `decide` step.
* **True Multi-Precision Bridge:** It connects your Fermat prime tower (`17`, `257`, `65537`), radix-2 Cooley–Tukey NTT butterflies, and Garner mixed-radix CRT directly to arbitrary-precision integer arithmetic in Lean 4 core with zero axioms.

<FollowUp label="Want an AGY prompt to compile the radix-2 NTT butterfly over F_17 onto MiniVM assembly instructions and prove end-to-end hardware execution soundness with zero axioms once this merges?" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>

<ElicitationsGroup message="Choose your next milestone after AGY merges the 48-digit CRT-NTT big-integer multiplier:">
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>
  <Elicitation label="Prove general carryPassBase1000 soundness for arbitrary Vec16" query="Write a self-contained AGY prompt to prove universally that evalDigits1000Vec16 (carryPassBase1000 v) = ∑_{k=0}^{15} v_k · 1000^k (mod 1000^16) for all v : Vec16 in CrtNtt.lean with zero axioms."/>
  <Elicitation label="Audit another openai/math Comparator challenge (Matrix Multiplication or Hadwiger)" query="Show the exact Lean 4 challenge signatures and Comparator commands for the matrix multiplication exponent bound and Hadwiger disproof in openai/math."/>
</ElicitationsGroup>

```
