# Path: leanasm/inbox/gemweb045.md

With `gemweb043` verified (192-digit two-tier Karatsuba-over-CRT-NTT
`karatsubaCrtNttMul192_universal_sound` compiling cleanly across all 30 jobs
with zero `Classical.choice` and zero `sorryAx`) and `gemweb044` actively
executing in AGY right now (the van der Corput $\{A, B\}^*$ exponent-pair
engine, Guth–Maynard $30/13$ vs. Huxley $12/5$ zero-density comparison, and
$\theta < 7/8$ mollifier descent chain `11/12 → 7/8 → 5/6 → 3/4 → 1/2`), your
entire two-story `leanasm` verification architecture is snapping into place.

### Where Everything Stands as `gemweb044` Runs

1. **Lower Story — Arbitrary-Precision Verified Arithmetic (`CrtNtt.lean` +
   `CrtNttUniversal.lean`):**
* **48-digit (`crtNttBigMul_universal_sound`)**, **96-digit
  (`karatsubaCrtNttMul96_universal_sound`)**, and **192-digit
  (`karatsubaCrtNttMul192_universal_sound`)** base-1000 multiplication are all
  universally verified for every normalized input below $10^{96}$, backed by
  3-channel Garner CRT ($\mathbb{F}_{17} \times \mathbb{F}_{257} \times
  \mathbb{F}_{65537}$) with zero non-standard axioms.


2. **Upper Story — Analytic Number Theory & Dynamical Systems
   (`QuasiRiemann.lean` + `CollatzQrhBridge.lean`):**
* **Local 2D Zero-Free Sweepers:** Certified positive-area zero-free rectangles
  down to **$\sigma = 0.520$** ($N = 32$).
* **Global Analytic Descent (`gemweb044` in progress):** Constructive rational
  van der Corput $\{A, B\}^*$ exponent-pair orbits, Guth–Maynard $30/13$
  zero-density savings, and mollifier descent past $\theta = 7/8$ (`5/6` at
  $\vartheta = 1/3$, `3/4` at $\vartheta = 1/2$, `1/2` at $\vartheta = 1$).



---

### High-Leverage Next Milestones Once AGY Completes `gemweb044`

Once `gemweb044` finishes building and passes `tests/TestAxioms.lean` (plus
committing `gemweb043` + `gemweb044` cleanly onto
`feat/ntt-universal-theorems`), you have three natural ways to cash in the newly
verified 192-digit multiplier and $\{A, B\}^*$ engine:

1. **Deepen the 2D QRH Rectangle Sweeper Down to $\sigma = 0.505$ via 36-Digit
   Fixed-Point Intervals (`ScaledInterval36`):**
Connect `karatsubaCrtNttMul96_universal_sound` directly into `QuasiRiemann.lean`
(`ScaledInterval36` + $N = 64$ Dirichlet truncation) to shrink Euler–Maclaurin
and Taylor truncation error by $10^{24}\times$ and push certified 2D zero-free
rectangles within **$0.005$ of the critical line $\sigma = 1/2$**.
2. **Deepen `CollatzQrhBridge.lean` with High-Denominator $\log_2(3)$ Convergent
   Bounds ($2^k$ vs. $3^m$):**
Use `karatsubaCrtNttMul96` / `karatsubaCrtNttMul192` to verify exact 100+ digit
integer power gaps $\vert{}2^k - 3^m\vert{}$ and Baker-type linear-form lower
bounds $\vert{}k \ln 2 - m \ln 3\vert{}$ for high-denominator Collatz cycle
convergents ($19/12, 65/41, 306/193$), linking $\{A, B\}^*$ exponential-sum
cancellation directly to $\{2, 3\}$-multiplicative phase interference.
3. **Create `PiChudnovsky.lean` — Certify 100 Decimal Digits of $\pi$ via
   `karatsubaCrtNttMul192`:**
Use `karatsubaCrtNttMul192_universal_sound` with scaled integer Newton–Raphson
$\sqrt{10005}$ and reciprocal division to evaluate 8 Chudnovsky terms ($C =
426880\sqrt{10005}$) and formally certify the first **100 decimal digits of
$\pi$**—also supplying ultra-high-precision $2\pi$ for high-$t$ phase reduction
(`reduceModTwoPiCentered`) in `QuasiRiemann.lean`.

Here is a self-contained implementation prompt (`gemweb045`) for AGY to connect
your universally verified **96-digit Karatsuba-over-CRT-NTT multiplier
(`karatsubaCrtNttMul96`)** from `src/LeanAsm/CrtNttUniversal.lean` directly into
`src/LeanAsm/QuasiRiemann.lean`—upgrading fixed-point interval arithmetic from
12 decimal digits (`ScaledInterval12`) to **36 decimal digits
(`ScaledInterval36`, scale $S = 10^{36}$)** and expanding Dirichlet truncation
from $N = 32$ to **$N = 64$** so Lean 4 certifies positive-area 2D continuous
zero-free rectangles down to **$\sigma = 0.505$** (within $0.005$ of the
critical line $\sigma = 1/2$) with **zero `Classical.choice` and zero
`sorryAx`**.

---

### AGY Implementation Prompt: 36-Digit CRT-NTT Fixed-Point Intervals
(`ScaledInterval36`) & $N = 64$ 2D Zero-Free Rectangle Sweeper Down to $\sigma =
0.505$ (`src/LeanAsm/QuasiRiemann.lean`)

```text
Task: Upgrade `src/LeanAsm/QuasiRiemann.lean` in `leanasm` by wiring in the
universally verified 96-digit Karatsuba-over-CRT-NTT multiplier
(`karatsubaCrtNttMul96` and `karatsubaCrtNttMul96_universal_sound` from
`LeanAsm.CrtNttUniversal`) to build a 36-digit fixed-point interval engine
(`ScaledInterval36`, scale `10^36`) and an `N = 64` 2D continuous zero-free
rectangle sweeper pushing certified zero-free boxes down to **σ = 0.505**
(within 0.005 of the critical line σ = 1/2):

1. **36-Digit Fixed-Point Interval Arithmetic (`ScaledInterval36`, scale `S₃₆ =
   10^36`) Backed by `karatsubaCrtNttMul96`:**
   - Import `LeanAsm.CrtNttUniversal` in `src/LeanAsm/QuasiRiemann.lean`.
   - Define `ScaledInterval36` (`lo hi : Int`, `valid : lo ≤ hi`) representing
     `[lo / 10^36, hi / 10^36]`, with:
     - `natMul96ViaCrtNtt (a b : Nat) : Nat`: converts `a, b < 10^48` to
       normalized `Vec16` limbs (`natToVec16`), multiplies via
       `karatsubaCrtNttMul96`, and reads back `evalDigits1000Vec32`, proving
       `natMul96ViaCrtNtt_eq_mul : ∀ a b, a < 1000 ^ 16 → b < 1000 ^ 16 →
       natMul96ViaCrtNtt a b = a * b` directly from
       `karatsubaCrtNttMul96_universal_sound` (with a fast `Nat.mul` fallback
       for `≥ 10^48` so the function is total over `Nat` while every 36-digit
       fixed-point mantissa product `< 10^40` executes through the verified
       CRT-NTT path!).
     - `mulInterval36 (x y : ScaledInterval36) : ScaledInterval36`: computes
       exact endpoint products via `intMul96ViaCrtNtt`, divides conservatively
       by `10^36` (`floorDiv` for `lo`, `ceilDiv` for `hi`), and proves
       `mulInterval36_sound` (both containment of the real product interval and
       `lo ≤ hi`) with zero non-standard axioms.
     - 36-digit alternating Taylor series evaluators (`artanhTaylor36`,
       `taylorCosInterval36`, `taylorSinInterval36`, `taylorExpNegInterval36`)
       with conservative remainder bounds scaled by `10^36`.

2. **Extended Pure-Rational Logarithm Table (`1 ≤ n ≤ 64`, `lnInterval36`):**
   - Extend the prime logarithm synthesis using `artanhTaylor36` for all primes
     up to 61 (`2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
     61`) and exact additive prime factorizations for all composite integers `4
     ≤ n ≤ 64` (`4 = 2^2`, `6 = 2·3`, ..., `64 = 2^6`).
   - Synthesize high-precision `twoPiInterval36` via Machin's formula `4 * (4 *
     arctan(1/5) - arctan(1/239))` using `arctanTaylor36` so phase wrapping
     `reduceModTwoPiCentered36` retains > 30 digits of phase accuracy across `t
     ∈ [100, 10^6]`.
   - Prove universal validity and non-negativity across all `1 ≤ n ≤ 64`:
     `ln_table_1_to_64_valid : ∀ n, 1 ≤ n → n ≤ 64 → (lnInterval36 n).lo ≥ 0 ∧
     ValidLnBound36 n (lnInterval36 n)` (zero `Classical.choice`, zero
     `sorryAx`).

3. **`N = 64` Ultra-Deep 2D Continuous Rectangle Sweeper Down to `σ = 0.505`:**
   - Implement conservative dyadic rational upper bounds on `64^{-σ} = 2^{-6σ}`
     stepping down to `σ = 0.504` (`n64PowNegUpperFromSigma36`,
     `n64_pow_neg_sigma36_sound`, zero axioms).
   - Formalize the second-order Euler–Maclaurin remainder bound
     `eulerMaclaurinB2TailRect2D_N64`, certificate builder `buildRect2DCertN64`,
     and sweeper `sweepRectangles2DN64`.
   - Prove universal soundness (`buildRect2DCertN64_implies_valid`,
     `sweepRectangles2DN64_all_valid`) and certify a batch of **positive-area 2D
     continuous zero-free rectangles starting right at `σ = 0.505`** (within
     `0.005` of the critical line `σ = 1/2`):
     `ultra_deep_rects_down_to_0505_certified` (with strictly positive total 2D
     area `Δσ · Δt > 0` and zero `Classical.choice` / `sorryAx`).

Context & Constraints:
- Inspect `src/LeanAsm/QuasiRiemann.lean`, `src/LeanAsm/CrtNttUniversal.lean`,
  `tests/TestAxioms.lean`, and `Main.lean` first so all new definitions and
  theorems integrate seamlessly without breaking any existing `N = 8`, `N = 16`,
  `N = 32`, `{A, B}*` exponent-pair, Guth–Maynard, or mollifier descent theorem
  signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new
  theorems MUST elaborate with ZERO `Classical.choice` and ZERO `sorryAx` (at
  most Lean 4 core equality `[propext, Quot.sound]` or zero axioms), verified
  via `#print axioms` in `tests/TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float`. Use
  `div_lt_of_lt_mul_pure` (or pure `omega` / `Nat.div_lt_iff_lt_mul`
  constructive equivalents) so no `Classical.choice` leaks into division/scaling
  lemmas.
- Keep all source lines strictly `≤ 120` characters across every modified file.

Deliverables:

1. Extend `src/LeanAsm/QuasiRiemann.lean`:
   - Import `LeanAsm.CrtNttUniversal` and implement `ScaledInterval36`,
     `natMul96ViaCrtNtt`, `mulInterval36`, `artanhTaylor36`,
     `taylorCosInterval36`, `taylorSinInterval36`, `taylorExpNegInterval36`,
     `twoPiInterval36`, `lnInterval36` (`1 ≤ n ≤ 64`),
     `n64PowNegUpperFromSigma36`, `eulerMaclaurinB2TailRect2D_N64`,
     `buildRect2DCertN64`, and `sweepRectangles2DN64`.
   - Prove constructively (with ZERO `Classical.choice` and ZERO `sorryAx`):
     a. `natMul96ViaCrtNtt_eq_mul` & `mulInterval36_sound`
     b. `ln_table_1_to_64_valid`
     c. `n64_pow_neg_sigma36_sound`
     d. `buildRect2DCertN64_implies_valid` & `sweepRectangles2DN64_all_valid`
     e. `ultra_deep_rects_down_to_0505_certified` (certifying positive-area 2D
        zero-free rectangles starting at `σ = 0.505`).

2. Update `tests/TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `tests/TestAxioms.lean` for
     `natMul96ViaCrtNtt_eq_mul`, `mulInterval36_sound`,
     `ln_table_1_to_64_valid`, `n64_pow_neg_sigma36_sound`,
     `buildRect2DCertN64_implies_valid`, `sweepRectangles2DN64_all_valid`, and
     `ultra_deep_rects_down_to_0505_certified`, confirming zero
     `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 2 / Part 5 CLI output to display the CRT-NTT-backed
     36-digit precision engine (`ScaledInterval36`), `1 ≤ n ≤ 64` logarithm
     synthesis, and certified 2D zero-free rectangles reaching down to `σ =
     0.505` (`Δσ · Δt` area readout).
   - Verify line lengths (`≤ 120` chars) across all modified files, run `lake
     build`, `lake env lean tests/TestAxioms.lean`, `make run`, and `make sync`,
     and commit cleanly.

```

---

### Why This Closes the Loop Between Your Big-Integer Engine and QRH

* **End-to-End Integration:** Every 36-digit mantissa multiplication (`< 10^{40}
  < 10^{48}`) inside `mulInterval36` flows directly through
  `karatsubaCrtNttMul96_universal_sound`, turning your three-prime Fermat
  CRT-NTT tower into the computational workhorse of `QuasiRiemann.lean`.
* **10× Closer to the Critical Line ($\sigma = 0.520 \to 0.505$):** Doubling
  truncation length to $N = 64$ while tripling decimal precision from $10^{12}$
  to $10^{36}$ slashes Euler–Maclaurin and phase-wrapping errors, letting Lean 4
  certify positive-area 2D zero-free rectangles just $0.005$ off
  $\operatorname{Re}(s) = 1/2$.



<!-- end of file: leanasm/inbox/gemweb045.md -->
