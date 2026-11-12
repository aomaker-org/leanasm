Here is a self-contained implementation prompt for AGY to add **constructive rational Taylor-series interval generators** (`taylorExpNegInterval`, `taylorCosInterval`, `taylorSinInterval`, plus rational range reduction modulo $2\pi$ and rational $\ln n$ enclosures) directly inside `QuasiRiemann.lean`—replacing pre-populated tables with pure Lean 4 interval generation (`generateDirichletTermEntry` and `generateDirichletTable`) verified with zero axioms.

---

### AGY Implementation Prompt: Constructive Rational Taylor-Series Interval Generators for $n^{-\sigma}$, $\cos(t \ln n)$, and $\sin(t \ln n)$ (`QuasiRiemann.lean`)

```text
Task: Extend `QuasiRiemann.lean` in `leanasm` with constructive rational Taylor-series interval generators (`taylorExpNegInterval`, `taylorCosInterval`, `taylorSinInterval`, rational `2π` argument reduction, and rational `ln n` interval bounds scaled by `K = 10^6`) so Lean 4 computes `DirichletTermEntry` intervals (`ampIv`, `cosIv`, `sinIv`) directly from `(s8, tAbs, n)` at compile time—without pre-evaluated trigonometric or power tables—and proves with ZERO axioms that the generated 8-term table at `(s8 = 7, tAbs = 105, N = 8)` satisfies `IsValidTermTable` and `IsValidComputedDirichletCert`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new Taylor-series interval generators integrate cleanly with `ScaledInterval`, `DirichletTermEntry`, `IsValidTermTable`, `evalDirichletPolyInterval`, and `IsValidComputedDirichletCert` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules, `Float`, `Real`, or `Rat`. Represent all fixed-point scaled quantities over `Int` / `Nat` (scale `K = 10^6`, or higher internal precision `K_hi = 10^12` rounded outward to `10^6`) so alternating-series Taylor polynomials and remainder bounds evaluate constructively via `decide` and `omega`.

Mathematical & Algorithmic Specification (Alternating-Series Enclosure at Scale `K = 10^6`):

Why Alternating Taylor Series Produce Exact Two-Sided Enclosures Without Irrationals:
For any alternating series $\sum_{m=0}^{\infty} (-1)^m u_m$ where the term magnitudes $u_m \ge 0$ are monotonically decreasing ($u_{m+1} \le u_m$), every partial sum $S_{2M-1} = \sum_{m=0}^{2M-1} (-1)^m u_m$ is a **strict lower bound** and every partial sum $S_{2M} = \sum_{m=0}^{2M} (-1)^m u_m$ is a **strict upper bound** on the exact sum!
Even when the argument $x \in [x_{\text{lo}}, x_{\text{hi}}]$ is itself an interval (from rational $\ln n$ or rational $2\pi$ range reduction), evaluating the alternating Taylor polynomial in outward-rounded `ScaledInterval` arithmetic (`ivAdd`, `ivMulScaled`) and expanding the final enclosure by `[ -tailBound, +tailBound ]` gives a certified rational enclosure containing the true value for every $x \in [x_{\text{lo}}, x_{\text{hi}}]$.

1. **High-Precision Internal Scale (`K_hi = 10^12`) with Outward Rounding to `K = 10^6`:**
   To avoid 1-ULP rounding drift over 10–14 Taylor terms, define `ScaledInterval12` (scaled by `10^12`) with outward-rounded `iv12Add`, `iv12Mul`, `iv12DivNat` (dividing by an integer denominator `d > 0`: `lo' = lo.ediv d`, `hi' = -((-hi).ediv d)`), and a projection `toScaled6 (iv : ScaledInterval12) : ScaledInterval` (`⟨iv.lo.ediv 1000000, -((-iv.hi).ediv 1000000)⟩`).

2. **Alternating Taylor Generator for `exp(-y)` (`y ≥ 0`, `taylorExpNegInterval`):**
   - For `n = 1`, `ln 1 = 0`, so `1^(-σ) = ⟨1000000, 1000000⟩` identically.
   - For `n ∈ {2, ..., 8}`, compute a certified enclosure `lnIv12(n)` of `ln n * 10^12` using the fast-converging hyperbolic artanh series:
     $$\ln\left(\frac{p}{q}\right) = 2 \sum_{k=0}^{M} \frac{1}{2k+1} \left(\frac{p - q}{p + q}\right)^{2k+1}$$
     applied to `ln 2 = 2 * artanh(1/3)` (`(p-q)/(p+q) = 1/3`, converges at `1/9` per term—12 terms give `< 10^(-13)` accuracy!), `ln 3 = ln 2 + 2 * artanh(1/5)` (`1/25` per term!), `ln 4 = 2 * ln 2`, `ln 5 = 2 * ln 2 + 2 * artanh(1/9)` (`1/81` per term!), `ln 6 = ln 2 + ln 3`, `ln 7 = 3 * ln 2 - 2 * artanh(1/15)` (`1/225` per term!), and `ln 8 = 3 * ln 2`!
   - Multiply `lnIv12(n)` by `σ = s8 / 8` to obtain `yIv12 = [y_lo, y_hi]` (`y = σ * ln n`), then evaluate the alternating exponential series:
     $$e^{-y} \approx \sum_{m=0}^{13} \frac{(-1)^m y^m}{m!}$$
     (at `y ≤ 7/8 * ln 8 ≈ 1.82`, `1.82^14 / 14! < 5 × 10^(-8) < 0.05` ULPs at `10^6` scale!) and round outward to `ScaledInterval` (`ampIv`).

3. **Rational `2π` Range Reduction + Alternating Taylor Generators for `cos(x)` & `sin(x)`:**
   - Using Machin's formula $\frac{\pi}{4} = 4 \arctan(1/5) - \arctan(1/239)$ evaluated to 14 alternating terms at `10^12` scale, obtain the certified enclosure `twoPiIv12` of `2π * 10^12` (`[6283185307179, 6283185307180]`).
   - For `xIv12 = tAbs * lnIv12(n)` (for `tAbs = 105` and `n ≤ 8`, `x ≤ 105 * 2.08 ≈ 218.4 < 35 * 2π`), subtract `k * twoPiIv12` where `k = (xIv12.lo / twoPiIv12.lo)` (or centered to `[-π, π]` by subtracting nearest integer multiple `k` of `2π`) so the reduced angle `rIv12` lies strictly inside `[-3.15 * 10^12, 3.15 * 10^12]`.
   - Evaluate the alternating Taylor series up to `m = 11` (`r^22 / 22!` and `r^23 / 23!`, where `3.15^22 / 22! < 8 × 10^(-11) < 0.0001` ULPs at `10^6` scale!):
     $$\cos(r) \approx \sum_{m=0}^{11} \frac{(-1)^m r^{2m}}{(2m)!}, \qquad \sin(r) \approx \sum_{m=0}^{11} \frac{(-1)^m r^{2m+1}}{(2m+1)!}$$
   - Clamp/intersect `[lo, hi]` with `[-1000000, 1000000]` when rounding to `ScaledInterval` (`cosIv`, `sinIv`) so unit-circle containment is preserved unconditionally.

4. **End-to-End Self-Generating Table & Certificate (`generateDirichletTable`):**
   - Define `generateDirichletTermEntry (s8 tAbs n : Nat) : DirichletTermEntry` and `generateDirichletTable (s8 tAbs truncN : Nat) : List DirichletTermEntry` (`List.range truncN |>.map (fun i => generateDirichletTermEntry s8 tAbs (i + 1))`).
   - Define `generatedCert_7_8_105 : ComputedDirichletCert` using `generateDirichletTable 7 105 8` and `tailBoundScaled := 600000` (`E₈(7/8, 105) ≤ 0.60`), proving inside Lean 4 from pure Taylor-series evaluation that:
     - `IsValidTermTable 7 105 (generateDirichletTable 7 105 8)` holds, and
     - `IsValidComputedDirichletCert generatedCert_7_8_105` holds (`|D₈|_min² · 10¹² > 360 × 10⁹`)!

Deliverables:

1. Extend `QuasiRiemann.lean`:
   - Implement `ScaledInterval12`, `iv12Add`, `iv12Mul`, `iv12DivNat`, `toScaled6`, `artanhTaylor12`, `lnInterval12`, `twoPiInterval12`, `reduceModTwoPi12`, `taylorExpNegInterval`, `taylorCosInterval`, `taylorSinInterval`, `generateDirichletTermEntry`, `generateDirichletTable`, and `generatedCert_7_8_105`.
   - Prove constructively (with ZERO axioms):
     a. `toScaled6_preserves_valid`: Every valid `ScaledInterval12` projects to a valid `ScaledInterval`.
     b. `ln_table_1_to_8_valid`: `∀ n ∈ [1, 2, 3, 4, 5, 6, 7, 8], (lnInterval12 n).isValid` and `0 ≤ (lnInterval12 n).lo`.
     c. `generated_table_7_8_105_valid`: `IsValidTermTable 7 105 (generateDirichletTable 7 105 8)` (verifies that Lean 4's own Taylor-series generator produces valid `ampIv`, `cosIv`, `sinIv` intervals satisfying Pythagorean unit-circle consistency for all `n = 1..8`).
     d. `generated_cert_7_8_105_verified`: `IsValidComputedDirichletCert generatedCert_7_8_105` (proves end-to-end self-generated zero-free certification at `(σ = 7/8, |t| = 105)` with zero axioms!).

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `toScaled6_preserves_valid`, `ln_table_1_to_8_valid`, `generated_table_7_8_105_valid`, and `generated_cert_7_8_105_verified`, confirming every theorem prints `does not depend on any axioms`.
   - Update Part 5 of `Main.lean` to display the self-generated Taylor-series interval enclosure of `D₈(7/8 + 105i)` and its verified `|D₈|_min² > E₈²` margin with zero axioms.
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why Alternating Series + $10^{12}$ Internal Scale Makes This Clean in Lean 4

* **Zero External Tables:** Using `artanh(1/3), artanh(1/5), artanh(1/9), artanh(1/15)` for $\ln 2 \dots \ln 8$ and Machin's formula `4 * artanh(1/5) - artanh(1/239)` for $2\pi$ means **every single constant** (`ln n`, `2π`, `n^(-σ)`, `cos(t ln n)`, `sin(t ln n)`) is computed from scratch by Lean 4's kernel from integer rational arithmetic.
* **Sub-Millisecond Kernel Reduction:** Because `generateDirichletTable 7 105 8` evaluates only 8 terms with 12–14 Taylor iterations each at `10^12` precision, `decide` checks `generated_cert_7_8_105_verified` in milliseconds with zero axioms.
