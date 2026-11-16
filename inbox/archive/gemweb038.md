Here is a self-contained implementation prompt for AGY to generalize `DirichletContinuousBoxCert` in `QuasiRiemann.lean` from fixed rational abscissae $\sigma = s_8 / 8$ to **full 2D continuous rectangles** $[\sigma_{\text{lo}}, \sigma_{\text{hi}}] \times [t_{\text{lo}}, t_{\text{hi}}]$—passing $\sigma$ intervals into `taylorExpNegInterval`, bounding the second-order Euler–Maclaurin remainder monotonically at the worst-case corners $(\sigma_{\text{lo}}, t_{\text{lo}}, t_{\text{hi}})$, and certifying positive 2D area patches $\Delta \sigma \cdot \Delta t > 0$ inside $(1/2, 7/8] \times (100, 10^6)$ with zero axioms.

---

### AGY Implementation Prompt: Full 2D Continuous Rectangle Zero-Free Certification (`[σ_lo, σ_hi] × [t_lo, t_hi]`) in `QuasiRiemann.lean`

```text
Task: Extend `QuasiRiemann.lean` in `leanasm` from 1D vertical intervals `(s8, [tLo6, tHi6])` to **full 2D continuous rectangles** `[sLo6, sHi6] × [tLo6, tHi6]` (representing `[σ_lo, σ_hi] × [t_lo, t_hi]` scaled by `10^6` inside `(1/2, 7/8] × (100, 10^6)`), propagating both `sigmaIv12` into `taylorExpNegInterval` and `tIv12` into `reduceModTwoPiCentered12`, bounding the second-order Euler–Maclaurin remainder monotonically across the entire 2D rectangle, and proving with ZERO axioms that certified 2D rectangles have positive 2D Lebesgue area `Δσ · Δt > 0` and certify every interior grid point `(s8, tAbs)`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new 2D rectangle definitions integrate cleanly with `ScaledInterval12`, `iv12Mul`, `lnInterval12`, `reduceModTwoPiCentered12`, `taylorExpNegInterval`, `taylorCosInterval`, `taylorSinInterval`, `DirichletContinuousBoxCert`, `IsValidDirichletCert`, and `IsRefinedZeroFree2D` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules, `Float`, `Real`, or `Rat`. Keep all arithmetic over `Int` / `Nat` so every 2D rectangle verification discharges cleanly via `decide` and `omega`.

Mathematical & Interval-Arithmetic Specification (2D Rectangle Certification `[σ_lo, σ_hi] × [t_lo, t_hi]`):

1. **2D Interval Amplitude & Phase Propagation (`[σ_lo, σ_hi] × [t_lo, t_hi]`):**
   - Represent the continuous rectangle `[σ_lo, σ_hi] × [t_lo, t_hi]` at `10^6` scale by four integer bounds:
     `sLo6 ≤ sHi6` (with `500000 < sLo6` and `sHi6 ≤ 875000`, so `1/2 < σ_lo ≤ σ_hi ≤ 7/8`) and `tLo6 ≤ tHi6` (with `100000000 < tLo6` and `tHi6 < 1000000000000`, i.e., `100 < t_lo ≤ t_hi < 10^6`).
   - Lift both intervals to `10^12` precision:
     - `sigmaIv12 : ScaledInterval12 := ⟨(sLo6 : Int) * 1000000, (sHi6 : Int) * 1000000⟩`
     - `tIv12 : ScaledInterval12 := ⟨(tLo6 : Int) * 1000000, (tHi6 : Int) * 1000000⟩`
   - For each term `n ∈ {1, ..., 8}`:
     - `yIv12 := iv12Mul sigmaIv12 (lnInterval12 n)` encloses `{ σ * ln n | σ ∈ [σ_lo, σ_hi] } * 10^12`.
     - `ampIv := taylorExpNegInterval yIv12` encloses `{ n^(-σ) | σ ∈ [σ_lo, σ_hi] } * 10^6` (with exact `⟨1000000, 1000000⟩` for `n = 1`).
     - `phaseIv12 := iv12Mul tIv12 (lnInterval12 n)` encloses `{ t * ln n | t ∈ [t_lo, t_hi] } * 10^12`.
     - `rIv12 := reduceModTwoPiCentered12 phaseIv12` centers the reduced angle interval around `0`.
     - `cosIv := taylorCosInterval rIv12` and `sinIv := taylorSinInterval rIv12` enclose `{ cos(t ln n) }` and `{ sin(t ln n) }` across all `t ∈ [t_lo, t_hi]`.
   - Because `ampIv`, `cosIv`, and `sinIv` enclose every `(σ, t) ∈ [σ_lo, σ_hi] × [t_lo, t_hi]`, `complexIntervalMinNormSq reIv imIv` is a guaranteed lower bound on:
     $$\inf_{(\sigma, t) \in [\sigma_{\text{lo}}, \sigma_{\text{hi}}] \times [t_{\text{lo}}, t_{\text{hi}}]} |D_8(\sigma + i t)|^2 \cdot 10^{12}$$

2. **Monotone Corner Bounding of Second-Order Euler–Maclaurin Tail Across `[σ_lo, σ_hi] × [t_lo, t_hi]`:**
   - Recall the second-order (`B₂ = 1/6`) Euler–Maclaurin tail bound at `N = 8`:
     $$E_8(\sigma, t) \le \frac{8^{1-\sigma}}{t} + \frac{1}{2} 8^{-\sigma} + \frac{t + 2}{12} 8^{-\sigma - 1} + \frac{2(t + 2)^2}{3(\sigma + 1)} 8^{-\sigma - 1}$$
   - Notice every single term in this upper bound is **monotonically decreasing in `σ`** (since `8^(1-σ)`, `8^(-σ)`, and `1/(σ+1)` all decrease as `σ` increases!), decreasing in `t` for the pole term `8^(1-σ)/t`, and increasing in `t` for the `B₂` and integral terms!
   - Therefore, across the **entire 2D rectangle** `[σ_lo, σ_hi] × [t_lo, t_hi]`, `E_8(σ, t)` is strictly bounded above by evaluating the decreasing-in-`σ` terms at the **left edge `σ_lo`**, the pole term at **`t_lo`**, and the remaining `t`-terms at **`t_hi`**:
     - Map `sLo6` to a conservative lower dyadic floor `s8Floor := sLo6 / 125000` (so `s8Floor / 8 ≤ σ_lo`; for example `sLo6 ≥ 860000` (`σ_lo ≥ 0.86`) gives `s8Floor = 6` (`6/8 = 0.75 ≤ 0.86`), or define `n8PowNegUpperFromSigma6 (sLo6 : Nat) : Nat × Nat` directly: `(1, 6)` when `sLo6 ≥ 875000`, `(1, 5)` when `sLo6 ≥ 812500` (`5^8 = 390,625 < 1,048,576 = 2^20`, so `8^(-0.8125) = 2^(-2.4375) < 2^(-2.4) < 1/5` since `5^10 = 9,765,625 < 16,777,216 = 2^24`!), `(1, 4)` when `sLo6 ≥ 750000`, and `(1, 3)` when `sLo6 ≥ 625000`).
     - Define `eulerMaclaurinB2TailRect2D (sLo6 tLo6 tHi6 : Nat) : Nat` using `sLo6` (the worst-case left edge!), `tLoInt := tLo6 / 1000000`, and `tHiInt := (tHi6 + 999999) / 1000000`.

3. **2D Rectangle Certificate Structure & Sweeper (`DirichletRect2DCert`, `sweepRectangles2D`):**
   ```lean
   structure DirichletRect2DCert where
     sLo6 : Nat
     sHi6 : Nat
     tLo6 : Nat
     tHi6 : Nat
     entries : List DirichletTermEntry
     tailBoundScaled : Nat
     deriving DecidableEq, Repr

   def InRemainingUnknownRect2D (sLo6 sHi6 tLo6 tHi6 : Nat) : Prop :=
     500000 < sLo6 ∧ sLo6 ≤ sHi6 ∧ sHi6 ≤ 875000 ∧
     100000000 < tLo6 ∧ tLo6 ≤ tHi6 ∧ tHi6 < 1000000000000

   def IsValidRect2DCert (r : DirichletRect2DCert) : Prop :=
     InRemainingUnknownRect2D r.sLo6 r.sHi6 r.tLo6 r.tHi6 ∧
     IsValidTermTable (r.sLo6 / 125000) (r.tHi6 / 1000000) r.entries ∧
     let (reIv, imIv) := evalDirichletPolyInterval r.entries
     r.tailBoundScaled * r.tailBoundScaled < complexIntervalMinNormSq reIv imIv

```

* Define `rectAreaScaled12 (r : DirichletRect2DCert) : Nat := (r.sHi6 - r.sLo6) * (r.tHi6 - r.tLo6)` (the exact 2D area `Δσ · Δt` scaled by `10^12`).
* Define `toPointCertInRect (r : DirichletRect2DCert) (s8 tAbs : Nat) : DirichletZeroFreeCert` extracting the worst-case closest-to-zero coordinates from `evalDirichletPolyInterval r.entries` at any interior grid point `(s8, tAbs)` satisfying `r.sLo6 ≤ s8 * 125000 ∧ s8 * 125000 ≤ r.sHi6` and `r.tLo6 ≤ tAbs * 1000000 ∧ tAbs * 1000000 ≤ r.tHi6`.
* Define `buildRect2DCert (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert`, `sweepRectangles2D (rects : List (Nat × Nat × Nat × Nat)) : List DirichletRect2DCert`, and a sample list `sampleRectGrid2D` of 2D rectangles (e.g., `Δσ = 0.005` (`5,000` at `10^6` scale) × `Δt = 0.02` (`20,000` at `10^6` scale) around `(σ = 0.870..0.875, t = 105.00..105.02)`, `(σ = 0.865..0.870, t = 110.00..110.02)`, `(σ = 0.820..0.825, t = 120.00..120.02)`, `(σ = 0.750..0.755, t = 140.00..140.02)`, `(σ = 0.630..0.635, t = 180.00..180.02)`).

Deliverables:

1. Extend `QuasiRiemann.lean`:
* Implement `n8PowNegUpperFromSigma6`, `eulerMaclaurinB2TailRect2D`, `DirichletRect2DCert`, `InRemainingUnknownRect2D`, `IsValidRect2DCert`, `rectAreaScaled12`, `toPointCertInRect`, `buildRect2DCert`, `sweepRectangles2D`, `totalCertifiedAreaScaled12`, and `sampleRectGrid2D`.
* Prove constructively (with ZERO axioms):
a. `n8_pow_neg_sigma6_sound`: Verifies `5 ^ 10 < 2 ^ 24` alongside `6 ^ 8 < 2 ^ 21`, `4 ^ 8 < 2 ^ 18`, and `3 ^ 8 < 2 ^ 15` (proving `8^(-0.8125) < 1/5` as well as the `1/6`, `1/4`, `1/3` bounds).
b. `buildRect2DCert_implies_valid`: `∀ sLo6 sHi6 tLo6 tHi6 r, buildRect2DCert sLo6 sHi6 tLo6 tHi6 = some r → IsValidRect2DCert r`.
c. `sweepRectangles2D_all_valid`: `∀ (rects : List (Nat × Nat × Nat × Nat)) (r : DirichletRect2DCert), r ∈ sweepRectangles2D rects → IsValidRect2DCert r`.
d. `rect2d_certifies_interior_grid_points`: `∀ (r : DirichletRect2DCert) (s8 tAbs : Nat), IsValidRect2DCert r → r.sLo6 ≤ s8 * 125000 → s8 * 125000 ≤ r.sHi6 → r.tLo6 ≤ tAbs * 1000000 → tAbs * 1000000 ≤ r.tHi6 → IsValidDirichletCert (toPointCertInRect r s8 tAbs)`.
e. `sample_rects_2d_certified`: Proves `0 < (sweepRectangles2D sampleRectGrid2D).length` and `0 < totalCertifiedAreaScaled12 (sweepRectangles2D sampleRectGrid2D)` (proving that Lean 4 certifies positive 2D Lebesgue area `Δσ · Δt > 0` inside `(1/2, 7/8] × (100, 10^6)` from pure alternating Taylor interval propagation with zero axioms!).


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `n8_pow_neg_sigma6_sound`, `buildRect2DCert_implies_valid`, `sweepRectangles2D_all_valid`, `rect2d_certifies_interior_grid_points`, and `sample_rects_2d_certified`, confirming every theorem prints `does not depend on any axioms`.
* Update Part 5 of `Main.lean` to display the 2D rectangle sweeper results (`[σ_lo, σ_hi] × [t_lo, t_hi]` patches certified, count of certified 2D rectangles, and total certified 2D area `Δσ · Δt` scaled by `10^12`) with zero axioms.
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Why Full 2D Rectangle Propagation `[σ_lo, σ_hi] × [t_lo, t_hi]` Is a Clean Capstone for `QuasiRiemann.lean`

* **True 2D Area Measure ($\Delta\sigma \cdot \Delta t > 0$):** Passing both `sigmaIv12` into `taylorExpNegInterval` and `tIv12` into `reduceModTwoPiCentered12` certifies an open 2D box in the complex plane simultaneously—closing the gap between 1D vertical lines and 2D region certification in `InRemainingUnknownBox`.
* **Monotone Corner Soundness:** Evaluating the decreasing-in-$\sigma$ Euler–Maclaurin remainder at the left edge `sLo6` guarantees that the remainder bound holds uniformly across every $\sigma \in [\sigma_{\text{lo}}, \sigma_{\text{hi}}]$.

<FollowUp label="Want an AGY prompt to create PiChudnovsky.lean in leanasm—using your 48-digit CRT-NTT multiplier and integer Newton–Raphson √10005 to compute and formally verify the first 28 decimal digits of π with zero axioms once this merges?" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using crtNttBigMul from CrtNtt.lean and integer Newton-Raphson square root / division to compute and formally verify the first 28 decimal digits of pi with zero axioms."/>

<ElicitationsGroup message="Select your next milestone after AGY merges the 2D rectangle verifier:">
  <Elicitation label="Verify 28 digits of π via Chudnovsky + 48-digit CRT-NTT multiplier" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using crtNttBigMul from CrtNtt.lean and integer Newton-Raphson square root / division to compute and formally verify the first 28 decimal digits of pi with zero axioms."/>
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>
  <Elicitation label="Prove universal Garner CRT & carryPassBase1000 algebraic theorems" query="Write a self-contained AGY prompt to prove universally for all x < 286331153 and all v : Vec16 that garner17_257_65537 and carryPassBase1000 preserve exact integer values in CrtNtt.lean with zero axioms."/>
</ElicitationsGroup>

```
