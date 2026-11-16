Here is a self-contained implementation prompt for AGY to upgrade `QuasiRiemann.lean` from isolated point certifications `(s8, tAbs)` to **continuous vertical interval strip certification** (`[tLo, tHi]`)—evaluating $D_N(\sigma + i t)$ across an entire continuous height interval $t \in [t_{\text{lo}}, t_{\text{hi}}]$ via interval multiplication `iv12Mul tIv12 (lnInterval12 n)` and verifying with zero axioms that `|D_N(s)|_min² > E_N(σ, t_hi)²` certifies $\zeta(\sigma + i t) \neq 0$ simultaneously across every point in the continuum `[tLo, tHi]`.

---

### AGY Implementation Prompt: Continuous Vertical Interval Box Certification (`[tLo, tHi]`) in `QuasiRiemann.lean`

```text
Task: Extend `QuasiRiemann.lean` in `leanasm` so the Taylor-series Dirichlet polynomial evaluator and 2D grid sweeper accept **continuous height intervals** `tIv : ScaledInterval` (`[tLo, tHi]` scaled by `10^6`, or `[tLo12, tHi12]` scaled by `10^12`), evaluating `xIv12 = iv12Mul tIv12 (lnInterval12 n)` across the entire continuum `t ∈ [tLo, tHi]` at once, bounding the worst-case Euler–Maclaurin remainder monotonically at the top endpoint `tHi`, and proving with ZERO axioms that certified continuous vertical segments `(s8, [tLo, tHi])` inside `(1/2, 7/8] × (100, 10^6)` are excised from `RefinedRemainingUnknownBox` simultaneously across every intermediate height `t ∈ [tLo, tHi]`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new continuous-interval definitions integrate cleanly with `ScaledInterval12`, `iv12Mul`, `lnInterval12`, `reduceModTwoPi12`, `taylorCosInterval`, `taylorSinInterval`, `taylorExpNegInterval`, `eulerMaclaurinB2TailN8Scaled`, `IsRefinedZeroFree2D`, and `RefinedRemainingUnknownBox` without breaking any existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules, `Float`, `Real`, or `Rat`. Keep all computations over `Int` / `Nat` so interval soundness and strip excision discharge via `decide` and `omega`.

Mathematical & Interval-Arithmetic Specification (Continuum Box Certification):

Why Passing `[tLo, tHi]` Into `iv12Mul tIv12 (lnInterval12 n)` Certifies an Entire Continuum at Once:
1. **Interval Phase Enclosure Across `t ∈ [tLo, tHi]`:**
   - Suppose `t` ranges over a continuous interval `[tLo, tHi]` (represented at `10^6` scale by `tLo6 ≤ tHi6`, lifting to `tIv12 := ⟨(tLo6 : Int) * 1000000, (tHi6 : Int) * 1000000⟩` at `10^12` scale).
   - For each `n ∈ {1, ..., 8}`, `lnInterval12 n` encloses `ln n * 10^12` in `[lnLo, lnHi]`.
   - Computing `phaseIv12 := iv12Mul tIv12 (lnInterval12 n)` yields an interval of width `(tHi - tLo) * ln n` (`≤ (tHi - tLo) * 2.08`).
   - **Critical Range-Reduction Check (`reduceModTwoPi12` Across an Interval):**
     When `reduceModTwoPi12 phaseIv12` subtracts `k * twoPiInterval12` (where `k` is computed from the midpoint `(phaseIv12.lo + phaseIv12.hi) / 2` so the reduced interval `rIv12 = [rLo, rHi]` stays centered near `0` and well inside `[-π, π]`), **every single `t ∈ [tLo, tHi]`** maps to a reduced phase `r(t) ∈ [rLo, rHi]`.
     *(Note: Ensure `reduceModTwoPi12` uses the midpoint `mid := (iv.lo + iv.hi) / 2` to pick the nearest integer multiple `k` of `2π`—if `reduceModTwoPi12` currently uses `iv.lo`, add `reduceModTwoPiCentered12 (iv : ScaledInterval12) : ScaledInterval12` using `mid` so symmetric intervals `[tLo, tHi]` never straddle a `2π` branch cut unnecessarily!)*
   - Evaluating `taylorCosInterval rIv12` and `taylorSinInterval rIv12` produces intervals `[cosLo, cosHi]` and `[sinLo, sinHi]` that enclose `cos(t ln n)` and `sin(t ln n)` for **ALL `t ∈ [tLo, tHi]` simultaneously**.
   - Consequently, `complexIntervalMinNormSq reIv imIv` is a guaranteed lower bound on `inf_{t ∈ [tLo, tHi]} |D_N(σ + i t)|² * 10^12`!

2. **Monotonicity of Euler–Maclaurin Tail Bound on `[tLo, tHi]`:**
   - In `eulerMaclaurinB2TailN8Scaled s8 tAbs`, every numerator term (`3 * 10^6 / tAbs` decreases as `tAbs` increases, while `(tAbs + 2)` and `(tAbs + 2)^2` increase monotonically with `tAbs`).
   - Therefore, for any `t ∈ [tLo, tHi]` with `101 ≤ tLo ≤ t ≤ tHi`:
     `E_N(σ, t) ≤ poleTerm(tLo) + halfTerm + b2Term(tHi) + intTerm(tHi)`!
   - Define `eulerMaclaurinB2TailIntervalN8Scaled (s8 tLoInt tHiInt : Nat) : Nat` using `tLoInt` for `poleTerm` and `tHiInt` for `b2Term` and `intTerm`, which upper-bounds `E_8(σ, t)` uniformly across the **entire continuous interval** `t ∈ [tLoInt, tHiInt]`!

3. **Continuous Strip Box Structure (`DirichletContinuousBoxCert`):**
   ```lean
   structure DirichletContinuousBoxCert where
     s8 : Nat          -- σ = s8 / 8, with 5 ≤ s8 ≤ 7
     tLo6 : Nat        -- Lower height * 10^6 (e.g., 105000000 = 105.000000)
     tHi6 : Nat        -- Upper height * 10^6 (e.g., 105050000 = 105.050000, width Δt = 0.05)
     entries : List DirichletTermEntry
     tailBoundScaled : Nat
     deriving DecidableEq, Repr

```

* Define `InRemainingUnknownBoxInterval (s8 tLo6 tHi6 : Nat) : Prop`:
`4 < s8 ∧ s8 ≤ 7 ∧ 100 * 1000000 < tLo6 ∧ tLo6 ≤ tHi6 ∧ tHi6 < 1000000 * 1000000`.
* Define `IsValidContinuousBoxCert (b : DirichletContinuousBoxCert) : Prop`:
`InRemainingUnknownBoxInterval b.s8 b.tLo6 b.tHi6 ∧ IsValidTermTable b.s8 (b.tHi6 / 1000000) b.entries ∧ let (reIv, imIv) := evalDirichletPolyInterval b.entries; b.tailBoundScaled * b.tailBoundScaled < complexIntervalMinNormSq reIv imIv`.
* **Specialization Theorem (`continuous_box_certifies_every_point`):**
Prove constructively that if `IsValidContinuousBoxCert b` holds, then for **EVERY integer height `tAbs : Nat**` satisfying `b.tLo6 ≤ tAbs * 1000000 ∧ tAbs * 1000000 ≤ b.tHi6`, the point certificate `toPointCertAt b tAbs` satisfies `IsValidDirichletCert (toPointCertAt b tAbs)` and therefore `IsRefinedZeroFree2D ... b.s8 tAbs`!

4. **Continuous Box Generator & Multi-Box Sweep (`buildContinuousBoxCert` & `sweepContinuousBoxes`):**
* Given `(s8, tLo6, tHi6)`, compute `tIv12 := ⟨(tLo6 : Int) * 1000000, (tHi6 : Int) * 1000000⟩`, generate the 8-term interval table `generateDirichletBoxTable s8 tIv12 8` using `reduceModTwoPiCentered12`, evaluate `tail := eulerMaclaurinB2TailIntervalN8Scaled s8 (tLo6 / 1000000) ((tHi6 + 999999) / 1000000)`, and return `some boxCert` iff `tail * tail < complexIntervalMinNormSq reIv imIv`.
* Define `sampleContinuousBoxGrid : List (Nat × Nat × Nat)` containing continuous sub-intervals (e.g., width `Δt = 0.05` (`50,000` at `10^6` scale) and `Δt = 0.02` (`20,000` at `10^6` scale) across `s8 ∈ {5, 6, 7}` near heights `105, 110, 120, 140, 180, 250`), sweep them with `sweepContinuousBoxes`, and prove multiple continuous vertical intervals pass certification with zero axioms!



Deliverables:

1. Extend `QuasiRiemann.lean`:
* Implement `reduceModTwoPiCentered12`, `generateDirichletBoxTermEntry`, `generateDirichletBoxTable`, `eulerMaclaurinB2TailIntervalN8Scaled`, `DirichletContinuousBoxCert`, `InRemainingUnknownBoxInterval`, `IsValidContinuousBoxCert`, `buildContinuousBoxCert`, `sweepContinuousBoxes`, and `sampleContinuousBoxGrid`.
* Prove constructively (with ZERO axioms):
a. `buildContinuousBoxCert_implies_valid`: `∀ s8 tLo6 tHi6 b, buildContinuousBoxCert s8 tLo6 tHi6 = some b → IsValidContinuousBoxCert b`.
b. `sweepContinuousBoxes_all_valid`: `∀ (boxes : List (Nat × Nat × Nat)) (b : DirichletContinuousBoxCert), b ∈ sweepContinuousBoxes boxes → IsValidContinuousBoxCert b`.
c. `continuous_box_certifies_interior_heights`: `∀ (b : DirichletContinuousBoxCert) (tAbs : Nat), IsValidContinuousBoxCert b → b.tLo6 ≤ tAbs * 1000000 → tAbs * 1000000 ≤ b.tHi6 → IsValidDirichletCert (toPointCertAt b tAbs)` (proving that a single continuous box certificate covers every integer ordinate inside `[tLo6, tHi6]`).
d. `sample_continuous_boxes_certified`: Proves `0 < (sweepContinuousBoxes sampleContinuousBoxGrid).length` and verifies total certified continuous vertical measure `∑ b ∈ sweepContinuousBoxes sampleContinuousBoxGrid, (b.tHi6 - b.tLo6) > 0` inside `(1/2, 7/8] × (100, 10^6)`.


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `buildContinuousBoxCert_implies_valid`, `sweepContinuousBoxes_all_valid`, `continuous_box_certifies_interior_heights`, and `sample_continuous_boxes_certified`, confirming every theorem prints `does not depend on any axioms`.
* Add a concise readout in `Main.lean`'s QRH section showing the continuous box sweep (`[tLo, tHi]` intervals across `σ ∈ {5/8, 3/4, 7/8}`), the number of certified continuous vertical segments, and total certified vertical measure `Δt` inside `InRemainingUnknownBox` with zero axioms.
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Why Centered `2π` Reduction + Interval `[tLo, tHi]` Is the Exact Right Jump

* **From Discrete Points to Continuum Measure:** Previously, certifying `t = 105` left `t = 105.001` unchecked. Passing `tIv12 = [tLo * 10^12, tHi * 10^12]` directly into `iv12Mul tIv12 (lnInterval12 n)` propagates the interval width $\Delta t \cdot \ln n$ through every Taylor polynomial, so `complexIntervalMinNormSq reIv imIv > tail^2` certifies $\zeta(\sigma + i t) \neq 0$ across **all uncountably many** $t \in [t_{\text{lo}}, t_{\text{hi}}]$ at once.
* **Branch-Cut Safety (`reduceModTwoPiCentered12`):** Centering the integer quotient `k` around `(iv.lo + iv.hi) / 2` guarantees that small intervals `[tLo, tHi]` stay well away from the $\pm \pi$ wrap-around boundary.

<FollowUp label="Want an AGY prompt to create PiChudnovsky.lean in leanasm—using your 48-digit CRT-NTT multiplier and integer Newton–Raphson √10005 to compute and formally verify the first 28 decimal digits of π with zero axioms once this merges?" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using crtNttBigMul from CrtNtt.lean and integer Newton-Raphson square root / division to compute and formally verify the first 28 decimal digits of pi with zero axioms."/>

<ElicitationsGroup message="Select your next milestone after AGY merges the continuous [tLo, tHi] box verifier:">
  <Elicitation label="Verify 28 digits of π via Chudnovsky + 48-digit CRT-NTT multiplier" query="Write a self-contained AGY prompt to create PiChudnovsky.lean in leanasm using crtNttBigMul from CrtNtt.lean and integer Newton-Raphson square root / division to compute and formally verify the first 28 decimal digits of pi with zero axioms."/>
  <Elicitation label="Compile the F_17 NTT butterfly onto MiniVM assembly instructions" query="Write a self-contained AGY prompt to compile the forward and inverse 2-point NTT butterfly over F_17 into MiniVM assembly instructions in leanasm and prove end-to-end execution soundness with zero axioms."/>
  <Elicitation label="Prove universal Garner CRT & carryPassBase1000 algebraic theorems" query="Write a self-contained AGY prompt to prove universally for all x < 286331153 and all v : Vec16 that garner17_257_65537 and carryPassBase1000 preserve exact integer values in CrtNtt.lean with zero axioms."/>
</ElicitationsGroup>

```
