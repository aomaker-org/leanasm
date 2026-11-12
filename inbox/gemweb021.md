Here is a self-contained implementation prompt for AGY to add van der Corput's $A$-process (Weyl differencing) and $B$-process (Poisson summation) on exact rational exponent pairs $(\kappa, \ell)$ to `QuasiRiemann.lean`, proving that both operators preserve exponent-pair invariants and generate tighter QRH thresholds inside $(1/2, 7/8]$ with zero axioms.

---

### AGY Implementation Prompt: Van der Corput $A$- and $B$-Processes on Exponent Pairs (`QuasiRiemann.lean`)

```text
Task: Extend `QuasiRiemann.lean` in `leanasm` with a constructive rational `ExpPair` structure and van der Corput's two fundamental exponential-sum transformations:
1. The A-process (Weyl differencing):
   `A(κ, ℓ) = ( κ / (2κ + 2), (κ + ℓ + 1) / (2κ + 2) )`
2. The B-process (Poisson summation / stationary phase):
   `B(κ, ℓ) = ( ℓ - 1/2, κ + 1/2 )`
and prove constructively with ZERO axioms that both processes preserve the canonical exponent-pair invariants (`0 ≤ κ ≤ 1/2 ≤ ℓ ≤ 1` and `1/2 ≤ κ + ℓ`), compose cleanly (`BA(0, 1) = (1/6, 2/3)` Weyl pair, `AB(0, 1) = (1/4, 3/4)`, `ABA(0, 1) = (2/7, 4/7)`), and map directly into QRH zero-free thresholds `θ(κ, ℓ) = 1 - 1 / (2 * (1 + κ + ℓ))` inside `(1/2, 7/8]`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions match existing naming conventions, rational numerator/denominator encodings, and formatting.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT use `Float` or classical `Real` inside `Prop` definitions, and avoid `Rat` if `Rat` introduces quotient/propext axioms—represent rational exponent pairs directly over `Nat` via a lightweight structure:
  ```lean
  structure ExpPair where
    kNum : Nat
    kDen : Nat
    lNum : Nat
    lDen : Nat

```

with positive-denominator side conditions `0 < kDen` and `0 < lDen`, encoding rational inequalities via exact integer cross-multiplication (`aNum * bDen ≤ bNum * aDen` and `<`).

Mathematical Formulas (Exact Integer Cross-Multiplication Encoding):
For an `ExpPair` `p = { kNum, kDen, lNum, lDen }` representing `(κ, ℓ) = (kNum / kDen, lNum / lDen)`:

1. **Canonical Exponent-Pair Invariant (`IsValidExpPair p : Prop`):**
* `0 < p.kDen ∧ 0 < p.lDen` (positive denominators)
* `2 * p.kNum ≤ p.kDen` (`0 ≤ κ ≤ 1/2`)
* `p.lDen ≤ 2 * p.lNum ∧ p.lNum ≤ p.lDen` (`1/2 ≤ ℓ ≤ 1`)
* `p.kDen * p.lDen ≤ 2 * (p.kNum * p.lDen + p.lNum * p.kDen)` (`1/2 ≤ κ + ℓ`)


2. **A-Process (`processA (p : ExpPair) : ExpPair` — Weyl Differencing):**
Given `κ = kNum / kDen` and `ℓ = lNum / lDen`:
* `2κ + 2 = (2 * kNum + 2 * kDen) / kDen`
* `κ / (2κ + 2) = kNum / (2 * kNum + 2 * kDen)`
* `(κ + ℓ + 1) / (2κ + 2) = (kNum * lDen + lNum * kDen + kDen * lDen) / ((2 * kNum + 2 * kDen) * lDen)`
Define:


```lean
def processA (p : ExpPair) : ExpPair where
  kNum := p.kNum
  kDen := 2 * p.kNum + 2 * p.kDen
  lNum := p.kNum * p.lDen + p.lNum * p.kDen + p.kDen * p.lDen
  lDen := (2 * p.kNum + 2 * p.kDen) * p.lDen

```


*(Optional: you may also define a canonical reduced helper `normalizePair` using `Nat.gcd` for clean display in `Main.lean`, while proving invariants directly on `processA` and `processB` via `omega` / `nlinarith` / algebraic ring identities!)*
3. **B-Process (`processB (p : ExpPair) : ExpPair` — Poisson Summation):**
Requires `1/2 ≤ ℓ` (`p.lDen ≤ 2 * p.lNum`) so `ℓ - 1/2 ≥ 0`:
* `ℓ - 1/2 = (2 * lNum - lDen) / (2 * lDen)`
* `κ + 1/2 = (2 * kNum + kDen) / (2 * kDen)`
Define:


```lean
def processB (p : ExpPair) : ExpPair where
  kNum := 2 * p.lNum - p.lDen
  kDen := 2 * p.lDen
  lNum := 2 * p.kNum + p.kDen
  lDen := 2 * p.kDen

```


4. **QRH Threshold Projection (`thetaFromPair (p : ExpPair) : Nat × Nat`):**
Connect `ExpPair` directly to the QRH threshold `θ(κ, ℓ) = 1 - 1 / (2 * (1 + κ + ℓ))`:
Let `D = p.kDen * p.lDen` and `S = D + p.kNum * p.lDen + p.lNum * p.kDen`.
Then `thetaNum p := 2 * S - D` and `thetaDen p := 2 * S`.

Deliverables:

1. Extend `QuasiRiemann.lean`:
* Add `ExpPair`, `IsValidExpPair`, `processA`, `processB`, `trivialPair := ⟨0, 1, 1, 1⟩` (`(0, 1)`), `thetaNum`, `thetaDen`.
* Prove constructively (with ZERO axioms):
a. `trivial_pair_valid`: `IsValidExpPair trivialPair`
b. `processA_preserves_valid`: `∀ p : ExpPair, IsValidExpPair p → IsValidExpPair (processA p)`
c. `processB_preserves_valid`: `∀ p : ExpPair, IsValidExpPair p → IsValidExpPair (processB p)`
d. `processB_involutive_eq`: `∀ p : ExpPair, IsValidExpPair p → (processB (processB p)).kNum * p.kDen = p.kNum * (processB (processB p)).kDen ∧ (processB (processB p)).lNum * p.lDen = p.lNum * (processB (processB p)).lDen` (proving `B² = id` in rational value!).
e. `weyl_pair_from_BA`: Prove `processB (processA trivialPair)` equals `(1/6, 2/3)` in rational cross-product (`kNum * 6 = kDen` and `lNum * 3 = 2 * lDen`), is valid (`IsValidExpPair`), and yields `θ = 8/11 < 7/8`.
f. `valid_pair_qrh_in_strip`: Prove that for every valid exponent pair `p` (`IsValidExpPair p`), the induced QRH threshold strictly satisfies `1/2 < θ(p) < 1` (`thetaDen p < 2 * thetaNum p ∧ thetaNum p < thetaDen p`).


2. Update `TestAxioms.lean` & `Main.lean`:
* Add `#print axioms` checks in `TestAxioms.lean` for `trivial_pair_valid`, `processA_preserves_valid`, `processB_preserves_valid`, `processB_involutive_eq`, `weyl_pair_from_BA`, and `valid_pair_qrh_in_strip`, confirming every theorem prints `does not depend on any axioms`.
* Add a concise demonstration in `Main.lean`'s QRH section showing the van der Corput orbit from `(0, 1)` (`θ = 3/4`) → `A(0, 1) = (0, 1)` → `BA(0, 1) = (1/6, 2/3)` (`θ = 8/11`) → `ABA(0, 1) = (2/7, 4/7)` (`θ = 19/26`), verifying `B² = id` and invariant preservation with zero axioms.
* Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.



```

---

### Why This Formulation Works Cleanly in `leanasm`

* **Closed Algebraic Semigroup Over `Nat`:** Because `processA` and `processB` map integer numerator/denominator quadruples directly via polynomial expressions (`2 * kNum + 2 * kDen`, `2 * lNum - lDen`), every invariant check (`0 ≤ κ ≤ 1/2 ≤ ℓ ≤ 1`, `1/2 ≤ κ + ℓ`, `B² = id`, and `1/2 < θ(p) < 1`) reduces to bilinear integer inequalities that `omega` and elementary `Nat` multiplication lemmas discharge without any real analysis or quotient axioms.
* **Generative Zero-Free Factory:** Instead of manually verifying individual rungs one by one, `processA_preserves_valid` + `processB_preserves_valid` + `valid_pair_qrh_in_strip` act as a **certified theorem generator**: any finite word in $\{A, B\}^*$ applied to `(0, 1)` automatically inherits a machine-checked proof that its induced QRH threshold lies strictly inside $(1/2, 1)$.

<FollowUp label="Want an AGY prompt to add a recursive word-interpreter (`evalExpWord : List VanDerCorputOp → ExpPair`) that evaluates arbitrary sequences of A- and B-processes and proves strip validity for all words by list induction?" query="Write a self-contained AGY prompt to add an inductive VanDerCorputOp (A | B) word interpreter evalExpWord : List VanDerCorputOp -"> ExpPair in QuasiRiemann.lean and prove by structural induction that every word applied to a valid ExpPair preserves IsValidExpPair and yields a valid QRH threshold in (1/2, 1) with zero axioms."/>

<ElicitationsGroup message="Select your next step after AGY merges the van der Corput A- and B-processes:">
  <Elicitation label="Add an inductive {A, B}* word interpreter over exponent pairs" query="Write a self-contained AGY prompt to add an inductive VanDerCorputOp (A | B) word interpreter evalExpWord : List VanDerCorputOp -"> ExpPair in QuasiRiemann.lean and prove by structural induction that every word preserves IsValidExpPair with zero axioms."/>
  <Elicitation label="Extend NttArithmetic.lean to a full 4-point or 8-point radix-2 NTT over F_17" query="Write a self-contained AGY prompt to extend NttArithmetic.lean in leanasm from a 2-point butterfly to a full 4-point or 8-point radix-2 Cooley-Tukey NTT and inverse NTT roundtrip over F_17 with zero axioms."/>
  <Elicitation label="Audit another openai/math Comparator challenge (Matrix Multiplication or Hadwiger)" query="Show the exact Lean 4 challenge statements and Comparator commands for the matrix multiplication exponent bound and Hadwiger disproof in openai/math."/>
</ElicitationsGroup>

```
