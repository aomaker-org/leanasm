Here is a self-contained implementation prompt for AGY to upgrade the concrete van der Corput theorems in `QuasiRiemann.lean` to universal, universally quantified preservation theorems (`processA_preserves_valid`, `processB_preserves_valid`, `processB_involutive_eq`, and `valid_pair_qrh_in_strip`) together with an inductive $\{A, B\}^*$ word evaluator (`evalVdcWord`) verified by structural list induction with zero axioms.

---

### AGY Implementation Prompt: Universal $\{A, B\}^*$ Word Engine & Universal Invariant Preservation (`QuasiRiemann.lean`)

```text
Task: Upgrade the van der Corput exponent-pair formalization in `QuasiRiemann.lean` (`leanasm`) from concrete orbit checks to universal polymorphic theorems over EVERY valid `ExpPair`, and add an inductive `{A, B}*` word interpreter `evalVdcWord` verified by structural list induction with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions and theorems reuse the exact existing `ExpPair`, `IsValidExpPair`, `processA`, `processB`, `trivialPair`, `thetaNum`, and `thetaDen` declarations without breaking existing theorem signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or use `Float`/`Real`/`Rat` quotient types. Keep all proofs purely constructive over `Nat` using `omega`, `Nat.mul_pos`, `Nat.add_le_add`, `Nat.mul_le_mul`, and elementary ring/associativity lemmas from Lean 4 core (`Nat.add_mul`, `Nat.mul_add`, `Nat.mul_comm`, `Nat.mul_left_comm`).

Algebraic Proof Guide (for discharging nonlinear `Nat` products cleanly without `nlinarith`):
Because `IsValidExpPair p` consists of:
- `h_kDen : 0 < p.kDen`
- `h_lDen : 0 < p.lDen`
- `h_kUpper : 2 * p.kNum ≤ p.kDen` (`κ ≤ 1/2`)
- `h_lLower : p.lDen ≤ 2 * p.lNum` (`1/2 ≤ ℓ`)
- `h_lUpper : p.lNum ≤ p.lDen` (`ℓ ≤ 1`)
- `h_sum : p.kDen * p.lDen ≤ 2 * (p.kNum * p.lDen + p.lNum * p.kDen)` (`1/2 ≤ κ + ℓ`)

1. **`processA_preserves_valid (p : ExpPair) (hp : IsValidExpPair p) : IsValidExpPair (processA p)`:**
   Recall `processA p` has:
   - `kNum' = p.kNum`
   - `kDen' = 2 * p.kNum + 2 * p.kDen`
   - `lNum' = p.kNum * p.lDen + p.lNum * p.kDen + p.kDen * p.lDen`
   - `lDen' = (2 * p.kNum + 2 * p.kDen) * p.lDen`
   Each conjunct reduces to linear/bilinear inequalities:
   - `0 < kDen'` and `0 < lDen'`: immediate from `0 < p.kDen`, `0 < p.lDen`, and `Nat.mul_pos`.
   - `2 * kNum' ≤ kDen'`: `2 * p.kNum ≤ 2 * p.kNum + 2 * p.kDen` (`omega`).
   - `lDen' ≤ 2 * lNum'`: expands to `(2 * p.kNum + 2 * p.kDen) * p.lDen ≤ 2 * (p.kNum * p.lDen + p.lNum * p.kDen + p.kDen * p.lDen)`, which is equivalent to `0 ≤ 2 * (p.lNum * p.kDen)` (`omega` after distributing `Nat.add_mul`).
   - `lNum' ≤ lDen'`: expands to `p.kNum * p.lDen + p.lNum * p.kDen + p.kDen * p.lDen ≤ 2 * (p.kNum * p.lDen) + 2 * (p.kDen * p.lDen)`, which follows directly from `p.lNum * p.kDen ≤ p.kDen * p.lDen` (via `Nat.mul_le_mul_right p.kDen h_lUpper` and `Nat.mul_comm`) plus `omega`!
   - `kDen' * lDen' ≤ 2 * (kNum' * lDen' + lNum' * kDen')`: note that `kDen'` factors out on both sides (`kDen' > 0`), reducing to `lDen' ≤ 2 * (kNum' * p.lDen + lNum')`, which simplifies via `omega` after distributing!

2. **`processB_preserves_valid (p : ExpPair) (hp : IsValidExpPair p) : IsValidExpPair (processB p)`:**
   Recall `processB p` has `kNum' = 2 * p.lNum - p.lDen`, `kDen' = 2 * p.lDen`, `lNum' = 2 * p.kNum + p.kDen`, `lDen' = 2 * p.kDen`.
   - `2 * kNum' ≤ kDen'`: `2 * (2 * p.lNum - p.lDen) ≤ 2 * p.lDen` follows directly from `h_lLower` (`p.lDen ≤ 2 * p.lNum`) and `h_lUpper` (`p.lNum ≤ p.lDen`) via `omega`.
   - `lDen' ≤ 2 * lNum'`: `2 * p.kDen ≤ 2 * (2 * p.kNum + p.kDen)` (`omega`).
   - `lNum' ≤ lDen'`: `2 * p.kNum + p.kDen ≤ 2 * p.kDen` follows directly from `h_kUpper` (`2 * p.kNum ≤ p.kDen`) via `omega`.
   - `kDen' * lDen' ≤ 2 * (kNum' * lDen' + lNum' * kDen')`: factors out `4` (`(2 * p.lDen) * (2 * p.kDen)` vs `2 * ((2 * p.lNum - p.lDen) * (2 * p.kDen) + (2 * p.kNum + p.kDen) * (2 * p.lDen))`) and discharges cleanly via `h_lLower` + `h_sum` + `Nat.mul_sub_right_distrib` + `omega`.

3. **`valid_pair_qrh_in_strip (p : ExpPair) (hp : IsValidExpPair p) : thetaDen p < 2 * thetaNum p ∧ thetaNum p < thetaDen p`:**
   With `D = p.kDen * p.lDen > 0` (`Nat.mul_pos hp.1 hp.2.1`) and `S = D + p.kNum * p.lDen + p.lNum * p.kDen ≥ D > 0`, `thetaNum p = 2 * S - D` and `thetaDen p = 2 * S`, so `2 * S < 2 * (2 * S - D)` (`2 * D < 2 * S`, true since `p.kDen * p.lDen ≤ 2 * (...)` implies `0 < p.kNum * p.lDen + p.lNum * p.kDen`) and `2 * S - D < 2 * S` (`omega`).

Deliverables:

1. Extend `QuasiRiemann.lean`:
   - Define the inductive van der Corput operator alphabet and recursive word evaluator:
     ```lean
     inductive VdcOp where
       | A : VdcOp
       | B : VdcOp
       deriving DecidableEq, Repr

     def applyVdcOp (op : VdcOp) (p : ExpPair) : ExpPair :=
       match op with
       | .A => processA p
       | .B => processB p

     def evalVdcWord (w : List VdcOp) (p : ExpPair := trivialPair) : ExpPair :=
       match w with
       | [] => p
       | op :: rest => evalVdcWord rest (applyVdcOp op p)
     ```
     *(Note: check whether left-to-right application order `op :: rest => evalVdcWord rest (applyVdcOp op p)` or mathematical function-composition order `op :: rest => applyVdcOp op (evalVdcWord rest p)` matches your existing `weyl_pair_from_AB` convention `processA (processB trivialPair)`—use mathematical composition order `op :: rest => applyVdcOp op (evalVdcWord rest p)` so `[.A, .B]` evaluates literally to `processA (processB trivialPair)`!)*
   - Prove constructively (with ZERO axioms):
     a. `processA_preserves_valid`: `∀ p : ExpPair, IsValidExpPair p → IsValidExpPair (processA p)`
     b. `processB_preserves_valid`: `∀ p : ExpPair, IsValidExpPair p → IsValidExpPair (processB p)`
     c. `processB_involutive_eq`: `∀ p : ExpPair, IsValidExpPair p → (processB (processB p)).kNum * p.kDen = p.kNum * (processB (processB p)).kDen ∧ (processB (processB p)).lNum * p.lDen = p.lNum * (processB (processB p)).lDen`
     d. `valid_pair_qrh_in_strip`: `∀ p : ExpPair, IsValidExpPair p → thetaDen p < 2 * thetaNum p ∧ thetaNum p < thetaDen p`
     e. `evalVdcWord_preserves_valid`: `∀ (w : List VdcOp) (p : ExpPair), IsValidExpPair p → IsValidExpPair (evalVdcWord w p)` (by structural induction on `w`).
     f. `vdc_word_yields_qrh_in_strip`: `∀ (w : List VdcOp), let p := evalVdcWord w trivialPair; thetaDen p < 2 * thetaNum p ∧ thetaNum p < thetaDen p` (corollary proving ANY finite word in `{A, B}*` applied to `(0, 1)` produces a QRH threshold strictly inside `(1/2, 1)`).
     g. `vdc_word_AAB_orbit_verified`: Concrete evaluation of `[.A, .A, .B]` (`AAB(0, 1) = (1/14, 11/14)`) and `[.B, .A, .B]` (`BAB(0, 1) = (1/6, 2/3)`), verifying `θ(1/14, 11/14) = 19/26 < 7/8`.

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `processA_preserves_valid`, `processB_preserves_valid`, `processB_involutive_eq`, `valid_pair_qrh_in_strip`, `evalVdcWord_preserves_valid`, `vdc_word_yields_qrh_in_strip`, and `vdc_word_AAB_orbit_verified`, confirming every theorem prints `does not depend on any axioms`.
   - Add a concise demonstration in `Main.lean`'s QRH section executing `evalVdcWord [.A, .A, .B] trivialPair` (`(1/14, 11/14)`, `θ = 19/26 < 7/8`) and reporting universal `{A, B}*` induction soundness with zero axioms.
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```
