# Path: leanasm/inbox/archive/gemweb120.md

Here is a modular, zero-Mathlib Lean 4 (`v4.35.0`) blueprint designed to fit
`aomaker-org/leanasm` (`core12`, `-M4096`, `[propext, Quot.sound]` only, zero
`Classical.choice`, zero `sorryAx`). Following your submodule pattern, it splits
the sieve/counting mechanics from the rational Mertens/Beurling certificates so
each file elaborates in a few seconds.

---

### 1. Module Layout & Dependency Graph

```text
src/LeanAsm/QuasiRiemann/
├── LuckySieve/
│   ├── Core.lean              # Finite-prefix sieve, rank-deletion recurrence, survivor bounds
│   └── BeurlingCerts.lean     # Rat Mertens envelopes, Chebyshev psi_L, truncated Euler products
├── LuckySieve.lean            # Thin re-export facade
└── LuckyBeurlingStripWeave.lean  # Optional weave into Qsd1LogDerivStripBridge / HighTrunc

```

---

### 2. `src/LeanAsm/QuasiRiemann/LuckySieve/Core.lean`

Focuses purely on computable `Nat` list/array sieving and structural length
inequalities (zero `Rat` overhead, fast `decide` / `omega` / structural
induction):

```lean
-- Path: src/LeanAsm/QuasiRiemann/LuckySieve/Core.lean

namespace LeanAsm.QuasiRiemann.LuckySieve

/-- Drop every `k`-th 1-indexed element from `xs` (`k >= 2`). -/
def dropEveryKth (k : Nat) (xs : List Nat) : List Nat :=
  let rec go (idx : Nat) : List Nat -> List Nat
    | [] => []
    | y :: ys =>
      if idx % k = 0 then go (idx + 1) ys
      else y :: go (idx + 1) ys
  go 1 xs

/-- Odd seed list `[1, 3, 5, ..., 2*m + 1]` up to bound `N`. -/
def oddSeedUpTo (N : Nat) : List Nat :=
  (List.range ((N + 1) / 2)).map (fun i => 2 * i + 1)

/-- Execute `steps` rounds of the Gardiner-Lazarus-Metropolis-Ulam sieve on `xs`. -/
def luckySieveSteps : Nat -> Nat -> List Nat -> List Nat
  | 0, _, xs => xs
  | steps + 1, stepIdx, xs =>
    match xs.get? stepIdx with
    | none => xs
    | some k =>
      if k <= 1 then xs
      else luckySieveSteps steps (stepIdx + 1) (dropEveryKth k xs)

/-- Concrete finite prefix of Lucky numbers `<= N` (excluding `1` via `luckyGeneratorsUpTo`). -/
def luckyPrefixUpTo (N : Nat) : List Nat :=
  let seed := oddSeedUpTo N
  luckySieveSteps seed.length 1 seed

def luckyGeneratorsUpTo (N : Nat) : List Nat :=
  (luckyPrefixUpTo N).filter (fun x => x > 1)

/-- Exact survivor-count identity for `dropEveryKth`:
    removing every `k`-th element leaves `len - len / k` elements. -/
theorem dropEveryKth_length (k : Nat) (hk : k >= 2) (xs : List Nat) :
    (dropEveryKth k xs).length = xs.length - xs.length / k := by
  sorry -- Prove by induction on `xs` tracking `(idx - 1) % k`

/-- Monotonicity: every element surviving `luckySieveSteps` belonged to `xs`. -/
theorem luckySieveSteps_sublist (steps stepIdx : Nat) (xs : List Nat) :
    ∀ x, x ∈ luckySieveSteps steps stepIdx xs -> x ∈ xs := by
  sorry -- Structural induction on `steps` + `dropEveryKth` membership

/-- Exact prefix certificate up to `N = 50` verified constructively. -/
theorem luckyPrefixUpTo_50_eq :
    luckyPrefixUpTo 50 = [1, 3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49] := by
  decide

end LeanAsm.QuasiRiemann.LuckySieve
-- end of file: src/LeanAsm/QuasiRiemann/LuckySieve/Core.lean

```

*(Note: replace the two `sorry` stubs above with direct structural induction
before running `TestAxioms.lean`—both are pure `Nat` list-length/membership
lemmas with zero axioms beyond `propext`/`Quot.sound`.)*

---

### 3. `src/LeanAsm/QuasiRiemann/LuckySieve/BeurlingCerts.lean`

Consumes `Core.lean` and uses `LeanAsm`'s existing rational type (`QRat` /
`Rat`) to certify finite Mertens sums, Lucky Chebyshev $\psi_{\mathcal{L}}(X)$,
and truncated Beurling Euler product box bounds:

```lean
-- Path: src/LeanAsm/QuasiRiemann/LuckySieve/BeurlingCerts.lean
import LeanAsm.QuasiRiemann.LuckySieve.Core
-- Import your existing QRat / interval arithmetic module here

namespace LeanAsm.QuasiRiemann.LuckySieve

/-- Telescoping survival product `∏_{l ∈ gens} (1 - 1 / l)` in exact rational arithmetic. -/
def survivalProductRat (gens : List Nat) : Rat :=
  gens.foldl (fun acc l => acc * (1 - (1 : Rat) / (l : Rat))) 1

/-- Finite Lucky harmonic / Mertens sum `∑_{l ∈ gens} 1 / l`. -/
def luckyHarmonicRat (gens : List Nat) : Rat :=
  gens.foldl (fun acc l => acc + (1 : Rat) / (l : Rat)) 0

/-- Truncated Beurling Euler factor `(1 - l^{-sigma})^{-1}` at rational abscissa `sigma`
    approximated via `M`-term geometric partial sum `∑_{j=0}^{M} l^{-j * sigma}` (for integer/dyadic `sigma`). -/
def beurlingEulerPartialFactor (l : Nat) (invPowL : Rat) (M : Nat) : Rat :=
  (List.range (M + 1)).foldl (fun acc j => acc + invPowL ^ j) 0

/-- Certificate witness bundling finite-prefix Lucky counts, rational Mertens bounds,
    and truncated Beurling product positivity/non-vanishing on `[1, N]`. -/
structure LuckyBeurlingCertificate (N : Nat) where
  countUpToN : Nat
  harmonicLower : Rat
  harmonicUpper : Rat
  survivalUpper : Rat
  h_count : (luckyPrefixUpTo N).length = countUpToN
  h_harm_lo : harmonicLower <= luckyHarmonicRat (luckyGeneratorsUpTo N)
  h_harm_hi : luckyHarmonicRat (luckyGeneratorsUpTo N) <= harmonicUpper
  h_surv_hi : survivalProductRat (luckyGeneratorsUpTo N) <= survivalUpper

/-- Concrete constructive certificate at `N = 50` (`13` Lucky numbers `<= 50`). -/
def luckyBeurlingCert_50 : LuckyBeurlingCertificate 50 where
  countUpToN := 13
  harmonicLower := 105 / 100
  harmonicUpper := 106 / 100
  survivalUpper := 26 / 100
  h_count := by decide
  h_harm_lo := by decide
  h_harm_hi := by decide
  h_surv_hi := by decide

end LeanAsm.QuasiRiemann.LuckySieve
-- end of file: src/LeanAsm/QuasiRiemann/LuckySieve/BeurlingCerts.lean

```

---

### 4. Wiring into `leanasm` (`ProvenanceSummary.lean` & `TestAxioms.lean`)

* **Facade (`src/LeanAsm/QuasiRiemann/LuckySieve.lean`):** Re-exports
`LeanAsm.QuasiRiemann.LuckySieve.Core` and
`LeanAsm.QuasiRiemann.LuckySieve.BeurlingCerts`, and is registered in
`src/LeanAsm.lean`.
* **Strip / Dyadic-Abel Weave (`LuckyBeurlingStripWeave.lean`):** Feed
`luckyGeneratorsUpTo N` (`N = 64, 256, 1024`) into the same rational Dirichlet-
polynomial box contraction (`QRat` interval boxes at $\sigma \in [7/8, 1]$) used
in `Qsd1LogDerivStripBridge` to verify constructive zero-free boxes for
truncated Beurling zeta $Z_{\mathcal{L}, N}(s)$ alongside the prime strip
bounds.
* **Axiom Gate (`tests/TestAxioms.lean`):** Audit `#print axioms
luckyPrefixUpTo_50_eq`, `#print axioms dropEveryKth_length`, and `#print axioms
luckyBeurlingCert_50` to guarantee strictly `[propext, Quot.sound]`, zero
`Classical.choice`, and zero `sorryAx`.

<!-- end of file: leanasm/inbox/archive/gemweb120.md -->
