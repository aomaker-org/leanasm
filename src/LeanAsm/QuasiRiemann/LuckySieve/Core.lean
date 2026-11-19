-- Path: leanasm/src/LeanAsm/QuasiRiemann/LuckySieve/Core.lean
-- Finite-prefix Gardiner-Lazarus-Metropolis-Ulam lucky sieve and survivor bounds.
-- Max Column: 120 Columns

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
    match xs[stepIdx]? with
    | none => xs
    | some k =>
      if k <= 1 then xs
      else luckySieveSteps steps (stepIdx + 1) (dropEveryKth k xs)

/-- Concrete finite prefix of Lucky numbers `<= N` (excluding `1` via `luckyGeneratorsUpTo`). -/
def luckyPrefixUpTo (N : Nat) : List Nat :=
  let seed := oddSeedUpTo N
  luckySieveSteps seed.length 1 seed

/-- Lucky generator sequence up to `N` (excluding `1`). -/
def luckyGeneratorsUpTo (N : Nat) : List Nat :=
  (luckyPrefixUpTo N).filter (fun x => x > 1)

/-- Monotonicity helper for `dropEveryKth.go`. -/
theorem dropEveryKth_go_sublist (k : Nat) (idx : Nat) (l : List Nat) (x : Nat) :
    x ∈ dropEveryKth.go k idx l → x ∈ l := by
  induction l generalizing idx with
  | nil =>
    intro h
    dsimp [dropEveryKth.go] at h
    cases h
  | cons y ys ih =>
    intro h
    dsimp [dropEveryKth.go] at h
    split at h
    · right; exact ih (idx + 1) h
    · cases h with
      | head => left
      | tail _ hmem => right; exact ih (idx + 1) hmem

/-- Monotonicity: every element surviving `dropEveryKth` belonged to `xs`. -/
theorem dropEveryKth_sublist (k : Nat) (xs : List Nat) :
    ∀ x, x ∈ dropEveryKth k xs → x ∈ xs := by
  intro x hx
  exact dropEveryKth_go_sublist k 1 xs x hx

/-- Monotonicity: every element surviving `luckySieveSteps` belonged to `xs`. -/
theorem luckySieveSteps_sublist (steps stepIdx : Nat) (xs : List Nat) :
    ∀ x, x ∈ luckySieveSteps steps stepIdx xs → x ∈ xs := by
  induction steps generalizing stepIdx xs with
  | zero =>
    intro x hx
    exact hx
  | succ n ih =>
    intro x hx
    dsimp [luckySieveSteps] at hx
    split at hx
    · exact hx
    · rename_i k heq
      split at hx
      · exact hx
      · have h_rec := ih (stepIdx + 1) (dropEveryKth k xs) x hx
        exact dropEveryKth_sublist k xs x h_rec

/-- Monotonicity: every element surviving `luckyPrefixUpTo N` belongs to the odd seed list. -/
theorem luckyPrefixUpTo_sublist_oddSeed (N : Nat) :
    ∀ x, x ∈ luckyPrefixUpTo N → x ∈ oddSeedUpTo N := by
  intro x hx
  dsimp [luckyPrefixUpTo] at hx
  exact luckySieveSteps_sublist (oddSeedUpTo N).length 1 (oddSeedUpTo N) x hx

/-- Exact prefix certificate up to `N = 50` verified constructively. -/
theorem luckyPrefixUpTo_50_eq :
    luckyPrefixUpTo 50 = [1, 3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49] := by
  rfl

/-- Exact prefix count certificate up to `N = 50`. -/
theorem luckyPrefixUpTo_50_length :
    (luckyPrefixUpTo 50).length = 13 := by
  rfl

/-- Exact generator certificate up to `N = 50`. -/
theorem luckyGeneratorsUpTo_50_eq :
    luckyGeneratorsUpTo 50 = [3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49] := by
  rfl

end LeanAsm.QuasiRiemann.LuckySieve

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/LuckySieve/Core.lean
