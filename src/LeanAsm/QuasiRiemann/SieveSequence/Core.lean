-- Path: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/Core.lean
-- Generalized prime-like and lucky number-like sieve sequences and operations.
-- Max Column: 120 Columns

namespace LeanAsm.QuasiRiemann.SieveSequence

/-- Drop every `k`-th 1-indexed element from `xs` (`k >= 1`). -/
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

/-- Natural sequence `[1, 2, ..., N]`. -/
def natRangeUpTo (N : Nat) : List Nat :=
  (List.range N).map (fun i => i + 1)

/-- Natural seed `[2, 3, ..., N]`. -/
def natSeedUpTo (N : Nat) : List Nat :=
  (List.range (N - 1)).map (fun i => i + 2)

/-- Execute `steps` rounds of the Gardiner-Lazarus-Metropolis-Ulam lucky sieve on `xs`. -/
def luckySieveSteps : Nat -> Nat -> List Nat -> List Nat
  | 0, _, xs => xs
  | steps + 1, stepIdx, xs =>
    match xs[stepIdx]? with
    | none => xs
    | some k =>
      if k <= 1 then xs
      else luckySieveSteps steps (stepIdx + 1) (dropEveryKth k xs)

/-- Concrete finite prefix of Lucky numbers `<= N` (OEIS A000959). -/
def luckyPrefixUpTo (N : Nat) : List Nat :=
  let seed := oddSeedUpTo N
  luckySieveSteps seed.length 1 seed

/-- Lucky Beurling generators up to `N` (excluding `1`). -/
def luckyGeneratorsUpTo (N : Nat) : List Nat :=
  (luckyPrefixUpTo N).filter (fun x => x > 1)

/-- Ludic sieve execution fuel-bounded by `steps`:
    At each step with survivor head `x`, take `x`, and sieve the tail `xs` by dropping every `x`-th element. -/
def ludicSieveSteps : Nat -> List Nat -> List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | steps + 1, x :: xs =>
    if x <= 1 then []
    else x :: ludicSieveSteps steps (dropEveryKth x xs)

/-- Ludic numbers up to `N` (OEIS A003309). -/
def ludicGeneratorsUpTo (N : Nat) : List Nat :=
  let seed := natSeedUpTo N
  ludicSieveSteps seed.length seed

/-- Josephus sieve execution: step `k` increments sequentially `2, 3, 4, ...`. -/
def josephusSieveSteps : Nat -> Nat -> List Nat -> List Nat
  | 0, _, xs => xs
  | steps + 1, k, xs =>
    if k > xs.length then xs
    else josephusSieveSteps steps (k + 1) (dropEveryKth k xs)

/-- Josephus sieve prefix up to `N` (OEIS A000960). -/
def josephusPrefixUpTo (N : Nat) : List Nat :=
  let seed := natRangeUpTo N
  josephusSieveSteps seed.length 2 seed

/-- Josephus Beurling generators up to `N` (excluding `1`). -/
def josephusGeneratorsUpTo (N : Nat) : List Nat :=
  (josephusPrefixUpTo N).filter (fun x => x > 1)

/-- Monotonicity: dropEveryKth does not increase list length. -/
theorem dropEveryKth_go_length (k : Nat) (idx : Nat) (xs : List Nat) :
    (dropEveryKth.go k idx xs).length ≤ xs.length := by
  induction xs generalizing idx with
  | nil =>
    dsimp [dropEveryKth.go]
    exact Nat.le_refl 0
  | cons y ys ih =>
    dsimp [dropEveryKth.go]
    split
    · have h := ih (idx + 1)
      omega
    · have h := ih (idx + 1)
      dsimp
      omega

theorem dropEveryKth_length (k : Nat) (xs : List Nat) :
    (dropEveryKth k xs).length ≤ xs.length := by
  dsimp [dropEveryKth]
  exact dropEveryKth_go_length k 1 xs

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

theorem dropEveryKth_sublist (k : Nat) (xs : List Nat) :
    ∀ x, x ∈ dropEveryKth k xs → x ∈ xs := by
  intro x hx
  exact dropEveryKth_go_sublist k 1 xs x hx

theorem luckyPrefixUpTo_50_eq :
    luckyPrefixUpTo 50 = [1, 3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49] := by
  rfl

theorem luckyGeneratorsUpTo_50_eq :
    luckyGeneratorsUpTo 50 = [3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49] := by
  rfl

theorem ludicGeneratorsUpTo_50_eq :
    ludicGeneratorsUpTo 50 = [2, 3, 5, 7, 11, 13, 17, 23, 25, 29, 37, 41, 43, 47] := by
  rfl

theorem ludicGeneratorsUpTo_50_length :
    (ludicGeneratorsUpTo 50).length = 14 := by
  rfl

theorem josephusPrefixUpTo_50_eq :
    josephusPrefixUpTo 50 = [1, 3, 7, 13, 19, 27, 39, 49] := by
  rfl

theorem josephusGeneratorsUpTo_50_eq :
    josephusGeneratorsUpTo 50 = [3, 7, 13, 19, 27, 39, 49] := by
  rfl

theorem josephusGeneratorsUpTo_50_length :
    (josephusGeneratorsUpTo 50).length = 7 := by
  rfl

set_option maxRecDepth 200000 in
theorem ludicGeneratorsUpTo_200_length :
    (ludicGeneratorsUpTo 200).length = 38 := by
  decide

set_option maxRecDepth 200000 in
theorem josephusGeneratorsUpTo_200_length :
    (josephusGeneratorsUpTo 200).length = 14 := by
  decide

end LeanAsm.QuasiRiemann.SieveSequence

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/SieveSequence/Core.lean
