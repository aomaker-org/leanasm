-- Path: leanasm/src/LeanAsm/Conjectures.lean
-- Mathematical explorations: Collatz sequence and arithmetic conjectures.
-- Max Column: 100 Columns

namespace Conjectures

/-- Step function for the Collatz (3n + 1) process. -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

/-- Iterate a function k times. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iterate f k (f x)

/-- Compute the Collatz trajectory up to a step limit. -/
def collatzTrajectory (n : Nat) (limit : Nat := 50) : List Nat :=
  loop n limit []
where
  loop (cur : Nat) (remaining : Nat) (acc : List Nat) : List Nat :=
    match remaining with
    | 0 => (cur :: acc).reverse
    | remaining' + 1 =>
      if cur ≤ 1 then
        (cur :: acc).reverse
      else
        loop (collatzStep cur) remaining' (cur :: acc)

/-- Formal statement: Collatz conjecture (every positive integer reaches 1). -/
def CollatzReachesOne (n : Nat) : Prop :=
  ∃ (k : Nat), iterate collatzStep k n = 1

-- Verified base cases: 1, 2, and 4 reach 1
theorem collatz_one_reaches_one : CollatzReachesOne 1 :=
  ⟨0, rfl⟩

theorem collatz_two_reaches_one : CollatzReachesOne 2 :=
  ⟨1, rfl⟩

theorem collatz_four_reaches_one : CollatzReachesOne 4 :=
  ⟨2, rfl⟩

end Conjectures

-- end of file: leanasm/src/LeanAsm/Conjectures.lean
