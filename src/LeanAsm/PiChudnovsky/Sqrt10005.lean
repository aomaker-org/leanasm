-- Path: leanasm/src/LeanAsm/PiChudnovsky/Sqrt10005.lean
-- Stage 2 checkpoint: Constructive Newton-Raphson √10005 · 10^110 certification.
-- Max Column: 120 Columns

import LeanAsm.PiChudnovsky.CrtMulBridge

namespace PiChudnovsky

private def fastLog2Loop (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if n < 4294967296 then Nat.log2 n
      else 32 + fastLog2Loop (n / 4294967296) fuel'

private def fastLog2 (n : Nat) : Nat := fastLog2Loop n 64

private def isqrtNewtonLoop (n x fuel : Nat) : Nat :=
  match fuel with
  | 0 => x
  | fuel' + 1 =>
      if x = 0 then 0
      else
        let next := (x + n / x) / 2
        if x ≤ next then x else isqrtNewtonLoop n next fuel'

/-- Fuel-bounded Newton-Raphson integer square root backed by `natMulBigViaCrtNtt`
(`karatsubaCrtNttMul192` on `< 10^96` limbs) for the final square verification check. -/
def isqrtNewton (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let lg := fastLog2 n
    let x0 := 2 ^ (lg / 2 + 1)
    let x := isqrtNewtonLoop n x0 (lg + 16)
    if natMulBigViaCrtNtt x x ≤ n then x else x - 1

/-- Pure `Nat` mirror of `isqrtNewton` used to avoid unfolding CRT-NTT inside `decide`. -/
def isqrtExact (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let lg := fastLog2 n
    let x0 := 2 ^ (lg / 2 + 1)
    let x := isqrtNewtonLoop n x0 (lg + 16)
    if x * x ≤ n then x else x - 1

/-- Semantic equivalence allowing proofs to rewrite `isqrtNewton` to `isqrtExact`. -/
theorem isqrtNewton_eq_exact (n : Nat) : isqrtNewton n = isqrtExact n := by
  dsimp only [isqrtNewton, isqrtExact]
  rw [natMulBigViaCrtNtt_eq_mul]

/-- Scale `10^110` target used for `sqrt(10005 * 10^220)`. -/
def sqrtTarget : Nat := 10005 * 10 ^ 220

/-- 113-digit floor of `√10005 · 10^110` computed via `isqrtNewton`. -/
def sqrt10005Scaled110 : Nat := isqrtNewton sqrtTarget

set_option exponentiation.threshold 1024 in
/-- Constructive certification of the exact 113-digit floor bracket for `√10005 · 10^110`
via `natMul192ViaCrtNtt` with zero non-standard axioms. -/
theorem sqrt10005_scaled110_certified :
    natMul192ViaCrtNtt sqrt10005Scaled110 sqrt10005Scaled110 ≤ sqrtTarget ∧
    sqrtTarget < natMul192ViaCrtNtt (sqrt10005Scaled110 + 1) (sqrt10005Scaled110 + 1) := by
  dsimp only [sqrt10005Scaled110]
  rw [natMul192ViaCrtNtt_total_eq_mul, natMul192ViaCrtNtt_total_eq_mul, isqrtNewton_eq_exact]
  decide

set_option exponentiation.threshold 1024 in
/-- Explicit 96-digit-limb CRT-NTT certification of the `√10005 · 10^110` square root bracket
using `natMulBigViaCrtNtt` (`karatsubaCrtNttMul192` on `< 10^96` limbs). -/
theorem sqrt10005_scaled110_crt_limbs_certified :
    natMulBigViaCrtNtt sqrt10005Scaled110 sqrt10005Scaled110 ≤ sqrtTarget ∧
    sqrtTarget < natMulBigViaCrtNtt (sqrt10005Scaled110 + 1) (sqrt10005Scaled110 + 1) := by
  dsimp only [sqrt10005Scaled110]
  rw [natMulBigViaCrtNtt_eq_mul, natMulBigViaCrtNtt_eq_mul, isqrtNewton_eq_exact]
  decide

end PiChudnovsky

-- end of file: leanasm/src/LeanAsm/PiChudnovsky/Sqrt10005.lean
