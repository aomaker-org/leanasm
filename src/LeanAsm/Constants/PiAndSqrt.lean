-- Path: leanasm/src/LeanAsm/Constants/PiAndSqrt.lean
-- Certified Chudnovsky and Newton-Raphson high-precision π and √10005 constants.
-- Max Column: 120 Columns

namespace LeanAsm.Constants.PiAndSqrt

/-- Fuel-bounded integer square root via pure integer Newton-Raphson. -/
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

/-- Pure `Nat` integer square root floor without external module dependencies. -/
def isqrtExact (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let lg := fastLog2 n
    let x0 := 2 ^ (lg / 2 + 1)
    let x := isqrtNewtonLoop n x0 (lg + 16)
    if x * x ≤ n then x else x - 1

/-- Chudnovsky binary-splitting multiplier `c3Over24 = 640320^3 / 24 = 10,939,058,860,032,000`. -/
def c3Over24 : Nat := 10939058860032000

/-- Theorem: `c3Over24` matches `(640320 ^ 3) / 24`. -/
theorem c3Over24_eq : c3Over24 = (640320 ^ 3) / 24 := by decide

/-- Target integer for `10^110`-scaled `√10005`: `10005 * 10^220`. -/
def sqrtTarget : Nat := 10005 * 10 ^ 220

/-- Literal 113-digit floor of `√10005 · 10^110`. -/
def sqrt10005Scaled110Lit : Nat :=
  10002499687578100594479218787635777800159502436869631465713551156965096785386430429231118794849997329775519388936

/-- Canonical definition of `sqrt10005Scaled110`. -/
def sqrt10005Scaled110 : Nat := sqrt10005Scaled110Lit

set_option exponentiation.threshold 1024 in
/-- Constructive certification that `sqrt10005Scaled110` is the exact integer floor of `√sqrtTarget`. -/
theorem sqrt10005_scaled110_certified :
    sqrt10005Scaled110 * sqrt10005Scaled110 ≤ sqrtTarget ∧
    sqrtTarget < (sqrt10005Scaled110 + 1) * (sqrt10005Scaled110 + 1) := by
  decide

set_option exponentiation.threshold 1024 in
/-- Equivalence of literal `sqrt10005Scaled110` with pure Newton-Raphson `isqrtExact sqrtTarget`. -/
theorem sqrt10005Scaled110_eq_isqrtExact :
    sqrt10005Scaled110 = isqrtExact sqrtTarget := by
  decide

/-- Precomputed binary-split numerator `chud8Num` for depth `m = 8`. -/
def chud8Num : Nat :=
  32614881514393284608851638252219019170798745519488384554762110592 * 10 ^ 66 +
    133794678206118593505092366080624776302577232031445337440541309375

/-- Precomputed binary-split denominator `chud8Den` for depth `m = 8`. -/
def chud8Den : Nat :=
  2399668902200934240538265661362538479646144714727726081987941826880160606384643329140253260934807552 *
    10 ^ 24

/-- Precomputed binary-split numerator `chud9Num` for depth `m = 9`. -/
def chud9Num : Nat :=
  182669367602645889911511415273438529917392322081438861100790399677917911305 * 10 ^ 75 +
    727883231331950027409809863302556417910319853909370835473472908684927640625

/-- Precomputed binary-split denominator `chud9Den` for depth `m = 9`. -/
def chud9Den : Nat :=
  13440061115271369015863253016401336693262177401770588731235619168830270043112996002291656808041106707686617375571968 *
    10 ^ 27

/-- Literal 100 decimal digits of `π` (`⌊π · 10^100⌋`). -/
def piDigits100 : Nat :=
  31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679

/-- Literal 105-digit certified lower bound for `π * 10^105`. -/
def piLower105 : Nat :=
  3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148

/-- Literal 105-digit certified upper bound for `π * 10^105`. -/
def piUpper105 : Nat :=
  3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982149

/-- Literal 108-digit certified lower bound for `π * 10^108`. -/
def piLower108 : Nat :=
  3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148086

/-- Literal 108-digit certified upper bound for `π * 10^108`. -/
def piUpper108 : Nat :=
  3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148087

set_option exponentiation.threshold 1024 in
/-- Verification certificate: `piLower105` matches `(426880 * sqrt10005Scaled110 * chud9Den) / (10^5 * chud9Num)`. -/
theorem piLower105_certified :
    piLower105 = (426880 * sqrt10005Scaled110 * chud9Den) / (10 ^ 5 * chud9Num) := by
  decide

set_option exponentiation.threshold 1024 in
/-- Verification certificate: `piUpper105` matches the ceiling formula from `chud8`. -/
theorem piUpper105_certified :
    piUpper105 =
      (426880 * (sqrt10005Scaled110 + 1) * chud8Den + (10 ^ 5 * chud8Num - 1)) / (10 ^ 5 * chud8Num) := by
  decide

set_option exponentiation.threshold 1024 in
/-- Verification certificate: `piLower108` matches `(426880 * sqrt10005Scaled110 * chud9Den) / (10^2 * chud9Num)`. -/
theorem piLower108_certified :
    piLower108 = (426880 * sqrt10005Scaled110 * chud9Den) / (10 ^ 2 * chud9Num) := by
  decide

set_option exponentiation.threshold 1024 in
/-- Verification certificate: `piUpper108` matches the ceiling formula from `chud8`. -/
theorem piUpper108_certified :
    piUpper108 =
      (426880 * (sqrt10005Scaled110 + 1) * chud8Den + (10 ^ 2 * chud8Num - 1)) / (10 ^ 2 * chud8Num) := by
  decide

set_option exponentiation.threshold 1024 in
/-- Certified `10^105`-scale bracket ordering and tight width (`piUpper105 - piLower105 < 10^4`). -/
theorem pi_105_bracket_valid :
    piLower105 ≤ piUpper105 ∧ piUpper105 - piLower105 < 10 ^ 4 := by
  decide

set_option exponentiation.threshold 1024 in
/-- The 108-digit bracket `[piLower108, piUpper108]` has width `1` (`10^-108` ULP). -/
theorem pi_108_bracket_valid :
    piLower108 ≤ piUpper108 ∧ piUpper108 - piLower108 = 1 := by
  decide

set_option exponentiation.threshold 1024 in
/-- Exact decimal projection from 105-digit bounds to 100 digits of `π`. -/
theorem pi_100_digits_certified :
    piLower105 / 10 ^ 5 = piDigits100 ∧
    piUpper105 / 10 ^ 5 = piDigits100 ∧
    piDigits100 =
      314159265358979323846264338327950288419716939937510 * 10 ^ 50 +
      58209749445923078164062862089986280348253421170679 := by
  decide

end LeanAsm.Constants.PiAndSqrt

-- end of file: leanasm/src/LeanAsm/Constants/PiAndSqrt.lean
