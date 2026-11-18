-- Path: leanasm/src/LeanAsm/Constants/PrimeTowers.lean
-- Certified Fermat and Proth prime towers, Garner inverses, and NTT twiddle parameters.
-- Max Column: 120 Columns

namespace LeanAsm.Constants.PrimeTowers

/-- Fermat primes `F_1 = 5`, `F_2 = 17`, `F_3 = 257`, `F_4 = 65537`. -/
def fermatTowerPrimes : List Nat := [5, 17, 257, 65537]

/-- Full 32-bit Fermat-prime factorization `[3, 5, 17, 257, 65537]` (`F_0..F_4`). -/
def fermatAllPrimes : List Nat := [3, 5, 17, 257, 65537]

/-- Exact 4-prime Fermat-tower CRT modulus `M_4 = 5 * 17 * 257 * 65537 = 1,431,655,765`. -/
def fermatTowerMod4 : Nat := 1431655765

/-- Canonical alias `M_4` for the 4-prime Fermat-tower CRT modulus. -/
def M_4 : Nat := fermatTowerMod4

/-- Proth prime `P_5 = 15 · 2^27 + 1 = 2,013,265,921`. -/
def prothPrime5 : Nat := 2013265921

/-- Canonical generator for Proth prime `P_5`: `prothGen = 40`. -/
def prothGen : Nat := 40

/-- Principal order-`2^27` twiddle root modulo `P_5`: `prothOmega27 = 440,564,289`. -/
def prothOmega27 : Nat := 440564289

/-- Order-4 twiddle root `ω₄ = 13` modulo 17. -/
def omega4 : Nat := 13

/-- Order-4 inverse twiddle root `ω₄⁻¹ = 4` modulo 17. -/
def invOmega4 : Nat := 4

/-- Scaling inverse `4⁻¹ ≡ 13` modulo 17. -/
def invFour : Nat := 13

/-- Order-8 twiddle root `ω₈ = 9` modulo 17. -/
def omega8 : Nat := 9

/-- Scaling inverse `8⁻¹ ≡ 15` modulo 17. -/
def inv8 : Nat := 15

/-- Modular inverse `2⁻¹ ≡ 9` modulo 17. -/
def invTwo : Nat := 9

/-- Scaling inverse `4⁻¹ ≡ 4` modulo 5. -/
def invFourMod5 : Nat := 4

/-- Garner mixed-radix step inverse `c12 = 5⁻¹ mod 17 = 7`. -/
def garnerInv12 : Nat := 7

/-- Garner mixed-radix step inverse `c123 = (5 · 17)⁻¹ mod 257 = 85⁻¹ mod 257 = 127`. -/
def garnerInv123 : Nat := 127

/-- Garner mixed-radix step inverse `c1234 = (5 · 17 · 257)⁻¹ mod 65537 = 21845⁻¹ mod 65537 = 32767`. -/
def garnerInv1234 : Nat := 32767

/-- Garner mixed-radix step inverse `M_4⁻¹ mod P_5 = 1431655765⁻¹ mod 2013265921 = 1327898798`. -/
def m4InvModP5 : Nat := 1327898798

/-- Sharp Fermat-Tower NTT convolution wrap-around ceiling for `N = 4`: `B ≤ 18918`. -/
def wrapBoundN4 : Nat := 18918

/-- Sharp Fermat-Tower NTT convolution wrap-around ceiling for `N = 8`: `B ≤ 13377`. -/
def wrapBoundN8 : Nat := 13377

/-- Sharp Fermat-Tower NTT convolution wrap-around ceiling for `N = 16`: `B ≤ 9459`. -/
def wrapBoundN16 : Nat := 9459

/-- Certified soundness theorems for Fermat tower modulus `M_4`. -/
theorem fermat_tower_mod4_certified :
    fermatTowerPrimes.prod = fermatTowerMod4 ∧
    fermatTowerMod4 = 5 * 17 * 257 * 65537 ∧
    3 * fermatTowerMod4 = 2 ^ 32 - 1 ∧
    2 ^ 30 < fermatTowerMod4 ∧ fermatTowerMod4 < 2 ^ 31 ∧
    (fermatTowerPrimes.map (· - 1)).prod = 2 ^ 30 := by
  decide

/-- Certified Garner mixed-radix inverses modulo Fermat primes. -/
theorem garner_inverses_certified :
    (5 * garnerInv12) % 17 = 1 ∧
    (85 * garnerInv123) % 257 = 1 ∧
    (21845 * garnerInv1234) % 65537 = 1 ∧
    (fermatTowerMod4 * m4InvModP5) % prothPrime5 = 1 := by
  decide

/-- Certified twiddle roots and scaling inverses modulo 17. -/
theorem twiddle_roots_sound :
    (omega4 ^ 4) % 17 = 1 ∧
    (omega4 ^ 2) % 17 = 16 ∧
    (omega4 * invOmega4) % 17 = 1 ∧
    (4 * invFour) % 17 = 1 ∧
    (omega8 ^ 8) % 17 = 1 ∧
    (omega8 ^ 4) % 17 = 16 ∧
    (8 * inv8) % 17 = 1 ∧
    (2 * invTwo) % 17 = 1 ∧
    (4 * invFourMod5) % 5 = 1 := by
  decide

/-- Certified sharp convolution wrap-around bounds against `M_4`. -/
theorem wrap_bounds_sharp_certified :
    4 * (wrapBoundN4 * wrapBoundN4) < fermatTowerMod4 ∧
    fermatTowerMod4 < 4 * ((wrapBoundN4 + 1) * (wrapBoundN4 + 1)) ∧
    8 * (wrapBoundN8 * wrapBoundN8) < fermatTowerMod4 ∧
    fermatTowerMod4 < 8 * ((wrapBoundN8 + 1) * (wrapBoundN8 + 1)) ∧
    16 * (wrapBoundN16 * wrapBoundN16) < fermatTowerMod4 ∧
    fermatTowerMod4 < 16 * ((wrapBoundN16 + 1) * (wrapBoundN16 + 1)) := by
  decide

/-- Certified Proth prime `P_5` arithmetic properties. -/
theorem proth_prime5_certified :
    prothPrime5 = 15 * 2 ^ 27 + 1 ∧
    prothPrime5 - 1 = 2 ^ 27 * 3 * 5 ∧
    Nat.gcd prothPrime5 fermatTowerMod4 = 1 ∧
    Nat.gcd prothPrime5 5 = 1 ∧ Nat.gcd prothPrime5 17 = 1 ∧
    Nat.gcd prothPrime5 257 = 1 ∧ Nat.gcd prothPrime5 65537 = 1 := by
  decide

end LeanAsm.Constants.PrimeTowers

-- end of file: leanasm/src/LeanAsm/Constants/PrimeTowers.lean
