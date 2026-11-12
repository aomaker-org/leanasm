-- Path: leanasm/src/LeanAsm/NttArithmetic.lean
-- Number Theoretic Transform (NTT) butterfly arithmetic over Fermat prime p = 17.
-- Demonstrates exact primitive roots and Cooley-Tukey butterfly with ZERO axioms.
-- Max Column: 100 Columns

namespace NttArithmetic

/-- Fermat prime modulus p = 2^(2^2) + 1 = 17. -/
def p : Nat := 17

/-- Primitive root modulo 17: g = 3. -/
def g : Nat := 3

/-- Principal 8-th root of unity modulo 17: ω = g^2 = 9. -/
def omega8 : Nat := 9

/-- Modular inverse of 2 modulo 17: 2 * 9 = 18 ≡ 1 (mod 17). -/
def invTwo : Nat := 9

/--
Radix-2 Cooley-Tukey NTT Forward Butterfly:
  (x0, x1) ↦ ((x0 + x1) % p, (x0 + p - (x1 % p)) % p)
-/
def nttButterfly2 (x0 x1 : Nat) : Nat × Nat :=
  ((x0 + x1) % p, (x0 + p - (x1 % p)) % p)

/--
Radix-2 Cooley-Tukey INTT Inverse Butterfly:
  (X0, X1) ↦ (((X0 + X1) * invTwo) % p, ((X0 + p - (X1 % p)) * invTwo) % p)
-/
def inttButterfly2 (X0 X1 : Nat) : Nat × Nat :=
  let s0 := (X0 + X1) % p
  let s1 := (X0 + p - (X1 % p)) % p
  ((s0 * invTwo) % p, (s1 * invTwo) % p)

-- =============================================================================
-- Formally Verified Theorems about NTT over F_17 (ZERO AXIOMS)
-- =============================================================================

/--
Theorem: Primitive root order and 8th root of unity properties modulo 17:
  3^16 ≡ 1 (mod 17)
  ω^8 = 9^8 ≡ 1 (mod 17)
  ω^4 = 9^4 ≡ 16 ≡ -1 (mod 17)
  2 * invTwo ≡ 1 (mod 17)
Proved constructively with ZERO axioms.
-/
theorem ntt_roots_of_unity_sound :
    (3 ^ 16) % 17 = 1 ∧
    (omega8 ^ 8) % 17 = 1 ∧
    (omega8 ^ 4) % 17 = 16 ∧
    (2 * invTwo) % 17 = 1 := by
  decide

/--
Theorem (NTT Radix-2 Butterfly Concrete Roundtrip):
Applying forward butterfly then inverse butterfly recovers the exact original inputs (5, 12).
Proved constructively with ZERO axioms.
-/
theorem ntt_butterfly2_roundtrip_5_12 :
    let (X0, X1) := nttButterfly2 5 12
    inttButterfly2 X0 X1 = (5, 12) := by
  decide

/--
Theorem (Full Search 2-Point Roundtrip Invertibility):
For all input pairs (x0, x1) in F_17, inttButterfly2 (nttButterfly2 x0 x1) = (x0, x1).
Proved constructively with ZERO axioms via decide.
-/
theorem ntt_butterfly2_sound_all_pairs :
    ∀ x0 < 17, ∀ x1 < 17,
      let (X0, X1) := nttButterfly2 x0 x1
      inttButterfly2 X0 X1 = (x0, x1) := by
  decide

end NttArithmetic

-- end of file: leanasm/src/LeanAsm/NttArithmetic.lean
