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

-- =============================================================================
-- 4-Point Radix-2 Cooley-Tukey NTT & Cyclic Convolution (gemweb024)
-- =============================================================================

/-- Principal 4th root of unity modulo 17: ω4 = ω8^2 = 81 ≡ 13 (mod 17). -/
def omega4 : Nat := 13

/-- Inverse 4th root of unity modulo 17: ω4⁻¹ = ω4^3 ≡ 4 (mod 17). -/
def invOmega4 : Nat := 4

/-- Transform length scaling inverse: 4⁻¹ ≡ 13 (mod 17). -/
def invFour : Nat := 13

/-- 4-Vector structure over Nat. -/
structure Vec4 where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  deriving DecidableEq, Repr

/-- Canonical reduction of a Vec4 into F_17. -/
def normVec4 (v : Vec4) : Vec4 :=
  ⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p⟩

/-- Pointwise (Hadamard) modular product of two 4-vectors. -/
def pointwiseMul4 (u v : Vec4) : Vec4 :=
  ⟨(u.x0 * v.x0) % p, (u.x1 * v.x1) % p, (u.x2 * v.x2) % p, (u.x3 * v.x3) % p⟩

/--
4-Point Radix-2 Decimation-in-Time Cooley-Tukey Forward NTT:
- Stage 1: 2-point butterflies on even (x0, x2) and odd (x1, x3) indices.
- Stage 2: Twiddle multiplication (1, 13) and final butterfly combination.
-/
def ntt4 (v : Vec4) : Vec4 :=
  let (e0, e1) := nttButterfly2 v.x0 v.x2
  let (o0, o1) := nttButterfly2 v.x1 v.x3
  let t0 := o0 % p
  let t1 := (o1 * omega4) % p
  ⟨(e0 + t0) % p, (e1 + t1) % p, (e0 + p - t0) % p, (e1 + p - t1) % p⟩

/--
4-Point Direct DFT Matrix Definition:
  X_k = ∑_{j=0}^3 x_j · ω4^(j·k) mod 17
-/
def dft4Direct (v : Vec4) : Vec4 :=
  let X0 := (v.x0 + v.x1 + v.x2 + v.x3) % p
  let X1 := (v.x0 + v.x1 * 13 + v.x2 * 16 + v.x3 * 4) % p
  let X2 := (v.x0 + v.x1 * 16 + v.x2 + v.x3 * 16) % p
  let X3 := (v.x0 + v.x1 * 4 + v.x2 * 16 + v.x3 * 13) % p
  ⟨X0, X1, X2, X3⟩

/--
4-Point Radix-2 Decimation-in-Time Inverse NTT:
- Stage 1: 2-point butterflies on (X0, X2) and (X1, X3).
- Stage 2: Twiddle multiplication with ω4⁻¹ = 4 and combine.
- Scale each lane by 4⁻¹ ≡ 13 (mod 17).
-/
def intt4 (X : Vec4) : Vec4 :=
  let (u0, u1) := nttButterfly2 X.x0 X.x2
  let (v0, v1) := nttButterfly2 X.x1 X.x3
  let w0 := v0 % p
  let w1 := (v1 * invOmega4) % p
  ⟨((u0 + w0) * invFour) % p,
   ((u1 + w1) * invFour) % p,
   ((u0 + p - w0) * invFour) % p,
   ((u1 + p - w1) * invFour) % p⟩

/--
4-Point Cyclic Polynomial Convolution modulo (x^4 - 1, 17):
  (a0 + a1 x + a2 x^2 + a3 x^3) * (b0 + b1 x + b2 x^2 + b3 x^3) mod (x^4 - 1, 17)
-/
def cyclicConv4 (a b : Vec4) : Vec4 :=
  ⟨(a.x0 * b.x0 + a.x1 * b.x3 + a.x2 * b.x2 + a.x3 * b.x1) % p,
   (a.x0 * b.x1 + a.x1 * b.x0 + a.x2 * b.x3 + a.x3 * b.x2) % p,
   (a.x0 * b.x2 + a.x1 * b.x1 + a.x2 * b.x0 + a.x3 * b.x3) % p,
   (a.x0 * b.x3 + a.x1 * b.x2 + a.x2 * b.x1 + a.x3 * b.x0) % p⟩

/--
Theorem: 4th root of unity and modular inverse identities in F_17:
  13^4 ≡ 1 (mod 17)
  13^2 ≡ 16 ≡ -1 (mod 17)
  1 + 13 + 16 + 4 ≡ 0 (mod 17) (orthogonality)
  13 * 4 ≡ 1 (mod 17) (root inverse)
  4 * 13 ≡ 1 (mod 17) (scaling inverse)
Proved constructively with ZERO axioms.
-/
theorem ntt4_fourth_roots_sound :
    (omega4 ^ 4) % p = 1 ∧
    (omega4 ^ 2) % p = 16 ∧
    (1 + omega4 + 16 + invOmega4) % p = 0 ∧
    (omega4 * invOmega4) % p = 1 ∧
    (4 * invFour) % p = 1 := by
  decide

/--
Theorem: 4-Point Cooley-Tukey NTT matches direct DFT on concrete test vector (1, 2, 3, 4).
Proved constructively with ZERO axioms.
-/
theorem ntt4_equals_direct_dft_concrete :
    let v : Vec4 := ⟨1, 2, 3, 4⟩
    ntt4 v = dft4Direct v := by
  decide

/--
Theorem: 4-Point NTT roundtrip invertibility on test vector (1, 2, 3, 4).
Proved constructively with ZERO axioms.
-/
theorem ntt4_roundtrip_concrete :
    let v : Vec4 := ⟨1, 2, 3, 4⟩
    intt4 (ntt4 v) = v := by
  decide

/--
Theorem (Cyclic Convolution Theorem over F_17):
Pointwise Hadamard product in the NTT domain reconstructs exact cyclic convolution
for inputs a = ⟨1, 2, 3, 4⟩ and b = ⟨5, 6, 7, 8⟩:
  intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b = ⟨15, 0, 15, 9⟩
Proved constructively with ZERO axioms.
-/
theorem ntt4_cyclic_convolution_concrete :
    let a : Vec4 := ⟨1, 2, 3, 4⟩
    let b : Vec4 := ⟨5, 6, 7, 8⟩
    intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b ∧
    cyclicConv4 a b = ⟨15, 0, 15, 9⟩ := by
  decide

end NttArithmetic

-- end of file: leanasm/src/LeanAsm/NttArithmetic.lean
