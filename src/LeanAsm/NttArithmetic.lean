-- Path: leanasm/src/LeanAsm/NttArithmetic.lean
-- Number Theoretic Transform (NTT) butterfly arithmetic over Fermat prime p = 17 and F_5.
-- Demonstrates exact primitive roots, Cooley-Tukey butterfly, universal two-sided invertibility,
-- and the universal 4-point cyclic convolution theorem with ZERO axioms.
-- Max Column: 120 Columns

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
def nttButterfly2 (x0 x1 : Nat) (modP : Nat := 17) : Nat × Nat :=
  ((x0 + x1) % modP, (x0 + modP - (x1 % modP)) % modP)

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
-- 4-Point Radix-2 Cooley-Tukey NTT & Cyclic Convolution (gemweb024 & gemweb041)
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

/-- Canonical reduction of a Vec4 into F_p. -/
def normVec4 (p : Nat) (v : Vec4) : Vec4 :=
  ⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p⟩

/-- Pointwise (Hadamard) modular product of two 4-vectors in F_p. -/
def pointwiseMul4 (p : Nat) (u v : Vec4) : Vec4 :=
  ⟨(u.x0 * v.x0) % p, (u.x1 * v.x1) % p, (u.x2 * v.x2) % p, (u.x3 * v.x3) % p⟩

/--
4-Point Radix-2 Decimation-in-Time Cooley-Tukey Forward NTT parameterized by modulus p and root w:
- Stage 1: 2-point butterflies on even (x0, x2) and odd (x1, x3) indices.
- Stage 2: Twiddle multiplication by w and butterfly combination.
-/
def ntt4 (p : Nat) (w : Nat) (v : Vec4) : Vec4 :=
  let (e0, e1) := nttButterfly2 v.x0 v.x2 p
  let (o0, o1) := nttButterfly2 v.x1 v.x3 p
  let t0 := o0 % p
  let t1 := (o1 * w) % p
  ⟨(e0 + t0) % p, (e1 + t1) % p, (e0 + p - (t0 % p)) % p, (e1 + p - (t1 % p)) % p⟩

/--
4-Point Direct DFT Matrix Definition over F_17:
  X_k = ∑_{j=0}^3 x_j · ω4^(j·k) mod 17
-/
def dft4Direct (v : Vec4) : Vec4 :=
  let X0 := (v.x0 + v.x1 + v.x2 + v.x3) % p
  let X1 := (v.x0 + v.x1 * 13 + v.x2 * 16 + v.x3 * 4) % p
  let X2 := (v.x0 + v.x1 * 16 + v.x2 + v.x3 * 16) % p
  let X3 := (v.x0 + v.x1 * 4 + v.x2 * 16 + v.x3 * 13) % p
  ⟨X0, X1, X2, X3⟩

/--
4-Point Radix-2 Decimation-in-Time Inverse NTT parameterized by modulus p, inverse length inv4, and root invW:
- Stage 1: 2-point butterflies on (X0, X2) and (X1, X3).
- Stage 2: Twiddle multiplication with invW and combine.
- Scale each lane by inv4 modulo p.
-/
def intt4 (p : Nat) (inv4 invW : Nat) (X : Vec4) : Vec4 :=
  let (u0, u1) := nttButterfly2 X.x0 X.x2 p
  let (v0, v1) := nttButterfly2 X.x1 X.x3 p
  let w0 := v0 % p
  let w1 := (v1 * invW) % p
  ⟨((u0 + w0) * inv4) % p,
   ((u1 + w1) * inv4) % p,
   ((u0 + p - (w0 % p)) * inv4) % p,
   ((u1 + p - (w1 % p)) * inv4) % p⟩

/--
4-Point Cyclic Polynomial Convolution modulo (x^4 - 1, p):
  (a0 + a1 x + a2 x^2 + a3 x^3) * (b0 + b1 x + b2 x^2 + b3 x^3) mod (x^4 - 1, p)
-/
def cyclicConv4 (p : Nat) (a b : Vec4) : Vec4 :=
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
    ntt4 17 13 v = dft4Direct v := by
  decide

/--
Theorem: 4-Point NTT roundtrip invertibility on test vector (1, 2, 3, 4).
Proved constructively with ZERO axioms.
-/
theorem ntt4_roundtrip_concrete :
    let v : Vec4 := ⟨1, 2, 3, 4⟩
    intt4 17 13 4 (ntt4 17 13 v) = v := by
  decide

/--
Theorem (Cyclic Convolution Theorem over F_17):
Pointwise Hadamard product in the NTT domain reconstructs exact cyclic convolution
for inputs a = ⟨1, 2, 3, 4⟩ and b = ⟨5, 6, 7, 8⟩:
  intt4 17 13 4 (pointwiseMul4 17 (ntt4 17 13 a) (ntt4 17 13 b)) = cyclicConv4 17 a b = ⟨15, 0, 15, 9⟩
Proved constructively with ZERO axioms.
-/
theorem ntt4_cyclic_convolution_concrete :
    let a : Vec4 := ⟨1, 2, 3, 4⟩
    let b : Vec4 := ⟨5, 6, 7, 8⟩
    intt4 17 13 4 (pointwiseMul4 17 (ntt4 17 13 a) (ntt4 17 13 b)) = cyclicConv4 17 a b ∧
    cyclicConv4 17 a b = ⟨15, 0, 15, 9⟩ := by
  decide

-- =============================================================================
-- Universal NTT Soundness & Cyclic Convolution Theorems (gemweb041)
-- =============================================================================

/-- Equality helper for Vec4 components. -/
theorem vec4_eq_intro (u v : Vec4)
    (h0 : u.x0 = v.x0) (h1 : u.x1 = v.x1) (h2 : u.x2 = v.x2) (h3 : u.x3 = v.x3) :
    u = v := by
  cases u; cases v; congr

-- Modular congruence lemmas
theorem mod_sub_mod_eq5 (a b : Nat) : (a % 5 + 5 - b % 5 % 5) % 5 = (a + 5 - b % 5) % 5 := by
  rw [Nat.mod_mod]
  have ha : a = 5 * (a / 5) + a % 5 := (Nat.div_add_mod a 5).symm
  conv =>
    rhs
    rw [ha]
  omega

theorem mod_sub_mod_eq17 (a b : Nat) : (a % 17 + 17 - b % 17 % 17) % 17 = (a + 17 - b % 17) % 17 := by
  rw [Nat.mod_mod]
  have ha : a = 17 * (a / 17) + a % 17 := (Nat.div_add_mod a 17).symm
  conv =>
    rhs
    rw [ha]
  omega

theorem add_mod_4 (p u0 u1 u2 u3 : Nat) :
  (u0 + u1 + u2 + u3) % p = (u0 % p + u1 % p + u2 % p + u3 % p) % p := by
  rw [Nat.add_mod (u0 + u1 + u2) u3]
  rw [Nat.add_mod (u0 + u1) u2]
  rw [Nat.add_mod u0 u1]
  rw [Nat.add_mod (u0 % p + u1 % p + u2 % p) (u3 % p)]
  rw [Nat.add_mod (u0 % p + u1 % p) (u2 % p)]
  rw [Nat.add_mod (u0 % p) (u1 % p)]
  simp only [Nat.mod_mod]

theorem conv_term4_mod (p a0 b0 a1 b1 a2 b2 a3 b3 : Nat) :
  (a0 % p * (b0 % p) + a1 % p * (b1 % p) + a2 % p * (b2 % p) + a3 % p * (b3 % p)) % p =
  (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3) % p := by
  rw [add_mod_4 p (a0 % p * (b0 % p)) (a1 % p * (b1 % p)) (a2 % p * (b2 % p)) (a3 % p * (b3 % p))]
  rw [add_mod_4 p (a0 * b0) (a1 * b1) (a2 * b2) (a3 * b3)]
  rw [Nat.mul_mod a0 b0, Nat.mul_mod a1 b1, Nat.mul_mod a2 b2, Nat.mul_mod a3 b3]

-- Modular congruence lemmas
theorem ntt4_normVec4_F5 (a : Vec4) : ntt4 5 2 (normVec4 5 a) = ntt4 5 2 a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  dsimp [ntt4, nttButterfly2, normVec4]
  have h_add02 : (a0 % 5 + a2 % 5) % 5 = (a0 + a2) % 5 := by rw [← Nat.add_mod]
  have h_add13 : (a1 % 5 + a3 % 5) % 5 = (a1 + a3) % 5 := by rw [← Nat.add_mod]
  have h_sub02 : (a0 % 5 + 5 - a2 % 5 % 5) % 5 = (a0 + 5 - a2 % 5) % 5 := mod_sub_mod_eq5 a0 a2
  have h_sub13 : (a1 % 5 + 5 - a3 % 5 % 5) % 5 = (a1 + 5 - a3 % 5) % 5 := mod_sub_mod_eq5 a1 a3
  rw [h_add02, h_add13, h_sub02, h_sub13]

theorem ntt4_normVec4_F17 (a : Vec4) : ntt4 17 4 (normVec4 17 a) = ntt4 17 4 a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  dsimp [ntt4, nttButterfly2, normVec4]
  have h_add02 : (a0 % 17 + a2 % 17) % 17 = (a0 + a2) % 17 := by rw [← Nat.add_mod]
  have h_add13 : (a1 % 17 + a3 % 17) % 17 = (a1 + a3) % 17 := by rw [← Nat.add_mod]
  have h_sub02 : (a0 % 17 + 17 - a2 % 17 % 17) % 17 = (a0 + 17 - a2 % 17) % 17 := mod_sub_mod_eq17 a0 a2
  have h_sub13 : (a1 % 17 + 17 - a3 % 17 % 17) % 17 = (a1 + 17 - a3 % 17) % 17 := mod_sub_mod_eq17 a1 a3
  rw [h_add02, h_add13, h_sub02, h_sub13]

theorem intt4_normVec4_F5 (X : Vec4) : intt4 5 4 3 (normVec4 5 X) = intt4 5 4 3 X := by
  obtain ⟨x0, x1, x2, x3⟩ := X
  dsimp [intt4, nttButterfly2, normVec4]
  have h_add02 : (x0 % 5 + x2 % 5) % 5 = (x0 + x2) % 5 := by rw [← Nat.add_mod]
  have h_add13 : (x1 % 5 + x3 % 5) % 5 = (x1 + x3) % 5 := by rw [← Nat.add_mod]
  have h_sub02 : (x0 % 5 + 5 - x2 % 5 % 5) % 5 = (x0 + 5 - x2 % 5) % 5 := mod_sub_mod_eq5 x0 x2
  have h_sub13 : (x1 % 5 + 5 - x3 % 5 % 5) % 5 = (x1 + 5 - x3 % 5) % 5 := mod_sub_mod_eq5 x1 x3
  rw [h_add02, h_add13, h_sub02, h_sub13]

theorem intt4_normVec4_F17 (X : Vec4) : intt4 17 13 13 (normVec4 17 X) = intt4 17 13 13 X := by
  obtain ⟨x0, x1, x2, x3⟩ := X
  dsimp [intt4, nttButterfly2, normVec4]
  have h_add02 : (x0 % 17 + x2 % 17) % 17 = (x0 + x2) % 17 := by rw [← Nat.add_mod]
  have h_add13 : (x1 % 17 + x3 % 17) % 17 = (x1 + x3) % 17 := by rw [← Nat.add_mod]
  have h_sub02 : (x0 % 17 + 17 - x2 % 17 % 17) % 17 = (x0 + 17 - x2 % 17) % 17 := mod_sub_mod_eq17 x0 x2
  have h_sub13 : (x1 % 17 + 17 - x3 % 17 % 17) % 17 = (x1 + 17 - x3 % 17) % 17 := mod_sub_mod_eq17 x1 x3
  rw [h_add02, h_add13, h_sub02, h_sub13]

theorem cyclicConv4_normVec4_F5 (a b : Vec4) :
    cyclicConv4 5 (normVec4 5 a) (normVec4 5 b) = cyclicConv4 5 a b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  dsimp [cyclicConv4, normVec4]
  apply vec4_eq_intro
  · exact conv_term4_mod 5 a0 b0 a1 b3 a2 b2 a3 b1
  · exact conv_term4_mod 5 a0 b1 a1 b0 a2 b3 a3 b2
  · exact conv_term4_mod 5 a0 b2 a1 b1 a2 b0 a3 b3
  · exact conv_term4_mod 5 a0 b3 a1 b2 a2 b1 a3 b0

theorem cyclicConv4_normVec4_F17 (a b : Vec4) :
    cyclicConv4 17 (normVec4 17 a) (normVec4 17 b) = cyclicConv4 17 a b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  dsimp [cyclicConv4, normVec4]
  apply vec4_eq_intro
  · exact conv_term4_mod 17 a0 b0 a1 b3 a2 b2 a3 b1
  · exact conv_term4_mod 17 a0 b1 a1 b0 a2 b3 a3 b2
  · exact conv_term4_mod 17 a0 b2 a1 b1 a2 b0 a3 b3
  · exact conv_term4_mod 17 a0 b3 a1 b2 a2 b1 a3 b0

-- Forward NTT lane reductions
theorem ntt4_lane0_5 (v : Vec4) : (ntt4 5 2 v).x0 = (v.x0 + v.x1 + v.x2 + v.x3) % 5 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane1_5 (v : Vec4) : (ntt4 5 2 v).x1 = (v.x0 + 2 * v.x1 + 4 * v.x2 + 3 * v.x3) % 5 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane2_5 (v : Vec4) : (ntt4 5 2 v).x2 = (v.x0 + 4 * v.x1 + v.x2 + 4 * v.x3) % 5 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane3_5 (v : Vec4) : (ntt4 5 2 v).x3 = (v.x0 + 3 * v.x1 + 4 * v.x2 + 2 * v.x3) % 5 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane0_17 (v : Vec4) : (ntt4 17 4 v).x0 = (v.x0 + v.x1 + v.x2 + v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane1_17 (v : Vec4) : (ntt4 17 4 v).x1 = (v.x0 + 4 * v.x1 + 16 * v.x2 + 13 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane2_17 (v : Vec4) : (ntt4 17 4 v).x2 = (v.x0 + 16 * v.x1 + v.x2 + 16 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

theorem ntt4_lane3_17 (v : Vec4) : (ntt4 17 4 v).x3 = (v.x0 + 13 * v.x1 + 16 * v.x2 + 4 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

-- Inverse NTT lane reductions
theorem intt4_lane0_5 (X : Vec4) : (intt4 5 4 3 X).x0 = ((X.x0 + X.x1 + X.x2 + X.x3) * 4) % 5 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane1_5 (X : Vec4) : (intt4 5 4 3 X).x1 = ((X.x0 + 3 * X.x1 + 4 * X.x2 + 2 * X.x3) * 4) % 5 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane2_5 (X : Vec4) : (intt4 5 4 3 X).x2 = ((X.x0 + 4 * X.x1 + X.x2 + 4 * X.x3) * 4) % 5 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane3_5 (X : Vec4) : (intt4 5 4 3 X).x3 = ((X.x0 + 2 * X.x1 + 4 * X.x2 + 3 * X.x3) * 4) % 5 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane0_17 (X : Vec4) : (intt4 17 13 13 X).x0 = ((X.x0 + X.x1 + X.x2 + X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane1_17 (X : Vec4) : (intt4 17 13 13 X).x1 = ((X.x0 + 13 * X.x1 + 16 * X.x2 + 4 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane2_17 (X : Vec4) : (intt4 17 13 13 X).x2 = ((X.x0 + 16 * X.x1 + X.x2 + 16 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

theorem intt4_lane3_17 (X : Vec4) : (intt4 17 13 13 X).x3 = ((X.x0 + 4 * X.x1 + 16 * X.x2 + 13 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

-- Linear algebra roundtrip lemmas
theorem intt4_ntt4_lanes_5 (a0 a1 a2 a3 Y0 Y1 Y2 Y3 : Nat)
    (hy0 : Y0 = (a0 + a1 + a2 + a3) % 5)
    (hy1 : Y1 = (a0 + 2 * a1 + 4 * a2 + 3 * a3) % 5)
    (hy2 : Y2 = (a0 + 4 * a1 + a2 + 4 * a3) % 5)
    (hy3 : Y3 = (a0 + 3 * a1 + 4 * a2 + 2 * a3) % 5) :
    ((Y0 + Y1 + Y2 + Y3) * 4) % 5 = a0 % 5 ∧
    ((Y0 + 3 * Y1 + 4 * Y2 + 2 * Y3) * 4) % 5 = a1 % 5 ∧
    ((Y0 + 4 * Y1 + Y2 + 4 * Y3) * 4) % 5 = a2 % 5 ∧
    ((Y0 + 2 * Y1 + 4 * Y2 + 3 * Y3) * 4) % 5 = a3 % 5 := by
  have h0 : a0 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h1 : a1 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h2 : a2 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h3 : a3 % 5 < 5 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem ntt4_intt4_lanes_5 (y0 y1 y2 y3 X0 X1 X2 X3 : Nat)
    (hx0 : X0 = ((y0 + y1 + y2 + y3) * 4) % 5)
    (hx1 : X1 = ((y0 + 3 * y1 + 4 * y2 + 2 * y3) * 4) % 5)
    (hx2 : X2 = ((y0 + 4 * y1 + y2 + 4 * y3) * 4) % 5)
    (hx3 : X3 = ((y0 + 2 * y1 + 4 * y2 + 3 * y3) * 4) % 5) :
    (X0 + X1 + X2 + X3) % 5 = y0 % 5 ∧
    (X0 + 2 * X1 + 4 * X2 + 3 * X3) % 5 = y1 % 5 ∧
    (X0 + 4 * X1 + X2 + 4 * X3) % 5 = y2 % 5 ∧
    (X0 + 3 * X1 + 4 * X2 + 2 * X3) % 5 = y3 % 5 := by
  have h0 : y0 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h1 : y1 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h2 : y2 % 5 < 5 := Nat.mod_lt _ (by decide)
  have h3 : y3 % 5 < 5 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem intt4_ntt4_lanes_17 (a0 a1 a2 a3 Y0 Y1 Y2 Y3 : Nat)
    (hy0 : Y0 = (a0 + a1 + a2 + a3) % 17)
    (hy1 : Y1 = (a0 + 4 * a1 + 16 * a2 + 13 * a3) % 17)
    (hy2 : Y2 = (a0 + 16 * a1 + a2 + 16 * a3) % 17)
    (hy3 : Y3 = (a0 + 13 * a1 + 16 * a2 + 4 * a3) % 17) :
    ((Y0 + Y1 + Y2 + Y3) * 13) % 17 = a0 % 17 ∧
    ((Y0 + 13 * Y1 + 16 * Y2 + 4 * Y3) * 13) % 17 = a1 % 17 ∧
    ((Y0 + 16 * Y1 + Y2 + 16 * Y3) * 13) % 17 = a2 % 17 ∧
    ((Y0 + 4 * Y1 + 16 * Y2 + 13 * Y3) * 13) % 17 = a3 % 17 := by
  have h0 : a0 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h1 : a1 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h2 : a2 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h3 : a3 % 17 < 17 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem ntt4_intt4_lanes_17 (y0 y1 y2 y3 X0 X1 X2 X3 : Nat)
    (hx0 : X0 = ((y0 + y1 + y2 + y3) * 13) % 17)
    (hx1 : X1 = ((y0 + 13 * y1 + 16 * y2 + 4 * y3) * 13) % 17)
    (hx2 : X2 = ((y0 + 16 * y1 + y2 + 16 * y3) * 13) % 17)
    (hx3 : X3 = ((y0 + 4 * y1 + 16 * y2 + 13 * y3) * 13) % 17) :
    (X0 + X1 + X2 + X3) % 17 = y0 % 17 ∧
    (X0 + 4 * X1 + 16 * X2 + 13 * X3) % 17 = y1 % 17 ∧
    (X0 + 16 * X1 + X2 + 16 * X3) % 17 = y2 % 17 ∧
    (X0 + 13 * X1 + 16 * X2 + 4 * X3) % 17 = y3 % 17 := by
  have h0 : y0 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h1 : y1 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h2 : y2 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h3 : y3 % 17 < 17 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega, by omega⟩

/--
Theorem: Universal 2-sided NTT Inversion over F_5 (Forward then Inverse).
intt4 5 4 3 (ntt4 5 2 a) = normVec4 5 a for all a : Vec4.
Proved constructively with ZERO axioms.
-/
theorem intt4_ntt4_universal_F5 (a : Vec4) :
    intt4 5 4 3 (ntt4 5 2 a) = normVec4 5 a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  have hy0 := ntt4_lane0_5 ⟨a0, a1, a2, a3⟩
  have hy1 := ntt4_lane1_5 ⟨a0, a1, a2, a3⟩
  have hy2 := ntt4_lane2_5 ⟨a0, a1, a2, a3⟩
  have hy3 := ntt4_lane3_5 ⟨a0, a1, a2, a3⟩
  have hi0 := intt4_lane0_5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩)
  have hi1 := intt4_lane1_5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩)
  have hi2 := intt4_lane2_5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩)
  have hi3 := intt4_lane3_5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩)
  have h_comb := intt4_ntt4_lanes_5 a0 a1 a2 a3
    (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x0 (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x1
    (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x2 (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x3
    hy0 hy1 hy2 hy3
  apply vec4_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2

/--
Theorem: Universal 2-sided NTT Inversion over F_5 (Inverse then Forward).
ntt4 5 2 (intt4 5 4 3 y) = normVec4 5 y for all y : Vec4.
Proved constructively with ZERO axioms.
-/
theorem ntt4_intt4_universal_F5 (y : Vec4) :
    ntt4 5 2 (intt4 5 4 3 y) = normVec4 5 y := by
  obtain ⟨y0, y1, y2, y3⟩ := y
  have hx0 := intt4_lane0_5 ⟨y0, y1, y2, y3⟩
  have hx1 := intt4_lane1_5 ⟨y0, y1, y2, y3⟩
  have hx2 := intt4_lane2_5 ⟨y0, y1, y2, y3⟩
  have hx3 := intt4_lane3_5 ⟨y0, y1, y2, y3⟩
  have hn0 := ntt4_lane0_5 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩)
  have hn1 := ntt4_lane1_5 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩)
  have hn2 := ntt4_lane2_5 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩)
  have hn3 := ntt4_lane3_5 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩)
  have h_comb := ntt4_intt4_lanes_5 y0 y1 y2 y3
    (intt4 5 4 3 ⟨y0, y1, y2, y3⟩).x0 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩).x1
    (intt4 5 4 3 ⟨y0, y1, y2, y3⟩).x2 (intt4 5 4 3 ⟨y0, y1, y2, y3⟩).x3
    hx0 hx1 hx2 hx3
  apply vec4_eq_intro
  · rw [hn0]; exact h_comb.1
  · rw [hn1]; exact h_comb.2.1
  · rw [hn2]; exact h_comb.2.2.1
  · rw [hn3]; exact h_comb.2.2.2

/--
Theorem: Universal 2-sided NTT Inversion over F_17 (Forward then Inverse).
intt4 17 13 13 (ntt4 17 4 a) = normVec4 17 a for all a : Vec4.
Proved constructively with ZERO axioms.
-/
theorem intt4_ntt4_universal_F17 (a : Vec4) :
    intt4 17 13 13 (ntt4 17 4 a) = normVec4 17 a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  have hy0 := ntt4_lane0_17 ⟨a0, a1, a2, a3⟩
  have hy1 := ntt4_lane1_17 ⟨a0, a1, a2, a3⟩
  have hy2 := ntt4_lane2_17 ⟨a0, a1, a2, a3⟩
  have hy3 := ntt4_lane3_17 ⟨a0, a1, a2, a3⟩
  have hi0 := intt4_lane0_17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩)
  have hi1 := intt4_lane1_17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩)
  have hi2 := intt4_lane2_17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩)
  have hi3 := intt4_lane3_17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩)
  have h_comb := intt4_ntt4_lanes_17 a0 a1 a2 a3
    (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x0 (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x1
    (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x2 (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x3
    hy0 hy1 hy2 hy3
  apply vec4_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2

/--
Theorem: Universal 2-sided NTT Inversion over F_17 (Inverse then Forward).
ntt4 17 4 (intt4 17 13 13 y) = normVec4 17 y for all y : Vec4.
Proved constructively with ZERO axioms.
-/
theorem ntt4_intt4_universal_F17 (y : Vec4) :
    ntt4 17 4 (intt4 17 13 13 y) = normVec4 17 y := by
  obtain ⟨y0, y1, y2, y3⟩ := y
  have hx0 := intt4_lane0_17 ⟨y0, y1, y2, y3⟩
  have hx1 := intt4_lane1_17 ⟨y0, y1, y2, y3⟩
  have hx2 := intt4_lane2_17 ⟨y0, y1, y2, y3⟩
  have hx3 := intt4_lane3_17 ⟨y0, y1, y2, y3⟩
  have hn0 := ntt4_lane0_17 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩)
  have hn1 := ntt4_lane1_17 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩)
  have hn2 := ntt4_lane2_17 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩)
  have hn3 := ntt4_lane3_17 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩)
  have h_comb := ntt4_intt4_lanes_17 y0 y1 y2 y3
    (intt4 17 13 13 ⟨y0, y1, y2, y3⟩).x0 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩).x1
    (intt4 17 13 13 ⟨y0, y1, y2, y3⟩).x2 (intt4 17 13 13 ⟨y0, y1, y2, y3⟩).x3
    hx0 hx1 hx2 hx3
  apply vec4_eq_intro
  · rw [hn0]; exact h_comb.1
  · rw [hn1]; exact h_comb.2.1
  · rw [hn2]; exact h_comb.2.2.1
  · rw [hn3]; exact h_comb.2.2.2

-- Bilinear polynomial product expansions over F_5
theorem mul_mod_expand_lane0_5 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + a1 + a2 + a3) % 5 * ((b0 + b1 + b2 + b3) % 5)) % 5 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 5 := by
  have h_prod : ((a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3)) % 5 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 5 := by
    have h_exp : (a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3) =
      (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
       a1*b0 + a1*b1 + a1*b2 + a1*b3 +
       a2*b0 + a2*b1 + a2*b2 + a2*b3 +
       a3*b0 + a3*b1 + a3*b2 + a3*b3) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
    rw [h_exp]
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane1_5 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 2*a1 + 4*a2 + 3*a3) % 5 * ((b0 + 2*b1 + 4*b2 + 3*b3) % 5)) % 5 =
    (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 3*(a0*b3) +
     2*(a1*b0) + 4*(a1*b1) + 3*(a1*b2) + a1*b3 +
     4*(a2*b0) + 3*(a2*b1) + a2*b2 + 2*(a2*b3) +
     3*(a3*b0) + a3*b1 + 2*(a3*b2) + 4*(a3*b3)) % 5 := by
  have h_prod : ((a0 + 2*a1 + 4*a2 + 3*a3) * (b0 + 2*b1 + 4*b2 + 3*b3)) % 5 =
    (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 3*(a0*b3) +
     2*(a1*b0) + 4*(a1*b1) + 3*(a1*b2) + a1*b3 +
     4*(a2*b0) + 3*(a2*b1) + a2*b2 + 2*(a2*b3) +
     3*(a3*b0) + a3*b1 + 2*(a3*b2) + 4*(a3*b3)) % 5 := by
    have h_exp : (a0 + 2*a1 + 4*a2 + 3*a3) * (b0 + 2*b1 + 4*b2 + 3*b3) =
      (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 3*(a0*b3) +
       2*(a1*b0) + 4*(a1*b1) + 8*(a1*b2) + 6*(a1*b3) +
       4*(a2*b0) + 8*(a2*b1) + 16*(a2*b2) + 12*(a2*b3) +
       3*(a3*b0) + 6*(a3*b1) + 12*(a3*b2) + 9*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane2_5 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 4*a1 + a2 + 4*a3) % 5 * ((b0 + 4*b1 + b2 + 4*b3) % 5)) % 5 =
    (a0*b0 + 4*(a0*b1) + a0*b2 + 4*(a0*b3) +
     4*(a1*b0) + a1*b1 + 4*(a1*b2) + a1*b3 +
     a2*b0 + 4*(a2*b1) + a2*b2 + 4*(a2*b3) +
     4*(a3*b0) + a3*b1 + 4*(a3*b2) + a3*b3) % 5 := by
  have h_prod : ((a0 + 4*a1 + a2 + 4*a3) * (b0 + 4*b1 + b2 + 4*b3)) % 5 =
    (a0*b0 + 4*(a0*b1) + a0*b2 + 4*(a0*b3) +
     4*(a1*b0) + a1*b1 + 4*(a1*b2) + a1*b3 +
     a2*b0 + 4*(a2*b1) + a2*b2 + 4*(a2*b3) +
     4*(a3*b0) + a3*b1 + 4*(a3*b2) + a3*b3) % 5 := by
    have h_exp : (a0 + 4*a1 + a2 + 4*a3) * (b0 + 4*b1 + b2 + 4*b3) =
      (a0*b0 + 4*(a0*b1) + a0*b2 + 4*(a0*b3) +
       4*(a1*b0) + 16*(a1*b1) + 4*(a1*b2) + 16*(a1*b3) +
       a2*b0 + 4*(a2*b1) + a2*b2 + 4*(a2*b3) +
       4*(a3*b0) + 16*(a3*b1) + 4*(a3*b2) + 16*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane3_5 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 3*a1 + 4*a2 + 2*a3) % 5 * ((b0 + 3*b1 + 4*b2 + 2*b3) % 5)) % 5 =
    (a0*b0 + 3*(a0*b1) + 4*(a0*b2) + 2*(a0*b3) +
     3*(a1*b0) + 4*(a1*b1) + 2*(a1*b2) + a1*b3 +
     4*(a2*b0) + 2*(a2*b1) + a2*b2 + 3*(a2*b3) +
     2*(a3*b0) + a3*b1 + 3*(a3*b2) + 4*(a3*b3)) % 5 := by
  have h_prod : ((a0 + 3*a1 + 4*a2 + 2*a3) * (b0 + 3*b1 + 4*b2 + 2*b3)) % 5 =
    (a0*b0 + 3*(a0*b1) + 4*(a0*b2) + 2*(a0*b3) +
     3*(a1*b0) + 4*(a1*b1) + 2*(a1*b2) + a1*b3 +
     4*(a2*b0) + 2*(a2*b1) + a2*b2 + 3*(a2*b3) +
     2*(a3*b0) + a3*b1 + 3*(a3*b2) + 4*(a3*b3)) % 5 := by
    have h_exp : (a0 + 3*a1 + 4*a2 + 2*a3) * (b0 + 3*b1 + 4*b2 + 2*b3) =
      (a0*b0 + 3*(a0*b1) + 4*(a0*b2) + 2*(a0*b3) +
       3*(a1*b0) + 9*(a1*b1) + 12*(a1*b2) + 6*(a1*b3) +
       4*(a2*b0) + 12*(a2*b1) + 16*(a2*b2) + 8*(a2*b3) +
       2*(a3*b0) + 6*(a3*b1) + 8*(a3*b2) + 4*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem conv_all_lanes_5 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (P0 P1 P2 P3 : Nat)
    (hP0 : P0 % 5 = (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
      a1*b0 + a1*b1 + a1*b2 + a1*b3 +
      a2*b0 + a2*b1 + a2*b2 + a2*b3 +
      a3*b0 + a3*b1 + a3*b2 + a3*b3) % 5)
    (hP1 : P1 % 5 = (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 3*(a0*b3) +
      2*(a1*b0) + 4*(a1*b1) + 3*(a1*b2) + a1*b3 +
      4*(a2*b0) + 3*(a2*b1) + a2*b2 + 2*(a2*b3) +
      3*(a3*b0) + a3*b1 + 2*(a3*b2) + 4*(a3*b3)) % 5)
    (hP2 : P2 % 5 = (a0*b0 + 4*(a0*b1) + a0*b2 + 4*(a0*b3) +
      4*(a1*b0) + a1*b1 + 4*(a1*b2) + a1*b3 +
      a2*b0 + 4*(a2*b1) + a2*b2 + 4*(a2*b3) +
      4*(a3*b0) + a3*b1 + 4*(a3*b2) + a3*b3) % 5)
    (hP3 : P3 % 5 = (a0*b0 + 3*(a0*b1) + 4*(a0*b2) + 2*(a0*b3) +
      3*(a1*b0) + 4*(a1*b1) + 2*(a1*b2) + a1*b3 +
      4*(a2*b0) + 2*(a2*b1) + a2*b2 + 3*(a2*b3) +
      2*(a3*b0) + a3*b1 + 3*(a3*b2) + 4*(a3*b3)) % 5) :
    ((P0 + P1 + P2 + P3) * 4) % 5 = (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) % 5 ∧
    ((P0 + 3 * P1 + 4 * P2 + 2 * P3) * 4) % 5 = (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2) % 5 ∧
    ((P0 + 4 * P1 + P2 + 4 * P3) * 4) % 5 = (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) % 5 ∧
    ((P0 + 2 * P1 + 4 * P2 + 3 * P3) * 4) % 5 = (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 5 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/--
Theorem: Universal 4-Point NTT Cyclic Convolution Soundness over F_5.
intt4 5 4 3 (pointwiseMul4 5 (ntt4 5 2 a) (ntt4 5 2 b)) = cyclicConv4 5 a b for all a b : Vec4.
Proved constructively with ZERO axioms.
-/
theorem cyclic_conv4_ntt_universal_F5 (a b : Vec4) :
    intt4 5 4 3 (pointwiseMul4 5 (ntt4 5 2 a) (ntt4 5 2 b)) = cyclicConv4 5 a b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  have ha0 : (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x0 % 5 = (a0 + a1 + a2 + a3) % 5 := by dsimp [ntt4, nttButterfly2]; omega
  have ha1 : (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x1 % 5 = (a0 + 2 * a1 + 4 * a2 + 3 * a3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have ha2 : (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x2 % 5 = (a0 + 4 * a1 + a2 + 4 * a3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have ha3 : (ntt4 5 2 ⟨a0, a1, a2, a3⟩).x3 % 5 = (a0 + 3 * a1 + 4 * a2 + 2 * a3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb0 : (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x0 % 5 = (b0 + b1 + b2 + b3) % 5 := by dsimp [ntt4, nttButterfly2]; omega
  have hb1 : (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x1 % 5 = (b0 + 2 * b1 + 4 * b2 + 3 * b3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb2 : (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x2 % 5 = (b0 + 4 * b1 + b2 + 4 * b3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb3 : (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x3 % 5 = (b0 + 3 * b1 + 4 * b2 + 2 * b3) % 5 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hP0 : (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x0 % 5 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 5 := by
    change ((ntt4 5 2 ⟨a0, a1, a2, a3⟩).x0 * (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x0) % 5 % 5 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha0, hb0, mul_mod_expand_lane0_5]
  have hP1 : (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x1 % 5 =
    (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 3*(a0*b3) +
     2*(a1*b0) + 4*(a1*b1) + 3*(a1*b2) + a1*b3 +
     4*(a2*b0) + 3*(a2*b1) + a2*b2 + 2*(a2*b3) +
     3*(a3*b0) + a3*b1 + 2*(a3*b2) + 4*(a3*b3)) % 5 := by
    change ((ntt4 5 2 ⟨a0, a1, a2, a3⟩).x1 * (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x1) % 5 % 5 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha1, hb1, mul_mod_expand_lane1_5]
  have hP2 : (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x2 % 5 =
    (a0*b0 + 4*(a0*b1) + a0*b2 + 4*(a0*b3) +
     4*(a1*b0) + a1*b1 + 4*(a1*b2) + a1*b3 +
     a2*b0 + 4*(a2*b1) + a2*b2 + 4*(a2*b3) +
     4*(a3*b0) + a3*b1 + 4*(a3*b2) + a3*b3) % 5 := by
    change ((ntt4 5 2 ⟨a0, a1, a2, a3⟩).x2 * (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x2) % 5 % 5 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha2, hb2, mul_mod_expand_lane2_5]
  have hP3 : (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x3 % 5 =
    (a0*b0 + 3*(a0*b1) + 4*(a0*b2) + 2*(a0*b3) +
     3*(a1*b0) + 4*(a1*b1) + 2*(a1*b2) + a1*b3 +
     4*(a2*b0) + 2*(a2*b1) + a2*b2 + 3*(a2*b3) +
     2*(a3*b0) + a3*b1 + 3*(a3*b2) + 4*(a3*b3)) % 5 := by
    change ((ntt4 5 2 ⟨a0, a1, a2, a3⟩).x3 * (ntt4 5 2 ⟨b0, b1, b2, b3⟩).x3) % 5 % 5 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha3, hb3, mul_mod_expand_lane3_5]
  have hi0 := intt4_lane0_5 (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩))
  have hi1 := intt4_lane1_5 (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩))
  have hi2 := intt4_lane2_5 (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩))
  have hi3 := intt4_lane3_5 (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩))
  have h_comb := conv_all_lanes_5 a0 a1 a2 a3 b0 b1 b2 b3
    (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x0
    (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x1
    (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x2
    (pointwiseMul4 5 (ntt4 5 2 ⟨a0, a1, a2, a3⟩) (ntt4 5 2 ⟨b0, b1, b2, b3⟩)).x3
    hP0 hP1 hP2 hP3
  apply vec4_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2

-- Bilinear polynomial product expansions over F_17
theorem mul_mod_expand_lane0_17 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + a1 + a2 + a3) % 17 * ((b0 + b1 + b2 + b3) % 17)) % 17 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 17 := by
  have h_prod : ((a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3)) % 17 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 17 := by
    have h_exp : (a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3) =
      (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
       a1*b0 + a1*b1 + a1*b2 + a1*b3 +
       a2*b0 + a2*b1 + a2*b2 + a2*b3 +
       a3*b0 + a3*b1 + a3*b2 + a3*b3) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
    rw [h_exp]
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane1_17 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 4*a1 + 16*a2 + 13*a3) % 17 * ((b0 + 4*b1 + 16*b2 + 13*b3) % 17)) % 17 =
    (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) +
     4*(a1*b0) + 16*(a1*b1) + 13*(a1*b2) + (a1*b3) +
     16*(a2*b0) + 13*(a2*b1) + (a2*b2) + 4*(a2*b3) +
     13*(a3*b0) + (a3*b1) + 4*(a3*b2) + 16*(a3*b3)) % 17 := by
  have h_prod : ((a0 + 4*a1 + 16*a2 + 13*a3) * (b0 + 4*b1 + 16*b2 + 13*b3)) % 17 =
    (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) +
     4*(a1*b0) + 16*(a1*b1) + 13*(a1*b2) + (a1*b3) +
     16*(a2*b0) + 13*(a2*b1) + (a2*b2) + 4*(a2*b3) +
     13*(a3*b0) + (a3*b1) + 4*(a3*b2) + 16*(a3*b3)) % 17 := by
    have h_exp : (a0 + 4*a1 + 16*a2 + 13*a3) * (b0 + 4*b1 + 16*b2 + 13*b3) =
      (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) +
       4*(a1*b0) + 16*(a1*b1) + 64*(a1*b2) + 52*(a1*b3) +
       16*(a2*b0) + 64*(a2*b1) + 256*(a2*b2) + 208*(a2*b3) +
       13*(a3*b0) + 52*(a3*b1) + 208*(a3*b2) + 169*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane2_17 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 16*a1 + a2 + 16*a3) % 17 * ((b0 + 16*b1 + b2 + 16*b3) % 17)) % 17 =
    (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) +
     16*(a1*b0) + a1*b1 + 16*(a1*b2) + a1*b3 +
     a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) +
     16*(a3*b0) + a3*b1 + 16*(a3*b2) + a3*b3) % 17 := by
  have h_prod : ((a0 + 16*a1 + a2 + 16*a3) * (b0 + 16*b1 + b2 + 16*b3)) % 17 =
    (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) +
     16*(a1*b0) + a1*b1 + 16*(a1*b2) + a1*b3 +
     a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) +
     16*(a3*b0) + a3*b1 + 16*(a3*b2) + a3*b3) % 17 := by
    have h_exp : (a0 + 16*a1 + a2 + 16*a3) * (b0 + 16*b1 + b2 + 16*b3) =
      (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) +
       16*(a1*b0) + 256*(a1*b1) + 16*(a1*b2) + 256*(a1*b3) +
       a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) +
       16*(a3*b0) + 256*(a3*b1) + 16*(a3*b2) + 256*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem mul_mod_expand_lane3_17 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    ((a0 + 13*a1 + 16*a2 + 4*a3) % 17 * ((b0 + 13*b1 + 16*b2 + 4*b3) % 17)) % 17 =
    (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) +
     13*(a1*b0) + 16*(a1*b1) + 4*(a1*b2) + a1*b3 +
     16*(a2*b0) + 4*(a2*b1) + a2*b2 + 13*(a2*b3) +
     4*(a3*b0) + a3*b1 + 13*(a3*b2) + 16*(a3*b3)) % 17 := by
  have h_prod : ((a0 + 13*a1 + 16*a2 + 4*a3) * (b0 + 13*b1 + 16*b2 + 4*b3)) % 17 =
    (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) +
     13*(a1*b0) + 16*(a1*b1) + 4*(a1*b2) + a1*b3 +
     16*(a2*b0) + 4*(a2*b1) + a2*b2 + 13*(a2*b3) +
     4*(a3*b0) + a3*b1 + 13*(a3*b2) + 16*(a3*b3)) % 17 := by
    have h_exp : (a0 + 13*a1 + 16*a2 + 4*a3) * (b0 + 13*b1 + 16*b2 + 4*b3) =
      (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) +
       13*(a1*b0) + 169*(a1*b1) + 208*(a1*b2) + 52*(a1*b3) +
       16*(a2*b0) + 208*(a2*b1) + 256*(a2*b2) + 64*(a2*b3) +
       4*(a3*b0) + 52*(a3*b1) + 64*(a3*b2) + 16*(a3*b3)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]; ac_rfl
    rw [h_exp]
    omega
  rw [Nat.mul_mod] at h_prod
  exact h_prod

theorem conv_all_lanes_17 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat)
    (P0 P1 P2 P3 : Nat)
    (hP0 : P0 % 17 = (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
      a1*b0 + a1*b1 + a1*b2 + a1*b3 +
      a2*b0 + a2*b1 + a2*b2 + a2*b3 +
      a3*b0 + a3*b1 + a3*b2 + a3*b3) % 17)
    (hP1 : P1 % 17 = (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) +
      4*(a1*b0) + 16*(a1*b1) + 13*(a1*b2) + (a1*b3) +
      16*(a2*b0) + 13*(a2*b1) + (a2*b2) + 4*(a2*b3) +
      13*(a3*b0) + (a3*b1) + 4*(a3*b2) + 16*(a3*b3)) % 17)
    (hP2 : P2 % 17 = (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) +
      16*(a1*b0) + a1*b1 + 16*(a1*b2) + a1*b3 +
      a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) +
      16*(a3*b0) + a3*b1 + 16*(a3*b2) + a3*b3) % 17)
    (hP3 : P3 % 17 = (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) +
      13*(a1*b0) + 16*(a1*b1) + 4*(a1*b2) + a1*b3 +
      16*(a2*b0) + 4*(a2*b1) + a2*b2 + 13*(a2*b3) +
      4*(a3*b0) + a3*b1 + 13*(a3*b2) + 16*(a3*b3)) % 17) :
    ((P0 + P1 + P2 + P3) * 13) % 17 = (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) % 17 ∧
    ((P0 + 13 * P1 + 16 * P2 + 4 * P3) * 13) % 17 = (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2) % 17 ∧
    ((P0 + 16 * P1 + P2 + 16 * P3) * 13) % 17 = (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) % 17 ∧
    ((P0 + 4 * P1 + 16 * P2 + 13 * P3) * 13) % 17 = (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % 17 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/--
Theorem: Universal 4-Point NTT Cyclic Convolution Soundness over F_17.
intt4 17 13 13 (pointwiseMul4 17 (ntt4 17 4 a) (ntt4 17 4 b)) = cyclicConv4 17 a b for all a b : Vec4.
Proved constructively with ZERO axioms.
-/
theorem cyclic_conv4_ntt_universal_F17 (a b : Vec4) :
    intt4 17 13 13 (pointwiseMul4 17 (ntt4 17 4 a) (ntt4 17 4 b)) = cyclicConv4 17 a b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  have ha0 : (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x0 % 17 = (a0 + a1 + a2 + a3) % 17 := by dsimp [ntt4, nttButterfly2]; omega
  have ha1 : (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x1 % 17 = (a0 + 4 * a1 + 16 * a2 + 13 * a3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have ha2 : (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x2 % 17 = (a0 + 16 * a1 + a2 + 16 * a3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have ha3 : (ntt4 17 4 ⟨a0, a1, a2, a3⟩).x3 % 17 = (a0 + 13 * a1 + 16 * a2 + 4 * a3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb0 : (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x0 % 17 = (b0 + b1 + b2 + b3) % 17 := by dsimp [ntt4, nttButterfly2]; omega
  have hb1 : (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x1 % 17 = (b0 + 4 * b1 + 16 * b2 + 13 * b3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb2 : (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x2 % 17 = (b0 + 16 * b1 + b2 + 16 * b3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hb3 : (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x3 % 17 = (b0 + 13 * b1 + 16 * b2 + 4 * b3) % 17 := by
    dsimp [ntt4, nttButterfly2]; omega
  have hP0 : (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x0 % 17 =
    (a0*b0 + a0*b1 + a0*b2 + a0*b3 +
     a1*b0 + a1*b1 + a1*b2 + a1*b3 +
     a2*b0 + a2*b1 + a2*b2 + a2*b3 +
     a3*b0 + a3*b1 + a3*b2 + a3*b3) % 17 := by
    change ((ntt4 17 4 ⟨a0, a1, a2, a3⟩).x0 * (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x0) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha0, hb0, mul_mod_expand_lane0_17]
  have hP1 : (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x1 % 17 =
    (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) +
     4*(a1*b0) + 16*(a1*b1) + 13*(a1*b2) + (a1*b3) +
     16*(a2*b0) + 13*(a2*b1) + (a2*b2) + 4*(a2*b3) +
     13*(a3*b0) + (a3*b1) + 4*(a3*b2) + 16*(a3*b3)) % 17 := by
    change ((ntt4 17 4 ⟨a0, a1, a2, a3⟩).x1 * (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x1) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha1, hb1, mul_mod_expand_lane1_17]
  have hP2 : (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x2 % 17 =
    (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) +
     16*(a1*b0) + a1*b1 + 16*(a1*b2) + a1*b3 +
     a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) +
     16*(a3*b0) + a3*b1 + 16*(a3*b2) + a3*b3) % 17 := by
    change ((ntt4 17 4 ⟨a0, a1, a2, a3⟩).x2 * (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x2) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha2, hb2, mul_mod_expand_lane2_17]
  have hP3 : (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x3 % 17 =
    (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) +
     13*(a1*b0) + 16*(a1*b1) + 4*(a1*b2) + a1*b3 +
     16*(a2*b0) + 4*(a2*b1) + a2*b2 + 13*(a2*b3) +
     4*(a3*b0) + a3*b1 + 13*(a3*b2) + 16*(a3*b3)) % 17 := by
    change ((ntt4 17 4 ⟨a0, a1, a2, a3⟩).x3 * (ntt4 17 4 ⟨b0, b1, b2, b3⟩).x3) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha3, hb3, mul_mod_expand_lane3_17]
  have hi0 := intt4_lane0_17 (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩))
  have hi1 := intt4_lane1_17 (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩))
  have hi2 := intt4_lane2_17 (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩))
  have hi3 := intt4_lane3_17 (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩))
  have h_comb := conv_all_lanes_17 a0 a1 a2 a3 b0 b1 b2 b3
    (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x0
    (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x1
    (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x2
    (pointwiseMul4 17 (ntt4 17 4 ⟨a0, a1, a2, a3⟩) (ntt4 17 4 ⟨b0, b1, b2, b3⟩)).x3
    hP0 hP1 hP2 hP3
  apply vec4_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2

end NttArithmetic

-- end of file: leanasm/src/LeanAsm/NttArithmetic.lean
