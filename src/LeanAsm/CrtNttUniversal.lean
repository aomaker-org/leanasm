-- Path: leanasm/src/LeanAsm/CrtNttUniversal.lean
-- Universal 16-Point NTT Inversion, Cyclic Convolution, 48-Digit crtNttBigMul_universal_sound,
-- and 96-Digit 2x2 Karatsuba-over-CRT-NTT Multiplier (gemweb042 Stage 2 & Stage 3).

import LeanAsm.CrtNtt
import LeanAsm.EulerFactorNonVanishing

namespace CrtNtt

-- =============================================================================
-- Part E: Universal 16-Point NTT Inversion, Cyclic Convolution, and
--         End-to-End 48-Digit crtNttBigMul_universal_sound (gemweb042 Stage 2)
-- =============================================================================

/-- Canonical componentwise modular reduction of Vec16 modulo p. -/
def normVec16 (p : Nat) (v : Vec16) : Vec16 :=
  ⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p,
   v.x4 % p, v.x5 % p, v.x6 % p, v.x7 % p,
   v.x8 % p, v.x9 % p, v.x10 % p, v.x11 % p,
   v.x12 % p, v.x13 % p, v.x14 % p, v.x15 % p⟩

/-- Componentwise addition on Vec16. -/
def addVec16 (u v : Vec16) : Vec16 :=
  ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3,
   u.x4 + v.x4, u.x5 + v.x5, u.x6 + v.x6, u.x7 + v.x7,
   u.x8 + v.x8, u.x9 + v.x9, u.x10 + v.x10, u.x11 + v.x11,
   u.x12 + v.x12, u.x13 + v.x13, u.x14 + v.x14, u.x15 + v.x15⟩

/-- Scalar multiplication on Vec16. -/
def scaleVec16 (c : Nat) (v : Vec16) : Vec16 :=
  ⟨c * v.x0, c * v.x1, c * v.x2, c * v.x3,
   c * v.x4, c * v.x5, c * v.x6, c * v.x7,
   c * v.x8, c * v.x9, c * v.x10, c * v.x11,
   c * v.x12, c * v.x13, c * v.x14, c * v.x15⟩

/-- Unreduced pointwise product on Vec16. -/
def pointwiseMul16Raw (u v : Vec16) : Vec16 :=
  ⟨u.x0 * v.x0, u.x1 * v.x1, u.x2 * v.x2, u.x3 * v.x3,
   u.x4 * v.x4, u.x5 * v.x5, u.x6 * v.x6, u.x7 * v.x7,
   u.x8 * v.x8, u.x9 * v.x9, u.x10 * v.x10, u.x11 * v.x11,
   u.x12 * v.x12, u.x13 * v.x13, u.x14 * v.x14, u.x15 * v.x15⟩

/-- Standard basis vector e_i in Vec16 for i < 16. -/
def basisVec16 (i : Nat) : Vec16 :=
  ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0,
   if i = 2 then 1 else 0, if i = 3 then 1 else 0,
   if i = 4 then 1 else 0, if i = 5 then 1 else 0,
   if i = 6 then 1 else 0, if i = 7 then 1 else 0,
   if i = 8 then 1 else 0, if i = 9 then 1 else 0,
   if i = 10 then 1 else 0, if i = 11 then 1 else 0,
   if i = 12 then 1 else 0, if i = 13 then 1 else 0,
   if i = 14 then 1 else 0, if i = 15 then 1 else 0⟩

/-- Unreduced Nat butterfly corresponding to butterflyWithTwiddle mod p. -/
def rawBfly (u v w nw : Nat) : Nat × Nat :=
  (u + w * v, u + nw * v)

/-- Unreduced 4-stage Cooley-Tukey 16-point NTT over Nat. -/
def ntt16Raw (w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 : Nat)
    (v : Vec16) : Vec16 :=
  let (s1_0,  s1_1)  := rawBfly v.x0  v.x8  w0 nw0
  let (s1_2,  s1_3)  := rawBfly v.x4  v.x12 w0 nw0
  let (s1_4,  s1_5)  := rawBfly v.x2  v.x10 w0 nw0
  let (s1_6,  s1_7)  := rawBfly v.x6  v.x14 w0 nw0
  let (s1_8,  s1_9)  := rawBfly v.x1  v.x9  w0 nw0
  let (s1_10, s1_11) := rawBfly v.x5  v.x13 w0 nw0
  let (s1_12, s1_13) := rawBfly v.x3  v.x11 w0 nw0
  let (s1_14, s1_15) := rawBfly v.x7  v.x15 w0 nw0
  let (s2_0,  s2_2)  := rawBfly s1_0  s1_2  w0 nw0
  let (s2_1,  s2_3)  := rawBfly s1_1  s1_3  w4 nw4
  let (s2_4,  s2_6)  := rawBfly s1_4  s1_6  w0 nw0
  let (s2_5,  s2_7)  := rawBfly s1_5  s1_7  w4 nw4
  let (s2_8,  s2_10) := rawBfly s1_8  s1_10 w0 nw0
  let (s2_9,  s2_11) := rawBfly s1_9  s1_11 w4 nw4
  let (s2_12, s2_14) := rawBfly s1_12 s1_14 w0 nw0
  let (s2_13, s2_15) := rawBfly s1_13 s1_15 w4 nw4
  let (s3_0,  s3_4)  := rawBfly s2_0  s2_4  w0 nw0
  let (s3_1,  s3_5)  := rawBfly s2_1  s2_5  w2 nw2
  let (s3_2,  s3_6)  := rawBfly s2_2  s2_6  w4 nw4
  let (s3_3,  s3_7)  := rawBfly s2_3  s2_7  w6 nw6
  let (s3_8,  s3_12) := rawBfly s2_8  s2_12 w0 nw0
  let (s3_9,  s3_13) := rawBfly s2_9  s2_13 w2 nw2
  let (s3_10, s3_14) := rawBfly s2_10 s2_14 w4 nw4
  let (s3_11, s3_15) := rawBfly s2_11 s2_15 w6 nw6
  let (s4_0, s4_8)   := rawBfly s3_0  s3_8  w0 nw0
  let (s4_1, s4_9)   := rawBfly s3_1  s3_9  w1 nw1
  let (s4_2, s4_10)  := rawBfly s3_2  s3_10 w2 nw2
  let (s4_3, s4_11)  := rawBfly s3_3  s3_11 w3 nw3
  let (s4_4, s4_12)  := rawBfly s3_4  s3_12 w4 nw4
  let (s4_5, s4_13)  := rawBfly s3_5  s3_13 w5 nw5
  let (s4_6, s4_14)  := rawBfly s3_6  s3_14 w6 nw6
  let (s4_7, s4_15)  := rawBfly s3_7  s3_15 w7 nw7
  ⟨s4_0, s4_1, s4_2, s4_3, s4_4, s4_5, s4_6, s4_7,
   s4_8, s4_9, s4_10, s4_11, s4_12, s4_13, s4_14, s4_15⟩

/-- Unreduced 16-point inverse NTT over Nat. -/
def intt16Raw
    (iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (v : Vec16) : Vec16 :=
  scaleVec16 inv16
    (ntt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 v)

/-- Componentwise normVec16 equality helper. -/
theorem normVec16_eq_of_comps (p : Nat) (u v : Vec16)
    (h0 : u.x0 % p = v.x0 % p) (h1 : u.x1 % p = v.x1 % p)
    (h2 : u.x2 % p = v.x2 % p) (h3 : u.x3 % p = v.x3 % p)
    (h4 : u.x4 % p = v.x4 % p) (h5 : u.x5 % p = v.x5 % p)
    (h6 : u.x6 % p = v.x6 % p) (h7 : u.x7 % p = v.x7 % p)
    (h8 : u.x8 % p = v.x8 % p) (h9 : u.x9 % p = v.x9 % p)
    (h10 : u.x10 % p = v.x10 % p) (h11 : u.x11 % p = v.x11 % p)
    (h12 : u.x12 % p = v.x12 % p) (h13 : u.x13 % p = v.x13 % p)
    (h14 : u.x14 % p = v.x14 % p) (h15 : u.x15 % p = v.x15 % p) :
    normVec16 p u = normVec16 p v := by
  dsimp [normVec16]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

/-- Scalar modular congruence helpers (non-looping). -/
theorem add_mod_congr (p a1 a2 b1 b2 : Nat)
    (h1 : a1 % p = a2 % p) (h2 : b1 % p = b2 % p) :
    (a1 + b1) % p = (a2 + b2) % p := by
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

theorem mul_mod_congr (p a1 a2 b1 b2 : Nat)
    (h1 : a1 % p = a2 % p) (h2 : b1 % p = b2 % p) :
    (a1 * b1) % p = (a2 * b2) % p := by
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem mul_const_mod_congr (p c a1 a2 : Nat) (h : a1 % p = a2 % p) :
    (c * a1) % p = (c * a2) % p := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- Norm congruence for addVec16. -/
theorem normVec16_add_congr (p : Nat) (u1 u2 v1 v2 : Vec16)
    (h1 : normVec16 p u1 = normVec16 p v1)
    (h2 : normVec16 p u2 = normVec16 p v2) :
    normVec16 p (addVec16 u1 u2) = normVec16 p (addVec16 v1 v2) := by
  refine normVec16_eq_of_comps p _ _
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x0 h1) (congrArg Vec16.x0 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x1 h1) (congrArg Vec16.x1 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x2 h1) (congrArg Vec16.x2 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x3 h1) (congrArg Vec16.x3 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x4 h1) (congrArg Vec16.x4 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x5 h1) (congrArg Vec16.x5 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x6 h1) (congrArg Vec16.x6 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x7 h1) (congrArg Vec16.x7 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x8 h1) (congrArg Vec16.x8 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x9 h1) (congrArg Vec16.x9 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x10 h1) (congrArg Vec16.x10 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x11 h1) (congrArg Vec16.x11 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x12 h1) (congrArg Vec16.x12 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x13 h1) (congrArg Vec16.x13 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x14 h1) (congrArg Vec16.x14 h2))
    (add_mod_congr p _ _ _ _ (congrArg Vec16.x15 h1) (congrArg Vec16.x15 h2))

/-- Norm congruence for scaleVec16. -/
theorem normVec16_scale_congr (p c : Nat) (u v : Vec16)
    (h : normVec16 p u = normVec16 p v) :
    normVec16 p (scaleVec16 c u) = normVec16 p (scaleVec16 c v) := by
  refine normVec16_eq_of_comps p _ _
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x0 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x1 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x2 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x3 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x4 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x5 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x6 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x7 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x8 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x9 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x10 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x11 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x12 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x13 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x14 h))
    (mul_const_mod_congr p c _ _ (congrArg Vec16.x15 h))

/-- Norm congruence for pointwiseMul16Mod vs pointwiseMul16Raw. -/
theorem pointwiseMul16Mod_norm_eq (p : Nat) (u u' v v' : Vec16)
    (hu : normVec16 p u = normVec16 p u')
    (hv : normVec16 p v = normVec16 p v') :
    pointwiseMul16Mod p u v = normVec16 p (pointwiseMul16Raw u' v') := by
  dsimp only [pointwiseMul16Mod, normVec16, pointwiseMul16Raw]
  congr 1
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x0 hu) (congrArg Vec16.x0 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x1 hu) (congrArg Vec16.x1 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x2 hu) (congrArg Vec16.x2 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x3 hu) (congrArg Vec16.x3 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x4 hu) (congrArg Vec16.x4 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x5 hu) (congrArg Vec16.x5 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x6 hu) (congrArg Vec16.x6 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x7 hu) (congrArg Vec16.x7 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x8 hu) (congrArg Vec16.x8 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x9 hu) (congrArg Vec16.x9 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x10 hu) (congrArg Vec16.x10 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x11 hu) (congrArg Vec16.x11 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x12 hu) (congrArg Vec16.x12 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x13 hu) (congrArg Vec16.x13 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x14 hu) (congrArg Vec16.x14 hv)
  · exact mul_mod_congr p _ _ _ _ (congrArg Vec16.x15 hu) (congrArg Vec16.x15 hv)

/-- Modular equivalence of a single radix-2 butterfly vs rawBfly. -/
theorem bfly_pair_mod (p u u' v v' w nw : Nat)
    (hp : 0 < p) (hnw : (w + nw) % p = 0)
    (hu : u % p = u' % p) (hv : v % p = v' % p) :
    (butterflyWithTwiddle p u v w).1 % p = (rawBfly u' v' w nw).1 % p ∧
    (butterflyWithTwiddle p u v w).2 % p = (rawBfly u' v' w nw).2 % p := by
  dsimp [butterflyWithTwiddle, rawBfly]
  constructor
  · rw [Nat.mod_mod]
    rw [Nat.add_mod u ((v * w) % p) p, Nat.mod_mod]
    rw [Nat.mul_mod v w p, hv, ← Nat.mul_mod v' w p]
    rw [hu, ← Nat.add_mod u' (v' * w) p, Nat.mul_comm v' w]
  · rw [Nat.mod_mod]
    let t := (v * w) % p
    have ht : t < p := Nat.mod_lt (v * w) hp
    have ht_mod : t % p = t := Nat.mod_eq_of_lt ht
    change (u + p - t % p) % p = (u' + nw * v') % p
    rw [ht_mod]
    have hsum : (t + nw * v) % p = 0 := by
      dsimp only [t]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod (v * w) (nw * v) p]
      have hfac : v * w + nw * v = v * (w + nw) := by rw [Nat.mul_add, Nat.mul_comm nw v]
      rw [hfac, Nat.mul_mod, hnw, Nat.mul_zero, Nat.zero_mod]
    have hsub : (u + p - t) % p = (u + nw * v) % p := by
      by_cases ht0 : t = 0
      · rw [ht0, Nat.sub_zero, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
        rw [ht0, Nat.zero_add] at hsum
        rw [Nat.add_mod u (nw * v) p, hsum, Nat.add_zero, Nat.mod_mod]
      · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
        let r := (nw * v) % p
        have hr : r < p := Nat.mod_lt (nw * v) hp
        have htr0 : (t + r) % p = 0 := by
          have hr_mod : r % p = (nw * v) % p := Nat.mod_mod _ _
          rw [Nat.add_mod, hr_mod, ← Nat.add_mod]
          exact hsum
        have htr_eq : t + r = p := by
          have hd := Nat.div_add_mod (t + r) p
          rw [htr0, Nat.add_zero] at hd
          match hq : (t + r) / p with
          | 0 =>
            rw [hq, Nat.mul_zero] at hd
            exact absurd hd.symm (Nat.ne_of_gt (Nat.add_pos_left htpos r))
          | 1 =>
            rw [hq, Nat.mul_one] at hd
            exact hd.symm
          | k + 2 =>
            rw [hq] at hd
            have hlt2 : t + r < p * (k + 2) := by
              have hpp : t + r < p + p := Nat.add_lt_add ht hr
              have hmul : p * (k + 2) = p * k + (p + p) := by
                rw [Nat.mul_add, Nat.mul_comm p 2, Nat.two_mul]
              rw [hmul]
              exact Nat.lt_of_lt_of_le hpp (Nat.le_add_left _ _)
            exact absurd hd (Nat.ne_of_gt hlt2)
        have hpt : p - t = r := by omega
        rw [Nat.add_sub_assoc (Nat.le_of_lt ht) u, hpt]
        dsimp only [r]
        rw [Nat.add_mod u ((nw * v) % p) p, Nat.mod_mod, ← Nat.add_mod u (nw * v) p]
    rw [hsub]
    rw [Nat.add_mod u (nw * v) p, hu, Nat.mul_mod nw v p, hv]
    rw [← Nat.mul_mod nw v' p, ← Nat.add_mod u' (nw * v') p]

/-- Exact modular equivalence between ntt16WithRoots and ntt16Raw. -/
theorem ntt16WithRoots_norm_eq
    (p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 : Nat)
    (hp : 0 < p)
    (h0 : (w0 + nw0) % p = 0) (h1 : (w1 + nw1) % p = 0)
    (h2 : (w2 + nw2) % p = 0) (h3 : (w3 + nw3) % p = 0)
    (h4 : (w4 + nw4) % p = 0) (h5 : (w5 + nw5) % p = 0)
    (h6 : (w6 + nw6) % p = 0) (h7 : (w7 + nw7) % p = 0)
    (u v : Vec16) (huv : normVec16 p u = normVec16 p v) :
    normVec16 p (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 u) =
    normVec16 p (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 v) := by
  have c0  : u.x0  % p = v.x0  % p := congrArg Vec16.x0  huv
  have c1  : u.x1  % p = v.x1  % p := congrArg Vec16.x1  huv
  have c2  : u.x2  % p = v.x2  % p := congrArg Vec16.x2  huv
  have c3  : u.x3  % p = v.x3  % p := congrArg Vec16.x3  huv
  have c4  : u.x4  % p = v.x4  % p := congrArg Vec16.x4  huv
  have c5  : u.x5  % p = v.x5  % p := congrArg Vec16.x5  huv
  have c6  : u.x6  % p = v.x6  % p := congrArg Vec16.x6  huv
  have c7  : u.x7  % p = v.x7  % p := congrArg Vec16.x7  huv
  have c8  : u.x8  % p = v.x8  % p := congrArg Vec16.x8  huv
  have c9  : u.x9  % p = v.x9  % p := congrArg Vec16.x9  huv
  have c10 : u.x10 % p = v.x10 % p := congrArg Vec16.x10 huv
  have c11 : u.x11 % p = v.x11 % p := congrArg Vec16.x11 huv
  have c12 : u.x12 % p = v.x12 % p := congrArg Vec16.x12 huv
  have c13 : u.x13 % p = v.x13 % p := congrArg Vec16.x13 huv
  have c14 : u.x14 % p = v.x14 % p := congrArg Vec16.x14 huv
  have c15 : u.x15 % p = v.x15 % p := congrArg Vec16.x15 huv
  dsimp only [ntt16WithRoots, ntt16Raw]
  have ⟨s1_0,  s1_1⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c0  c8
  have ⟨s1_2,  s1_3⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c4  c12
  have ⟨s1_4,  s1_5⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c2  c10
  have ⟨s1_6,  s1_7⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c6  c14
  have ⟨s1_8,  s1_9⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c1  c9
  have ⟨s1_10, s1_11⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c5  c13
  have ⟨s1_12, s1_13⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c3  c11
  have ⟨s1_14, s1_15⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 c7  c15
  have ⟨s2_0,  s2_2⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s1_0  s1_2
  have ⟨s2_1,  s2_3⟩  := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s1_1  s1_3
  have ⟨s2_4,  s2_6⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s1_4  s1_6
  have ⟨s2_5,  s2_7⟩  := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s1_5  s1_7
  have ⟨s2_8,  s2_10⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s1_8  s1_10
  have ⟨s2_9,  s2_11⟩ := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s1_9  s1_11
  have ⟨s2_12, s2_14⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s1_12 s1_14
  have ⟨s2_13, s2_15⟩ := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s1_13 s1_15
  have ⟨s3_0,  s3_4⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s2_0  s2_4
  have ⟨s3_1,  s3_5⟩  := bfly_pair_mod p _ _ _ _ w2 nw2 hp h2 s2_1  s2_5
  have ⟨s3_2,  s3_6⟩  := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s2_2  s2_6
  have ⟨s3_3,  s3_7⟩  := bfly_pair_mod p _ _ _ _ w6 nw6 hp h6 s2_3  s2_7
  have ⟨s3_8,  s3_12⟩ := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s2_8  s2_12
  have ⟨s3_9,  s3_13⟩ := bfly_pair_mod p _ _ _ _ w2 nw2 hp h2 s2_9  s2_13
  have ⟨s3_10, s3_14⟩ := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s2_10 s2_14
  have ⟨s3_11, s3_15⟩ := bfly_pair_mod p _ _ _ _ w6 nw6 hp h6 s2_11 s2_15
  have ⟨s4_0,  s4_8⟩  := bfly_pair_mod p _ _ _ _ w0 nw0 hp h0 s3_0  s3_8
  have ⟨s4_1,  s4_9⟩  := bfly_pair_mod p _ _ _ _ w1 nw1 hp h1 s3_1  s3_9
  have ⟨s4_2,  s4_10⟩ := bfly_pair_mod p _ _ _ _ w2 nw2 hp h2 s3_2  s3_10
  have ⟨s4_3,  s4_11⟩ := bfly_pair_mod p _ _ _ _ w3 nw3 hp h3 s3_3  s3_11
  have ⟨s4_4,  s4_12⟩ := bfly_pair_mod p _ _ _ _ w4 nw4 hp h4 s3_4  s3_12
  have ⟨s4_5,  s4_13⟩ := bfly_pair_mod p _ _ _ _ w5 nw5 hp h5 s3_5  s3_13
  have ⟨s4_6,  s4_14⟩ := bfly_pair_mod p _ _ _ _ w6 nw6 hp h6 s3_6  s3_14
  have ⟨s4_7,  s4_15⟩ := bfly_pair_mod p _ _ _ _ w7 nw7 hp h7 s3_7  s3_15
  exact normVec16_eq_of_comps p _ _
    s4_0 s4_1 s4_2 s4_3 s4_4 s4_5 s4_6 s4_7
    s4_8 s4_9 s4_10 s4_11 s4_12 s4_13 s4_14 s4_15

/-- Exact modular equivalence between intt16WithRoots and intt16Raw. -/
theorem intt16WithRoots_norm_eq
    (p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (hp : 0 < p)
    (h0 : (iw0 + niw0) % p = 0) (h1 : (iw1 + niw1) % p = 0)
    (h2 : (iw2 + niw2) % p = 0) (h3 : (iw3 + niw3) % p = 0)
    (h4 : (iw4 + niw4) % p = 0) (h5 : (iw5 + niw5) % p = 0)
    (h6 : (iw6 + niw6) % p = 0) (h7 : (iw7 + niw7) % p = 0)
    (u v : Vec16) (huv : normVec16 p u = normVec16 p v) :
    normVec16 p (intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 u) =
    normVec16 p (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
                  niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 v) := by
  have h := ntt16WithRoots_norm_eq p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
    niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 hp h0 h1 h2 h3 h4 h5 h6 h7 u v huv
  have hs := normVec16_scale_congr p inv16 _ _ h
  dsimp only [intt16WithRoots, intt16Raw, normVec16, scaleVec16] at hs ⊢
  simp only [Nat.mod_mod, Nat.mul_comm _ inv16] at hs ⊢
  exact hs

/-- ntt16WithRoots outputs are already reduced modulo p. -/
theorem normVec16_ntt16WithRoots (p w0 w1 w2 w3 w4 w5 w6 w7 : Nat) (v : Vec16) :
    normVec16 p (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 v) =
    ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 v := by
  dsimp only [ntt16WithRoots, butterflyWithTwiddle, normVec16]
  simp only [Nat.mod_mod]

/-- intt16WithRoots outputs are already reduced modulo p. -/
theorem normVec16_intt16WithRoots (p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 : Nat) (v : Vec16) :
    normVec16 p (intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 v) =
    intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 v := by
  dsimp only [intt16WithRoots, normVec16]
  simp only [Nat.mod_mod]

/-- rawBfly additivity over Nat. -/
theorem rawBfly_add (u1 u2 v1 v2 w nw : Nat) :
    rawBfly (u1 + u2) (v1 + v2) w nw =
    ((rawBfly u1 v1 w nw).1 + (rawBfly u2 v2 w nw).1,
     (rawBfly u1 v1 w nw).2 + (rawBfly u2 v2 w nw).2) := by
  dsimp [rawBfly]
  rw [Nat.mul_add, Nat.mul_add]
  ext <;> ac_rfl

/-- rawBfly scalar homogeneity over Nat. -/
theorem rawBfly_scale (c u v w nw : Nat) :
    rawBfly (c * u) (c * v) w nw =
    (c * (rawBfly u v w nw).1, c * (rawBfly u v w nw).2) := by
  dsimp [rawBfly]
  rw [Nat.mul_add, Nat.mul_add]
  ext <;> ac_rfl

/-- Additivity of ntt16Raw over Nat. -/
theorem ntt16Raw_add (w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 : Nat)
    (u v : Vec16) :
    ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 (addVec16 u v) =
    addVec16
      (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 u)
      (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 v) := by
  dsimp only [ntt16Raw, addVec16]
  simp only [rawBfly_add]

/-- Scalar homogeneity of ntt16Raw over Nat. -/
theorem ntt16Raw_scale (w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 c : Nat)
    (v : Vec16) :
    ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 (scaleVec16 c v) =
    scaleVec16 c (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 v) := by
  dsimp only [ntt16Raw, scaleVec16]
  simp only [rawBfly_scale]

/-- Additivity of scaleVec16. -/
theorem scaleVec16_add (c : Nat) (u v : Vec16) :
    scaleVec16 c (addVec16 u v) = addVec16 (scaleVec16 c u) (scaleVec16 c v) := by
  dsimp only [scaleVec16, addVec16]
  simp only [Nat.mul_add]

/-- Composition of scaleVec16. -/
theorem scaleVec16_scale (c d : Nat) (v : Vec16) :
    scaleVec16 d (scaleVec16 c v) = scaleVec16 c (scaleVec16 d v) := by
  dsimp only [scaleVec16]
  simp only [Nat.mul_left_comm]

/-- Additivity of intt16Raw. -/
theorem intt16Raw_add
    (iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (u v : Vec16) :
    intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
      (addVec16 u v) =
    addVec16
      (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 u)
      (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 v) := by
  dsimp only [intt16Raw]
  rw [ntt16Raw_add, scaleVec16_add]

/-- Scalar homogeneity of intt16Raw. -/
theorem intt16Raw_scale
    (iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 c : Nat)
    (v : Vec16) :
    intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
      (scaleVec16 c v) =
    scaleVec16 c
      (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 v) := by
  dsimp only [intt16Raw]
  rw [ntt16Raw_scale, scaleVec16_scale]

/-- Left and right bilinearity of pointwiseMul16Raw. -/
theorem pointwiseMul16Raw_add_left (u1 u2 v : Vec16) :
    pointwiseMul16Raw (addVec16 u1 u2) v =
    addVec16 (pointwiseMul16Raw u1 v) (pointwiseMul16Raw u2 v) := by
  dsimp only [pointwiseMul16Raw, addVec16]
  simp only [Nat.add_mul]

theorem pointwiseMul16Raw_add_right (u v1 v2 : Vec16) :
    pointwiseMul16Raw u (addVec16 v1 v2) =
    addVec16 (pointwiseMul16Raw u v1) (pointwiseMul16Raw u v2) := by
  dsimp only [pointwiseMul16Raw, addVec16]
  simp only [Nat.mul_add]

theorem pointwiseMul16Raw_scale_left (c : Nat) (u v : Vec16) :
    pointwiseMul16Raw (scaleVec16 c u) v = scaleVec16 c (pointwiseMul16Raw u v) := by
  dsimp only [pointwiseMul16Raw, scaleVec16]
  simp only [Nat.mul_assoc]

theorem pointwiseMul16Raw_scale_right (c : Nat) (u v : Vec16) :
    pointwiseMul16Raw u (scaleVec16 c v) = scaleVec16 c (pointwiseMul16Raw u v) := by
  dsimp only [pointwiseMul16Raw, scaleVec16]
  simp only [Nat.mul_left_comm]

theorem add16_swap (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Nat) :
    (a0 + b0) + (a1 + b1) + (a2 + b2) + (a3 + b3) +
    (a4 + b4) + (a5 + b5) + (a6 + b6) + (a7 + b7) +
    (a8 + b8) + (a9 + b9) + (a10 + b10) + (a11 + b11) +
    (a12 + b12) + (a13 + b13) + (a14 + b14) + (a15 + b15) =
    (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 +
     a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15) +
    (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 +
     b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15) := by
  omega

/-- Left and right bilinearity of exactIntCyclicConv16. -/
theorem exactIntCyclicConv16_add_left (a1 a2 b : Vec16) :
    exactIntCyclicConv16 (addVec16 a1 a2) b =
    addVec16 (exactIntCyclicConv16 a1 b) (exactIntCyclicConv16 a2 b) := by
  dsimp only [exactIntCyclicConv16, addVec16]
  simp only [Nat.add_mul]
  congr 1 <;> apply add16_swap

theorem exactIntCyclicConv16_add_right (a b1 b2 : Vec16) :
    exactIntCyclicConv16 a (addVec16 b1 b2) =
    addVec16 (exactIntCyclicConv16 a b1) (exactIntCyclicConv16 a b2) := by
  dsimp only [exactIntCyclicConv16, addVec16]
  simp only [Nat.mul_add]
  congr 1 <;> apply add16_swap

theorem exactIntCyclicConv16_scale_left (c : Nat) (a b : Vec16) :
    exactIntCyclicConv16 (scaleVec16 c a) b = scaleVec16 c (exactIntCyclicConv16 a b) := by
  dsimp only [exactIntCyclicConv16, scaleVec16]
  simp only [Nat.mul_add, Nat.mul_assoc]

theorem exactIntCyclicConv16_scale_right (c : Nat) (a b : Vec16) :
    exactIntCyclicConv16 a (scaleVec16 c b) = scaleVec16 c (exactIntCyclicConv16 a b) := by
  dsimp only [exactIntCyclicConv16, scaleVec16]
  simp only [Nat.mul_add, Nat.mul_left_comm]

/-- Linear combination of basis vectors over Vec16. -/
def vec16FromBasis (a : Vec16) (f : Nat → Vec16) : Vec16 :=
  addVec16 (scaleVec16 a.x0 (f 0))
   (addVec16 (scaleVec16 a.x1 (f 1))
    (addVec16 (scaleVec16 a.x2 (f 2))
     (addVec16 (scaleVec16 a.x3 (f 3))
      (addVec16 (scaleVec16 a.x4 (f 4))
       (addVec16 (scaleVec16 a.x5 (f 5))
        (addVec16 (scaleVec16 a.x6 (f 6))
         (addVec16 (scaleVec16 a.x7 (f 7))
          (addVec16 (scaleVec16 a.x8 (f 8))
           (addVec16 (scaleVec16 a.x9 (f 9))
            (addVec16 (scaleVec16 a.x10 (f 10))
             (addVec16 (scaleVec16 a.x11 (f 11))
              (addVec16 (scaleVec16 a.x12 (f 12))
               (addVec16 (scaleVec16 a.x13 (f 13))
                (addVec16 (scaleVec16 a.x14 (f 14))
                          (scaleVec16 a.x15 (f 15))))))))))))))))

theorem vec16_basis_eq (a : Vec16) : a = vec16FromBasis a basisVec16 := by
  cases a
  simp [vec16FromBasis, addVec16, scaleVec16, basisVec16]

theorem vec16FromBasis_norm_congr (p : Nat) (a : Vec16) (f g : Nat → Vec16)
    (h0 : normVec16 p (f 0) = normVec16 p (g 0))
    (h1 : normVec16 p (f 1) = normVec16 p (g 1))
    (h2 : normVec16 p (f 2) = normVec16 p (g 2))
    (h3 : normVec16 p (f 3) = normVec16 p (g 3))
    (h4 : normVec16 p (f 4) = normVec16 p (g 4))
    (h5 : normVec16 p (f 5) = normVec16 p (g 5))
    (h6 : normVec16 p (f 6) = normVec16 p (g 6))
    (h7 : normVec16 p (f 7) = normVec16 p (g 7))
    (h8 : normVec16 p (f 8) = normVec16 p (g 8))
    (h9 : normVec16 p (f 9) = normVec16 p (g 9))
    (h10 : normVec16 p (f 10) = normVec16 p (g 10))
    (h11 : normVec16 p (f 11) = normVec16 p (g 11))
    (h12 : normVec16 p (f 12) = normVec16 p (g 12))
    (h13 : normVec16 p (f 13) = normVec16 p (g 13))
    (h14 : normVec16 p (f 14) = normVec16 p (g 14))
    (h15 : normVec16 p (f 15) = normVec16 p (g 15)) :
    normVec16 p (vec16FromBasis a f) = normVec16 p (vec16FromBasis a g) := by
  dsimp only [vec16FromBasis]
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h0) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h1) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h2) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h3) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h4) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h5) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h6) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h7) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h8) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h9) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h10) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h11) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h12) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h13) ?_
  refine normVec16_add_congr p _ _ _ _ (normVec16_scale_congr p _ _ _ h14) ?_
  exact normVec16_scale_congr p _ _ _ h15

/-- Boolean universal quantifier over indices 0..n-1 for kernel decide checks. -/
def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, P => allLt n P && P n

theorem allLt_spec (n : Nat) (P : Nat → Bool) (h : allLt n P = true) :
    ∀ i, i < n → P i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    simp only [allLt, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h.1 i hlt
    · subst heq; exact h.2

theorem allLt_of_forall (n : Nat) (P : Nat → Bool) (h : ∀ i, i < n → P i = true) :
    allLt n P = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [allLt, Bool.and_eq_true]
    exact ⟨ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)⟩

/-- Universal linear lifting: two Nat-linear Vec16 maps agreeing mod p on basisVec16 agree everywhere. -/
theorem vec16_linear_mod_eq (p : Nat) (F G : Vec16 → Vec16)
    (hF_add : ∀ u v, F (addVec16 u v) = addVec16 (F u) (F v))
    (hF_scale : ∀ c v, F (scaleVec16 c v) = scaleVec16 c (F v))
    (hG_add : ∀ u v, G (addVec16 u v) = addVec16 (G u) (G v))
    (hG_scale : ∀ c v, G (scaleVec16 c v) = scaleVec16 c (G v))
    (hbasis : allLt 16 (fun i => normVec16 p (F (basisVec16 i)) ==
                                  normVec16 p (G (basisVec16 i))) = true)
    (a : Vec16) :
    normVec16 p (F a) = normVec16 p (G a) := by
  have hb := allLt_spec 16 _ hbasis
  simp only [beq_iff_eq] at hb
  have hF : F a = vec16FromBasis a (fun i => F (basisVec16 i)) := by
    conv => lhs; rw [vec16_basis_eq a]
    simp only [vec16FromBasis, hF_add, hF_scale]
  have hG : G a = vec16FromBasis a (fun i => G (basisVec16 i)) := by
    conv => lhs; rw [vec16_basis_eq a]
    simp only [vec16FromBasis, hG_add, hG_scale]
  rw [hF, hG]
  exact vec16FromBasis_norm_congr p a
    (fun i => F (basisVec16 i)) (fun i => G (basisVec16 i))
    (hb 0 (by decide)) (hb 1 (by decide)) (hb 2 (by decide)) (hb 3 (by decide))
    (hb 4 (by decide)) (hb 5 (by decide)) (hb 6 (by decide)) (hb 7 (by decide))
    (hb 8 (by decide)) (hb 9 (by decide)) (hb 10 (by decide)) (hb 11 (by decide))
    (hb 12 (by decide)) (hb 13 (by decide)) (hb 14 (by decide)) (hb 15 (by decide))

/-- Universal bilinear lifting: two Nat-bilinear Vec16 maps agreeing mod p on basis pairs agree everywhere. -/
theorem vec16_bilinear_mod_eq (p : Nat) (F G : Vec16 → Vec16 → Vec16)
    (hF_addL : ∀ u1 u2 v, F (addVec16 u1 u2) v = addVec16 (F u1 v) (F u2 v))
    (hF_scaleL : ∀ c u v, F (scaleVec16 c u) v = scaleVec16 c (F u v))
    (hF_addR : ∀ u v1 v2, F u (addVec16 v1 v2) = addVec16 (F u v1) (F u v2))
    (hF_scaleR : ∀ c u v, F u (scaleVec16 c v) = scaleVec16 c (F u v))
    (hG_addL : ∀ u1 u2 v, G (addVec16 u1 u2) v = addVec16 (G u1 v) (G u2 v))
    (hG_scaleL : ∀ c u v, G (scaleVec16 c u) v = scaleVec16 c (G u v))
    (hG_addR : ∀ u v1 v2, G u (addVec16 v1 v2) = addVec16 (G u v1) (G u v2))
    (hG_scaleR : ∀ c u v, G u (scaleVec16 c v) = scaleVec16 c (G u v))
    (hbasis : allLt 16 (fun i => allLt 16 (fun j =>
      normVec16 p (F (basisVec16 i) (basisVec16 j)) ==
      normVec16 p (G (basisVec16 i) (basisVec16 j)))) = true)
    (a b : Vec16) :
    normVec16 p (F a b) = normVec16 p (G a b) := by
  have hb := allLt_spec 16 _ hbasis
  have hcol : ∀ j, j < 16 →
      normVec16 p (F a (basisVec16 j)) = normVec16 p (G a (basisVec16 j)) := by
    intro j hj
    have hbj : allLt 16 (fun i =>
        normVec16 p (F (basisVec16 i) (basisVec16 j)) ==
        normVec16 p (G (basisVec16 i) (basisVec16 j))) = true := by
      apply allLt_of_forall
      intro i hi
      exact allLt_spec 16 _ (hb i hi) j hj
    exact vec16_linear_mod_eq p (fun x => F x (basisVec16 j)) (fun x => G x (basisVec16 j))
      (fun u1 u2 => hF_addL u1 u2 (basisVec16 j)) (fun c u => hF_scaleL c u (basisVec16 j))
      (fun u1 u2 => hG_addL u1 u2 (basisVec16 j)) (fun c u => hG_scaleL c u (basisVec16 j)) hbj a
  have hrow : allLt 16 (fun j =>
      normVec16 p (F a (basisVec16 j)) == normVec16 p (G a (basisVec16 j))) = true := by
    apply allLt_of_forall
    intro j hj
    simp only [beq_iff_eq]
    exact hcol j hj
  exact vec16_linear_mod_eq p (F a) (G a)
    (hF_addR a) (fun c v => hF_scaleR c a v)
    (hG_addR a) (fun c v => hG_scaleR c a v) hrow b

-- Generic parametric 16-point NTT theorems lifted from basis checks

theorem intt16_ntt16_universal_generic
    (p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
       iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (hp : 0 < p)
    (hw0 : (w0 + nw0) % p = 0) (hw1 : (w1 + nw1) % p = 0)
    (hw2 : (w2 + nw2) % p = 0) (hw3 : (w3 + nw3) % p = 0)
    (hw4 : (w4 + nw4) % p = 0) (hw5 : (w5 + nw5) % p = 0)
    (hw6 : (w6 + nw6) % p = 0) (hw7 : (w7 + nw7) % p = 0)
    (hiw0 : (iw0 + niw0) % p = 0) (hiw1 : (iw1 + niw1) % p = 0)
    (hiw2 : (iw2 + niw2) % p = 0) (hiw3 : (iw3 + niw3) % p = 0)
    (hiw4 : (iw4 + niw4) % p = 0) (hiw5 : (iw5 + niw5) % p = 0)
    (hiw6 : (iw6 + niw6) % p = 0) (hiw7 : (iw7 + niw7) % p = 0)
    (hbasis : allLt 16 (fun i =>
      normVec16 p (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
                    niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
                    (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
                      (basisVec16 i))) ==
      normVec16 p (basisVec16 i)) = true)
    (a : Vec16) :
    intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16
      (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a) = normVec16 p a := by
  have h1 : normVec16 p (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a) =
            normVec16 p (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 a) :=
    ntt16WithRoots_norm_eq p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
      hp hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 a a rfl
  have h2 := intt16WithRoots_norm_eq p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
    niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 hp hiw0 hiw1 hiw2 hiw3 hiw4 hiw5 hiw6 hiw7
    (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a)
    (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 a) h1
  rw [normVec16_intt16WithRoots] at h2
  rw [h2]
  exact vec16_linear_mod_eq p
    (fun v => intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
      (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 v))
    id
    (fun u v => by rw [ntt16Raw_add, intt16Raw_add])
    (fun c v => by rw [ntt16Raw_scale, intt16Raw_scale])
    (fun _ _ => rfl) (fun _ _ => rfl) hbasis a

theorem ntt16_intt16_universal_generic
    (p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
       iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (hp : 0 < p)
    (hw0 : (w0 + nw0) % p = 0) (hw1 : (w1 + nw1) % p = 0)
    (hw2 : (w2 + nw2) % p = 0) (hw3 : (w3 + nw3) % p = 0)
    (hw4 : (w4 + nw4) % p = 0) (hw5 : (w5 + nw5) % p = 0)
    (hw6 : (w6 + nw6) % p = 0) (hw7 : (w7 + nw7) % p = 0)
    (hiw0 : (iw0 + niw0) % p = 0) (hiw1 : (iw1 + niw1) % p = 0)
    (hiw2 : (iw2 + niw2) % p = 0) (hiw3 : (iw3 + niw3) % p = 0)
    (hiw4 : (iw4 + niw4) % p = 0) (hiw5 : (iw5 + niw5) % p = 0)
    (hiw6 : (iw6 + niw6) % p = 0) (hiw7 : (iw7 + niw7) % p = 0)
    (hbasis : allLt 16 (fun i =>
      normVec16 p (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
                    (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
                      niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 (basisVec16 i))) ==
      normVec16 p (basisVec16 i)) = true)
    (y : Vec16) :
    ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7
      (intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 y) = normVec16 p y := by
  have h1 : normVec16 p (intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 y) =
            normVec16 p (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
                          niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 y) :=
    intt16WithRoots_norm_eq p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
      niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
      hp hiw0 hiw1 hiw2 hiw3 hiw4 hiw5 hiw6 hiw7 y y rfl
  have h2 := ntt16WithRoots_norm_eq p w0 w1 w2 w3 w4 w5 w6 w7
    nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 hp hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
    (intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16 y)
    (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 y) h1
  rw [normVec16_ntt16WithRoots] at h2
  rw [h2]
  exact vec16_linear_mod_eq p
    (fun v => ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
      (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 v))
    id
    (fun u v => by rw [intt16Raw_add, ntt16Raw_add])
    (fun c v => by rw [intt16Raw_scale, ntt16Raw_scale])
    (fun _ _ => rfl) (fun _ _ => rfl) hbasis y

theorem cyclic_conv16_ntt_universal_generic
    (p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
       iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 : Nat)
    (hp : 0 < p)
    (hw0 : (w0 + nw0) % p = 0) (hw1 : (w1 + nw1) % p = 0)
    (hw2 : (w2 + nw2) % p = 0) (hw3 : (w3 + nw3) % p = 0)
    (hw4 : (w4 + nw4) % p = 0) (hw5 : (w5 + nw5) % p = 0)
    (hw6 : (w6 + nw6) % p = 0) (hw7 : (w7 + nw7) % p = 0)
    (hiw0 : (iw0 + niw0) % p = 0) (hiw1 : (iw1 + niw1) % p = 0)
    (hiw2 : (iw2 + niw2) % p = 0) (hiw3 : (iw3 + niw3) % p = 0)
    (hiw4 : (iw4 + niw4) % p = 0) (hiw5 : (iw5 + niw5) % p = 0)
    (hiw6 : (iw6 + niw6) % p = 0) (hiw7 : (iw7 + niw7) % p = 0)
    (hbasis : allLt 16 (fun i => allLt 16 (fun j =>
      normVec16 p (intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
                    niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
                    (pointwiseMul16Raw
                      (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 (basisVec16 i))
                      (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 (basisVec16 j)))) ==
      normVec16 p (exactIntCyclicConv16 (basisVec16 i) (basisVec16 j)))) = true)
    (a b : Vec16) :
    intt16WithRoots p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 inv16
      (pointwiseMul16Mod p
        (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a)
        (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 b)) =
    normVec16 p (exactIntCyclicConv16 a b) := by
  have ha : normVec16 p (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a) =
            normVec16 p (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 a) :=
    ntt16WithRoots_norm_eq p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
      hp hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 a a rfl
  have hb : normVec16 p (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 b) =
            normVec16 p (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 b) :=
    ntt16WithRoots_norm_eq p w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7
      hp hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 b b rfl
  have hpmod := pointwiseMul16Mod_norm_eq p
    (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a)
    (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 a)
    (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 b)
    (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 b) ha hb
  have hnorm_pw : normVec16 p
      (pointwiseMul16Mod p
        (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 a)
        (ntt16WithRoots p w0 w1 w2 w3 w4 w5 w6 w7 b)) =
      normVec16 p (pointwiseMul16Raw
        (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 a)
        (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 b)) := by
    rw [hpmod]
    dsimp only [normVec16]
    simp only [Nat.mod_mod]
  have hfinal := intt16WithRoots_norm_eq p iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7
    niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16 hp hiw0 hiw1 hiw2 hiw3 hiw4 hiw5 hiw6 hiw7
    _ _ hnorm_pw
  rw [normVec16_intt16WithRoots] at hfinal
  rw [hfinal]
  exact vec16_bilinear_mod_eq p
    (fun u v => intt16Raw iw0 iw1 iw2 iw3 iw4 iw5 iw6 iw7 niw0 niw1 niw2 niw3 niw4 niw5 niw6 niw7 inv16
      (pointwiseMul16Raw
        (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 u)
        (ntt16Raw w0 w1 w2 w3 w4 w5 w6 w7 nw0 nw1 nw2 nw3 nw4 nw5 nw6 nw7 v)))
    exactIntCyclicConv16
    (fun u1 u2 v => by rw [ntt16Raw_add, pointwiseMul16Raw_add_left, intt16Raw_add])
    (fun c u v => by rw [ntt16Raw_scale, pointwiseMul16Raw_scale_left, intt16Raw_scale])
    (fun u v1 v2 => by rw [ntt16Raw_add, pointwiseMul16Raw_add_right, intt16Raw_add])
    (fun c u v => by rw [ntt16Raw_scale, pointwiseMul16Raw_scale_right, intt16Raw_scale])
    exactIntCyclicConv16_add_left exactIntCyclicConv16_scale_left
    exactIntCyclicConv16_add_right exactIntCyclicConv16_scale_right
    hbasis a b

-- -----------------------------------------------------------------------------
-- Universal 16-Point NTT Theorems over F_17, F_257, and F_65537
-- -----------------------------------------------------------------------------

/-- Universal 16-Point NTT Left Invertibility over F_17. -/
theorem intt16_ntt16_universal_F17 (a : Vec16) :
    intt16Mod17 (ntt16Mod17 a) = normVec16 17 a :=
  intt16_ntt16_universal_generic 17
    1 3 9 10 13 5 15 11 16 14 8 7 4 12 2 6
    1 6 2 12 4 7 8 14 16 11 15 5 13 10 9 3 16
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a

/-- Universal 16-Point NTT Right Invertibility over F_17. -/
theorem ntt16_intt16_universal_F17 (y : Vec16) :
    ntt16Mod17 (intt16Mod17 y) = normVec16 17 y :=
  ntt16_intt16_universal_generic 17
    1 3 9 10 13 5 15 11 16 14 8 7 4 12 2 6
    1 6 2 12 4 7 8 14 16 11 15 5 13 10 9 3 16
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) y

/-- Universal 16-Point Cyclic Convolution Theorem over F_17. -/
theorem cyclic_conv16_ntt_universal_F17 (a b : Vec16) :
    intt16Mod17 (pointwiseMul16Mod 17 (ntt16Mod17 a) (ntt16Mod17 b)) =
    normVec16 17 (exactIntCyclicConv16 a b) :=
  cyclic_conv16_ntt_universal_generic 17
    1 3 9 10 13 5 15 11 16 14 8 7 4 12 2 6
    1 6 2 12 4 7 8 14 16 11 15 5 13 10 9 3 16
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a b

/-- Universal 16-Point NTT Left Invertibility over F_257. -/
theorem intt16_ntt16_universal_F257 (a : Vec16) :
    intt16Mod257 (ntt16Mod257 a) = normVec16 257 a :=
  intt16_ntt16_universal_generic 257
    1 2 4 8 16 32 64 128 256 255 253 249 241 225 193 129
    1 129 193 225 241 249 253 255 256 128 64 32 16 8 4 2 241
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a

/-- Universal 16-Point NTT Right Invertibility over F_257. -/
theorem ntt16_intt16_universal_F257 (y : Vec16) :
    ntt16Mod257 (intt16Mod257 y) = normVec16 257 y :=
  ntt16_intt16_universal_generic 257
    1 2 4 8 16 32 64 128 256 255 253 249 241 225 193 129
    1 129 193 225 241 249 253 255 256 128 64 32 16 8 4 2 241
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) y

/-- Universal 16-Point Cyclic Convolution Theorem over F_257. -/
theorem cyclic_conv16_ntt_universal_F257 (a b : Vec16) :
    intt16Mod257 (pointwiseMul16Mod 257 (ntt16Mod257 a) (ntt16Mod257 b)) =
    normVec16 257 (exactIntCyclicConv16 a b) :=
  cyclic_conv16_ntt_universal_generic 257
    1 2 4 8 16 32 64 128 256 255 253 249 241 225 193 129
    1 129 193 225 241 249 253 255 256 128 64 32 16 8 4 2 241
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a b

/-- Universal 16-Point NTT Left Invertibility over F_65537. -/
theorem intt16_ntt16_universal_F65537 (a : Vec16) :
    intt16Mod65537 (ntt16Mod65537 a) = normVec16 65537 a :=
  intt16_ntt16_universal_generic 65537
    1 4 16 64 256 1024 4096 16384 65536 65533 65521 65473 65281 64513 61441 49153
    1 49153 61441 64513 65281 65473 65521 65533 65536 16384 4096 1024 256 64 16 4 61441
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a

/-- Universal 16-Point NTT Right Invertibility over F_65537. -/
theorem ntt16_intt16_universal_F65537 (y : Vec16) :
    ntt16Mod65537 (intt16Mod65537 y) = normVec16 65537 y :=
  ntt16_intt16_universal_generic 65537
    1 4 16 64 256 1024 4096 16384 65536 65533 65521 65473 65281 64513 61441 49153
    1 49153 61441 64513 65281 65473 65521 65533 65536 16384 4096 1024 256 64 16 4 61441
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) y

/-- Universal 16-Point Cyclic Convolution Theorem over F_65537. -/
theorem cyclic_conv16_ntt_universal_F65537 (a b : Vec16) :
    intt16Mod65537 (pointwiseMul16Mod 65537 (ntt16Mod65537 a) (ntt16Mod65537 b)) =
    normVec16 65537 (exactIntCyclicConv16 a b) :=
  cyclic_conv16_ntt_universal_generic 65537
    1 4 16 64 256 1024 4096 16384 65536 65533 65521 65473 65281 64513 61441 49153
    1 49153 61441 64513 65281 65473 65521 65533 65536 16384 4096 1024 256 64 16 4 61441
    (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a b

-- -----------------------------------------------------------------------------
-- End-to-End 48-Digit CRT-NTT Big-Integer Multiplier Soundness
-- -----------------------------------------------------------------------------

/-- Predicate: all 8 base-1000 limbs of Vec8 are strictly below 1000. -/
def isNormalizedVec8 (v : Vec8) : Prop :=
  v.x0 < 1000 ∧ v.x1 < 1000 ∧ v.x2 < 1000 ∧ v.x3 < 1000 ∧
  v.x4 < 1000 ∧ v.x5 < 1000 ∧ v.x6 < 1000 ∧ v.x7 < 1000

/-- Positional evaluation of 8 base-1000 digits using Horner's rule. -/
def evalDigits1000Vec8 (d : Vec8) : Nat :=
  d.x0 + 1000 * (d.x1 + 1000 * (d.x2 + 1000 * (d.x3 + 1000 * (
  d.x4 + 1000 * (d.x5 + 1000 * (d.x6 + 1000 * d.x7))))))

/-- Zero-pad an 8-limb vector to a 16-limb vector. -/
def padVec8To16 (v : Vec8) : Vec16 :=
  ⟨v.x0, v.x1, v.x2, v.x3, v.x4, v.x5, v.x6, v.x7, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Convert Nat into 8 base-1000 limbs. -/
def toBase1000Vec8 (n : Nat) : Vec8 where
  x0 := limb1000 n 0
  x1 := limb1000 n 1
  x2 := limb1000 n 2
  x3 := limb1000 n 3
  x4 := limb1000 n 4
  x5 := limb1000 n 5
  x6 := limb1000 n 6
  x7 := limb1000 n 7

/-- CRT-NTT multiplication directly on normalized 8-limb base-1000 vectors. -/
def crtNttBigMulVec8 (a b : Vec8) : Vec16 :=
  carryPassBase1000 (crtNttConv16 (padVec8To16 a) (padVec8To16 b))

theorem evalDigits1000Vec8_lt (a : Vec8) (ha : isNormalizedVec8 a) :
    evalDigits1000Vec8 a < 1000 ^ 8 := by
  rcases ha with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp [evalDigits1000Vec8]
  omega

theorem padVec8_conv_bound_helper (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (ha : a0 < 1000 ∧ a1 < 1000 ∧ a2 < 1000 ∧ a3 < 1000 ∧
          a4 < 1000 ∧ a5 < 1000 ∧ a6 < 1000 ∧ a7 < 1000)
    (hb : b0 < 1000 ∧ b1 < 1000 ∧ b2 < 1000 ∧ b3 < 1000 ∧
          b4 < 1000 ∧ b5 < 1000 ∧ b6 < 1000 ∧ b7 < 1000) :
    let c := exactIntCyclicConv16
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, 0, 0, 0, 0, 0, 0, 0, 0⟩
      ⟨b0, b1, b2, b3, b4, b5, b6, b7, 0, 0, 0, 0, 0, 0, 0, 0⟩
    c.x0 < 286331153 ∧ c.x1 < 286331153 ∧ c.x2 < 286331153 ∧ c.x3 < 286331153 ∧
    c.x4 < 286331153 ∧ c.x5 < 286331153 ∧ c.x6 < 286331153 ∧ c.x7 < 286331153 ∧
    c.x8 < 286331153 ∧ c.x9 < 286331153 ∧ c.x10 < 286331153 ∧ c.x11 < 286331153 ∧
    c.x12 < 286331153 ∧ c.x13 < 286331153 ∧ c.x14 < 286331153 ∧ c.x15 < 286331153 := by
  have mb : ∀ x y, x < 1000 → y < 1000 → x * y < 1000000 :=
    fun x y hx hy => Nat.mul_lt_mul_of_lt_of_lt hx hy
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  dsimp only [exactIntCyclicConv16]
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · have := mb _ _ ha0 hb0; omega
  · have := mb _ _ ha0 hb1; have := mb _ _ ha1 hb0; omega
  · have := mb _ _ ha0 hb2; have := mb _ _ ha1 hb1; have := mb _ _ ha2 hb0; omega
  · have := mb _ _ ha0 hb3; have := mb _ _ ha1 hb2; have := mb _ _ ha2 hb1
    have := mb _ _ ha3 hb0; omega
  · have := mb _ _ ha0 hb4; have := mb _ _ ha1 hb3; have := mb _ _ ha2 hb2
    have := mb _ _ ha3 hb1; have := mb _ _ ha4 hb0; omega
  · have := mb _ _ ha0 hb5; have := mb _ _ ha1 hb4; have := mb _ _ ha2 hb3
    have := mb _ _ ha3 hb2; have := mb _ _ ha4 hb1; have := mb _ _ ha5 hb0; omega
  · have := mb _ _ ha0 hb6; have := mb _ _ ha1 hb5; have := mb _ _ ha2 hb4
    have := mb _ _ ha3 hb3; have := mb _ _ ha4 hb2; have := mb _ _ ha5 hb1
    have := mb _ _ ha6 hb0; omega
  · have := mb _ _ ha0 hb7; have := mb _ _ ha1 hb6; have := mb _ _ ha2 hb5
    have := mb _ _ ha3 hb4; have := mb _ _ ha4 hb3; have := mb _ _ ha5 hb2
    have := mb _ _ ha6 hb1; have := mb _ _ ha7 hb0; omega
  · have := mb _ _ ha1 hb7; have := mb _ _ ha2 hb6; have := mb _ _ ha3 hb5
    have := mb _ _ ha4 hb4; have := mb _ _ ha5 hb3; have := mb _ _ ha6 hb2
    have := mb _ _ ha7 hb1; omega
  · have := mb _ _ ha2 hb7; have := mb _ _ ha3 hb6; have := mb _ _ ha4 hb5
    have := mb _ _ ha5 hb4; have := mb _ _ ha6 hb3; have := mb _ _ ha7 hb2; omega
  · have := mb _ _ ha3 hb7; have := mb _ _ ha4 hb6; have := mb _ _ ha5 hb5
    have := mb _ _ ha6 hb4; have := mb _ _ ha7 hb3; omega
  · have := mb _ _ ha4 hb7; have := mb _ _ ha5 hb6; have := mb _ _ ha6 hb5
    have := mb _ _ ha7 hb4; omega
  · have := mb _ _ ha5 hb7; have := mb _ _ ha6 hb6; have := mb _ _ ha7 hb5; omega
  · have := mb _ _ ha6 hb7; have := mb _ _ ha7 hb6; omega
  · have := mb _ _ ha7 hb7; omega

theorem crtNttConv16_padVec8_eq (a b : Vec8) (ha : isNormalizedVec8 a) (hb : isNormalizedVec8 b) :
    crtNttConv16 (padVec8To16 a) (padVec8To16 b) =
    exactIntCyclicConv16 (padVec8To16 a) (padVec8To16 b) := by
  dsimp only [crtNttConv16]
  rw [cyclic_conv16_ntt_universal_F17, cyclic_conv16_ntt_universal_F257,
      cyclic_conv16_ntt_universal_F65537]
  let c := exactIntCyclicConv16 (padVec8To16 a) (padVec8To16 b)
  change garnerVec16_17_257_65537 (normVec16 17 c) (normVec16 257 c) (normVec16 65537 c) = c
  have hbd := padVec8_conv_bound_helper
    a.x0 a.x1 a.x2 a.x3 a.x4 a.x5 a.x6 a.x7
    b.x0 b.x1 b.x2 b.x3 b.x4 b.x5 b.x6 b.x7 ha hb
  rcases hbd with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  dsimp only [garnerVec16_17_257_65537, normVec16]
  rw [garner_17_257_65537_roundtrip_all c.x0 h0,
      garner_17_257_65537_roundtrip_all c.x1 h1,
      garner_17_257_65537_roundtrip_all c.x2 h2,
      garner_17_257_65537_roundtrip_all c.x3 h3,
      garner_17_257_65537_roundtrip_all c.x4 h4,
      garner_17_257_65537_roundtrip_all c.x5 h5,
      garner_17_257_65537_roundtrip_all c.x6 h6,
      garner_17_257_65537_roundtrip_all c.x7 h7,
      garner_17_257_65537_roundtrip_all c.x8 h8,
      garner_17_257_65537_roundtrip_all c.x9 h9,
      garner_17_257_65537_roundtrip_all c.x10 h10,
      garner_17_257_65537_roundtrip_all c.x11 h11,
      garner_17_257_65537_roundtrip_all c.x12 h12,
      garner_17_257_65537_roundtrip_all c.x13 h13,
      garner_17_257_65537_roundtrip_all c.x14 h14,
      garner_17_257_65537_roundtrip_all c.x15 h15]

theorem evalPoly1000Vec16_padVec8_conv (a b : Vec8) :
    evalPoly1000Vec16 (exactIntCyclicConv16 (padVec8To16 a) (padVec8To16 b)) =
    evalDigits1000Vec8 a * evalDigits1000Vec8 b := by
  dsimp [evalPoly1000Vec16, exactIntCyclicConv16, padVec8To16, evalDigits1000Vec8]
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
             Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  ac_rfl

/-- Universal Base-1000 8-Limb CRT-NTT Multiplication Soundness (48-Digit Product). -/
theorem crtNttBigMulVec8_universal_sound (a b : Vec8)
    (ha : isNormalizedVec8 a) (hb : isNormalizedVec8 b) :
    evalDigits1000Vec16 (crtNttBigMulVec8 a b) =
    evalDigits1000Vec8 a * evalDigits1000Vec8 b := by
  dsimp only [crtNttBigMulVec8]
  rw [crtNttConv16_padVec8_eq a b ha hb]
  have hlt : evalPoly1000Vec16 (exactIntCyclicConv16 (padVec8To16 a) (padVec8To16 b)) < 1000 ^ 16 := by
    rw [evalPoly1000Vec16_padVec8_conv]
    have ha_lt := evalDigits1000Vec8_lt a ha
    have hb_lt := evalDigits1000Vec8_lt b hb
    have hpow : (1000 ^ 8) * (1000 ^ 8) = 1000 ^ 16 := by decide
    rw [← hpow]
    exact Nat.mul_lt_mul_of_lt_of_lt ha_lt hb_lt
  rw [carryPassBase1000_exact_when_bounded _ hlt]
  exact evalPoly1000Vec16_padVec8_conv a b

theorem toBase1000Vec8_normalized (n : Nat) : isNormalizedVec8 (toBase1000Vec8 n) := by
  dsimp [isNormalizedVec8, toBase1000Vec8, limb1000]
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

private theorem div_lt_of_lt_mul_pure {n m k : Nat} (h : n < m * k) : n / m < k := by
  have hd := Nat.div_add_mod n m
  by_cases hc : k ≤ n / m
  · have hle : m * k ≤ m * (n / m) := Nat.mul_le_mul_left m hc
    have hle2 : m * (n / m) ≤ n :=
      Nat.le_trans (Nat.le_add_right (m * (n / m)) (n % m)) (Nat.le_of_eq hd)
    exact absurd (Nat.lt_of_lt_of_le h (Nat.le_trans hle hle2)) (Nat.lt_irrefl n)
  · exact Nat.lt_of_not_le hc

private theorem base1000_div_step (n k : Nat) :
    (n / 1000 ^ k) % 1000 + 1000 * (n / 1000 ^ (k + 1)) = n / 1000 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mod_add_div (n / 1000 ^ k) 1000

theorem evalDigits1000Vec8_toBase1000Vec8 (n : Nat) (hn : n < 1000 ^ 8) :
    evalDigits1000Vec8 (toBase1000Vec8 n) = n := by
  dsimp only [evalDigits1000Vec8, toBase1000Vec8, limb1000]
  have h7 : n / 1000 ^ 7 < 1000 :=
    div_lt_of_lt_mul_pure (Nat.pow_succ 1000 7 ▸ hn)
  rw [Nat.mod_eq_of_lt h7]
  rw [base1000_div_step n 6, base1000_div_step n 5, base1000_div_step n 4,
      base1000_div_step n 3, base1000_div_step n 2, base1000_div_step n 1]
  have h0 := base1000_div_step n 0
  simp only [Nat.pow_zero, Nat.div_one] at h0
  rw [Nat.div_one]
  exact h0

/-- Universal End-to-End 48-Digit CRT-NTT Big-Integer Multiplication Theorem. -/
theorem crtNttBigMul_universal_sound (a b : Nat) (ha : a < 1000 ^ 8) (hb : b < 1000 ^ 8) :
    crtNttBigMul a b = a * b := by
  have hpad : ∀ n, toBase1000Vec16 n = padVec8To16 (toBase1000Vec8 n) := fun _ => rfl
  have hmul : crtNttBigMul a b =
      evalDigits1000Vec16 (crtNttBigMulVec8 (toBase1000Vec8 a) (toBase1000Vec8 b)) := by
    dsimp only [crtNttBigMul, crtNttBigMulVec8]
    rw [hpad a, hpad b]
  rw [hmul, crtNttBigMulVec8_universal_sound _ _
    (toBase1000Vec8_normalized a) (toBase1000Vec8_normalized b)]
  rw [evalDigits1000Vec8_toBase1000Vec8 a ha, evalDigits1000Vec8_toBase1000Vec8 b hb]

-- -----------------------------------------------------------------------------
-- Stage 3: 2x2 Karatsuba-over-CRT-NTT 96-Digit Big-Integer Multiplier
-- -----------------------------------------------------------------------------

/-- Predicate: all 16 base-1000 limbs of Vec16 are strictly below 1000. -/
def isNormalizedVec16 (v : Vec16) : Prop :=
  v.x0 < 1000 ∧ v.x1 < 1000 ∧ v.x2 < 1000 ∧ v.x3 < 1000 ∧
  v.x4 < 1000 ∧ v.x5 < 1000 ∧ v.x6 < 1000 ∧ v.x7 < 1000 ∧
  v.x8 < 1000 ∧ v.x9 < 1000 ∧ v.x10 < 1000 ∧ v.x11 < 1000 ∧
  v.x12 < 1000 ∧ v.x13 < 1000 ∧ v.x14 < 1000 ∧ v.x15 < 1000

/-- Split a 16-limb vector into low and high 8-limb halves. -/
def splitVec16 (v : Vec16) : Vec8 × Vec8 :=
  (⟨v.x0, v.x1, v.x2, v.x3, v.x4, v.x5, v.x6, v.x7⟩,
   ⟨v.x8, v.x9, v.x10, v.x11, v.x12, v.x13, v.x14, v.x15⟩)

/-- Concatenate two 8-limb vectors into a 16-limb vector. -/
def mergeVec8 (lo hi : Vec8) : Vec16 :=
  ⟨lo.x0, lo.x1, lo.x2, lo.x3, lo.x4, lo.x5, lo.x6, lo.x7,
   hi.x0, hi.x1, hi.x2, hi.x3, hi.x4, hi.x5, hi.x6, hi.x7⟩

/-- 32-Limb Base-1000 Vector (96 decimal digits) represented as two Vec16 halves. -/
structure Vec32 where
  lo : Vec16
  hi : Vec16
  deriving DecidableEq, Repr

/-- Predicate: all 32 base-1000 limbs of Vec32 are strictly below 1000. -/
def isNormalizedVec32 (v : Vec32) : Prop :=
  isNormalizedVec16 v.lo ∧ isNormalizedVec16 v.hi

/-- Positional evaluation of a 32-limb base-1000 integer. -/
def evalDigits1000Vec32 (v : Vec32) : Nat :=
  evalDigits1000Vec16 v.lo + (1000 ^ 16) * evalDigits1000Vec16 v.hi

private def zeroVec8 : Vec8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

private def zeroVec16 : Vec16 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def oneVec16 : Vec16 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def addLimb1000 (x y cin : Nat) : Nat × Nat :=
  let s := x + y + cin
  (s % 1000, s / 1000)

private def subLimb1000 (x y bin : Nat) : Nat × Nat :=
  let t := 1000 + x - (y + bin)
  (t % 1000, 1 - t / 1000)

private def addVec8WithCarryIn (a b : Vec8) (cin : Nat) : Vec8 × Nat :=
  let (s0, c0) := addLimb1000 a.x0 b.x0 cin
  let (s1, c1) := addLimb1000 a.x1 b.x1 c0
  let (s2, c2) := addLimb1000 a.x2 b.x2 c1
  let (s3, c3) := addLimb1000 a.x3 b.x3 c2
  let (s4, c4) := addLimb1000 a.x4 b.x4 c3
  let (s5, c5) := addLimb1000 a.x5 b.x5 c4
  let (s6, c6) := addLimb1000 a.x6 b.x6 c5
  let (s7, c7) := addLimb1000 a.x7 b.x7 c6
  (⟨s0, s1, s2, s3, s4, s5, s6, s7⟩, c7)

/-- 8-limb base-1000 ripple-carry addition returning (sum, carry_out). -/
def addVec8WithCarry (a b : Vec8) : Vec8 × Nat :=
  addVec8WithCarryIn a b 0

private def addVec16WithCarryIn (a b : Vec16) (cin : Nat) : Vec16 × Nat :=
  let (a0, a1) := splitVec16 a
  let (b0, b1) := splitVec16 b
  let (s0, c0) := addVec8WithCarryIn a0 b0 cin
  let (s1, c1) := addVec8WithCarryIn a1 b1 c0
  (mergeVec8 s0 s1, c1)

/-- 16-limb base-1000 ripple-carry addition returning (sum, carry_out). -/
def addVec16WithCarry (a b : Vec16) : Vec16 × Nat :=
  addVec16WithCarryIn a b 0

private def subVec8WithBorrowIn (a b : Vec8) (bin : Nat) : Vec8 × Nat :=
  let (d0, b0) := subLimb1000 a.x0 b.x0 bin
  let (d1, b1) := subLimb1000 a.x1 b.x1 b0
  let (d2, b2) := subLimb1000 a.x2 b.x2 b1
  let (d3, b3) := subLimb1000 a.x3 b.x3 b2
  let (d4, b4) := subLimb1000 a.x4 b.x4 b3
  let (d5, b5) := subLimb1000 a.x5 b.x5 b4
  let (d6, b6) := subLimb1000 a.x6 b.x6 b5
  let (d7, b7) := subLimb1000 a.x7 b.x7 b6
  (⟨d0, d1, d2, d3, d4, d5, d6, d7⟩, b7)

private def subVec16WithBorrowIn (a b : Vec16) (bin : Nat) : Vec16 × Nat :=
  let (a0, a1) := splitVec16 a
  let (b0, b1) := splitVec16 b
  let (d0, r0) := subVec8WithBorrowIn a0 b0 bin
  let (d1, r1) := subVec8WithBorrowIn a1 b1 r0
  (mergeVec8 d0 d1, r1)

/-- 16-limb base-1000 ripple-borrow subtraction returning (diff, borrow_out). -/
def subVec16WithBorrow (a b : Vec16) : Vec16 × Nat :=
  subVec16WithBorrowIn a b 0

/-- Shift a Vec32 (< 1000^24) left by 8 base-1000 limbs (× 1000^8). -/
def shiftLeft8ToVec32 (v : Vec32) : Vec32 :=
  let (lo0, lo1) := splitVec16 v.lo
  let (hi0, _) := splitVec16 v.hi
  ⟨mergeVec8 zeroVec8 lo0, mergeVec8 lo1 hi0⟩

/-- Shift a Vec16 left by 16 base-1000 limbs (× 1000^16) into Vec32. -/
def shiftLeft16ToVec32 (v : Vec16) : Vec32 :=
  ⟨zeroVec16, v⟩

/-- 32-limb base-1000 addition (exact modulo 1000^32). -/
def addVec32 (a b : Vec32) : Vec32 :=
  let (lo, c0) := addVec16WithCarryIn a.lo b.lo 0
  let (hi, _) := addVec16WithCarryIn a.hi b.hi c0
  ⟨lo, hi⟩

/-- 32-limb base-1000 subtraction (exact when b ≤ a). -/
def subVec32 (a b : Vec32) : Vec32 :=
  let (lo, b0) := subVec16WithBorrowIn a.lo b.lo 0
  let (hi, _) := subVec16WithBorrowIn a.hi b.hi b0
  ⟨lo, hi⟩

/-- 2x2 Karatsuba-over-CRT-NTT 96-digit base-1000 big-integer multiplier. -/
def karatsubaCrtNttMul96 (A B : Vec16) : Vec32 :=
  let (a0, a1) := splitVec16 A
  let (b0, b1) := splitVec16 B
  let p0 := crtNttBigMulVec8 a0 b0
  let p2 := crtNttBigMulVec8 a1 b1
  let (sa, ca) := addVec8WithCarry a0 a1
  let (sb, cb) := addVec8WithCarry b0 b1
  let pmid := crtNttBigMulVec8 sa sb
  let tCa : Vec32 := if ca = 0 then ⟨zeroVec16, zeroVec16⟩ else ⟨mergeVec8 zeroVec8 sb, zeroVec16⟩
  let tCb : Vec32 := if cb = 0 then ⟨zeroVec16, zeroVec16⟩ else ⟨mergeVec8 zeroVec8 sa, zeroVec16⟩
  let tCab : Vec32 :=
    if ca = 0 then ⟨zeroVec16, zeroVec16⟩
    else if cb = 0 then ⟨zeroVec16, zeroVec16⟩
    else ⟨zeroVec16, oneVec16⟩
  let crossProd := addVec32 ⟨pmid, zeroVec16⟩ (addVec32 tCa (addVec32 tCb tCab))
  let z1 := subVec32 (subVec32 crossProd ⟨p0, zeroVec16⟩) ⟨p2, zeroVec16⟩
  let z0 : Vec32 := ⟨p0, zeroVec16⟩
  let z1s := shiftLeft8ToVec32 z1
  let z2 := shiftLeft16ToVec32 p2
  addVec32 z0 (addVec32 z1s z2)

private theorem pow8_1000 :
    1000 ^ 8 = 1000 * (1000 * (1000 * (1000 * (1000 * (1000 * (1000 * 1000)))))) := by
  decide

private theorem pow16_1000 : (1000 ^ 8) * (1000 ^ 8) = 1000 ^ 16 := by decide
private theorem pow32_1000 : (1000 ^ 16) * (1000 ^ 16) = 1000 ^ 32 := by decide

/-- Positional decomposition of a 16-limb base-1000 vector into two 8-limb halves. -/
theorem splitVec16_eval (v : Vec16) :
    evalDigits1000Vec16 v =
    evalDigits1000Vec8 (splitVec16 v).1 + (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v).2 := by
  dsimp only [evalDigits1000Vec16, evalDigits1000Vec8, splitVec16]
  rw [pow8_1000]
  simp only [Nat.mul_add, Nat.mul_assoc]
  ac_rfl

private theorem mergeVec8_eval (lo hi : Vec8) :
    evalDigits1000Vec16 (mergeVec8 lo hi) =
    evalDigits1000Vec8 lo + (1000 ^ 8) * evalDigits1000Vec8 hi := by
  have hsp : splitVec16 (mergeVec8 lo hi) = (lo, hi) := rfl
  have h := splitVec16_eval (mergeVec8 lo hi)
  rw [hsp] at h
  exact h

private theorem splitVec16_normalized (v : Vec16) (hv : isNormalizedVec16 v) :
    isNormalizedVec8 (splitVec16 v).1 ∧ isNormalizedVec8 (splitVec16 v).2 := by
  rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩⟩

private theorem mergeVec8_normalized (lo hi : Vec8)
    (hlo : isNormalizedVec8 lo) (hhi : isNormalizedVec8 hi) :
    isNormalizedVec16 (mergeVec8 lo hi) := by
  rcases hlo with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  rcases hhi with ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

private theorem mul_lt_mul_bound (a b A B : Nat) (ha : a < A) (hb : b < B) :
    a + A * b < A * B := by
  have h1 : a + A * b < A + A * b := Nat.add_lt_add_right ha (A * b)
  have h2 : A + A * b = A * (b + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  have h3 : A * (b + 1) ≤ A * B := Nat.mul_le_mul_left A hb
  exact Nat.lt_of_lt_of_le h1 (h2 ▸ h3)

private theorem evalDigits1000Vec16_lt (v : Vec16) (hv : isNormalizedVec16 v) :
    evalDigits1000Vec16 v < 1000 ^ 16 := by
  rw [splitVec16_eval v, ← pow16_1000]
  have hsp := splitVec16_normalized v hv
  exact mul_lt_mul_bound _ _ _ _ (evalDigits1000Vec8_lt _ hsp.1) (evalDigits1000Vec8_lt _ hsp.2)

private theorem addLimb1000_sound (x y cin : Nat) (hx : x < 1000) (hy : y < 1000) (hc : cin ≤ 1) :
    let r := addLimb1000 x y cin
    r.1 < 1000 ∧ r.2 ≤ 1 ∧ r.1 + 1000 * r.2 = x + y + cin := by
  dsimp only [addLimb1000]
  refine ⟨Nat.mod_lt _ (by decide), ?_, Nat.mod_add_div _ 1000⟩
  omega

private theorem subLimb1000_sound (x y bin : Nat) (hx : x < 1000) (hy : y < 1000) (hb : bin ≤ 1) :
    (subLimb1000 x y bin).1 < 1000 ∧ (subLimb1000 x y bin).2 ≤ 1 ∧
    (subLimb1000 x y bin).1 + y + bin = x + 1000 * (subLimb1000 x y bin).2 := by
  dsimp only [subLimb1000]
  have htlt : 1000 + x - (y + bin) < 2 * 1000 := by omega
  have hdlt : (1000 + x - (y + bin)) / 1000 < 2 :=
    div_lt_of_lt_mul_pure (by rw [Nat.mul_comm]; exact htlt)
  have hdm := Nat.mod_add_div (1000 + x - (y + bin)) 1000
  refine ⟨Nat.mod_lt _ (by decide), by omega, by omega⟩

private theorem carry_chain_step (B0 s a b cin cout cTop sRest A B K : Nat)
    (h : s + B0 * cout = a + b + cin) (hRest : sRest + K * cTop = A + B + cout) :
    (s + B0 * sRest) + (B0 * K) * cTop = (a + B0 * A) + (b + B0 * B) + cin := by
  calc (s + B0 * sRest) + (B0 * K) * cTop
      = s + B0 * (sRest + K * cTop) := by rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add]
    _ = s + B0 * (A + B + cout) := by rw [hRest]
    _ = (s + B0 * cout) + B0 * A + B0 * B := by
          rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    _ = (a + B0 * A) + (b + B0 * B) + cin := by rw [h]; ac_rfl

private theorem borrow_chain_step (B0 d a b bin bout bTop dRest A B K : Nat)
    (h : d + b + bin = a + B0 * bout) (hRest : dRest + B + bout = A + K * bTop) :
    (d + B0 * dRest) + (b + B0 * B) + bin = (a + B0 * A) + (B0 * K) * bTop := by
  calc (d + B0 * dRest) + (b + B0 * B) + bin
      = (d + b + bin) + (B0 * dRest + B0 * B) := by ac_rfl
    _ = a + B0 * (dRest + B + bout) := by
          rw [h, ← Nat.mul_add, Nat.add_assoc a, ← Nat.mul_add]
          have hcom : bout + (dRest + B) = dRest + B + bout := by ac_rfl
          rw [hcom]
    _ = a + B0 * (A + K * bTop) := by rw [hRest]
    _ = (a + B0 * A) + (B0 * K) * bTop := by rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

private theorem addVec8WithCarryIn_sound (a b : Vec8) (cin : Nat)
    (ha : isNormalizedVec8 a) (hb : isNormalizedVec8 b) (hc : cin ≤ 1) :
    isNormalizedVec8 (addVec8WithCarryIn a b cin).1 ∧
    (addVec8WithCarryIn a b cin).2 ≤ 1 ∧
    evalDigits1000Vec8 (addVec8WithCarryIn a b cin).1 + (1000 ^ 8) * (addVec8WithCarryIn a b cin).2 =
    evalDigits1000Vec8 a + evalDigits1000Vec8 b + cin := by
  rcases ha with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases hb with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  dsimp only [addVec8WithCarryIn]
  have h0 := addLimb1000_sound a.x0 b.x0 cin a0 b0 hc
  have h1 := addLimb1000_sound a.x1 b.x1 (addLimb1000 a.x0 b.x0 cin).2 a1 b1 h0.2.1
  have h2 := addLimb1000_sound a.x2 b.x2 _ a2 b2 h1.2.1
  have h3 := addLimb1000_sound a.x3 b.x3 _ a3 b3 h2.2.1
  have h4 := addLimb1000_sound a.x4 b.x4 _ a4 b4 h3.2.1
  have h5 := addLimb1000_sound a.x5 b.x5 _ a5 b5 h4.2.1
  have h6 := addLimb1000_sound a.x6 b.x6 _ a6 b6 h5.2.1
  have h7 := addLimb1000_sound a.x7 b.x7 _ a7 b7 h6.2.1
  refine ⟨⟨h0.1, h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1⟩, h7.2.1, ?_⟩
  dsimp only [evalDigits1000Vec8]
  rw [pow8_1000]
  have s6 := carry_chain_step 1000 _ _ _ _ _ _ _ a.x7 b.x7 1000 h6.2.2 h7.2.2
  have s5 := carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h5.2.2 s6
  have s4 := carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h4.2.2 s5
  have s3 := carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h3.2.2 s4
  have s2 := carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h2.2.2 s3
  have s1 := carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h1.2.2 s2
  exact carry_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h0.2.2 s1

/-- Constructive soundness and 1-bit carry bound of 8-limb ripple addition. -/
theorem addVec8WithCarry_sound (a b : Vec8) (ha : isNormalizedVec8 a) (hb : isNormalizedVec8 b) :
    let (s, c) := addVec8WithCarry a b
    isNormalizedVec8 s ∧ c ≤ 1 ∧
    evalDigits1000Vec8 s + (1000 ^ 8) * c = evalDigits1000Vec8 a + evalDigits1000Vec8 b := by
  have h := addVec8WithCarryIn_sound a b 0 ha hb (by decide)
  simpa only [addVec8WithCarry, Nat.add_zero] using h

private theorem addVec16WithCarryIn_sound (a b : Vec16) (cin : Nat)
    (ha : isNormalizedVec16 a) (hb : isNormalizedVec16 b) (hc : cin ≤ 1) :
    isNormalizedVec16 (addVec16WithCarryIn a b cin).1 ∧
    (addVec16WithCarryIn a b cin).2 ≤ 1 ∧
    evalDigits1000Vec16 (addVec16WithCarryIn a b cin).1 +
      (1000 ^ 16) * (addVec16WithCarryIn a b cin).2 =
    evalDigits1000Vec16 a + evalDigits1000Vec16 b + cin := by
  have has := splitVec16_normalized a ha
  have hbs := splitVec16_normalized b hb
  dsimp only [addVec16WithCarryIn]
  have hlo := addVec8WithCarryIn_sound (splitVec16 a).1 (splitVec16 b).1 cin has.1 hbs.1 hc
  have hhi := addVec8WithCarryIn_sound (splitVec16 a).2 (splitVec16 b).2
    (addVec8WithCarryIn (splitVec16 a).1 (splitVec16 b).1 cin).2 has.2 hbs.2 hlo.2.1
  refine ⟨mergeVec8_normalized _ _ hlo.1 hhi.1, hhi.2.1, ?_⟩
  rw [mergeVec8_eval, splitVec16_eval a, splitVec16_eval b, ← pow16_1000]
  exact carry_chain_step (1000 ^ 8) _ _ _ _ _ _ _ _ _ (1000 ^ 8) hlo.2.2 hhi.2.2

private theorem subVec8WithBorrowIn_sound (a b : Vec8) (bin : Nat)
    (ha : isNormalizedVec8 a) (hb : isNormalizedVec8 b) (hbn : bin ≤ 1) :
    isNormalizedVec8 (subVec8WithBorrowIn a b bin).1 ∧
    (subVec8WithBorrowIn a b bin).2 ≤ 1 ∧
    evalDigits1000Vec8 (subVec8WithBorrowIn a b bin).1 + evalDigits1000Vec8 b + bin =
    evalDigits1000Vec8 a + (1000 ^ 8) * (subVec8WithBorrowIn a b bin).2 := by
  rcases ha with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases hb with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  dsimp only [subVec8WithBorrowIn]
  let r0 := subLimb1000 a.x0 b.x0 bin
  let r1 := subLimb1000 a.x1 b.x1 r0.2
  let r2 := subLimb1000 a.x2 b.x2 r1.2
  let r3 := subLimb1000 a.x3 b.x3 r2.2
  let r4 := subLimb1000 a.x4 b.x4 r3.2
  let r5 := subLimb1000 a.x5 b.x5 r4.2
  let r6 := subLimb1000 a.x6 b.x6 r5.2
  let r7 := subLimb1000 a.x7 b.x7 r6.2
  have h0 := subLimb1000_sound a.x0 b.x0 bin a0 b0 hbn
  have h1 := subLimb1000_sound a.x1 b.x1 r0.2 a1 b1 h0.2.1
  have h2 := subLimb1000_sound a.x2 b.x2 r1.2 a2 b2 h1.2.1
  have h3 := subLimb1000_sound a.x3 b.x3 r2.2 a3 b3 h2.2.1
  have h4 := subLimb1000_sound a.x4 b.x4 r3.2 a4 b4 h3.2.1
  have h5 := subLimb1000_sound a.x5 b.x5 r4.2 a5 b5 h4.2.1
  have h6 := subLimb1000_sound a.x6 b.x6 r5.2 a6 b6 h5.2.1
  have h7 := subLimb1000_sound a.x7 b.x7 r6.2 a7 b7 h6.2.1
  refine ⟨⟨h0.1, h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1⟩, h7.2.1, ?_⟩
  dsimp only [evalDigits1000Vec8]
  rw [pow8_1000]
  have s6 := borrow_chain_step 1000 _ _ _ _ _ _ _ a.x7 b.x7 1000 h6.2.2 h7.2.2
  have s5 := borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h5.2.2 s6
  have s4 := borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h4.2.2 s5
  have s3 := borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h3.2.2 s4
  have s2 := borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h2.2.2 s3
  have s1 := borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h1.2.2 s2
  exact borrow_chain_step 1000 _ _ _ _ _ _ _ _ _ _ h0.2.2 s1

private theorem subVec16WithBorrowIn_sound (a b : Vec16) (bin : Nat)
    (ha : isNormalizedVec16 a) (hb : isNormalizedVec16 b) (hbn : bin ≤ 1) :
    isNormalizedVec16 (subVec16WithBorrowIn a b bin).1 ∧
    (subVec16WithBorrowIn a b bin).2 ≤ 1 ∧
    evalDigits1000Vec16 (subVec16WithBorrowIn a b bin).1 + evalDigits1000Vec16 b + bin =
    evalDigits1000Vec16 a + (1000 ^ 16) * (subVec16WithBorrowIn a b bin).2 := by
  have has := splitVec16_normalized a ha
  have hbs := splitVec16_normalized b hb
  dsimp only [subVec16WithBorrowIn]
  have hlo := subVec8WithBorrowIn_sound (splitVec16 a).1 (splitVec16 b).1 bin has.1 hbs.1 hbn
  have hhi := subVec8WithBorrowIn_sound (splitVec16 a).2 (splitVec16 b).2
    (subVec8WithBorrowIn (splitVec16 a).1 (splitVec16 b).1 bin).2 has.2 hbs.2 hlo.2.1
  refine ⟨mergeVec8_normalized _ _ hlo.1 hhi.1, hhi.2.1, ?_⟩
  rw [mergeVec8_eval, splitVec16_eval a, splitVec16_eval b, ← pow16_1000]
  exact borrow_chain_step (1000 ^ 8) _ _ _ _ _ _ _ _ _ (1000 ^ 8) hlo.2.2 hhi.2.2

private theorem evalDigits1000Vec32_lt (v : Vec32) (hv : isNormalizedVec32 v) :
    evalDigits1000Vec32 v < 1000 ^ 32 := by
  dsimp only [evalDigits1000Vec32]
  rw [← pow32_1000]
  exact mul_lt_mul_bound _ _ _ _
    (evalDigits1000Vec16_lt v.lo hv.1) (evalDigits1000Vec16_lt v.hi hv.2)

private theorem addVec32_sound (a b : Vec32) (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b)
    (hlt : evalDigits1000Vec32 a + evalDigits1000Vec32 b < 1000 ^ 32) :
    isNormalizedVec32 (addVec32 a b) ∧
    evalDigits1000Vec32 (addVec32 a b) = evalDigits1000Vec32 a + evalDigits1000Vec32 b := by
  let rlo := addVec16WithCarryIn a.lo b.lo 0
  let rhi := addVec16WithCarryIn a.hi b.hi rlo.2
  have hlo := addVec16WithCarryIn_sound a.lo b.lo 0 ha.1 hb.1 (by decide)
  have hhi := addVec16WithCarryIn_sound a.hi b.hi rlo.2 ha.2 hb.2 hlo.2.1
  change isNormalizedVec32 ⟨rlo.1, rhi.1⟩ ∧
    evalDigits1000Vec32 ⟨rlo.1, rhi.1⟩ = evalDigits1000Vec32 a + evalDigits1000Vec32 b
  refine ⟨⟨hlo.1, hhi.1⟩, ?_⟩
  have hch := carry_chain_step (1000 ^ 16) _ _ _ _ _ _ _ _ _ (1000 ^ 16) hlo.2.2 hhi.2.2
  dsimp only [evalDigits1000Vec32]
  rw [Nat.add_zero, pow32_1000] at hch
  have hc0 : rhi.2 = 0 := by
    by_cases hcz : rhi.2 = 0
    · exact hcz
    · have : 1000 ^ 32 ≤ (1000 ^ 32) * (addVec16WithCarryIn a.hi b.hi rlo.2).2 :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hcz)
      dsimp only [evalDigits1000Vec32, rhi, rlo] at hlt hch ⊢
      omega
  rw [hc0, Nat.mul_zero, Nat.add_zero] at hch
  exact hch

private theorem subVec32_sound (a b : Vec32) (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b)
    (hle : evalDigits1000Vec32 b ≤ evalDigits1000Vec32 a) :
    isNormalizedVec32 (subVec32 a b) ∧
    evalDigits1000Vec32 (subVec32 a b) + evalDigits1000Vec32 b = evalDigits1000Vec32 a := by
  let rlo := subVec16WithBorrowIn a.lo b.lo 0
  let rhi := subVec16WithBorrowIn a.hi b.hi rlo.2
  have hlo := subVec16WithBorrowIn_sound a.lo b.lo 0 ha.1 hb.1 (by decide)
  have hhi := subVec16WithBorrowIn_sound a.hi b.hi rlo.2 ha.2 hb.2 hlo.2.1
  change isNormalizedVec32 ⟨rlo.1, rhi.1⟩ ∧
    evalDigits1000Vec32 ⟨rlo.1, rhi.1⟩ + evalDigits1000Vec32 b = evalDigits1000Vec32 a
  refine ⟨⟨hlo.1, hhi.1⟩, ?_⟩
  have hch := borrow_chain_step (1000 ^ 16) _ _ _ _ _ _ _ _ _ (1000 ^ 16) hlo.2.2 hhi.2.2
  dsimp only [evalDigits1000Vec32]
  rw [Nat.add_zero, pow32_1000] at hch
  have hb0 : rhi.2 = 0 := by
    by_cases hbz : rhi.2 = 0
    · exact hbz
    · have : 1000 ^ 32 ≤ (1000 ^ 32) * (subVec16WithBorrowIn a.hi b.hi rlo.2).2 :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hbz)
      have hsublt := evalDigits1000Vec32_lt ⟨rlo.1, rhi.1⟩ ⟨hlo.1, hhi.1⟩
      dsimp only [evalDigits1000Vec32, rhi, rlo] at hle hsublt hch ⊢
      omega
  rw [hb0, Nat.mul_zero, Nat.add_zero] at hch
  exact hch

private theorem zeroVec8_norm : isNormalizedVec8 zeroVec8 := by
  dsimp [isNormalizedVec8, zeroVec8]; refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

private theorem zeroVec16_norm : isNormalizedVec16 zeroVec16 :=
  mergeVec8_normalized _ _ zeroVec8_norm zeroVec8_norm

private theorem oneVec16_norm : isNormalizedVec16 oneVec16 := by
  dsimp only [isNormalizedVec16, oneVec16]; refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

private theorem eval_zeroVec8 : evalDigits1000Vec8 zeroVec8 = 0 := by decide
private theorem eval_zeroVec16 : evalDigits1000Vec16 zeroVec16 = 0 := by decide
private theorem eval_oneVec16 : evalDigits1000Vec16 oneVec16 = 1 := by decide

private theorem crtNttBigMulVec8_normalized (a b : Vec8) :
    isNormalizedVec16 (crtNttBigMulVec8 a b) := by
  dsimp only [isNormalizedVec16, crtNttBigMulVec8, carryPassBase1000]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
         Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

private theorem shiftLeft8ToVec32_sound (v : Vec32) (hv : isNormalizedVec32 v)
    (hlt : evalDigits1000Vec32 v < 1000 ^ 24) :
    isNormalizedVec32 (shiftLeft8ToVec32 v) ∧
    evalDigits1000Vec32 (shiftLeft8ToVec32 v) = (1000 ^ 8) * evalDigits1000Vec32 v := by
  have hlo := splitVec16_normalized v.lo hv.1
  have hhi := splitVec16_normalized v.hi hv.2
  have hhi_lt : evalDigits1000Vec16 v.hi < 1000 ^ 8 := by
    have hmul : (1000 ^ 16) * (1000 ^ 8) = 1000 ^ 24 := by decide
    dsimp only [evalDigits1000Vec32] at hlt
    by_cases hc : evalDigits1000Vec16 v.hi < 1000 ^ 8
    · exact hc
    · have hge : 1000 ^ 8 ≤ evalDigits1000Vec16 v.hi := Nat.le_of_not_lt hc
      have : 1000 ^ 24 ≤ (1000 ^ 16) * evalDigits1000Vec16 v.hi := by
        rw [← hmul]; exact Nat.mul_le_mul_left _ hge
      omega
  have hhi1_zero : evalDigits1000Vec8 (splitVec16 v.hi).2 = 0 := by
    rw [splitVec16_eval v.hi] at hhi_lt
    by_cases hz : evalDigits1000Vec8 (splitVec16 v.hi).2 = 0
    · exact hz
    · have hge : 1 ≤ evalDigits1000Vec8 (splitVec16 v.hi).2 := Nat.pos_of_ne_zero hz
      have : 1000 ^ 8 ≤ (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.hi).2 :=
        Nat.le_mul_of_pos_right _ hge
      omega
  dsimp only [shiftLeft8ToVec32]
  refine ⟨⟨mergeVec8_normalized _ _ zeroVec8_norm hlo.1,
           mergeVec8_normalized _ _ hlo.2 hhi.1⟩, ?_⟩
  dsimp only [evalDigits1000Vec32]
  rw [mergeVec8_eval, mergeVec8_eval, eval_zeroVec8, Nat.zero_add]
  rw [splitVec16_eval v.lo, splitVec16_eval v.hi, hhi1_zero, Nat.mul_zero, Nat.add_zero]
  have h24 : (1000 ^ 16) * (1000 ^ 8) = (1000 ^ 8) * (1000 ^ 16) := Nat.mul_comm _ _
  calc (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.lo).1 +
        (1000 ^ 16) * (evalDigits1000Vec8 (splitVec16 v.lo).2 +
        (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.hi).1)
      = (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.lo).1 +
        ((1000 ^ 16) * evalDigits1000Vec8 (splitVec16 v.lo).2 +
        (1000 ^ 16) * ((1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.hi).1)) := by
          rw [Nat.mul_add]
    _ = (1000 ^ 8) * (evalDigits1000Vec8 (splitVec16 v.lo).1 +
        (1000 ^ 8) * evalDigits1000Vec8 (splitVec16 v.lo).2 +
        (1000 ^ 16) * evalDigits1000Vec8 (splitVec16 v.hi).1) := by
          rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, pow16_1000, h24]
          ac_rfl

/-- Exact algebraic Karatsuba polynomial identity over Nat. -/
theorem karatsuba_algebraic_identity (A0 A1 B0 B1 K : Nat) :
    (A0 + K * A1) * (B0 + K * B1) =
    A0 * B0 + K * ((A0 + A1) * (B0 + B1) - A0 * B0 - A1 * B1) + K * K * (A1 * B1) := by
  have hmid : (A0 + A1) * (B0 + B1) - A0 * B0 - A1 * B1 = A0 * B1 + A1 * B0 := by
    have hexp : (A0 + A1) * (B0 + B1) = A0 * B0 + (A0 * B1 + A1 * B0 + A1 * B1) := by
      simp only [Nat.mul_add, Nat.add_mul]; ac_rfl
    rw [hexp, Nat.add_comm (A0 * B0) _, Nat.add_sub_cancel]
    have hcom : A0 * B1 + A1 * B0 + A1 * B1 = (A0 * B1 + A1 * B0) + A1 * B1 := by ac_rfl
    rw [hcom, Nat.add_sub_cancel]
  rw [hmid]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  have hc : K * (A1 * B0) = K * A1 * B0 := by rw [Nat.mul_assoc]
  ac_rfl

private theorem karatsuba_middle_identity (a0 a1 b0 b1 sa ca sb cb K : Nat)
    (ha : sa + K * ca = a0 + a1) (hb : sb + K * cb = b0 + b1) :
    sa * sb + (ca * (K * sb) + (cb * (K * sa) + (ca * cb) * (K * K))) =
    (a0 + a1) * (b0 + b1) := by
  rw [← ha, ← hb]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  ac_rfl

private theorem karatsubaCrtNttMul96_core (A B : Vec16)
    (hA : isNormalizedVec16 A) (hB : isNormalizedVec16 B) :
    isNormalizedVec32 (karatsubaCrtNttMul96 A B) ∧
    evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) =
    evalDigits1000Vec16 A * evalDigits1000Vec16 B := by
  dsimp only [karatsubaCrtNttMul96]
  have hAs := splitVec16_normalized A hA
  have hBs := splitVec16_normalized B hB
  let a0 := (splitVec16 A).1
  let a1 := (splitVec16 A).2
  let b0 := (splitVec16 B).1
  let b1 := (splitVec16 B).2
  let p0 := crtNttBigMulVec8 a0 b0
  let p2 := crtNttBigMulVec8 a1 b1
  let sa := (addVec8WithCarry a0 a1).1
  let ca := (addVec8WithCarry a0 a1).2
  let sb := (addVec8WithCarry b0 b1).1
  let cb := (addVec8WithCarry b0 b1).2
  let pmid := crtNttBigMulVec8 sa sb
  have hsumA := addVec8WithCarry_sound a0 a1 hAs.1 hAs.2
  have hsumB := addVec8WithCarry_sound b0 b1 hBs.1 hBs.2
  have hp0_norm : isNormalizedVec16 p0 := crtNttBigMulVec8_normalized a0 b0
  have hp2_norm : isNormalizedVec16 p2 := crtNttBigMulVec8_normalized a1 b1
  have hpm_norm : isNormalizedVec16 pmid := crtNttBigMulVec8_normalized sa sb
  have hp0_val := crtNttBigMulVec8_universal_sound a0 b0 hAs.1 hBs.1
  have hp2_val := crtNttBigMulVec8_universal_sound a1 b1 hAs.2 hBs.2
  have hpm_val := crtNttBigMulVec8_universal_sound sa sb hsumA.1 hsumB.1
  let tCa : Vec32 := if ca = 0 then ⟨zeroVec16, zeroVec16⟩ else ⟨mergeVec8 zeroVec8 sb, zeroVec16⟩
  let tCb : Vec32 := if cb = 0 then ⟨zeroVec16, zeroVec16⟩ else ⟨mergeVec8 zeroVec8 sa, zeroVec16⟩
  let tCab : Vec32 :=
    if ca = 0 then ⟨zeroVec16, zeroVec16⟩
    else if cb = 0 then ⟨zeroVec16, zeroVec16⟩
    else ⟨zeroVec16, oneVec16⟩
  have htCa_norm : isNormalizedVec32 tCa := by
    dsimp only [tCa]; split
    · exact ⟨zeroVec16_norm, zeroVec16_norm⟩
    · exact ⟨mergeVec8_normalized _ _ zeroVec8_norm hsumB.1, zeroVec16_norm⟩
  have htCb_norm : isNormalizedVec32 tCb := by
    dsimp only [tCb]; split
    · exact ⟨zeroVec16_norm, zeroVec16_norm⟩
    · exact ⟨mergeVec8_normalized _ _ zeroVec8_norm hsumA.1, zeroVec16_norm⟩
  have htCab_norm : isNormalizedVec32 tCab := by
    dsimp only [tCab]; split
    · exact ⟨zeroVec16_norm, zeroVec16_norm⟩
    · split
      · exact ⟨zeroVec16_norm, zeroVec16_norm⟩
      · exact ⟨zeroVec16_norm, oneVec16_norm⟩
  have htCa_val : evalDigits1000Vec32 tCa = ca * (1000 ^ 8 * evalDigits1000Vec8 sb) := by
    have hca1 : ca ≤ 1 := hsumA.2.1
    dsimp only [tCa, evalDigits1000Vec32]; split
    · rename_i hcz; rw [hcz, Nat.zero_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero]
    · rename_i hcz
      have hca_eq : ca = 1 := by omega
      rw [hca_eq, Nat.one_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero, mergeVec8_eval, eval_zeroVec8, Nat.zero_add]
  have htCb_val : evalDigits1000Vec32 tCb = cb * (1000 ^ 8 * evalDigits1000Vec8 sa) := by
    have hcb1 : cb ≤ 1 := hsumB.2.1
    dsimp only [tCb, evalDigits1000Vec32]; split
    · rename_i hcz; rw [hcz, Nat.zero_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero]
    · rename_i hcz
      have hcb_eq : cb = 1 := by omega
      rw [hcb_eq, Nat.one_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero, mergeVec8_eval, eval_zeroVec8, Nat.zero_add]
  have htCab_val : evalDigits1000Vec32 tCab = (ca * cb) * 1000 ^ 16 := by
    have hca1 : ca ≤ 1 := hsumA.2.1
    have hcb1 : cb ≤ 1 := hsumB.2.1
    dsimp only [tCab, evalDigits1000Vec32]; split
    · rename_i hca; rw [hca, Nat.zero_mul, Nat.zero_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero]
    · rename_i hca
      have hca_eq : ca = 1 := by omega
      split
      · rename_i hcb; rw [hcb, Nat.mul_zero, Nat.zero_mul, eval_zeroVec16, Nat.mul_zero, Nat.add_zero]
      · rename_i hcb
        have hcb_eq : cb = 1 := by omega
        rw [hca_eq, hcb_eq, Nat.mul_one, Nat.one_mul,
            eval_zeroVec16, eval_oneVec16, Nat.mul_one, Nat.zero_add]
  have htCa_lt : evalDigits1000Vec32 tCa < 1000 ^ 16 := by
    rw [htCa_val, ← pow16_1000]
    have hsb := evalDigits1000Vec8_lt sb hsumB.1
    by_cases hcz : ca = 0
    · rw [hcz, Nat.zero_mul]; decide
    · have hca1 : ca ≤ 1 := hsumA.2.1
      have hca_eq : ca = 1 := by omega
      rw [hca_eq, Nat.one_mul]
      exact Nat.mul_lt_mul_of_pos_left hsb (by decide)
  have htCb_lt : evalDigits1000Vec32 tCb < 1000 ^ 16 := by
    rw [htCb_val, ← pow16_1000]
    have hsa := evalDigits1000Vec8_lt sa hsumA.1
    by_cases hcz : cb = 0
    · rw [hcz, Nat.zero_mul]; decide
    · have hcb1 : cb ≤ 1 := hsumB.2.1
      have hcb_eq : cb = 1 := by omega
      rw [hcb_eq, Nat.one_mul]
      exact Nat.mul_lt_mul_of_pos_left hsa (by decide)
  have htCab_le : evalDigits1000Vec32 tCab ≤ 1000 ^ 16 := by
    rw [htCab_val]
    have hca1 : ca ≤ 1 := hsumA.2.1
    have hcb1 : cb ≤ 1 := hsumB.2.1
    have hprod1 : ca * cb ≤ 1 := Nat.mul_le_mul hca1 hcb1
    exact Nat.le_trans (Nat.mul_le_mul_right (1000 ^ 16) hprod1) (Nat.le_of_eq (Nat.one_mul _))
  have hpm_lt : evalDigits1000Vec32 ⟨pmid, zeroVec16⟩ < 1000 ^ 16 := by
    dsimp only [evalDigits1000Vec32]
    rw [eval_zeroVec16, Nat.mul_zero, Nat.add_zero]
    exact evalDigits1000Vec16_lt pmid hpm_norm
  have h16x4 : 4 * 1000 ^ 16 + 1 ≤ 1000 ^ 32 := by decide
  have hs1 := addVec32_sound tCb tCab htCb_norm htCab_norm (by omega)
  have hs2 := addVec32_sound tCa (addVec32 tCb tCab) htCa_norm hs1.1 (by omega)
  have hs3 := addVec32_sound ⟨pmid, zeroVec16⟩ (addVec32 tCa (addVec32 tCb tCab))
    ⟨hpm_norm, zeroVec16_norm⟩ hs2.1 (by omega)
  have hcross_val : evalDigits1000Vec32 (addVec32 ⟨pmid, zeroVec16⟩ (addVec32 tCa (addVec32 tCb tCab))) =
      (evalDigits1000Vec8 a0 + evalDigits1000Vec8 a1) * (evalDigits1000Vec8 b0 + evalDigits1000Vec8 b1) := by
    rw [hs3.2, hs2.2, hs1.2, htCa_val, htCb_val, htCab_val, ← pow16_1000]
    have hm0 : evalDigits1000Vec32 ⟨pmid, zeroVec16⟩ = evalDigits1000Vec8 sa * evalDigits1000Vec8 sb := by
      dsimp only [evalDigits1000Vec32]; rw [eval_zeroVec16, Nat.mul_zero, Nat.add_zero]; exact hpm_val
    rw [hm0]
    exact karatsuba_middle_identity _ _ _ _ _ _ _ _ (1000 ^ 8) hsumA.2.2 hsumB.2.2
  have hp0_v32 : evalDigits1000Vec32 ⟨p0, zeroVec16⟩ =
      evalDigits1000Vec8 a0 * evalDigits1000Vec8 b0 := by
    dsimp only [evalDigits1000Vec32]; rw [eval_zeroVec16, Nat.mul_zero, Nat.add_zero]; exact hp0_val
  have hp2_v32 : evalDigits1000Vec32 ⟨p2, zeroVec16⟩ =
      evalDigits1000Vec8 a1 * evalDigits1000Vec8 b1 := by
    dsimp only [evalDigits1000Vec32]; rw [eval_zeroVec16, Nat.mul_zero, Nat.add_zero]; exact hp2_val
  have hle0 : evalDigits1000Vec32 ⟨p0, zeroVec16⟩ ≤
      evalDigits1000Vec32 (addVec32 ⟨pmid, zeroVec16⟩ (addVec32 tCa (addVec32 tCb tCab))) := by
    rw [hp0_v32, hcross_val]
    exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hsub1 := subVec32_sound _ ⟨p0, zeroVec16⟩ hs3.1 ⟨hp0_norm, zeroVec16_norm⟩ hle0
  have hsub1_eq : evalDigits1000Vec32 (subVec32 (addVec32 ⟨pmid, zeroVec16⟩
      (addVec32 tCa (addVec32 tCb tCab))) ⟨p0, zeroVec16⟩) =
      (evalDigits1000Vec8 a0 + evalDigits1000Vec8 a1) *
      (evalDigits1000Vec8 b0 + evalDigits1000Vec8 b1) -
      evalDigits1000Vec8 a0 * evalDigits1000Vec8 b0 := by
    have h2 := hsub1.2
    rw [hcross_val, hp0_v32] at h2
    exact Nat.eq_sub_of_add_eq h2
  have hle2 : evalDigits1000Vec32 ⟨p2, zeroVec16⟩ ≤
      evalDigits1000Vec32 (subVec32 (addVec32 ⟨pmid, zeroVec16⟩
        (addVec32 tCa (addVec32 tCb tCab))) ⟨p0, zeroVec16⟩) := by
    rw [hp2_v32, hsub1_eq]
    have hmul_ge : evalDigits1000Vec8 a0 * evalDigits1000Vec8 b0 +
        evalDigits1000Vec8 a1 * evalDigits1000Vec8 b1 ≤
        (evalDigits1000Vec8 a0 + evalDigits1000Vec8 a1) *
        (evalDigits1000Vec8 b0 + evalDigits1000Vec8 b1) := by
      simp only [Nat.mul_add, Nat.add_mul]; omega
    omega
  have hsub2 := subVec32_sound _ ⟨p2, zeroVec16⟩ hsub1.1 ⟨hp2_norm, zeroVec16_norm⟩ hle2
  let z1 := subVec32 (subVec32 (addVec32 ⟨pmid, zeroVec16⟩
    (addVec32 tCa (addVec32 tCb tCab))) ⟨p0, zeroVec16⟩) ⟨p2, zeroVec16⟩
  have hz1_eq : evalDigits1000Vec32 z1 =
      (evalDigits1000Vec8 a0 + evalDigits1000Vec8 a1) *
      (evalDigits1000Vec8 b0 + evalDigits1000Vec8 b1) -
      evalDigits1000Vec8 a0 * evalDigits1000Vec8 b0 -
      evalDigits1000Vec8 a1 * evalDigits1000Vec8 b1 := by
    have h2 := hsub2.2
    rw [hsub1_eq, hp2_v32] at h2
    exact Nat.eq_sub_of_add_eq h2
  have hz1_lt : evalDigits1000Vec32 z1 < 1000 ^ 24 := by
    have ha0_lt := evalDigits1000Vec8_lt a0 hAs.1
    have ha1_lt := evalDigits1000Vec8_lt a1 hAs.2
    have hb0_lt := evalDigits1000Vec8_lt b0 hBs.1
    have hb1_lt := evalDigits1000Vec8_lt b1 hBs.2
    have hsum_lt : (evalDigits1000Vec8 a0 + evalDigits1000Vec8 a1) *
        (evalDigits1000Vec8 b0 + evalDigits1000Vec8 b1) < 4 * 1000 ^ 16 := by
      have h416 : (2 * 1000 ^ 8) * (2 * 1000 ^ 8) = 4 * 1000 ^ 16 := by decide
      rw [← h416]
      exact Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
    have h4_lt : 4 * 1000 ^ 16 < 1000 ^ 24 := by decide
    omega
  have hz1s := shiftLeft8ToVec32_sound z1 hsub2.1 hz1_lt
  have hz2_norm : isNormalizedVec32 (shiftLeft16ToVec32 p2) := ⟨zeroVec16_norm, hp2_norm⟩
  have hz2_val : evalDigits1000Vec32 (shiftLeft16ToVec32 p2) =
      1000 ^ 16 * (evalDigits1000Vec8 a1 * evalDigits1000Vec8 b1) := by
    dsimp only [shiftLeft16ToVec32, evalDigits1000Vec32]
    rw [eval_zeroVec16, Nat.zero_add, hp2_val]
  have hkar : evalDigits1000Vec16 A * evalDigits1000Vec16 B =
      evalDigits1000Vec32 ⟨p0, zeroVec16⟩ +
      (evalDigits1000Vec32 (shiftLeft8ToVec32 z1) +
       evalDigits1000Vec32 (shiftLeft16ToVec32 p2)) := by
    rw [splitVec16_eval A, splitVec16_eval B]
    rw [karatsuba_algebraic_identity _ _ _ _ (1000 ^ 8)]
    rw [hp0_v32, hz1s.2, hz1_eq, hz2_val, pow16_1000, Nat.add_assoc]
  have hAB_lt : evalDigits1000Vec16 A * evalDigits1000Vec16 B < 1000 ^ 32 := by
    rw [← pow32_1000]
    exact Nat.mul_lt_mul_of_lt_of_lt (evalDigits1000Vec16_lt A hA) (evalDigits1000Vec16_lt B hB)
  have hsum2_lt : evalDigits1000Vec32 (shiftLeft8ToVec32 z1) +
      evalDigits1000Vec32 (shiftLeft16ToVec32 p2) < 1000 ^ 32 := by omega
  have hfin1 := addVec32_sound (shiftLeft8ToVec32 z1) (shiftLeft16ToVec32 p2)
    hz1s.1 hz2_norm hsum2_lt
  have hsum_all_lt : evalDigits1000Vec32 ⟨p0, zeroVec16⟩ +
      evalDigits1000Vec32 (addVec32 (shiftLeft8ToVec32 z1) (shiftLeft16ToVec32 p2)) < 1000 ^ 32 := by
    rw [hfin1.2]; omega
  have hfin2 := addVec32_sound ⟨p0, zeroVec16⟩
    (addVec32 (shiftLeft8ToVec32 z1) (shiftLeft16ToVec32 p2))
    ⟨hp0_norm, zeroVec16_norm⟩ hfin1.1 hsum_all_lt
  refine ⟨hfin2.1, ?_⟩
  rw [hfin2.2, hfin1.2, ← hkar]

/-- Every limb of karatsubaCrtNttMul96 output is normalized (< 1000). -/
theorem karatsubaCrtNttMul96_normalized (A B : Vec16)
    (hA : isNormalizedVec16 A) (hB : isNormalizedVec16 B) :
    isNormalizedVec32 (karatsubaCrtNttMul96 A B) :=
  (karatsubaCrtNttMul96_core A B hA hB).1

/-- Universal 96-digit Karatsuba-over-CRT-NTT big-integer multiplication theorem. -/
theorem karatsubaCrtNttMul96_universal_sound (A B : Vec16)
    (hA : isNormalizedVec16 A) (hB : isNormalizedVec16 B) :
    evalDigits1000Vec32 (karatsubaCrtNttMul96 A B) =
    evalDigits1000Vec16 A * evalDigits1000Vec16 B :=
  (karatsubaCrtNttMul96_core A B hA hB).2

/-- Concrete 96-digit maximum product: (10^48 - 1) * (10^48 - 1) = 10^96 - 2 * 10^48 + 1. -/
theorem karatsuba_96_digit_max_verified :
    let max48 : Vec16 := ⟨999, 999, 999, 999, 999, 999, 999, 999,
                          999, 999, 999, 999, 999, 999, 999, 999⟩
    evalDigits1000Vec32 (karatsubaCrtNttMul96 max48 max48) = 10 ^ 96 - 2 * 10 ^ 48 + 1 ∧
    (10 ^ 48 - 1) * (10 ^ 48 - 1) = 10 ^ 96 - 2 * 10 ^ 48 + 1 := by
  let max48 : Vec16 := ⟨999, 999, 999, 999, 999, 999, 999, 999,
                        999, 999, 999, 999, 999, 999, 999, 999⟩
  have hnorm : isNormalizedVec16 max48 := by
    dsimp only [isNormalizedVec16, max48]
    refine ⟨by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide⟩
  have hev : evalDigits1000Vec16 max48 = 10 ^ 48 - 1 := by decide
  have hmax : (10 ^ 48 - 1) * (10 ^ 48 - 1) = 10 ^ 96 - 2 * 10 ^ 48 + 1 := by decide
  refine ⟨?_, hmax⟩
  rw [karatsubaCrtNttMul96_universal_sound max48 max48 hnorm hnorm, hev, hmax]

-- ============================================================================
-- Stage 4: 192-Digit (64-Limb Base-1000) 2x2 Karatsuba Multiplier (gemweb043)
-- ============================================================================

/-- A 64-limb (192-decimal-digit) base-1000 unsigned integer split into two 32-limb halves. -/
structure Vec64 where
  lo : Vec32
  hi : Vec32
  deriving DecidableEq, Repr

/-- Every limb in a Vec64 is strictly less than 1000. -/
def isNormalizedVec64 (v : Vec64) : Prop :=
  isNormalizedVec32 v.lo ∧ isNormalizedVec32 v.hi

/-- Evaluate a Vec64 in base 1000 using lo + 1000^32 * hi. -/
def evalDigits1000Vec64 (v : Vec64) : Nat :=
  evalDigits1000Vec32 v.lo + (1000 ^ 32) * evalDigits1000Vec32 v.hi

private def zeroVec32 : Vec32 := ⟨zeroVec16, zeroVec16⟩
private def oneVec32 : Vec32 := ⟨oneVec16, zeroVec16⟩

private theorem zeroVec32_norm : isNormalizedVec32 zeroVec32 := ⟨zeroVec16_norm, zeroVec16_norm⟩
private theorem oneVec32_norm : isNormalizedVec32 oneVec32 := ⟨oneVec16_norm, zeroVec16_norm⟩

private theorem eval_zeroVec32 : evalDigits1000Vec32 zeroVec32 = 0 := by
  dsimp only [evalDigits1000Vec32, zeroVec32]
  rw [eval_zeroVec16, Nat.mul_zero, Nat.add_zero]

private theorem eval_oneVec32 : evalDigits1000Vec32 oneVec32 = 1 := by
  dsimp only [evalDigits1000Vec32, oneVec32]
  rw [eval_oneVec16, eval_zeroVec16, Nat.mul_zero, Nat.add_zero]

private def addVec32WithCarryIn (a b : Vec32) (cin : Nat) : Vec32 × Nat :=
  let r0 := addVec16WithCarryIn a.lo b.lo cin
  let r1 := addVec16WithCarryIn a.hi b.hi r0.2
  (⟨r0.1, r1.1⟩, r1.2)

/-- Add two Vec32 values with carry-in 0, returning the 32-limb sum and carry-out bit. -/
def addVec32WithCarry (a b : Vec32) : Vec32 × Nat :=
  addVec32WithCarryIn a b 0

private def subVec32WithBorrowIn (a b : Vec32) (bin : Nat) : Vec32 × Nat :=
  let r0 := subVec16WithBorrowIn a.lo b.lo bin
  let r1 := subVec16WithBorrowIn a.hi b.hi r0.2
  (⟨r0.1, r1.1⟩, r1.2)

/-- Subtract two Vec32 values with borrow-in 0, returning the 32-limb difference and borrow-out bit. -/
def subVec32WithBorrow (a b : Vec32) : Vec32 × Nat :=
  subVec32WithBorrowIn a b 0

/-- Multiply a Vec64 (whose upper 16 limbs are zero) by 1000^16. -/
def shiftLeft16ToVec64 (v : Vec64) : Vec64 :=
  ⟨⟨zeroVec16, v.lo.lo⟩, ⟨v.lo.hi, v.hi.lo⟩⟩

/-- Multiply a Vec32 by 1000^32 inside a Vec64. -/
def shiftLeft32ToVec64 (v : Vec32) : Vec64 :=
  ⟨zeroVec32, v⟩

/-- Add two Vec64 values, discarding final carry-out above 1000^64. -/
def addVec64 (a b : Vec64) : Vec64 :=
  let r0 := addVec32WithCarryIn a.lo b.lo 0
  let r1 := addVec32WithCarryIn a.hi b.hi r0.2
  ⟨r0.1, r1.1⟩

/-- Subtract two Vec64 values, discarding final borrow-out. -/
def subVec64 (a b : Vec64) : Vec64 :=
  let r0 := subVec32WithBorrowIn a.lo b.lo 0
  let r1 := subVec32WithBorrowIn a.hi b.hi r0.2
  ⟨r0.1, r1.1⟩

/-- Universal 192-digit (64-limb) 2x2 Karatsuba multiplier using 3 calls to karatsubaCrtNttMul96. -/
def karatsubaCrtNttMul192 (A B : Vec32) : Vec64 :=
  let scA := addVec16WithCarry A.lo A.hi
  let scB := addVec16WithCarry B.lo B.hi
  let sA := scA.1
  let cA := scA.2
  let sB := scB.1
  let cB := scB.2
  let z0 := karatsubaCrtNttMul96 A.lo B.lo
  let z2 := karatsubaCrtNttMul96 A.hi B.hi
  let pLow := karatsubaCrtNttMul96 sA sB
  let p0 : Vec64 := ⟨pLow, zeroVec32⟩
  let termA : Vec64 := ⟨⟨zeroVec16, if cA = 0 then zeroVec16 else sB⟩, zeroVec32⟩
  let termB : Vec64 := ⟨⟨zeroVec16, if cB = 0 then zeroVec16 else sA⟩, zeroVec32⟩
  let termAB : Vec64 := ⟨zeroVec32, if cA = 0 ∨ cB = 0 then zeroVec32 else oneVec32⟩
  let z1Sum := addVec64 p0 (addVec64 termA (addVec64 termB termAB))
  let z064 : Vec64 := ⟨z0, zeroVec32⟩
  let z264 : Vec64 := ⟨z2, zeroVec32⟩
  let z1 := subVec64 z1Sum (addVec64 z064 z264)
  let z1Shifted := shiftLeft16ToVec64 z1
  let z2Shifted := shiftLeft32ToVec64 z2
  addVec64 (addVec64 z064 z1Shifted) z2Shifted

private theorem addVec16WithCarry_sound (a b : Vec16) (ha : isNormalizedVec16 a) (hb : isNormalizedVec16 b) :
    let r := addVec16WithCarry a b
    isNormalizedVec16 r.1 ∧ r.2 ≤ 1 ∧
    evalDigits1000Vec16 r.1 + (1000 ^ 16) * r.2 = evalDigits1000Vec16 a + evalDigits1000Vec16 b := by
  simpa [addVec16WithCarry] using addVec16WithCarryIn_sound a b 0 ha hb (Nat.zero_le 1)

private theorem pow64_1000 : (1000 : Nat) ^ 64 = (1000 ^ 32) * (1000 ^ 32) := by
  exact Nat.pow_add 1000 32 32

private theorem pow48_1000 : (1000 : Nat) ^ 48 = (1000 ^ 32) * (1000 ^ 16) := by
  exact Nat.pow_add 1000 32 16

private theorem addVec32WithCarryIn_sound (a b : Vec32) (cin : Nat)
    (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b) (hcin : cin ≤ 1) :
    let r := addVec32WithCarryIn a b cin
    isNormalizedVec32 r.1 ∧ r.2 ≤ 1 ∧
    evalDigits1000Vec32 r.1 + (1000 ^ 32) * r.2 =
      evalDigits1000Vec32 a + evalDigits1000Vec32 b + cin := by
  dsimp only [addVec32WithCarryIn]
  have h0 := addVec16WithCarryIn_sound a.lo b.lo cin ha.1 hb.1 hcin
  have h1 := addVec16WithCarryIn_sound a.hi b.hi (addVec16WithCarryIn a.lo b.lo cin).2 ha.2 hb.2 h0.2.1
  refine ⟨⟨h0.1, h1.1⟩, h1.2.1, ?_⟩
  dsimp only [evalDigits1000Vec32]
  rw [← pow32_1000]
  exact carry_chain_step (1000 ^ 16) _ _ _ _ _ _ _ _ _ _ h0.2.2 h1.2.2

/-- Soundness of 32-limb base-1000 addition with carry-out. -/
theorem addVec32WithCarry_sound (a b : Vec32) (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b) :
    let r := addVec32WithCarry a b
    isNormalizedVec32 r.1 ∧ r.2 ≤ 1 ∧
    evalDigits1000Vec32 r.1 + (1000 ^ 32) * r.2 =
      evalDigits1000Vec32 a + evalDigits1000Vec32 b := by
  simpa [addVec32WithCarry] using addVec32WithCarryIn_sound a b 0 ha hb (Nat.zero_le 1)

private theorem subVec32WithBorrowIn_sound (a b : Vec32) (bin : Nat)
    (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b) (hbin : bin ≤ 1) :
    let r := subVec32WithBorrowIn a b bin
    isNormalizedVec32 r.1 ∧ r.2 ≤ 1 ∧
    evalDigits1000Vec32 r.1 + evalDigits1000Vec32 b + bin =
      evalDigits1000Vec32 a + (1000 ^ 32) * r.2 := by
  dsimp only [subVec32WithBorrowIn]
  have h0 := subVec16WithBorrowIn_sound a.lo b.lo bin ha.1 hb.1 hbin
  have h1 := subVec16WithBorrowIn_sound a.hi b.hi (subVec16WithBorrowIn a.lo b.lo bin).2 ha.2 hb.2 h0.2.1
  refine ⟨⟨h0.1, h1.1⟩, h1.2.1, ?_⟩
  dsimp only [evalDigits1000Vec32]
  rw [← pow32_1000]
  exact borrow_chain_step (1000 ^ 16) _ _ _ _ _ _ _ _ _ _ h0.2.2 h1.2.2

/-- Soundness of 32-limb base-1000 subtraction with borrow-out. -/
theorem subVec32WithBorrow_sound (a b : Vec32) (ha : isNormalizedVec32 a) (hb : isNormalizedVec32 b) :
    let r := subVec32WithBorrow a b
    isNormalizedVec32 r.1 ∧ r.2 ≤ 1 ∧
    evalDigits1000Vec32 r.1 + evalDigits1000Vec32 b =
      evalDigits1000Vec32 a + (1000 ^ 32) * r.2 := by
  simpa [subVec32WithBorrow] using subVec32WithBorrowIn_sound a b 0 ha hb (Nat.zero_le 1)

private theorem evalDigits1000Vec64_lt (v : Vec64) (hv : isNormalizedVec64 v) :
    evalDigits1000Vec64 v < 1000 ^ 64 := by
  dsimp only [evalDigits1000Vec64]
  rw [pow64_1000]
  exact mul_lt_mul_bound _ _ _ _ (evalDigits1000Vec32_lt v.lo hv.1) (evalDigits1000Vec32_lt v.hi hv.2)

private theorem vec64_add_chain (B32 B64 sLo sHi aLo aHi bLo bHi c0 c1 : Nat)
    (hB : B32 * B32 = B64)
    (h0 : sLo + B32 * c0 = aLo + bLo + 0)
    (h1 : sHi + B32 * c1 = aHi + bHi + c0) :
    (sLo + B32 * sHi) + B64 * c1 = (aLo + B32 * aHi) + (bLo + B32 * bHi) := by
  rw [← hB]
  simpa using carry_chain_step B32 sLo aLo bLo 0 c0 c1 sHi aHi bHi B32 h0 h1

private theorem vec64_sub_chain (B32 B64 dLo dHi aLo aHi bLo bHi b0 b1 : Nat)
    (hB : B32 * B32 = B64)
    (h0 : dLo + bLo + 0 = aLo + B32 * b0)
    (h1 : dHi + bHi + b0 = aHi + B32 * b1) :
    (dLo + B32 * dHi) + (bLo + B32 * bHi) = (aLo + B32 * aHi) + B64 * b1 := by
  rw [← hB]
  simpa using borrow_chain_step B32 dLo aLo bLo 0 b0 b1 dHi aHi bHi B32 h0 h1

private theorem addVec64_sound (a b : Vec64) (ha : isNormalizedVec64 a) (hb : isNormalizedVec64 b)
    (hlt : evalDigits1000Vec64 a + evalDigits1000Vec64 b < 1000 ^ 64) :
    isNormalizedVec64 (addVec64 a b) ∧
    evalDigits1000Vec64 (addVec64 a b) = evalDigits1000Vec64 a + evalDigits1000Vec64 b := by
  dsimp only [addVec64]
  have h0 := addVec32WithCarryIn_sound a.lo b.lo 0 ha.1 hb.1 (Nat.zero_le 1)
  have h1 := addVec32WithCarryIn_sound a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2 ha.2 hb.2 h0.2.1
  have heq : evalDigits1000Vec64 ⟨(addVec32WithCarryIn a.lo b.lo 0).1,
      (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).1⟩ +
      (1000 ^ 64) * (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).2 =
      evalDigits1000Vec64 a + evalDigits1000Vec64 b := by
    dsimp only [evalDigits1000Vec64]
    exact vec64_add_chain (1000 ^ 32) (1000 ^ 64)
      (evalDigits1000Vec32 (addVec32WithCarryIn a.lo b.lo 0).1)
      (evalDigits1000Vec32 (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).1)
      (evalDigits1000Vec32 a.lo) (evalDigits1000Vec32 a.hi)
      (evalDigits1000Vec32 b.lo) (evalDigits1000Vec32 b.hi)
      (addVec32WithCarryIn a.lo b.lo 0).2
      (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).2
      (Nat.pow_add 1000 32 32).symm h0.2.2 h1.2.2
  have hcTop : (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).2 = 0 := by
    cases hc : (addVec32WithCarryIn a.hi b.hi (addVec32WithCarryIn a.lo b.lo 0).2).2 with
    | zero => rfl
    | succ k =>
      rw [hc] at heq
      have hge : 1000 ^ 64 ≤ (1000 ^ 64) * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
      omega
  rw [hcTop, Nat.mul_zero, Nat.add_zero] at heq
  exact ⟨⟨h0.1, h1.1⟩, heq⟩

private theorem subVec64_sound (a b : Vec64) (ha : isNormalizedVec64 a) (hb : isNormalizedVec64 b)
    (hle : evalDigits1000Vec64 b ≤ evalDigits1000Vec64 a) :
    isNormalizedVec64 (subVec64 a b) ∧
    evalDigits1000Vec64 (subVec64 a b) + evalDigits1000Vec64 b = evalDigits1000Vec64 a := by
  dsimp only [subVec64]
  have h0 := subVec32WithBorrowIn_sound a.lo b.lo 0 ha.1 hb.1 (Nat.zero_le 1)
  have h1 := subVec32WithBorrowIn_sound a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2 ha.2 hb.2 h0.2.1
  have hnorm : isNormalizedVec64 ⟨(subVec32WithBorrowIn a.lo b.lo 0).1,
      (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).1⟩ := ⟨h0.1, h1.1⟩
  have heq : evalDigits1000Vec64 ⟨(subVec32WithBorrowIn a.lo b.lo 0).1,
      (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).1⟩ +
      evalDigits1000Vec64 b =
      evalDigits1000Vec64 a +
        (1000 ^ 64) * (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).2 := by
    dsimp only [evalDigits1000Vec64]
    exact vec64_sub_chain (1000 ^ 32) (1000 ^ 64)
      (evalDigits1000Vec32 (subVec32WithBorrowIn a.lo b.lo 0).1)
      (evalDigits1000Vec32 (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).1)
      (evalDigits1000Vec32 a.lo) (evalDigits1000Vec32 a.hi)
      (evalDigits1000Vec32 b.lo) (evalDigits1000Vec32 b.hi)
      (subVec32WithBorrowIn a.lo b.lo 0).2
      (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).2
      (Nat.pow_add 1000 32 32).symm h0.2.2 h1.2.2
  have hdlt : evalDigits1000Vec64 ⟨(subVec32WithBorrowIn a.lo b.lo 0).1,
      (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).1⟩ < 1000 ^ 64 :=
    evalDigits1000Vec64_lt _ hnorm
  have hbTop : (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).2 = 0 := by
    cases hbt : (subVec32WithBorrowIn a.hi b.hi (subVec32WithBorrowIn a.lo b.lo 0).2).2 with
    | zero => rfl
    | succ k =>
      rw [hbt] at heq
      have hge : 1000 ^ 64 ≤ (1000 ^ 64) * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
      omega
  rw [hbTop, Nat.mul_zero, Nat.add_zero] at heq
  exact ⟨hnorm, heq⟩

private theorem shiftLeft16_algebra (B16 B32 x0 x1 x2 : Nat) (hB : B16 * B16 = B32) :
    B16 * x0 + B32 * (x1 + B16 * x2) = B16 * (x0 + B16 * x1 + B32 * x2) := by
  rw [← hB, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  ac_rfl

private theorem shiftLeft16ToVec64_sound (v : Vec64) (hv : isNormalizedVec64 v)
    (hlt : evalDigits1000Vec64 v < 1000 ^ 48) :
    isNormalizedVec64 (shiftLeft16ToVec64 v) ∧
    evalDigits1000Vec64 (shiftLeft16ToVec64 v) = (1000 ^ 16) * evalDigits1000Vec64 v := by
  have hvhh : evalDigits1000Vec16 v.hi.hi = 0 := by
    dsimp only [evalDigits1000Vec64, evalDigits1000Vec32] at hlt
    cases he : evalDigits1000Vec16 v.hi.hi with
    | zero => rfl
    | succ k =>
      have hge1 : 1000 ^ 16 ≤ (1000 ^ 16) * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
      have hge2 : 1000 ^ 48 ≤ (1000 ^ 32) * ((1000 ^ 16) * (k + 1)) := by
        rw [pow48_1000]
        exact Nat.mul_le_mul_left _ hge1
      omega
  refine ⟨⟨⟨zeroVec16_norm, hv.1.1⟩, ⟨hv.1.2, hv.2.1⟩⟩, ?_⟩
  dsimp only [shiftLeft16ToVec64, evalDigits1000Vec64, evalDigits1000Vec32]
  rw [eval_zeroVec16, Nat.zero_add, hvhh, Nat.mul_zero, Nat.add_zero]
  exact shiftLeft16_algebra (1000 ^ 16) (1000 ^ 32) _ _ _ pow32_1000

private theorem shiftLeft32ToVec64_sound (v : Vec32) (hv : isNormalizedVec32 v) :
    isNormalizedVec64 (shiftLeft32ToVec64 v) ∧
    evalDigits1000Vec64 (shiftLeft32ToVec64 v) = (1000 ^ 32) * evalDigits1000Vec32 v := by
  refine ⟨⟨zeroVec32_norm, hv⟩, ?_⟩
  dsimp only [shiftLeft32ToVec64, evalDigits1000Vec64]
  rw [eval_zeroVec32, Nat.zero_add]

private theorem pow48_bound_karatsuba192 : 4 * (1000 : Nat) ^ 32 < 1000 ^ 48 := by
  rw [pow48_1000]
  have h4 : 4 < (1000 : Nat) ^ 16 := by decide
  have hp : 0 < (1000 : Nat) ^ 32 := Nat.pow_pos (by decide)
  have := Nat.mul_lt_mul_of_pos_right h4 hp
  omega

private theorem pow48_lt_pow64 : (1000 : Nat) ^ 48 < 1000 ^ 64 := by
  have h16_gt1 : 1 < (1000 : Nat) ^ 16 :=
    Nat.lt_of_lt_of_le (by decide : 1 < 1000 ^ 1) (Nat.pow_le_pow_right (by decide) (by decide : 1 ≤ 16))
  have h16 : (1000 : Nat) ^ 16 < 1000 ^ 32 := by
    rw [← pow32_1000]
    have hmul := Nat.mul_lt_mul_of_pos_right h16_gt1 (Nat.pow_pos (by decide : 0 < 1000) : 0 < 1000 ^ 16)
    rw [Nat.one_mul] at hmul
    exact hmul
  rw [pow48_1000, pow64_1000]
  exact Nat.mul_lt_mul_of_pos_left h16 (Nat.pow_pos (by decide))

private theorem two_k_sq (K : Nat) : (2 * K) * (2 * K) = 4 * (K * K) := by
  calc (2 * K) * (2 * K)
      = 2 * (K * (2 * K)) := by rw [Nat.mul_assoc]
    _ = 2 * (2 * (K * K)) := by rw [Nat.mul_comm K (2 * K), Nat.mul_assoc]
    _ = 4 * (K * K) := by rw [← Nat.mul_assoc]

private theorem karatsubaCrtNttMul192_core (A B : Vec32)
    (hA : isNormalizedVec32 A) (hB : isNormalizedVec32 B) :
    isNormalizedVec64 (karatsubaCrtNttMul192 A B) ∧
    evalDigits1000Vec64 (karatsubaCrtNttMul192 A B) =
      evalDigits1000Vec32 A * evalDigits1000Vec32 B := by
  dsimp only [karatsubaCrtNttMul192]
  have hscA := addVec16WithCarry_sound A.lo A.hi hA.1 hA.2
  have hscB := addVec16WithCarry_sound B.lo B.hi hB.1 hB.2
  let sA := (addVec16WithCarry A.lo A.hi).1
  let cA := (addVec16WithCarry A.lo A.hi).2
  let sB := (addVec16WithCarry B.lo B.hi).1
  let cB := (addVec16WithCarry B.lo B.hi).2
  have hz0Norm := karatsubaCrtNttMul96_normalized A.lo B.lo hA.1 hB.1
  have hz2Norm := karatsubaCrtNttMul96_normalized A.hi B.hi hA.2 hB.2
  have hpLowNorm := karatsubaCrtNttMul96_normalized sA sB hscA.1 hscB.1
  have hz0Ev := karatsubaCrtNttMul96_universal_sound A.lo B.lo hA.1 hB.1
  have hz2Ev := karatsubaCrtNttMul96_universal_sound A.hi B.hi hA.2 hB.2
  have hpLowEv := karatsubaCrtNttMul96_universal_sound sA sB hscA.1 hscB.1
  let z0 := karatsubaCrtNttMul96 A.lo B.lo
  let z2 := karatsubaCrtNttMul96 A.hi B.hi
  let pLow := karatsubaCrtNttMul96 sA sB
  let p0 : Vec64 := ⟨pLow, zeroVec32⟩
  let tA := if cA = 0 then zeroVec16 else sB
  let tB := if cB = 0 then zeroVec16 else sA
  let tAB := if cA = 0 ∨ cB = 0 then zeroVec32 else oneVec32
  let termA : Vec64 := ⟨⟨zeroVec16, tA⟩, zeroVec32⟩
  let termB : Vec64 := ⟨⟨zeroVec16, tB⟩, zeroVec32⟩
  let termAB : Vec64 := ⟨zeroVec32, tAB⟩
  have hp0Norm : isNormalizedVec64 p0 := ⟨hpLowNorm, zeroVec32_norm⟩
  have htANorm : isNormalizedVec16 tA := by
    dsimp only [tA]; split
    · exact zeroVec16_norm
    · exact hscB.1
  have htBNorm : isNormalizedVec16 tB := by
    dsimp only [tB]; split
    · exact zeroVec16_norm
    · exact hscA.1
  have htABNorm : isNormalizedVec32 tAB := by
    dsimp only [tAB]; split
    · exact zeroVec32_norm
    · exact oneVec32_norm
  have htermANorm : isNormalizedVec64 termA := ⟨⟨zeroVec16_norm, htANorm⟩, zeroVec32_norm⟩
  have htermBNorm : isNormalizedVec64 termB := ⟨⟨zeroVec16_norm, htBNorm⟩, zeroVec32_norm⟩
  have htermABNorm : isNormalizedVec64 termAB := ⟨zeroVec32_norm, htABNorm⟩
  have hp0Ev : evalDigits1000Vec64 p0 = evalDigits1000Vec32 pLow := by
    dsimp only [p0, evalDigits1000Vec64]
    rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero]
  have hp0Lt : evalDigits1000Vec64 p0 < 1000 ^ 32 := by
    rw [hp0Ev]; exact evalDigits1000Vec32_lt pLow hpLowNorm
  have htermAEv : evalDigits1000Vec64 termA = cA * ((1000 ^ 16) * evalDigits1000Vec16 sB) := by
    dsimp only [termA, tA, evalDigits1000Vec64]
    rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero]
    dsimp only [evalDigits1000Vec32]
    rw [eval_zeroVec16, Nat.zero_add]
    split
    · rename_i hc0; rw [hc0, eval_zeroVec16, Nat.mul_zero, Nat.zero_mul]
    · rename_i hcne
      have hc1 : cA = 1 := by have := hscA.2.1; omega
      rw [hc1, Nat.one_mul]
  have htermBEv : evalDigits1000Vec64 termB = cB * ((1000 ^ 16) * evalDigits1000Vec16 sA) := by
    dsimp only [termB, tB, evalDigits1000Vec64]
    rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero]
    dsimp only [evalDigits1000Vec32]
    rw [eval_zeroVec16, Nat.zero_add]
    split
    · rename_i hc0; rw [hc0, eval_zeroVec16, Nat.mul_zero, Nat.zero_mul]
    · rename_i hcne
      have hc1 : cB = 1 := by have := hscB.2.1; omega
      rw [hc1, Nat.one_mul]
  have htermABEv : evalDigits1000Vec64 termAB = (cA * cB) * (1000 ^ 32) := by
    dsimp only [termAB, tAB, evalDigits1000Vec64]
    rw [eval_zeroVec32, Nat.zero_add]
    split
    · rename_i h0
      rw [eval_zeroVec32, Nat.mul_zero]
      rcases h0 with hcA0 | hcB0
      · rw [hcA0, Nat.zero_mul, Nat.zero_mul]
      · rw [hcB0, Nat.mul_zero, Nat.zero_mul]
    · rename_i hne
      have hcA1 : cA = 1 := by have := hscA.2.1; omega
      have hcB1 : cB = 1 := by have := hscB.2.1; omega
      rw [eval_oneVec32, Nat.mul_one, hcA1, hcB1, Nat.mul_one, Nat.one_mul]
  have htermALt : evalDigits1000Vec64 termA < 1000 ^ 32 := by
    rw [htermAEv, ← pow32_1000]
    have hltS := evalDigits1000Vec16_lt sB hscB.1
    cases hc : cA with
    | zero => rw [Nat.zero_mul]; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    | succ k =>
      have hk : k = 0 := by have := hscA.2.1; omega
      rw [hk, Nat.zero_add, Nat.one_mul]
      exact Nat.mul_lt_mul_of_pos_left hltS (Nat.pow_pos (by decide))
  have htermBLt : evalDigits1000Vec64 termB < 1000 ^ 32 := by
    rw [htermBEv, ← pow32_1000]
    have hltS := evalDigits1000Vec16_lt sA hscA.1
    cases hc : cB with
    | zero => rw [Nat.zero_mul]; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    | succ k =>
      have hk : k = 0 := by have := hscB.2.1; omega
      rw [hk, Nat.zero_add, Nat.one_mul]
      exact Nat.mul_lt_mul_of_pos_left hltS (Nat.pow_pos (by decide))
  have htermABLe : evalDigits1000Vec64 termAB ≤ 1000 ^ 32 := by
    rw [htermABEv]
    have hca : cA ≤ 1 := hscA.2.1
    have hcb : cB ≤ 1 := hscB.2.1
    have hcab : cA * cB ≤ 1 := by
      rw [← Nat.one_mul 1]
      exact Nat.mul_le_mul hca hcb
    calc (cA * cB) * 1000 ^ 32 ≤ 1 * 1000 ^ 32 := Nat.mul_le_mul_right _ hcab
      _ = 1000 ^ 32 := Nat.one_mul _
  have hlt1 : evalDigits1000Vec64 termB + evalDigits1000Vec64 termAB < 1000 ^ 64 := by
    have := pow48_bound_karatsuba192
    have := pow48_lt_pow64
    omega
  have hsumB := addVec64_sound termB termAB htermBNorm htermABNorm hlt1
  have hlt2 : evalDigits1000Vec64 termA + evalDigits1000Vec64 (addVec64 termB termAB) < 1000 ^ 64 := by
    rw [hsumB.2]
    have := pow48_bound_karatsuba192
    have := pow48_lt_pow64
    omega
  have hsumA := addVec64_sound termA (addVec64 termB termAB) htermANorm hsumB.1 hlt2
  have hlt3 : evalDigits1000Vec64 p0 +
      evalDigits1000Vec64 (addVec64 termA (addVec64 termB termAB)) < 1000 ^ 64 := by
    rw [hsumA.2, hsumB.2]
    have := pow48_bound_karatsuba192
    have := pow48_lt_pow64
    omega
  have hz1Sum := addVec64_sound p0 (addVec64 termA (addVec64 termB termAB)) hp0Norm hsumA.1 hlt3
  have hz1SumVal : evalDigits1000Vec64 (addVec64 p0 (addVec64 termA (addVec64 termB termAB))) =
      (evalDigits1000Vec16 A.lo + evalDigits1000Vec16 A.hi) *
      (evalDigits1000Vec16 B.lo + evalDigits1000Vec16 B.hi) := by
    rw [hz1Sum.2, hsumA.2, hsumB.2, hp0Ev, hpLowEv, htermAEv, htermBEv, htermABEv, ← pow32_1000]
    exact karatsuba_middle_identity _ _ _ _ _ _ _ _ (1000 ^ 16) hscA.2.2 hscB.2.2
  have hz064Norm : isNormalizedVec64 ⟨z0, zeroVec32⟩ := ⟨hz0Norm, zeroVec32_norm⟩
  have hz264Norm : isNormalizedVec64 ⟨z2, zeroVec32⟩ := ⟨hz2Norm, zeroVec32_norm⟩
  have hz064Ev : evalDigits1000Vec64 ⟨z0, zeroVec32⟩ =
      evalDigits1000Vec16 A.lo * evalDigits1000Vec16 B.lo := by
    dsimp only [evalDigits1000Vec64]; rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero, hz0Ev]
  have hz264Ev : evalDigits1000Vec64 ⟨z2, zeroVec32⟩ =
      evalDigits1000Vec16 A.hi * evalDigits1000Vec16 B.hi := by
    dsimp only [evalDigits1000Vec64]; rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero, hz2Ev]
  have hz0Lt : evalDigits1000Vec64 ⟨z0, zeroVec32⟩ < 1000 ^ 32 := by
    dsimp only [evalDigits1000Vec64]; rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero]
    exact evalDigits1000Vec32_lt z0 hz0Norm
  have hz2Lt : evalDigits1000Vec64 ⟨z2, zeroVec32⟩ < 1000 ^ 32 := by
    dsimp only [evalDigits1000Vec64]; rw [eval_zeroVec32, Nat.mul_zero, Nat.add_zero]
    exact evalDigits1000Vec32_lt z2 hz2Norm
  have hlt02 : evalDigits1000Vec64 ⟨z0, zeroVec32⟩ + evalDigits1000Vec64 ⟨z2, zeroVec32⟩ < 1000 ^ 64 := by
    have := pow48_bound_karatsuba192
    have := pow48_lt_pow64
    omega
  have hz0PlusZ2 := addVec64_sound ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩ hz064Norm hz264Norm hlt02
  have hleMiddle : evalDigits1000Vec64 (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩) ≤
      evalDigits1000Vec64 (addVec64 p0 (addVec64 termA (addVec64 termB termAB))) := by
    rw [hz0PlusZ2.2, hz064Ev, hz264Ev, hz1SumVal]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have hz1 := subVec64_sound _ _ hz1Sum.1 hz0PlusZ2.1 hleMiddle
  have hz1Val : evalDigits1000Vec64 (subVec64 (addVec64 p0 (addVec64 termA (addVec64 termB termAB)))
      (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩)) =
      (evalDigits1000Vec16 A.lo + evalDigits1000Vec16 A.hi) *
        (evalDigits1000Vec16 B.lo + evalDigits1000Vec16 B.hi) -
      evalDigits1000Vec16 A.lo * evalDigits1000Vec16 B.lo -
      evalDigits1000Vec16 A.hi * evalDigits1000Vec16 B.hi := by
    have hsub := hz1.2
    rw [hz0PlusZ2.2, hz064Ev, hz264Ev, hz1SumVal] at hsub
    omega
  have hz1Lt48 : evalDigits1000Vec64 (subVec64 (addVec64 p0 (addVec64 termA (addVec64 termB termAB)))
      (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩)) < 1000 ^ 48 := by
    rw [hz1Val]
    have hAlo := evalDigits1000Vec16_lt A.lo hA.1
    have hAhi := evalDigits1000Vec16_lt A.hi hA.2
    have hBlo := evalDigits1000Vec16_lt B.lo hB.1
    have hBhi := evalDigits1000Vec16_lt B.hi hB.2
    have hprod4 : (evalDigits1000Vec16 A.lo + evalDigits1000Vec16 A.hi) *
        (evalDigits1000Vec16 B.lo + evalDigits1000Vec16 B.hi) < 4 * 1000 ^ 32 := by
      have hm := two_k_sq (1000 ^ 16)
      rw [pow32_1000] at hm
      rw [← hm]
      exact Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
    have := pow48_bound_karatsuba192
    omega
  have hz1Sh := shiftLeft16ToVec64_sound _ hz1.1 hz1Lt48
  have hz2Sh := shiftLeft32ToVec64_sound z2 hz2Norm
  have hz2ShEv : evalDigits1000Vec64 (shiftLeft32ToVec64 z2) =
      (1000 ^ 32) * (evalDigits1000Vec16 A.hi * evalDigits1000Vec16 B.hi) := by
    rw [hz2Sh.2, hz2Ev]
  have hz1ShEv : evalDigits1000Vec64 (shiftLeft16ToVec64 (subVec64 (addVec64 p0
      (addVec64 termA (addVec64 termB termAB))) (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩))) =
      (1000 ^ 16) * ((evalDigits1000Vec16 A.lo + evalDigits1000Vec16 A.hi) *
        (evalDigits1000Vec16 B.lo + evalDigits1000Vec16 B.hi) -
      evalDigits1000Vec16 A.lo * evalDigits1000Vec16 B.lo -
      evalDigits1000Vec16 A.hi * evalDigits1000Vec16 B.hi) := by
    rw [hz1Sh.2, hz1Val]
  have hALt : evalDigits1000Vec32 A < 1000 ^ 32 := evalDigits1000Vec32_lt A hA
  have hBLt : evalDigits1000Vec32 B < 1000 ^ 32 := evalDigits1000Vec32_lt B hB
  have hprodLt : evalDigits1000Vec32 A * evalDigits1000Vec32 B < 1000 ^ 64 := by
    rw [pow64_1000]
    exact Nat.mul_lt_mul_of_lt_of_lt hALt hBLt
  have hkar : evalDigits1000Vec32 A * evalDigits1000Vec32 B =
      evalDigits1000Vec64 ⟨z0, zeroVec32⟩ +
      evalDigits1000Vec64 (shiftLeft16ToVec64 (subVec64 (addVec64 p0
        (addVec64 termA (addVec64 termB termAB))) (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩))) +
      evalDigits1000Vec64 (shiftLeft32ToVec64 z2) := by
    dsimp only [evalDigits1000Vec32]
    rw [karatsuba_algebraic_identity _ _ _ _ (1000 ^ 16), hz064Ev, hz1ShEv, hz2ShEv, ← pow32_1000]
  have hlt01 : evalDigits1000Vec64 ⟨z0, zeroVec32⟩ +
      evalDigits1000Vec64 (shiftLeft16ToVec64 (subVec64 (addVec64 p0
      (addVec64 termA (addVec64 termB termAB))) (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩))) < 1000 ^ 64 := by
    omega
  have hsum01 := addVec64_sound ⟨z0, zeroVec32⟩ _ hz064Norm hz1Sh.1 hlt01
  have hlt012 : evalDigits1000Vec64 (addVec64 ⟨z0, zeroVec32⟩ (shiftLeft16ToVec64 (subVec64
      (addVec64 p0 (addVec64 termA (addVec64 termB termAB)))
      (addVec64 ⟨z0, zeroVec32⟩ ⟨z2, zeroVec32⟩)))) +
      evalDigits1000Vec64 (shiftLeft32ToVec64 z2) < 1000 ^ 64 := by
    rw [hsum01.2]
    omega
  have hfinal := addVec64_sound _ _ hsum01.1 hz2Sh.1 hlt012
  refine ⟨hfinal.1, ?_⟩
  rw [hfinal.2, hsum01.2, ← hkar]

/-- Normalization preservation for the 192-digit 2x2 Karatsuba multiplier. -/
theorem karatsubaCrtNttMul192_normalized (A B : Vec32)
    (hA : isNormalizedVec32 A) (hB : isNormalizedVec32 B) :
    isNormalizedVec64 (karatsubaCrtNttMul192 A B) :=
  (karatsubaCrtNttMul192_core A B hA hB).1

/-- Universal 192-digit Karatsuba-over-CRT-NTT big-integer multiplication theorem. -/
theorem karatsubaCrtNttMul192_universal_sound (A B : Vec32)
    (hA : isNormalizedVec32 A) (hB : isNormalizedVec32 B) :
    evalDigits1000Vec64 (karatsubaCrtNttMul192 A B) =
    evalDigits1000Vec32 A * evalDigits1000Vec32 B :=
  (karatsubaCrtNttMul192_core A B hA hB).2

private theorem eval_max96_algebra (K : Nat) (hK : 1 ≤ K) :
    (K - 1) + K * (K - 1) = K * K - 1 := by
  have hk1 : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have hsum : (K - 1) + K * (K - 1) + 1 = K * K := by
    calc (K - 1) + K * (K - 1) + 1
        = K + K * (K - 1) := by omega
      _ = K * 1 + K * (K - 1) := by rw [Nat.mul_one]
      _ = K * (1 + (K - 1)) := by rw [← Nat.mul_add]
      _ = K * K := by rw [show 1 + (K - 1) = K by omega]
  omega

private theorem pred_sq_algebra (m : Nat) :
    ((m + 2) - 1) * ((m + 2) - 1) = (m + 2) * (m + 2) - 2 * (m + 2) + 1 := by
  have h1 : (m + 2) - 1 = m + 1 := by omega
  rw [h1]
  have hl : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hr : (m + 2) * (m + 2) = (m * m + 2 * m) + 2 * (m + 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [hl, hr]
  omega

/-- Concrete 192-digit maximum product: (10^96 - 1) * (10^96 - 1) = 10^192 - 2 * 10^96 + 1. -/
theorem karatsuba_192_digit_max_verified :
    let max48 : Vec16 := ⟨999, 999, 999, 999, 999, 999, 999, 999,
                          999, 999, 999, 999, 999, 999, 999, 999⟩
    let max96 : Vec32 := ⟨max48, max48⟩
    evalDigits1000Vec64 (karatsubaCrtNttMul192 max96 max96) = 10 ^ 192 - 2 * 10 ^ 96 + 1 ∧
    (10 ^ 96 - 1) * (10 ^ 96 - 1) = 10 ^ 192 - 2 * 10 ^ 96 + 1 := by
  let max48 : Vec16 := ⟨999, 999, 999, 999, 999, 999, 999, 999,
                        999, 999, 999, 999, 999, 999, 999, 999⟩
  let max96 : Vec32 := ⟨max48, max48⟩
  have hnorm16 : isNormalizedVec16 max48 := by
    dsimp only [isNormalizedVec16, max48]
    refine ⟨by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide,
            by decide, by decide, by decide, by decide⟩
  have hnorm : isNormalizedVec32 max96 := ⟨hnorm16, hnorm16⟩
  have hev16 : evalDigits1000Vec16 max48 = 10 ^ 48 - 1 := by decide
  have hpow16 : (1000 : Nat) ^ 16 = 10 ^ 48 := by decide
  have hpow48 : (10 : Nat) ^ 48 * 10 ^ 48 = 10 ^ 96 := by rw [← Nat.pow_add]
  have hpow96 : (10 : Nat) ^ 96 * 10 ^ 96 = 10 ^ 192 := by rw [← Nat.pow_add]
  have hk1 : 1 ≤ (10 : Nat) ^ 48 := Nat.pow_pos (by decide)
  have hev96 : evalDigits1000Vec32 max96 = 10 ^ 96 - 1 := by
    dsimp only [evalDigits1000Vec32, max96]
    rw [hev16, hpow16, eval_max96_algebra (10 ^ 48) hk1, hpow48]
  have hk2 : 2 ≤ (10 : Nat) ^ 96 := by
    exact Nat.le_trans (by decide : 2 ≤ 10 ^ 1) (Nat.pow_le_pow_right (by decide) (by decide : 1 ≤ 96))
  have hmax : (10 ^ 96 - 1) * (10 ^ 96 - 1) = 10 ^ 192 - 2 * 10 ^ 96 + 1 := by
    have hm : (10 ^ 96 - 2) + 2 = 10 ^ 96 := Nat.sub_add_cancel hk2
    calc (10 ^ 96 - 1) * (10 ^ 96 - 1)
        = (((10 ^ 96 - 2) + 2) - 1) * (((10 ^ 96 - 2) + 2) - 1) := by rw [hm]
      _ = ((10 ^ 96 - 2) + 2) * ((10 ^ 96 - 2) + 2) - 2 * ((10 ^ 96 - 2) + 2) + 1 :=
          pred_sq_algebra (10 ^ 96 - 2)
      _ = 10 ^ 192 - 2 * 10 ^ 96 + 1 := by rw [hm, hpow96]
  refine ⟨?_, hmax⟩
  rw [karatsubaCrtNttMul192_universal_sound max96 max96 hnorm hnorm, hev96, hmax]

-- =============================================================================
-- Part H: Fermat-Tower 4-Prime Garner CRT & Convolution Wrap-Around Bounds
-- =============================================================================

/-- Exact 4-prime Fermat-tower CRT modulus `M_4 = 5 * 17 * 257 * 65537`. -/
def fermatTowerMod4 : Nat :=
  5 * 17 * 257 * 65537

/-- Fermat-tower dynamic range & unsigned 31-bit embedding bounds:
`M_4 = 1,431,655,765 = EulerFactorNonVanishing.fermatTowerPrimes.prod`,
`3 * M_4 = 2^32 - 1 = 4,294,967,295`, and `2^30 < M_4 < 2^31`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermat_tower_crt_modulus_bounds :
    fermatTowerMod4 = 1431655765 ∧
    fermatTowerMod4 = EulerFactorNonVanishing.fermatTowerPrimes.prod ∧
    3 * fermatTowerMod4 = 2 ^ 32 - 1 ∧
    2 ^ 30 < fermatTowerMod4 ∧ fermatTowerMod4 < 2 ^ 31 := by
  have hft := EulerFactorNonVanishing.fermat_tower_product_eq_2pow32_sub_1
  have hm4 : fermatTowerMod4 = 1431655765 := by decide
  refine ⟨hm4, ?_, by decide, by decide, by decide⟩
  rw [hm4, hft.2.1]

/-- Intermediate 3-prime Garner reconstruction for `{5, 17, 257}` (`M_3 = 21,845`):
`(5 * 17)⁻¹ ≡ 127 (mod 257)`. -/
def garner5_17_257 (r1 r2 r3 : Nat) : Nat :=
  let x12 := garner5_17 r1 r2
  let v3 := ((r3 % 257 + 257 - (x12 % 257)) * 127) % 257
  x12 + 85 * v3

/-- Constructive 4-prime Garner mixed-radix CRT reconstruction over `{5, 17, 257, 65537}`:
- `c12 = 5⁻¹ mod 17 = 7`
- `c123 = 85⁻¹ mod 257 = 127`
- `c1234 = 21845⁻¹ mod 65537 = 32767`
Avoids `O(M_4^2)` intermediate big-modulus multiplications. -/
def garnerReconstruct4 (r1 r2 r3 r4 : Nat) : Nat :=
  let x123 := garner5_17_257 r1 r2 r3
  let v4 := ((r4 % 65537 + 65537 - (x123 % 65537)) * 32767) % 65537
  x123 + 21845 * v4

/-- Certified mixed-radix Garner inverses over `(5, 17, 257, 65537)`. -/
theorem garner_4ch_inverses_sound :
    (5 * 7) % 17 = 1 ∧
    (85 * 127) % 257 = 1 ∧
    (21845 * 32767) % 65537 = 1 := by
  decide

private theorem garner5_17_roundtrip (y : Nat) (hy : y < 85) :
    garner5_17 (y % 5) (y % 17) = y := by
  dsimp [garner5_17]
  omega

private theorem garner5_17_257_roundtrip (z : Nat) (hz : z < 21845) :
    garner5_17_257 (z % 5) (z % 17) (z % 257) = z := by
  dsimp [garner5_17_257]
  let y := z % 85
  have hy : y < 85 := Nat.mod_lt z (by decide)
  have hd5 : 5 ∣ 85 := ⟨17, rfl⟩
  have hd17 : 17 ∣ 85 := ⟨5, by decide⟩
  have hpart : garner5_17 (z % 5) (z % 17) = y := by
    rw [← Nat.mod_mod_of_dvd z hd5, ← Nat.mod_mod_of_dvd z hd17]
    exact garner5_17_roundtrip y hy
  rw [hpart]
  omega

/-- Output range bound: `garnerReconstruct4 r1 r2 r3 r4 < fermatTowerMod4` for all inputs. -/
theorem garnerReconstruct4_lt (r1 r2 r3 r4 : Nat) :
    garnerReconstruct4 r1 r2 r3 r4 < fermatTowerMod4 := by
  dsimp [garnerReconstruct4, garner5_17_257, garner5_17, fermatTowerMod4]
  omega

/-- Constructive 4-Prime Garner Mixed-Radix CRT Roundtrip Soundness:
Reconstructs every `x < M_4 = 1,431,655,765` from `(x % 5, x % 17, x % 257, x % 65537)`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem garnerReconstruct4_sound (x : Nat) (hx : x < fermatTowerMod4) :
    garnerReconstruct4 (x % 5) (x % 17) (x % 257) (x % 65537) = x := by
  dsimp [fermatTowerMod4] at hx
  dsimp [garnerReconstruct4]
  let z := x % 21845
  have hz : z < 21845 := Nat.mod_lt x (by decide)
  have hd5 : 5 ∣ 21845 := ⟨4369, rfl⟩
  have hd17 : 17 ∣ 21845 := ⟨1285, by decide⟩
  have hd257 : 257 ∣ 21845 := ⟨85, by decide⟩
  have hpart : garner5_17_257 (x % 5) (x % 17) (x % 257) = z := by
    rw [← Nat.mod_mod_of_dvd x hd5, ← Nat.mod_mod_of_dvd x hd17,
        ← Nat.mod_mod_of_dvd x hd257]
    exact garner5_17_257_roundtrip z hz
  rw [hpart]
  omega

/-- Generic `m`-term convolution inner-product sum `∑_{i < m} a i * b (idx i)`
covering cyclic/negacyclic index permutations `idx : Nat → Nat`. -/
def convPairSum (a b : Nat → Nat) (idx : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => convPairSum a b idx m + a m * b (idx m)

private theorem convPairSum_le_prefix (a b : Nat → Nat) (idx : Nat → Nat) (N B m : Nat)
    (hm : m ≤ N) (ha : ∀ i, i < N → a i ≤ B) (hb : ∀ j, j < N → b j ≤ B)
    (hidx : ∀ i, i < N → idx i < N) :
    convPairSum a b idx m ≤ m * (B * B) := by
  induction m with
  | zero =>
    dsimp [convPairSum]
    exact Nat.zero_le _
  | succ k ih =>
    have hkN : k < N := hm
    have hk_le : k ≤ N := Nat.le_of_lt hkN
    have ihk := ih hk_le
    have ha_k : a k ≤ B := ha k hkN
    have hb_k : b (idx k) ≤ B := hb (idx k) (hidx k hkN)
    have hprod : a k * b (idx k) ≤ B * B := Nat.mul_le_mul ha_k hb_k
    dsimp [convPairSum]
    calc convPairSum a b idx k + a k * b (idx k)
        ≤ k * (B * B) + B * B := Nat.add_le_add ihk hprod
      _ = (k + 1) * (B * B) := (Nat.succ_mul k (B * B)).symm

/-- Constructive NTT Convolution Wrap-Around Safety Theorem:
For any length-`N` integer polynomials with `0 ≤ a_i, b_j ≤ B` (`idx i < N`),
every `N`-term convolution coefficient satisfies `c ≤ N * B^2`; whenever
`N * B^2 < M_4`, `garnerReconstruct4` recovers `c` with zero wrap-around.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem ntt_convolution_no_wraparound (a b : Nat → Nat) (idx : Nat → Nat) (N B : Nat)
    (ha : ∀ i, i < N → a i ≤ B) (hb : ∀ j, j < N → b j ≤ B)
    (hidx : ∀ i, i < N → idx i < N) (hfit : N * (B * B) < fermatTowerMod4) :
    let c := convPairSum a b idx N
    c ≤ N * (B * B) ∧
    c < fermatTowerMod4 ∧
    garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c := by
  intro c
  have hle : c ≤ N * (B * B) :=
    convPairSum_le_prefix a b idx N B N (Nat.le_refl N) ha hb hidx
  have hlt : c < fermatTowerMod4 := Nat.lt_of_le_of_lt hle hfit
  exact ⟨hle, hlt, garnerReconstruct4_sound c hlt⟩

/-- Sharp Fermat-Tower NTT Convolution Wrap-Around Certificates (`M_4 = 1,431,655,765`):
Certifies the exact maximum single-limb bounds for `N ∈ {4, 8, 16}`:
1. `N = 4`:  `B ≤ 18918` (`4 * 18918^2 = 1431562896 < M_4 < 4 * 18919^2`)
2. `N = 8`:  `B ≤ 13377` (`8 * 13377^2 = 1431553032 < M_4 < 8 * 13378^2`)
3. `N = 16`: `B ≤ 9459`  (`16 * 9459^2 = 1431562896 < M_4 < 16 * 9460^2`)
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermat_tower_conv_bound_certs :
    (4 * (18918 * 18918) = 1431562896 ∧
      4 * (18918 * 18918) < fermatTowerMod4 ∧
      fermatTowerMod4 < 4 * (18919 * 18919)) ∧
    (8 * (13377 * 13377) = 1431553032 ∧
      8 * (13377 * 13377) < fermatTowerMod4 ∧
      fermatTowerMod4 < 8 * (13378 * 13378)) ∧
    (16 * (9459 * 9459) = 1431562896 ∧
      16 * (9459 * 9459) < fermatTowerMod4 ∧
      fermatTowerMod4 < 16 * (9460 * 9460)) ∧
    (∀ (a b : Nat → Nat) (idx : Nat → Nat),
      (∀ i, i < 4 → a i ≤ 18918) → (∀ j, j < 4 → b j ≤ 18918) →
      (∀ i, i < 4 → idx i < 4) →
      let c := convPairSum a b idx 4
      c < fermatTowerMod4 ∧
      garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c) ∧
    (∀ (a b : Nat → Nat) (idx : Nat → Nat),
      (∀ i, i < 8 → a i ≤ 13377) → (∀ j, j < 8 → b j ≤ 13377) →
      (∀ i, i < 8 → idx i < 8) →
      let c := convPairSum a b idx 8
      c < fermatTowerMod4 ∧
      garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c) ∧
    (∀ (a b : Nat → Nat) (idx : Nat → Nat),
      (∀ i, i < 16 → a i ≤ 9459) → (∀ j, j < 16 → b j ≤ 9459) →
      (∀ i, i < 16 → idx i < 16) →
      let c := convPairSum a b idx 16
      c < fermatTowerMod4 ∧
      garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c) := by
  have hc4 : 4 * (18918 * 18918) < fermatTowerMod4 := by decide
  have hc8 : 8 * (13377 * 13377) < fermatTowerMod4 := by decide
  have hc16 : 16 * (9459 * 9459) < fermatTowerMod4 := by decide
  refine ⟨⟨rfl, hc4, by decide⟩, ⟨rfl, hc8, by decide⟩, ⟨rfl, hc16, by decide⟩, ?_, ?_, ?_⟩
  · intro a b idx ha hb hidx
    have h := ntt_convolution_no_wraparound a b idx 4 18918 ha hb hidx hc4
    exact ⟨h.2.1, h.2.2⟩
  · intro a b idx ha hb hidx
    have h := ntt_convolution_no_wraparound a b idx 8 13377 ha hb hidx hc8
    exact ⟨h.2.1, h.2.2⟩
  · intro a b idx ha hb hidx
    have h := ntt_convolution_no_wraparound a b idx 16 9459 ha hb hidx hc16
    exact ⟨h.2.1, h.2.2⟩

end CrtNtt

-- end of file: leanasm/src/LeanAsm/CrtNttUniversal.lean
