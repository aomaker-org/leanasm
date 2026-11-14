-- Path: leanasm/src/LeanAsm/MiniVMNttBridge.lean
import LeanAsm.MiniVM
import LeanAsm.NttArithmetic

/-!
# MiniVM F_17 NTT Assembly Bridge (Issue #11)

Verified assembly implementations on `LeanAsm.MiniVM` over `F_17`:
- 2-point NTT/INTT (`ntt2AsmF17`, `intt2AsmF17`) over `(r0, r1)` using
  scratch registers `(r2, r3)` with explicit `+ 17` bias before `subReg`.
- 4-point Cooley-Tukey DIT NTT/INTT (`ntt4AsmF17`, `intt4AsmF17`) over
  `(r0, r1, r2, r3)` using scratch registers `(t0, t1)`, `omega4 = 13`,
  `invOmega4 = 4`, and `invFour = 13`.

All soundness and roundtrip theorems are proved symbolically over all `Nat`
register values `< 17` (`289` and `83,521` states) with ZERO `Classical.choice`
and ZERO `sorryAx`.
-/

namespace MiniVMNttBridge

open MiniVM
open NttArithmetic

-- =============================================================================
-- Generic In-Place Radix-2 Butterfly on MiniVM (F_17)
-- =============================================================================

/--
Radix-2 butterfly modulo `p = 17` on `(rA, rB)` using scratch registers
`(scr1, scr2)`. Adds explicit `+ 17` bias after reducing `rB` mod `17` so `Nat`
subtraction never underflows for arbitrary initial `rA, rB : Nat`.
-/
def butterfly2AsmF17 (rA rB scr1 scr2 : Reg) : List Instr := [
  Instr.modImm rB p,
  Instr.movReg scr1 rA,
  Instr.addReg scr1 rB,
  Instr.modImm scr1 p,
  Instr.movReg scr2 rA,
  Instr.addImm scr2 p,
  Instr.subReg scr2 rB,
  Instr.modImm scr2 p,
  Instr.movReg rA scr1,
  Instr.movReg rB scr2
]

private theorem butterfly_sum_mod (a b : Nat) :
    (a + b % p) % p = (a + b) % p := by
  dsimp [p]
  omega

/--
Symbolic execution semantics for `butterfly2AsmF17` on distinct registers
`rA, rB, scr1, scr2`. Updates `(rA, rB)` to `nttButterfly2 (s.get rA) (s.get rB) p`
and preserves every register other than `rA, rB, scr1, scr2`.
-/
theorem runProgram_butterfly2AsmF17 (s : State) (rA rB scr1 scr2 : Reg)
    (hAB : rA ≠ rB) (hA1 : rA ≠ scr1) (hA2 : rA ≠ scr2)
    (hB1 : rB ≠ scr1) (hB2 : rB ≠ scr2) (h12 : scr1 ≠ scr2) :
    let s' := runProgram s (butterfly2AsmF17 rA rB scr1 scr2)
    s'.get rA = (nttButterfly2 (s.get rA) (s.get rB) p).1 ∧
    s'.get rB = (nttButterfly2 (s.get rA) (s.get rB) p).2 ∧
    ∀ r, r ≠ rA → r ≠ rB → r ≠ scr1 → r ≠ scr2 → s'.get r = s.get r := by
  dsimp [butterfly2AsmF17, runProgram, step, nttButterfly2]
  simp only [get_set_pc, get_set_same,
    get_set_other _ _ _ _ hAB.symm,
    get_set_other _ _ _ _ hA1.symm,
    get_set_other _ _ _ _ hA2,
    get_set_other _ _ _ _ hB1.symm,
    get_set_other _ _ _ _ hB2.symm,
    get_set_other _ _ _ _ h12.symm]
  refine ⟨butterfly_sum_mod (s.get rA) (s.get rB), trivial, ?_⟩
  intro r hrA hrB hr1 hr2
  simp only [get_set_pc,
    get_set_other _ _ _ _ (Ne.symm hrA),
    get_set_other _ _ _ _ (Ne.symm hrB),
    get_set_other _ _ _ _ (Ne.symm hr1),
    get_set_other _ _ _ _ (Ne.symm hr2)]

-- =============================================================================
-- 2-Point F_17 NTT & INTT Assembly Programs (289 Register States)
-- =============================================================================

/--
Compiled 2-point F_17 forward NTT assembly program over input registers
`(r0, r1)` using scratch registers `(r2, r3)`.
-/
def ntt2AsmF17 : List Instr :=
  butterfly2AsmF17 Reg.r0 Reg.r1 Reg.r2 Reg.r3

/--
Compiled 2-point F_17 inverse NTT assembly program over input registers
`(r0, r1)` using scratch registers `(r2, r3)` and `invTwo = 9`.
-/
def intt2AsmF17 : List Instr :=
  butterfly2AsmF17 Reg.r0 Reg.r1 Reg.r2 Reg.r3 ++ [
    Instr.movImm Reg.r2 invTwo,
    Instr.mulModReg Reg.r0 Reg.r2 p,
    Instr.mulModReg Reg.r1 Reg.r2 p
  ]

/--
Soundness theorem for `ntt2AsmF17` across all `a, b < 17` (`289` register states).
-/
theorem ntt2AsmF17_sound (s : State) (a b : Nat)
    (_ha : a < p) (_hb : b < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) :
    let s' := runProgram s ntt2AsmF17
    (s'.r0, s'.r1) = nttButterfly2 a b p := by
  have h := runProgram_butterfly2AsmF17 s Reg.r0 Reg.r1 Reg.r2 Reg.r3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases h with ⟨h0, h1, _⟩
  dsimp [ntt2AsmF17, State.get] at h0 h1 ⊢
  rw [hr0, hr1] at h0 h1
  exact Prod.ext h0 h1

/--
Soundness theorem for `intt2AsmF17` across all `a, b < 17` (`289` register states).
-/
theorem intt2AsmF17_sound (s : State) (a b : Nat)
    (_ha : a < p) (_hb : b < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) :
    let s' := runProgram s intt2AsmF17
    (s'.r0, s'.r1) = inttButterfly2 a b := by
  have h := runProgram_butterfly2AsmF17 s Reg.r0 Reg.r1 Reg.r2 Reg.r3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases h with ⟨h0, h1, _⟩
  dsimp [State.get] at h0 h1
  rw [hr0, hr1] at h0 h1
  dsimp [intt2AsmF17]
  rw [runProgram_append]
  generalize runProgram s (butterfly2AsmF17 Reg.r0 Reg.r1 Reg.r2 Reg.r3) = s1 at h0 h1 ⊢
  rcases s1 with ⟨x0, x1, x2, x3, u0, u1, ipc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc, inttButterfly2] at h0 h1 ⊢
  rw [h0, h1]
  rfl

/--
Roundtrip invertibility of `ntt2AsmF17` followed by `intt2AsmF17` across all
`a, b < 17` (`289` states).
-/
theorem intt2_ntt2_asm_F17_roundtrip (s : State) (a b : Nat)
    (ha : a < p) (hb : b < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) :
    let s1 := runProgram s ntt2AsmF17
    let s2 := runProgram s1 intt2AsmF17
    (s2.r0, s2.r1) = (a, b) := by
  dsimp
  have h1 := ntt2AsmF17_sound s a b ha hb hr0 hr1
  have hb1 : (nttButterfly2 a b p).1 < p := by
    dsimp [nttButterfly2]
    exact Nat.mod_lt _ (by decide)
  have hb2 : (nttButterfly2 a b p).2 < p := by
    dsimp [nttButterfly2]
    exact Nat.mod_lt _ (by decide)
  have hr0' : (runProgram s ntt2AsmF17).r0 = (nttButterfly2 a b p).1 :=
    congrArg Prod.fst h1
  have hr1' : (runProgram s ntt2AsmF17).r1 = (nttButterfly2 a b p).2 :=
    congrArg Prod.snd h1
  have h2 := intt2AsmF17_sound (runProgram s ntt2AsmF17)
    (nttButterfly2 a b p).1 (nttButterfly2 a b p).2 hb1 hb2 hr0' hr1'
  rw [h2]
  dsimp [inttButterfly2, nttButterfly2, p, invTwo] at *
  have hL : ((((a + b) % 17 + (a + 17 - b % 17) % 17) % 17) * 9) % 17 = a := by
    omega
  have hR : ((((a + b) % 17 + 17 - ((a + 17 - b % 17) % 17) % 17) % 17) * 9) % 17 = b := by
    omega
  exact Prod.ext hL hR

-- =============================================================================
-- 4-Point F_17 NTT & INTT Assembly Programs (83,521 Register States)
-- =============================================================================

/--
Shared 4-point radix-2 decimation-in-time butterfly skeleton parameterized by
twiddle factor `w` over input registers `(r0, r1, r2, r3)` and scratch registers
`(t0, t1)`.
-/
def dit4AsmF17 (w : Nat) : List Instr :=
  butterfly2AsmF17 Reg.r0 Reg.r2 Reg.t0 Reg.t1 ++
  butterfly2AsmF17 Reg.r1 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p] ++
  butterfly2AsmF17 Reg.r0 Reg.r1 Reg.t0 Reg.t1 ++
  butterfly2AsmF17 Reg.r2 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r2, Instr.movReg Reg.r2 Reg.t0]

/--
Compiled 4-point F_17 forward NTT assembly program over `(r0, r1, r2, r3)`
using `omega4 = 13`.
-/
def ntt4AsmF17 : List Instr :=
  dit4AsmF17 omega4

/--
Compiled 4-point F_17 inverse NTT assembly program over `(r0, r1, r2, r3)`
using `invOmega4 = 4` and `invFour = 13`.
-/
def intt4AsmF17 : List Instr :=
  dit4AsmF17 invOmega4 ++ [
    Instr.movImm Reg.t0 invFour,
    Instr.mulModReg Reg.r0 Reg.t0 p,
    Instr.mulModReg Reg.r1 Reg.t0 p,
    Instr.mulModReg Reg.r2 Reg.t0 p,
    Instr.mulModReg Reg.r3 Reg.t0 p
  ]

private theorem runProgram_twiddle (s : State) (w : Nat) :
    let s' := runProgram s [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p]
    s'.get Reg.r0 = s.get Reg.r0 ∧
    s'.get Reg.r1 = s.get Reg.r1 ∧
    s'.get Reg.r2 = s.get Reg.r2 ∧
    s'.get Reg.r3 = (s.get Reg.r3 * w) % p := by
  rcases s with ⟨r0, r1, r2, r3, t0, t1, pc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runProgram_swap12 (s : State) :
    let s' := runProgram s
      [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r2, Instr.movReg Reg.r2 Reg.t0]
    s'.r0 = s.get Reg.r0 ∧
    s'.r1 = s.get Reg.r2 ∧
    s'.r2 = s.get Reg.r1 ∧
    s'.r3 = s.get Reg.r3 := by
  rcases s with ⟨r0, r1, r2, r3, t0, t1, pc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runProgram_dit4AsmF17 (s : State) (w : Nat) :
    let v : Vec4 := ⟨s.r0, s.r1, s.r2, s.r3⟩
    let s' := runProgram s (dit4AsmF17 w)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = ntt4 p w v := by
  dsimp [dit4AsmF17, ntt4]
  simp only [runProgram_append]
  have hs1 := runProgram_butterfly2AsmF17 s Reg.r0 Reg.r2 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s (butterfly2AsmF17 Reg.r0 Reg.r2 Reg.t0 Reg.t1) = s1 at hs1 ⊢
  rcases hs1 with ⟨h1_r0, h1_r2, h1_pres⟩
  have h1_r1 : s1.get Reg.r1 = s.get Reg.r1 :=
    h1_pres Reg.r1 (by decide) (by decide) (by decide) (by decide)
  have h1_r3 : s1.get Reg.r3 = s.get Reg.r3 :=
    h1_pres Reg.r3 (by decide) (by decide) (by decide) (by decide)
  have hs2 := runProgram_butterfly2AsmF17 s1 Reg.r1 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s1 (butterfly2AsmF17 Reg.r1 Reg.r3 Reg.t0 Reg.t1) = s2 at hs2 ⊢
  rcases hs2 with ⟨h2_r1, h2_r3, h2_pres⟩
  have h2_r0 : s2.get Reg.r0 = s1.get Reg.r0 :=
    h2_pres Reg.r0 (by decide) (by decide) (by decide) (by decide)
  have h2_r2 : s2.get Reg.r2 = s1.get Reg.r2 :=
    h2_pres Reg.r2 (by decide) (by decide) (by decide) (by decide)
  have hs3 := runProgram_twiddle s2 w
  generalize runProgram s2 [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p] = s3
    at hs3 ⊢
  rcases hs3 with ⟨h3_r0, h3_r1, h3_r2, h3_r3⟩
  have hs4 := runProgram_butterfly2AsmF17 s3 Reg.r0 Reg.r1 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s3 (butterfly2AsmF17 Reg.r0 Reg.r1 Reg.t0 Reg.t1) = s4 at hs4 ⊢
  rcases hs4 with ⟨h4_r0, h4_r1, h4_pres⟩
  have h4_r2 : s4.get Reg.r2 = s3.get Reg.r2 :=
    h4_pres Reg.r2 (by decide) (by decide) (by decide) (by decide)
  have h4_r3 : s4.get Reg.r3 = s3.get Reg.r3 :=
    h4_pres Reg.r3 (by decide) (by decide) (by decide) (by decide)
  have hs5 := runProgram_butterfly2AsmF17 s4 Reg.r2 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s4 (butterfly2AsmF17 Reg.r2 Reg.r3 Reg.t0 Reg.t1) = s5 at hs5 ⊢
  rcases hs5 with ⟨h5_r2, h5_r3, h5_pres⟩
  have h5_r0 : s5.get Reg.r0 = s4.get Reg.r0 :=
    h5_pres Reg.r0 (by decide) (by decide) (by decide) (by decide)
  have h5_r1 : s5.get Reg.r1 = s4.get Reg.r1 :=
    h5_pres Reg.r1 (by decide) (by decide) (by decide) (by decide)
  have hs6 := runProgram_swap12 s5
  rcases hs6 with ⟨h6_r0, h6_r1, h6_r2, h6_r3⟩
  rw [h6_r0, h6_r1, h6_r2, h6_r3]
  rw [h5_r0, h5_r2, h5_r1, h5_r3, h4_r0, h4_r1, h4_r2, h4_r3,
      h3_r0, h3_r1, h3_r2, h3_r3, h2_r0, h2_r1, h2_r2, h2_r3,
      h1_r0, h1_r1, h1_r2, h1_r3]
  dsimp [State.get, nttButterfly2]
  have hm0 :
      ((s.r0 + s.r2) % p + ((s.r1 + s.r3) % p) % p) % p =
      ((s.r0 + s.r2) % p + (s.r1 + s.r3) % p) % p := by
    dsimp [p]
    omega
  have hm2 :
      ((s.r0 + s.r2) % p + p - (((s.r1 + s.r3) % p) % p) % p) % p =
      ((s.r0 + s.r2) % p + p - ((s.r1 + s.r3) % p) % p) % p := by
    dsimp [p]
    omega
  rw [hm0, hm2]

/--
Soundness theorem for `ntt4AsmF17` across all `a, b, c, d < 17` (`83,521` states).
-/
theorem ntt4AsmF17_sound (s : State) (a b c d : Nat)
    (_ha : a < p) (_hb : b < p) (_hc : c < p) (_hd : d < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s' := runProgram s ntt4AsmF17
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = ntt4 p omega4 ⟨a, b, c, d⟩ := by
  have h := runProgram_dit4AsmF17 s omega4
  rw [hr0, hr1, hr2, hr3] at h
  exact h

/--
Soundness theorem for `intt4AsmF17` across all `a, b, c, d < 17` (`83,521` states).
-/
theorem intt4AsmF17_sound (s : State) (a b c d : Nat)
    (_ha : a < p) (_hb : b < p) (_hc : c < p) (_hd : d < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s' := runProgram s intt4AsmF17
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = intt4 p invFour invOmega4 ⟨a, b, c, d⟩ := by
  have h := runProgram_dit4AsmF17 s invOmega4
  rw [hr0, hr1, hr2, hr3] at h
  dsimp [intt4AsmF17]
  rw [runProgram_append]
  generalize runProgram s (dit4AsmF17 invOmega4) = s1 at h ⊢
  rcases s1 with ⟨x0, x1, x2, x3, u0, u1, ipc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  have hx0 : x0 = (ntt4 p invOmega4 ⟨a, b, c, d⟩).x0 := congrArg Vec4.x0 h
  have hx1 : x1 = (ntt4 p invOmega4 ⟨a, b, c, d⟩).x1 := congrArg Vec4.x1 h
  have hx2 : x2 = (ntt4 p invOmega4 ⟨a, b, c, d⟩).x2 := congrArg Vec4.x2 h
  have hx3 : x3 = (ntt4 p invOmega4 ⟨a, b, c, d⟩).x3 := congrArg Vec4.x3 h
  rw [hx0, hx1, hx2, hx3]
  dsimp [ntt4, intt4]
  simp only [Nat.mod_mul_mod]

private theorem ntt4_omega4_lane0 (v : Vec4) :
    (ntt4 17 13 v).x0 = (v.x0 + v.x1 + v.x2 + v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

private theorem ntt4_omega4_lane1 (v : Vec4) :
    (ntt4 17 13 v).x1 = (v.x0 + 13 * v.x1 + 16 * v.x2 + 4 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

private theorem ntt4_omega4_lane2 (v : Vec4) :
    (ntt4 17 13 v).x2 = (v.x0 + 16 * v.x1 + v.x2 + 16 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

private theorem ntt4_omega4_lane3 (v : Vec4) :
    (ntt4 17 13 v).x3 = (v.x0 + 4 * v.x1 + 16 * v.x2 + 13 * v.x3) % 17 := by
  dsimp [ntt4, nttButterfly2]; omega

private theorem intt4_invOmega4_lane0 (X : Vec4) :
    (intt4 17 13 4 X).x0 = ((X.x0 + X.x1 + X.x2 + X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

private theorem intt4_invOmega4_lane1 (X : Vec4) :
    (intt4 17 13 4 X).x1 = ((X.x0 + 4 * X.x1 + 16 * X.x2 + 13 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

private theorem intt4_invOmega4_lane2 (X : Vec4) :
    (intt4 17 13 4 X).x2 = ((X.x0 + 16 * X.x1 + X.x2 + 16 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

private theorem intt4_invOmega4_lane3 (X : Vec4) :
    (intt4 17 13 4 X).x3 = ((X.x0 + 13 * X.x1 + 16 * X.x2 + 4 * X.x3) * 13) % 17 := by
  dsimp [intt4, nttButterfly2]; omega

private theorem intt4_ntt4_omega4_lanes (a0 a1 a2 a3 Y0 Y1 Y2 Y3 : Nat)
    (hy0 : Y0 = (a0 + a1 + a2 + a3) % 17)
    (hy1 : Y1 = (a0 + 13 * a1 + 16 * a2 + 4 * a3) % 17)
    (hy2 : Y2 = (a0 + 16 * a1 + a2 + 16 * a3) % 17)
    (hy3 : Y3 = (a0 + 4 * a1 + 16 * a2 + 13 * a3) % 17) :
    ((Y0 + Y1 + Y2 + Y3) * 13) % 17 = a0 % 17 ∧
    ((Y0 + 4 * Y1 + 16 * Y2 + 13 * Y3) * 13) % 17 = a1 % 17 ∧
    ((Y0 + 16 * Y1 + Y2 + 16 * Y3) * 13) % 17 = a2 % 17 ∧
    ((Y0 + 13 * Y1 + 16 * Y2 + 4 * Y3) * 13) % 17 = a3 % 17 := by
  have h0 : a0 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h1 : a1 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h2 : a2 % 17 < 17 := Nat.mod_lt _ (by decide)
  have h3 : a3 % 17 < 17 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem intt4_ntt4_omega4_F17 (a b c d : Nat)
    (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p) :
    intt4 p invFour invOmega4 (ntt4 p omega4 ⟨a, b, c, d⟩) = ⟨a, b, c, d⟩ := by
  dsimp [p, omega4, invOmega4, invFour] at *
  have hy0 := ntt4_omega4_lane0 ⟨a, b, c, d⟩
  have hy1 := ntt4_omega4_lane1 ⟨a, b, c, d⟩
  have hy2 := ntt4_omega4_lane2 ⟨a, b, c, d⟩
  have hy3 := ntt4_omega4_lane3 ⟨a, b, c, d⟩
  have hi0 := intt4_invOmega4_lane0 (ntt4 17 13 ⟨a, b, c, d⟩)
  have hi1 := intt4_invOmega4_lane1 (ntt4 17 13 ⟨a, b, c, d⟩)
  have hi2 := intt4_invOmega4_lane2 (ntt4 17 13 ⟨a, b, c, d⟩)
  have hi3 := intt4_invOmega4_lane3 (ntt4 17 13 ⟨a, b, c, d⟩)
  have hcomb := intt4_ntt4_omega4_lanes a b c d
    (ntt4 17 13 ⟨a, b, c, d⟩).x0 (ntt4 17 13 ⟨a, b, c, d⟩).x1
    (ntt4 17 13 ⟨a, b, c, d⟩).x2 (ntt4 17 13 ⟨a, b, c, d⟩).x3
    hy0 hy1 hy2 hy3
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at hcomb
  apply vec4_eq_intro
  · rw [hi0]; exact hcomb.1
  · rw [hi1]; exact hcomb.2.1
  · rw [hi2]; exact hcomb.2.2.1
  · rw [hi3]; exact hcomb.2.2.2

/--
Roundtrip invertibility of `ntt4AsmF17` followed by `intt4AsmF17` across all
`a, b, c, d < 17` (`83,521` states).
-/
theorem intt4_ntt4_asm_F17_roundtrip (s : State) (a b c d : Nat)
    (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s1 := runProgram s ntt4AsmF17
    let s2 := runProgram s1 intt4AsmF17
    (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : Vec4) = ⟨a, b, c, d⟩ := by
  dsimp
  have h1 := ntt4AsmF17_sound s a b c d ha hb hc hd hr0 hr1 hr2 hr3
  let Y := ntt4 p omega4 ⟨a, b, c, d⟩
  have hy0 : Y.x0 < p := by
    dsimp [Y, ntt4]
    exact Nat.mod_lt _ (by decide)
  have hy1 : Y.x1 < p := by
    dsimp [Y, ntt4]
    exact Nat.mod_lt _ (by decide)
  have hy2 : Y.x2 < p := by
    dsimp [Y, ntt4]
    exact Nat.mod_lt _ (by decide)
  have hy3 : Y.x3 < p := by
    dsimp [Y, ntt4]
    exact Nat.mod_lt _ (by decide)
  have hr0' : (runProgram s ntt4AsmF17).r0 = Y.x0 := congrArg Vec4.x0 h1
  have hr1' : (runProgram s ntt4AsmF17).r1 = Y.x1 := congrArg Vec4.x1 h1
  have hr2' : (runProgram s ntt4AsmF17).r2 = Y.x2 := congrArg Vec4.x2 h1
  have hr3' : (runProgram s ntt4AsmF17).r3 = Y.x3 := congrArg Vec4.x3 h1
  have h2 := intt4AsmF17_sound (runProgram s ntt4AsmF17)
    Y.x0 Y.x1 Y.x2 Y.x3 hy0 hy1 hy2 hy3 hr0' hr1' hr2' hr3'
  have hYeta : (⟨Y.x0, Y.x1, Y.x2, Y.x3⟩ : Vec4) = Y := by
    cases Y
    rfl
  rw [h2, hYeta]
  exact intt4_ntt4_omega4_F17 a b c d ha hb hc hd

end MiniVMNttBridge

-- end of file: leanasm/src/LeanAsm/MiniVMNttBridge.lean
