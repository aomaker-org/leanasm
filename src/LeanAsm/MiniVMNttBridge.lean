-- Path: leanasm/src/LeanAsm/MiniVMNttBridge.lean
import LeanAsm.MiniVM
import LeanAsm.NttArithmetic
import LeanAsm.CrtNttUniversal

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
  rcases s1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, u0, u1, ipc⟩
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
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runProgram_swap12 (s : State) :
    let s' := runProgram s
      [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r2, Instr.movReg Reg.r2 Reg.t0]
    s'.r0 = s.get Reg.r0 ∧
    s'.r1 = s.get Reg.r2 ∧
    s'.r2 = s.get Reg.r1 ∧
    s'.r3 = s.get Reg.r3 := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
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
  rcases s1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, u0, u1, ipc⟩
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

-- =============================================================================
-- Parametric 4-Prime Fermat-Tower NTT/INTT Compilation (Issue #53)
-- =============================================================================

/--
Generic in-place radix-2 butterfly modulo `p` on `(rA, rB)` using scratch
registers `(scr1, scr2)`. Adds `+ p` bias after reducing `rB` mod `p` so `Nat`
subtraction never underflows.
-/
def butterfly2Asm (p : Nat) (rA rB scr1 scr2 : Reg) : List Instr := [
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

private theorem add_mod_self_right (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/--
Symbolic execution semantics for `butterfly2Asm p` on distinct registers
`rA, rB, scr1, scr2`. Updates `(rA, rB)` to `nttButterfly2 (s.get rA) (s.get rB) p`
and preserves every other register.
-/
theorem runProgram_butterfly2Asm (p : Nat) (s : State) (rA rB scr1 scr2 : Reg)
    (hAB : rA ≠ rB) (hA1 : rA ≠ scr1) (hA2 : rA ≠ scr2)
    (hB1 : rB ≠ scr1) (hB2 : rB ≠ scr2) (h12 : scr1 ≠ scr2) :
    let s' := runProgram s (butterfly2Asm p rA rB scr1 scr2)
    s'.get rA = (nttButterfly2 (s.get rA) (s.get rB) p).1 ∧
    s'.get rB = (nttButterfly2 (s.get rA) (s.get rB) p).2 ∧
    ∀ r, r ≠ rA → r ≠ rB → r ≠ scr1 → r ≠ scr2 → s'.get r = s.get r := by
  dsimp [butterfly2Asm, runProgram, step, nttButterfly2]
  simp only [get_set_pc, get_set_same,
    get_set_other _ _ _ _ hAB.symm,
    get_set_other _ _ _ _ hA1.symm,
    get_set_other _ _ _ _ hA2,
    get_set_other _ _ _ _ hB1.symm,
    get_set_other _ _ _ _ hB2.symm,
    get_set_other _ _ _ _ h12.symm]
  refine ⟨add_mod_self_right (s.get rA) (s.get rB) p, trivial, ?_⟩
  intro r hrA hrB hr1 hr2
  simp only [get_set_pc,
    get_set_other _ _ _ _ (Ne.symm hrA),
    get_set_other _ _ _ _ (Ne.symm hrB),
    get_set_other _ _ _ _ (Ne.symm hr1),
    get_set_other _ _ _ _ (Ne.symm hr2)]

/--
Parametric 4-point radix-2 DIT butterfly skeleton modulo `p` with twiddle factor
`w` over input registers `(r0, r1, r2, r3)` and scratch `(t0, t1)`.
-/
def dit4Asm (p w : Nat) : List Instr :=
  butterfly2Asm p Reg.r0 Reg.r2 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r1 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p] ++
  butterfly2Asm p Reg.r0 Reg.r1 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r2 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r2, Instr.movReg Reg.r2 Reg.t0]

/-- Parametric 4-point forward NTT assembly program over `(r0, r1, r2, r3)`. -/
def ntt4AsmFermat (p w : Nat) : List Instr :=
  dit4Asm p w

/-- Parametric 4-point inverse NTT assembly program over `(r0, r1, r2, r3)`. -/
def intt4AsmFermat (p inv4 invW : Nat) : List Instr :=
  dit4Asm p invW ++ [
    Instr.movImm Reg.t0 inv4,
    Instr.mulModReg Reg.r0 Reg.t0 p,
    Instr.mulModReg Reg.r1 Reg.t0 p,
    Instr.mulModReg Reg.r2 Reg.t0 p,
    Instr.mulModReg Reg.r3 Reg.t0 p
  ]

private theorem runProgram_twiddleMod (p : Nat) (s : State) (w : Nat) :
    let s' := runProgram s [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p]
    s'.get Reg.r0 = s.get Reg.r0 ∧
    s'.get Reg.r1 = s.get Reg.r1 ∧
    s'.get Reg.r2 = s.get Reg.r2 ∧
    s'.get Reg.r3 = (s.get Reg.r3 * w) % p := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runProgram_dit4Asm (p w : Nat) (s : State) :
    let v : Vec4 := ⟨s.r0, s.r1, s.r2, s.r3⟩
    let s' := runProgram s (dit4Asm p w)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = ntt4 p w v := by
  dsimp [dit4Asm, ntt4]
  simp only [runProgram_append]
  have hs1 := runProgram_butterfly2Asm p s Reg.r0 Reg.r2 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s (butterfly2Asm p Reg.r0 Reg.r2 Reg.t0 Reg.t1) = s1 at hs1 ⊢
  rcases hs1 with ⟨h1_r0, h1_r2, h1_pres⟩
  have h1_r1 : s1.get Reg.r1 = s.get Reg.r1 :=
    h1_pres Reg.r1 (by decide) (by decide) (by decide) (by decide)
  have h1_r3 : s1.get Reg.r3 = s.get Reg.r3 :=
    h1_pres Reg.r3 (by decide) (by decide) (by decide) (by decide)
  have hs2 := runProgram_butterfly2Asm p s1 Reg.r1 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s1 (butterfly2Asm p Reg.r1 Reg.r3 Reg.t0 Reg.t1) = s2 at hs2 ⊢
  rcases hs2 with ⟨h2_r1, h2_r3, h2_pres⟩
  have h2_r0 : s2.get Reg.r0 = s1.get Reg.r0 :=
    h2_pres Reg.r0 (by decide) (by decide) (by decide) (by decide)
  have h2_r2 : s2.get Reg.r2 = s1.get Reg.r2 :=
    h2_pres Reg.r2 (by decide) (by decide) (by decide) (by decide)
  have hs3 := runProgram_twiddleMod p s2 w
  generalize runProgram s2 [Instr.movImm Reg.t0 w, Instr.mulModReg Reg.r3 Reg.t0 p] = s3
    at hs3 ⊢
  rcases hs3 with ⟨h3_r0, h3_r1, h3_r2, h3_r3⟩
  have hs4 := runProgram_butterfly2Asm p s3 Reg.r0 Reg.r1 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s3 (butterfly2Asm p Reg.r0 Reg.r1 Reg.t0 Reg.t1) = s4 at hs4 ⊢
  rcases hs4 with ⟨h4_r0, h4_r1, h4_pres⟩
  have h4_r2 : s4.get Reg.r2 = s3.get Reg.r2 :=
    h4_pres Reg.r2 (by decide) (by decide) (by decide) (by decide)
  have h4_r3 : s4.get Reg.r3 = s3.get Reg.r3 :=
    h4_pres Reg.r3 (by decide) (by decide) (by decide) (by decide)
  have hs5 := runProgram_butterfly2Asm p s4 Reg.r2 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize runProgram s4 (butterfly2Asm p Reg.r2 Reg.r3 Reg.t0 Reg.t1) = s5 at hs5 ⊢
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
    rw [Nat.mod_mod]
  have hm2 :
      ((s.r0 + s.r2) % p + p - (((s.r1 + s.r3) % p) % p) % p) % p =
      ((s.r0 + s.r2) % p + p - ((s.r1 + s.r3) % p) % p) % p := by
    rw [Nat.mod_mod]
  rw [hm0, hm2]

/-- Symbolic soundness of `ntt4AsmFermat p w` matching `NttArithmetic.ntt4 p w`. -/
theorem ntt4AsmFermat_sound (p w : Nat) (s : State) (a b c d : Nat)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s' := runProgram s (ntt4AsmFermat p w)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = ntt4 p w ⟨a, b, c, d⟩ := by
  have h := runProgram_dit4Asm p w s
  rw [hr0, hr1, hr2, hr3] at h
  exact h

/-- Symbolic soundness of `intt4AsmFermat p inv4 invW` matching `NttArithmetic.intt4`. -/
theorem intt4AsmFermat_sound (p inv4 invW : Nat) (s : State) (a b c d : Nat)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s' := runProgram s (intt4AsmFermat p inv4 invW)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : Vec4) = intt4 p inv4 invW ⟨a, b, c, d⟩ := by
  have h := runProgram_dit4Asm p invW s
  rw [hr0, hr1, hr2, hr3] at h
  dsimp [intt4AsmFermat]
  rw [runProgram_append]
  generalize runProgram s (dit4Asm p invW) = s1 at h ⊢
  rcases s1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, u0, u1, ipc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  have hx0 : x0 = (ntt4 p invW ⟨a, b, c, d⟩).x0 := congrArg Vec4.x0 h
  have hx1 : x1 = (ntt4 p invW ⟨a, b, c, d⟩).x1 := congrArg Vec4.x1 h
  have hx2 : x2 = (ntt4 p invW ⟨a, b, c, d⟩).x2 := congrArg Vec4.x2 h
  have hx3 : x3 = (ntt4 p invW ⟨a, b, c, d⟩).x3 := congrArg Vec4.x3 h
  rw [hx0, hx1, hx2, hx3]
  dsimp [ntt4, intt4]
  simp only [Nat.mod_mul_mod]

/-- Parameter bundle for 4-point NTT/INTT over a Fermat-tower prime `p`. -/
structure FermatNtt4Spec where
  p : Nat
  omega4 : Nat
  invOmega4 : Nat
  invFour : Nat
  deriving DecidableEq, Repr

/-- Algebraic validity of a 4-point Fermat-tower parameter configuration. -/
def FermatNtt4Spec.Valid (cfg : FermatNtt4Spec) : Prop :=
  1 < cfg.p ∧
  (cfg.omega4 * cfg.omega4 + 1) % cfg.p = 0 ∧
  (cfg.omega4 * cfg.invOmega4) % cfg.p = 1 ∧
  (4 * cfg.invFour) % cfg.p = 1

/-- Canonical 4-point NTT parameters for `F_1 = 5` (`omega4 = 2`). -/
def fermatNtt4Spec5 : FermatNtt4Spec :=
  { p := 5, omega4 := 2, invOmega4 := 3, invFour := 4 }

/-- Canonical 4-point NTT parameters for `F_2 = 17` (`omega4 = 4`). -/
def fermatNtt4Spec17 : FermatNtt4Spec :=
  { p := 17, omega4 := 4, invOmega4 := 13, invFour := 13 }

/-- Canonical 4-point NTT parameters for `F_3 = 257` (`omega4 = 16`). -/
def fermatNtt4Spec257 : FermatNtt4Spec :=
  { p := 257, omega4 := 16, invOmega4 := 241, invFour := 193 }

/-- Canonical 4-point NTT parameters for `F_4 = 65537` (`omega4 = 256`). -/
def fermatNtt4Spec65537 : FermatNtt4Spec :=
  { p := 65537, omega4 := 256, invOmega4 := 65281, invFour := 49153 }

/-- All four Fermat-tower 4-point NTT parameter configurations. -/
def fermatTowerNtt4Specs : List FermatNtt4Spec :=
  [fermatNtt4Spec5, fermatNtt4Spec17, fermatNtt4Spec257, fermatNtt4Spec65537]

theorem fermatNtt4Spec5_valid : fermatNtt4Spec5.Valid := by
  dsimp [FermatNtt4Spec.Valid, fermatNtt4Spec5]; decide

theorem fermatNtt4Spec17_valid : fermatNtt4Spec17.Valid := by
  dsimp [FermatNtt4Spec.Valid, fermatNtt4Spec17]; decide

theorem fermatNtt4Spec257_valid : fermatNtt4Spec257.Valid := by
  dsimp [FermatNtt4Spec.Valid, fermatNtt4Spec257]; decide

theorem fermatNtt4Spec65537_valid : fermatNtt4Spec65537.Valid := by
  dsimp [FermatNtt4Spec.Valid, fermatNtt4Spec65537]; decide

/-- Decidable verification that all four Fermat-tower configurations are valid. -/
theorem fermatTowerNtt4Specs_valid :
    ∀ cfg ∈ fermatTowerNtt4Specs, cfg.Valid := by
  intro cfg hmem
  dsimp [fermatTowerNtt4Specs] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact fermatNtt4Spec5_valid
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · exact fermatNtt4Spec17_valid
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact fermatNtt4Spec257_valid
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact fermatNtt4Spec65537_valid
        · contradiction

private theorem natCast_add_int (a b : Nat) :
    ((a + b : Nat) : Int) = (a : Int) + (b : Int) := rfl

private theorem natCast_mul_int (a b : Nat) :
    ((a * b : Nat) : Int) = (a : Int) * (b : Int) := rfl

private theorem mod_add_congr_int (p a b : Nat) :
    (((a + b) % p : Nat) : Int) % (p : Int) = ((a : Int) + (b : Int)) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod, natCast_add_int]

private theorem mod_sub_congr_int (p a b : Nat) (hp : 0 < p) :
    (((a + p - b % p) % p : Nat) : Int) % (p : Int) = ((a : Int) - (b : Int)) % (p : Int) := by
  have hle : b % p ≤ a + p := by
    have := Nat.mod_lt b hp
    omega
  rw [Int.natCast_emod, Int.emod_emod, Int.ofNat_sub hle]
  have ha : ((a + p : Nat) : Int) = (a : Int) + p := rfl
  rw [ha, Int.natCast_emod, Int.sub_emod, Int.add_emod, Int.emod_self, Int.add_zero,
      Int.emod_emod, Int.emod_emod, ← Int.sub_emod]

private theorem mod_mul_congr_int (p a b : Nat) :
    (((a * b) % p : Nat) : Int) % (p : Int) = ((a : Int) * (b : Int)) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod, natCast_mul_int]

private theorem mod_mod_congr_int (p a : Nat) :
    (((a % p) : Nat) : Int) % (p : Int) = (a : Int) % (p : Int) := by
  rw [Int.natCast_emod, Int.emod_emod]

private theorem emod_add_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x + y) % p = (z + u) % p := by
  rw [Int.add_emod, hx, hy, ← Int.add_emod]

private theorem emod_sub_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x - y) % p = (z - u) % p := by
  rw [Int.sub_emod, hx, hy, ← Int.sub_emod]

private theorem emod_mul_cancel {x y z u p : Int}
    (hx : x % p = z % p) (hy : y % p = u % p) :
    (x * y) % p = (z * u) % p := by
  rw [Int.mul_emod, hx, hy, ← Int.mul_emod]

private theorem nat_mod_of_int_mod_eq (p a c : Nat) (b : Int)
    (h : ((a % p : Nat) : Int) % (p : Int) = b % (p : Int))
    (hc : ((c % p : Nat) : Int) % (p : Int) = b % (p : Int)) :
    a % p = c % p := by
  have h1 : ((a % p : Nat) : Int) % (p : Int) = ((c % p : Nat) : Int) % (p : Int) :=
    h.trans hc.symm
  rw [← Int.natCast_emod, ← Int.natCast_emod, Nat.mod_mod, Nat.mod_mod] at h1
  exact Int.ofNat.inj h1

private theorem ntt4_mod_int (p w : Nat) (hp : 0 < p) (v : Vec4) :
    (((ntt4 p w v).x0 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 + ((v.x1 : Int) + v.x3)) % p) ∧
    (((ntt4 p w v).x1 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 + ((v.x1 : Int) - v.x3) * w) % p) ∧
    (((ntt4 p w v).x2 : Int) % (p : Int) =
      ((v.x0 : Int) + v.x2 - ((v.x1 : Int) + v.x3)) % p) ∧
    (((ntt4 p w v).x3 : Int) % (p : Int) =
      ((v.x0 : Int) - v.x2 - ((v.x1 : Int) - v.x3) * w) % p) := by
  rcases v with ⟨a, b, c, d⟩
  dsimp [ntt4, nttButterfly2]
  have he0 := mod_add_congr_int p a c
  have he1 := mod_sub_congr_int p a c hp
  have ht0 : ((↑((b + d) % p % p) : Int)) % p = ((b : Int) + d) % p :=
    (mod_mod_congr_int p ((b + d) % p)).trans (mod_add_congr_int p b d)
  have ht1 : ((↑((b + p - d % p) % p * w % p) : Int)) % p = (((b : Int) - d) * w) % p :=
    (mod_mul_congr_int p _ w).trans (emod_mul_cancel (mod_sub_congr_int p b d hp) rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mod_add_congr_int p _ _).trans (emod_add_cancel he0 ht0)
  · exact (mod_add_congr_int p _ _).trans (emod_add_cancel he1 ht1)
  · exact (mod_sub_congr_int p _ _ hp).trans (emod_sub_cancel he0 ht0)
  · exact (mod_sub_congr_int p _ _ hp).trans (emod_sub_cancel he1 ht1)

private theorem intt4_mod_int (p inv4 invW : Nat) (hp : 0 < p) (X : Vec4) :
    (((intt4 p inv4 invW X).x0 : Int) % (p : Int) =
      (((X.x0 : Int) + X.x2 + ((X.x1 : Int) + X.x3)) * inv4) % p) ∧
    (((intt4 p inv4 invW X).x1 : Int) % (p : Int) =
      (((X.x0 : Int) - X.x2 + ((X.x1 : Int) - X.x3) * invW) * inv4) % p) ∧
    (((intt4 p inv4 invW X).x2 : Int) % (p : Int) =
      (((X.x0 : Int) + X.x2 - ((X.x1 : Int) + X.x3)) * inv4) % p) ∧
    (((intt4 p inv4 invW X).x3 : Int) % (p : Int) =
      (((X.x0 : Int) - X.x2 - ((X.x1 : Int) - X.x3) * invW) * inv4) % p) := by
  rcases X with ⟨x0, x1, x2, x3⟩
  dsimp [intt4, nttButterfly2]
  have hu0 := mod_add_congr_int p x0 x2
  have hu1 := mod_sub_congr_int p x0 x2 hp
  have hw0 : ((↑((x1 + x3) % p % p) : Int)) % p = ((x1 : Int) + x3) % p :=
    (mod_mod_congr_int p ((x1 + x3) % p)).trans (mod_add_congr_int p x1 x3)
  have hw1 : ((↑((x1 + p - x3 % p) % p * invW % p) : Int)) % p =
      (((x1 : Int) - x3) * invW) % p :=
    (mod_mul_congr_int p _ invW).trans (emod_mul_cancel (mod_sub_congr_int p x1 x3 hp) rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (mod_mul_congr_int p _ _).trans (emod_mul_cancel ?_ rfl)
    rw [natCast_add_int]
    exact emod_add_cancel hu0 hw0
  · refine (mod_mul_congr_int p _ _).trans (emod_mul_cancel ?_ rfl)
    rw [natCast_add_int]
    exact emod_add_cancel hu1 hw1
  · refine (mod_mul_congr_int p _ _).trans (emod_mul_cancel ?_ rfl)
    have hle : ((x1 + x3) % p % p) % p ≤ (x0 + x2) % p + p := by
      have := Nat.mod_lt ((x1 + x3) % p % p) hp
      omega
    rw [Int.ofNat_sub hle, natCast_add_int]
    have hsub : (((x0 + x2) % p : Nat) : Int) + (p : Int) -
        (((x1 + x3) % p % p % p : Nat) : Int) =
        ((((x0 + x2) % p : Nat) : Int) - (((x1 + x3) % p % p % p : Nat) : Int)) + (p : Int) := by
      omega
    rw [hsub, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
    exact emod_sub_cancel hu0 ((mod_mod_congr_int p _).trans hw0)
  · refine (mod_mul_congr_int p _ _).trans (emod_mul_cancel ?_ rfl)
    have hle : (x1 + p - x3 % p) % p * invW % p % p ≤ (x0 + p - x2 % p) % p + p := by
      have := Nat.mod_lt ((x1 + p - x3 % p) % p * invW % p) hp
      omega
    rw [Int.ofNat_sub hle, natCast_add_int]
    have hsub : (((x0 + p - x2 % p) % p : Nat) : Int) + (p : Int) -
        (((x1 + p - x3 % p) % p * invW % p % p : Nat) : Int) =
        ((((x0 + p - x2 % p) % p : Nat) : Int) -
          (((x1 + p - x3 % p) % p * invW % p % p : Nat) : Int)) + (p : Int) := by
      omega
    rw [hsub, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
    exact emod_sub_cancel hu1 ((mod_mod_congr_int p _).trans hw1)

/--
Generic algebraic 4-point NTT/INTT invertibility over arbitrary moduli satisfying
`0 < p`, `w * invW ≡ 1 (mod p)`, and `4 * inv4 ≡ 1 (mod p)`.
-/
theorem intt4_ntt4_generic (p w inv4 invW : Nat)
    (hp : 0 < p) (hwinv : (w * invW) % p = 1 % p) (h4inv : (4 * inv4) % p = 1 % p)
    (v : Vec4) :
    intt4 p inv4 invW (ntt4 p w v) = normVec4 p v := by
  have hwi : ((w : Int) * (invW : Int)) % (p : Int) = 1 % (p : Int) := by
    rw [← natCast_mul_int, ← Int.natCast_emod, hwinv, Int.natCast_emod]; rfl
  have h4i : (4 * (inv4 : Int)) % (p : Int) = 1 % (p : Int) := by
    have h4 : (4 : Int) = ((4 : Nat) : Int) := rfl
    rw [h4, ← natCast_mul_int, ← Int.natCast_emod, h4inv, Int.natCast_emod]; rfl
  rcases ntt4_mod_int p w hp v with ⟨hx0, hx1, hx2, hx3⟩
  rcases intt4_mod_int p inv4 invW hp (ntt4 p w v) with ⟨hi0, hi1, hi2, hi3⟩
  have he : ((↑(ntt4 p w v).x0 + ↑(ntt4 p w v).x2) : Int) % p =
      (2 * ((v.x0 : Int) + v.x2)) % p :=
    (emod_add_cancel hx0 hx2).trans (by congr 1; omega)
  have ho : ((↑(ntt4 p w v).x0 - ↑(ntt4 p w v).x2) : Int) % p =
      (2 * ((v.x1 : Int) + v.x3)) % p :=
    (emod_sub_cancel hx0 hx2).trans (by congr 1; omega)
  have hf : ((↑(ntt4 p w v).x1 + ↑(ntt4 p w v).x3) : Int) % p =
      (2 * ((v.x0 : Int) - v.x2)) % p :=
    (emod_add_cancel hx1 hx3).trans (by congr 1; omega)
  have hg : (((↑(ntt4 p w v).x1 - ↑(ntt4 p w v).x3) : Int) * invW) % p =
      (2 * ((v.x1 : Int) - v.x3)) % p := by
    have hdiff : ((↑(ntt4 p w v).x1 - ↑(ntt4 p w v).x3) : Int) % p =
        (2 * (((v.x1 : Int) - v.x3) * w)) % p :=
      (emod_sub_cancel hx1 hx3).trans (by congr 1; omega)
    calc (((↑(ntt4 p w v).x1 - ↑(ntt4 p w v).x3) : Int) * invW) % p
        = ((2 * (((v.x1 : Int) - v.x3) * w)) * invW) % p := emod_mul_cancel hdiff rfl
      _ = ((2 * ((v.x1 : Int) - v.x3)) * (w * invW)) % p := by
            rw [← Int.mul_assoc 2, Int.mul_assoc (2 * ((v.x1 : Int) - v.x3)) w invW]
      _ = ((2 * ((v.x1 : Int) - v.x3)) * 1) % p := emod_mul_cancel rfl hwi
      _ = (2 * ((v.x1 : Int) - v.x3)) % p := by rw [Int.mul_one]
  have hmul4 : ∀ x : Int, ((4 * x) * (inv4 : Int)) % (p : Int) = x % (p : Int) := by
    intro x
    calc ((4 * x) * (inv4 : Int)) % p
        = (x * (4 * (inv4 : Int))) % p := by rw [Int.mul_comm 4 x, Int.mul_assoc]
      _ = (x * 1) % p := emod_mul_cancel rfl h4i
      _ = x % p := by rw [Int.mul_one]
  have hs0 : (((intt4 p inv4 invW (ntt4 p w v)).x0 : Int)) % p = (v.x0 : Int) % p :=
    hi0.trans (emod_mul_cancel ((emod_add_cancel he hf).trans (by congr 1; omega)) rfl)
      |>.trans (hmul4 _)
  have hs1 : (((intt4 p inv4 invW (ntt4 p w v)).x1 : Int)) % p = (v.x1 : Int) % p :=
    hi1.trans (emod_mul_cancel ((emod_add_cancel ho hg).trans (by congr 1; omega)) rfl)
      |>.trans (hmul4 _)
  have hs2 : (((intt4 p inv4 invW (ntt4 p w v)).x2 : Int)) % p = (v.x2 : Int) % p :=
    hi2.trans (emod_mul_cancel ((emod_sub_cancel he hf).trans (by congr 1; omega)) rfl)
      |>.trans (hmul4 _)
  have hs3 : (((intt4 p inv4 invW (ntt4 p w v)).x3 : Int)) % p = (v.x3 : Int) % p :=
    hi3.trans (emod_mul_cancel ((emod_sub_cancel ho hg).trans (by congr 1; omega)) rfl)
      |>.trans (hmul4 _)
  have m0 : (intt4 p inv4 invW (ntt4 p w v)).x0 % p =
      (intt4 p inv4 invW (ntt4 p w v)).x0 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m1 : (intt4 p inv4 invW (ntt4 p w v)).x1 % p =
      (intt4 p inv4 invW (ntt4 p w v)).x1 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m2 : (intt4 p inv4 invW (ntt4 p w v)).x2 % p =
      (intt4 p inv4 invW (ntt4 p w v)).x2 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m3 : (intt4 p inv4 invW (ntt4 p w v)).x3 % p =
      (intt4 p inv4 invW (ntt4 p w v)).x3 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  dsimp [normVec4]
  apply vec4_eq_intro
  · rw [← m0]
    exact nat_mod_of_int_mod_eq p _ _ (v.x0 : Int) (by rw [m0]; exact hs0) (mod_mod_congr_int p _)
  · rw [← m1]
    exact nat_mod_of_int_mod_eq p _ _ (v.x1 : Int) (by rw [m1]; exact hs1) (mod_mod_congr_int p _)
  · rw [← m2]
    exact nat_mod_of_int_mod_eq p _ _ (v.x2 : Int) (by rw [m2]; exact hs2) (mod_mod_congr_int p _)
  · rw [← m3]
    exact nat_mod_of_int_mod_eq p _ _ (v.x3 : Int) (by rw [m3]; exact hs3) (mod_mod_congr_int p _)

/--
Symbolic roundtrip invertibility of `ntt4AsmFermat` followed by `intt4AsmFermat`
across any valid Fermat-tower configuration and all `a, b, c, d < cfg.p`.
-/
theorem intt4_ntt4_asm_fermat_roundtrip (cfg : FermatNtt4Spec) (hcfg : cfg.Valid)
    (s : State) (a b c d : Nat)
    (ha : a < cfg.p) (hb : b < cfg.p) (hc : c < cfg.p) (hd : d < cfg.p)
    (hr0 : s.r0 = a) (hr1 : s.r1 = b) (hr2 : s.r2 = c) (hr3 : s.r3 = d) :
    let s1 := runProgram s (ntt4AsmFermat cfg.p cfg.omega4)
    let s2 := runProgram s1 (intt4AsmFermat cfg.p cfg.invFour cfg.invOmega4)
    (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : Vec4) = ⟨a, b, c, d⟩ := by
  rcases hcfg with ⟨hp1, _, hwinv, h4inv⟩
  have hp0 : 0 < cfg.p := Nat.lt_trans Nat.zero_lt_one hp1
  have h1 := ntt4AsmFermat_sound cfg.p cfg.omega4 s a b c d hr0 hr1 hr2 hr3
  let Y := ntt4 cfg.p cfg.omega4 ⟨a, b, c, d⟩
  have hr0' : (runProgram s (ntt4AsmFermat cfg.p cfg.omega4)).r0 = Y.x0 := congrArg Vec4.x0 h1
  have hr1' : (runProgram s (ntt4AsmFermat cfg.p cfg.omega4)).r1 = Y.x1 := congrArg Vec4.x1 h1
  have hr2' : (runProgram s (ntt4AsmFermat cfg.p cfg.omega4)).r2 = Y.x2 := congrArg Vec4.x2 h1
  have hr3' : (runProgram s (ntt4AsmFermat cfg.p cfg.omega4)).r3 = Y.x3 := congrArg Vec4.x3 h1
  have h2 := intt4AsmFermat_sound cfg.p cfg.invFour cfg.invOmega4
    (runProgram s (ntt4AsmFermat cfg.p cfg.omega4)) Y.x0 Y.x1 Y.x2 Y.x3 hr0' hr1' hr2' hr3'
  have hwinv' : (cfg.omega4 * cfg.invOmega4) % cfg.p = 1 % cfg.p := by
    rw [hwinv, Nat.mod_eq_of_lt hp1]
  have h4inv' : (4 * cfg.invFour) % cfg.p = 1 % cfg.p := by
    rw [h4inv, Nat.mod_eq_of_lt hp1]
  have hinv := intt4_ntt4_generic cfg.p cfg.omega4 cfg.invFour cfg.invOmega4
    hp0 hwinv' h4inv' ⟨a, b, c, d⟩
  dsimp [normVec4] at hinv
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at hinv
  exact h2.trans hinv

/--
Bundled parametric 4-point NTT/INTT assembly roundtrip certificates across all
four Fermat-tower primes `{5, 17, 257, 65537}` (up to `65537^4` states).
-/
theorem fermatTowerNtt4_asm_roundtrip_certs :
    (∀ (cfg : FermatNtt4Spec), cfg ∈ fermatTowerNtt4Specs →
      ∀ (s : State) (a b c d : Nat),
        a < cfg.p → b < cfg.p → c < cfg.p → d < cfg.p →
        s.r0 = a → s.r1 = b → s.r2 = c → s.r3 = d →
        let s1 := runProgram s (ntt4AsmFermat cfg.p cfg.omega4)
        let s2 := runProgram s1 (intt4AsmFermat cfg.p cfg.invFour cfg.invOmega4)
        (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : Vec4) = ⟨a, b, c, d⟩) := by
  intro cfg hmem s a b c d ha hb hc hd hr0 hr1 hr2 hr3
  exact intt4_ntt4_asm_fermat_roundtrip cfg (fermatTowerNtt4Specs_valid cfg hmem)
    s a b c d ha hb hc hd hr0 hr1 hr2 hr3

-- =============================================================================
-- Compiled 4-Channel Garner Mixed-Radix CRT Reconstruction (Issue #53)
-- =============================================================================

private def garnerStep1Asm : List Instr := [
  Instr.modImm Reg.r0 5
]

private def garnerStep2Asm : List Instr := [
  Instr.modImm Reg.r1 17,
  Instr.movReg Reg.t0 Reg.r0,
  Instr.modImm Reg.t0 17,
  Instr.addImm Reg.r1 17,
  Instr.subReg Reg.r1 Reg.t0,
  Instr.movImm Reg.t0 7,
  Instr.mulModReg Reg.r1 Reg.t0 17,
  Instr.movImm Reg.t0 5,
  Instr.mulModReg Reg.r1 Reg.t0 CrtNtt.fermatTowerMod4,
  Instr.addReg Reg.r0 Reg.r1
]

private def garnerStep3Asm : List Instr := [
  Instr.modImm Reg.r2 257,
  Instr.movReg Reg.t0 Reg.r0,
  Instr.modImm Reg.t0 257,
  Instr.addImm Reg.r2 257,
  Instr.subReg Reg.r2 Reg.t0,
  Instr.movImm Reg.t0 127,
  Instr.mulModReg Reg.r2 Reg.t0 257,
  Instr.movImm Reg.t0 85,
  Instr.mulModReg Reg.r2 Reg.t0 CrtNtt.fermatTowerMod4,
  Instr.addReg Reg.r0 Reg.r2
]

private def garnerStep4Asm : List Instr := [
  Instr.modImm Reg.r3 65537,
  Instr.movReg Reg.t0 Reg.r0,
  Instr.modImm Reg.t0 65537,
  Instr.addImm Reg.r3 65537,
  Instr.subReg Reg.r3 Reg.t0,
  Instr.movImm Reg.t0 32767,
  Instr.mulModReg Reg.r3 Reg.t0 65537,
  Instr.movImm Reg.t0 21845,
  Instr.mulModReg Reg.r3 Reg.t0 CrtNtt.fermatTowerMod4,
  Instr.addReg Reg.r0 Reg.r3
]

/--
Compiled 4-prime Garner mixed-radix CRT reconstruction program over moduli
`(5, 17, 257, 65537)` with precomputed inverses `(7, 127, 32767)` (`M_4 = 1,431,655,765`).
Takes residues in `(r0, r1, r2, r3)` and returns the reconstructed `< M_4` value in `r0`.
-/
def garnerReconstruct4Asm : List Instr :=
  garnerStep1Asm ++ garnerStep2Asm ++ garnerStep3Asm ++ garnerStep4Asm

private theorem runProgram_garnerStep1 (s : State) :
    let s' := runProgram s garnerStep1Asm
    s'.r0 = s.r0 % 5 ∧ s'.r1 = s.r1 ∧ s'.r2 = s.r2 ∧ s'.r3 = s.r3 := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
  dsimp [garnerStep1Asm, runProgram, step, State.get, State.set, State.setPc]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem runProgram_garnerStep2 (s : State) :
    let s' := runProgram s garnerStep2Asm
    s'.r0 = s.r0 + 5 * (((s.r1 % 17 + 17 - s.r0 % 17) * 7) % 17) ∧
    s'.r2 = s.r2 ∧ s'.r3 = s.r3 := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
  dsimp [garnerStep2Asm, runProgram, step, State.get, State.set, State.setPc,
    CrtNtt.fermatTowerMod4]
  have hv2lt : ((r1 % 17 + 17 - r0 % 17) * 7) % 17 * 5 < 1431655765 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide : 0 < 17)) (by decide : 0 < 5))
      (by decide)
  rw [Nat.mod_eq_of_lt hv2lt, Nat.mul_comm _ 5]
  exact ⟨rfl, rfl, rfl⟩

private theorem runProgram_garnerStep3 (s : State) :
    let s' := runProgram s garnerStep3Asm
    s'.r0 = s.r0 + 85 * (((s.r2 % 257 + 257 - s.r0 % 257) * 127) % 257) ∧
    s'.r3 = s.r3 := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩
  dsimp [garnerStep3Asm, runProgram, step, State.get, State.set, State.setPc,
    CrtNtt.fermatTowerMod4]
  have hv3lt : ((r2 % 257 + 257 - r0 % 257) * 127) % 257 * 85 < 1431655765 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide : 0 < 257)) (by decide : 0 < 85))
      (by decide)
  rw [Nat.mod_eq_of_lt hv3lt, Nat.mul_comm _ 85]
  exact ⟨rfl, rfl⟩

private theorem step_modImm_r3 (s : State) (m : Nat) :
    step s (Instr.modImm Reg.r3 m) = { s with r3 := s.r3 % m, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_movReg_t0_r0 (s : State) :
    step s (Instr.movReg Reg.t0 Reg.r0) = { s with t0 := s.r0, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_modImm_t0 (s : State) (m : Nat) :
    step s (Instr.modImm Reg.t0 m) = { s with t0 := s.t0 % m, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_addImm_r3 (s : State) (k : Nat) :
    step s (Instr.addImm Reg.r3 k) = { s with r3 := s.r3 + k, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_subReg_r3_t0 (s : State) :
    step s (Instr.subReg Reg.r3 Reg.t0) = { s with r3 := s.r3 - s.t0, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_movImm_t0 (s : State) (v : Nat) :
    step s (Instr.movImm Reg.t0 v) = { s with t0 := v, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_mulModReg_r3_t0 (s : State) (m : Nat) :
    step s (Instr.mulModReg Reg.r3 Reg.t0 m) = { s with r3 := (s.r3 * s.t0) % m, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem step_addReg_r0_r3 (s : State) :
    step s (Instr.addReg Reg.r0 Reg.r3) = { s with r0 := s.r0 + s.r3, pc := s.pc + 1 } := by
  rcases s with ⟨r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, pc⟩; rfl

private theorem runProgram_garnerStep4 (s : State) :
    let s' := runProgram s garnerStep4Asm
    s'.r0 = s.r0 + 21845 * (((s.r3 % 65537 + 65537 - s.r0 % 65537) * 32767) % 65537) := by
  dsimp only [garnerStep4Asm]
  simp only [runProgram, step_modImm_r3, step_movReg_t0_r0, step_modImm_t0,
    step_addImm_r3, step_subReg_r3_t0, step_movImm_t0, step_mulModReg_r3_t0, step_addReg_r0_r3]
  have hv4lt : ((s.r3 % 65537 + 65537 - s.r0 % 65537) * 32767) % 65537 * 21845 < 1431655765 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide : 0 < 65537)) (by decide : 0 < 21845))
      (by decide)
  rw [show CrtNtt.fermatTowerMod4 = 1431655765 by rfl, Nat.mod_eq_of_lt hv4lt, Nat.mul_comm _ 21845]

/--
Symbolic execution equivalence: `garnerReconstruct4Asm` matches
`CrtNtt.garnerReconstruct4` across all initial register states.
-/
theorem runProgram_garnerReconstruct4Asm (s : State) :
    (runProgram s garnerReconstruct4Asm).r0 =
      CrtNtt.garnerReconstruct4 s.r0 s.r1 s.r2 s.r3 := by
  dsimp [garnerReconstruct4Asm]
  simp only [runProgram_append]
  have h1 := runProgram_garnerStep1 s
  generalize runProgram s garnerStep1Asm = s1 at h1 ⊢
  have h2 := runProgram_garnerStep2 s1
  generalize runProgram s1 garnerStep2Asm = s2 at h2 ⊢
  have h3 := runProgram_garnerStep3 s2
  generalize runProgram s2 garnerStep3Asm = s3 at h3 ⊢
  have h4 := runProgram_garnerStep4 s3
  rcases h1 with ⟨h10, h11, h12, h13⟩
  rcases h2 with ⟨h20, h22, h23⟩
  rcases h3 with ⟨h30, h33⟩
  rw [h4, h30, h33, h20, h22, h23, h10, h11, h12, h13]
  rfl


/--
Compiled 4-channel Garner CRT soundness: reconstructs every `x < 1,431,655,765`
from its `(x % 5, x % 17, x % 257, x % 65537)` residues in `(r0, r1, r2, r3)`.
-/
theorem garnerReconstruct4Asm_sound (s : State) (x : Nat)
    (hx : x < CrtNtt.fermatTowerMod4)
    (hr0 : s.r0 = x % 5) (hr1 : s.r1 = x % 17)
    (hr2 : s.r2 = x % 257) (hr3 : s.r3 = x % 65537) :
    (runProgram s garnerReconstruct4Asm).r0 = x := by
  rw [runProgram_garnerReconstruct4Asm, hr0, hr1, hr2, hr3]
  exact CrtNtt.garnerReconstruct4_sound x hx

-- =============================================================================
-- End-to-End 4-Point CRT-NTT Cyclic Convolution Assembly Bridge (Issue #53)
-- =============================================================================

private theorem poly_w_add (oA qA w oB qB : Int) :
    (oA + qA * w) * (oB + qB * w) + (oA - qA * w) * (oB - qB * w) =
      2 * (oA * oB) + 2 * (qA * qB) * (w * w) := by
  calc (oA + qA * w) * (oB + qB * w) + (oA - qA * w) * (oB - qB * w)
      = 2 * oA * oB + 2 * (qA * (w * (qB * w))) := by
          simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
          omega
    _ = 2 * (oA * oB) + 2 * ((qA * qB) * (w * w)) := by
          rw [Int.mul_assoc 2 oA oB, Int.mul_left_comm w qB w, ← Int.mul_assoc qA qB]
    _ = 2 * (oA * oB) + 2 * (qA * qB) * (w * w) := by
          rw [Int.mul_assoc 2 (qA * qB) (w * w)]

private theorem poly_w_sub (oA qA w oB qB : Int) :
    (oA + qA * w) * (oB + qB * w) - (oA - qA * w) * (oB - qB * w) =
      2 * (oA * qB + qA * oB) * w := by
  calc (oA + qA * w) * (oB + qB * w) - (oA - qA * w) * (oB - qB * w)
      = 2 * (oA * (qB * w) + qA * (w * oB)) := by
          simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
          have h3 : qA * (w * (qB * w)) = (qA * qB) * (w * w) := by
            rw [Int.mul_left_comm w qB w, ← Int.mul_assoc]
          omega
    _ = 2 * ((oA * qB) * w + (qA * oB) * w) := by
          rw [← Int.mul_assoc oA qB w, Int.mul_comm w oB, ← Int.mul_assoc qA oB w]
    _ = 2 * (oA * qB + qA * oB) * w := by
          rw [← Int.add_mul, Int.mul_assoc]

private theorem poly_sum_diff_add (x y u v : Int) :
    (x + y) * (u + v) + (x - y) * (u - v) = 2 * (x * u + y * v) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

private theorem poly_sum_diff_sub (x y u v : Int) :
    (x + y) * (u + v) - (x - y) * (u - v) = 2 * (x * v + y * u) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

private theorem conv4_combine_0 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    2 * (((a0 + a2) * (b0 + b2)) + ((a1 + a3) * (b1 + b3))) +
        2 * (((a0 - a2) * (b0 - b2)) - ((a1 - a3) * (b1 - b3))) =
      4 * (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

private theorem conv4_combine_1 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    2 * (((a0 + a2) * (b1 + b3)) + ((a1 + a3) * (b0 + b2))) +
        2 * (((a0 - a2) * (b1 - b3)) + ((a1 - a3) * (b0 - b2))) =
      4 * (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

private theorem conv4_combine_2 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    2 * (((a0 + a2) * (b0 + b2)) + ((a1 + a3) * (b1 + b3))) -
        2 * (((a0 - a2) * (b0 - b2)) - ((a1 - a3) * (b1 - b3))) =
      4 * (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

private theorem conv4_combine_3 (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    2 * (((a0 + a2) * (b1 + b3)) + ((a1 + a3) * (b0 + b2))) -
        2 * (((a0 - a2) * (b1 - b3)) + ((a1 - a3) * (b0 - b2))) =
      4 * (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

/--
Generic symbolic 4-point NTT cyclic convolution soundness over arbitrary valid
moduli satisfying `0 < p`, `w^2 + 1 ≡ 0 (mod p)`, `w * invW ≡ 1 (mod p)`, and
`4 * inv4 ≡ 1 (mod p)`.
-/
theorem cyclic_conv4_ntt_generic (p w inv4 invW : Nat)
    (hp : 0 < p) (hw2 : (w * w + 1) % p = 0)
    (hwinv : (w * invW) % p = 1 % p) (h4inv : (4 * inv4) % p = 1 % p)
    (a b : Vec4) :
    intt4 p inv4 invW (pointwiseMul4 p (ntt4 p w a) (ntt4 p w b)) = cyclicConv4 p a b := by
  have hw2i : ((w : Int) * (w : Int)) % (p : Int) = (-1 : Int) % (p : Int) := by
    have h0 : ((w * w + 1 : Nat) : Int) % (p : Int) = 0 % (p : Int) := by
      rw [← Int.natCast_emod, hw2]; rfl
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdiff : ((w : Int) * (w : Int) - (-1 : Int)) = ((w * w + 1 : Nat) : Int) := by
      rw [natCast_add_int, natCast_mul_int]; rfl
    simpa [hdiff] using h0
  have hwi : ((w : Int) * (invW : Int)) % (p : Int) = 1 % (p : Int) := by
    rw [← natCast_mul_int, ← Int.natCast_emod, hwinv, Int.natCast_emod]; rfl
  have h4i : (4 * (inv4 : Int)) % (p : Int) = 1 % (p : Int) := by
    have h4 : (4 : Int) = ((4 : Nat) : Int) := rfl
    rw [h4, ← natCast_mul_int, ← Int.natCast_emod, h4inv, Int.natCast_emod]; rfl
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  let A := ntt4 p w ⟨a0, a1, a2, a3⟩
  let B := ntt4 p w ⟨b0, b1, b2, b3⟩
  let P := pointwiseMul4 p A B
  rcases ntt4_mod_int p w hp ⟨a0, a1, a2, a3⟩ with ⟨ha0, ha1, ha2, ha3⟩
  rcases ntt4_mod_int p w hp ⟨b0, b1, b2, b3⟩ with ⟨hb0, hb1, hb2, hb3⟩
  rcases intt4_mod_int p inv4 invW hp P with ⟨hi0, hi1, hi2, hi3⟩
  have hP0 : (P.x0 : Int) % p = (((a0 : Int) + a2 + ((a1 : Int) + a3)) *
      ((b0 : Int) + b2 + ((b1 : Int) + b3))) % p :=
    (mod_mul_congr_int p A.x0 B.x0).trans (emod_mul_cancel ha0 hb0)
  have hP1 : (P.x1 : Int) % p = (((a0 : Int) - a2 + ((a1 : Int) - a3) * w) *
      ((b0 : Int) - b2 + ((b1 : Int) - b3) * w)) % p :=
    (mod_mul_congr_int p A.x1 B.x1).trans (emod_mul_cancel ha1 hb1)
  have hP2 : (P.x2 : Int) % p = (((a0 : Int) + a2 - ((a1 : Int) + a3)) *
      ((b0 : Int) + b2 - ((b1 : Int) + b3))) % p :=
    (mod_mul_congr_int p A.x2 B.x2).trans (emod_mul_cancel ha2 hb2)
  have hP3 : (P.x3 : Int) % p = (((a0 : Int) - a2 - ((a1 : Int) - a3) * w) *
      ((b0 : Int) - b2 - ((b1 : Int) - b3) * w)) % p :=
    (mod_mul_congr_int p A.x3 B.x3).trans (emod_mul_cancel ha3 hb3)
  have he : ((P.x0 : Int) + P.x2) % p =
      (2 * (((a0 : Int) + a2) * ((b0 : Int) + b2) +
        ((a1 : Int) + a3) * ((b1 : Int) + b3))) % p := by
    rw [emod_add_cancel hP0 hP2, poly_sum_diff_add]
  have ho : ((P.x0 : Int) - P.x2) % p =
      (2 * (((a0 : Int) + a2) * ((b1 : Int) + b3) +
        ((a1 : Int) + a3) * ((b0 : Int) + b2))) % p := by
    rw [emod_sub_cancel hP0 hP2, poly_sum_diff_sub]
  have hf : ((P.x1 : Int) + P.x3) % p =
      (2 * (((a0 : Int) - a2) * ((b0 : Int) - b2) -
        ((a1 : Int) - a3) * ((b1 : Int) - b3))) % p := by
    rw [emod_add_cancel hP1 hP3, poly_w_add]
    have hneg : (2 * (((a1 : Int) - a3) * ((b1 : Int) - b3)) * ((w : Int) * w)) % p =
        (2 * (((a1 : Int) - a3) * ((b1 : Int) - b3)) * (-1 : Int)) % p :=
      emod_mul_cancel rfl hw2i
    rw [emod_add_cancel rfl hneg]
    congr 1; omega
  have hg : (((P.x1 : Int) - P.x3) * invW) % p =
      (2 * (((a0 : Int) - a2) * ((b1 : Int) - b3) +
        ((a1 : Int) - a3) * ((b0 : Int) - b2))) % p := by
    have hsub : ((P.x1 : Int) - P.x3) % p =
        (2 * (((a0 : Int) - a2) * ((b1 : Int) - b3) +
          ((a1 : Int) - a3) * ((b0 : Int) - b2)) * w) % p := by
      rw [emod_sub_cancel hP1 hP3, poly_w_sub]
    calc (((P.x1 : Int) - P.x3) * invW) % p
        = ((2 * (((a0 : Int) - a2) * ((b1 : Int) - b3) +
              ((a1 : Int) - a3) * ((b0 : Int) - b2)) * w) * invW) % p :=
            emod_mul_cancel hsub rfl
      _ = ((2 * (((a0 : Int) - a2) * ((b1 : Int) - b3) +
              ((a1 : Int) - a3) * ((b0 : Int) - b2))) * ((w : Int) * invW)) % p := by
            rw [Int.mul_assoc]
      _ = ((2 * (((a0 : Int) - a2) * ((b1 : Int) - b3) +
              ((a1 : Int) - a3) * ((b0 : Int) - b2))) * 1) % p := emod_mul_cancel rfl hwi
      _ = _ := by rw [Int.mul_one]
  have hmul4 : ∀ x : Int, ((4 * x) * (inv4 : Int)) % (p : Int) = x % (p : Int) := by
    intro x
    calc ((4 * x) * (inv4 : Int)) % p
        = (x * (4 * (inv4 : Int))) % p := by rw [Int.mul_comm 4 x, Int.mul_assoc]
      _ = (x * 1) % p := emod_mul_cancel rfl h4i
      _ = x % p := by rw [Int.mul_one]
  have hc0 : ((intt4 p inv4 invW P).x0 : Int) % p =
      ((a0 : Int) * b0 + a1 * b3 + a2 * b2 + a3 * b1) % p :=
    hi0.trans (emod_mul_cancel ((emod_add_cancel he hf).trans (by rw [conv4_combine_0])) rfl)
      |>.trans (hmul4 _)
  have hc1 : ((intt4 p inv4 invW P).x1 : Int) % p =
      ((a0 : Int) * b1 + a1 * b0 + a2 * b3 + a3 * b2) % p :=
    hi1.trans (emod_mul_cancel ((emod_add_cancel ho hg).trans (by rw [conv4_combine_1])) rfl)
      |>.trans (hmul4 _)
  have hc2 : ((intt4 p inv4 invW P).x2 : Int) % p =
      ((a0 : Int) * b2 + a1 * b1 + a2 * b0 + a3 * b3) % p :=
    hi2.trans (emod_mul_cancel ((emod_sub_cancel he hf).trans (by rw [conv4_combine_2])) rfl)
      |>.trans (hmul4 _)
  have hc3 : ((intt4 p inv4 invW P).x3 : Int) % p =
      ((a0 : Int) * b3 + a1 * b2 + a2 * b1 + a3 * b0) % p :=
    hi3.trans (emod_mul_cancel ((emod_sub_cancel ho hg).trans (by rw [conv4_combine_3])) rfl)
      |>.trans (hmul4 _)
  have m0 : (intt4 p inv4 invW P).x0 % p = (intt4 p inv4 invW P).x0 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m1 : (intt4 p inv4 invW P).x1 % p = (intt4 p inv4 invW P).x1 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m2 : (intt4 p inv4 invW P).x2 % p = (intt4 p inv4 invW P).x2 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  have m3 : (intt4 p inv4 invW P).x3 % p = (intt4 p inv4 invW P).x3 := by
    dsimp [intt4]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
  dsimp [cyclicConv4]
  apply vec4_eq_intro
  · rw [← m0]
    exact nat_mod_of_int_mod_eq p _ _ ((a0 : Int) * b0 + a1 * b3 + a2 * b2 + a3 * b1)
      (by rw [m0]; exact hc0) (mod_mod_congr_int p _)
  · rw [← m1]
    exact nat_mod_of_int_mod_eq p _ _ ((a0 : Int) * b1 + a1 * b0 + a2 * b3 + a3 * b2)
      (by rw [m1]; exact hc1) (mod_mod_congr_int p _)
  · rw [← m2]
    exact nat_mod_of_int_mod_eq p _ _ ((a0 : Int) * b2 + a1 * b1 + a2 * b0 + a3 * b3)
      (by rw [m2]; exact hc2) (mod_mod_congr_int p _)
  · rw [← m3]
    exact nat_mod_of_int_mod_eq p _ _ ((a0 : Int) * b3 + a1 * b2 + a2 * b1 + a3 * b0)
      (by rw [m3]; exact hc3) (mod_mod_congr_int p _)

/-- Single-lane modular multiplication `r0 := (r0 * t0) % p` on `MiniVM`. -/
def pointwiseMulLaneAsm (p : Nat) : List Instr :=
  [Instr.mulModReg Reg.r0 Reg.t0 p]

/--
Full 4-point NTT convolution pipeline on `MiniVM` for a single Fermat-tower prime
channel `cfg`: forward `ntt4AsmFermat` on `a` and `b`, lane-wise `pointwiseMulLaneAsm`,
and inverse `intt4AsmFermat`.
-/
def crtNtt4ChannelConvAsm (cfg : FermatNtt4Spec) (a b : Vec4) : Vec4 :=
  let sA := runProgram { r0 := a.x0, r1 := a.x1, r2 := a.x2, r3 := a.x3 }
    (ntt4AsmFermat cfg.p cfg.omega4)
  let sB := runProgram { r0 := b.x0, r1 := b.x1, r2 := b.x2, r3 := b.x3 }
    (ntt4AsmFermat cfg.p cfg.omega4)
  let p0 := (runProgram { r0 := sA.r0, t0 := sB.r0 } (pointwiseMulLaneAsm cfg.p)).r0
  let p1 := (runProgram { r0 := sA.r1, t0 := sB.r1 } (pointwiseMulLaneAsm cfg.p)).r0
  let p2 := (runProgram { r0 := sA.r2, t0 := sB.r2 } (pointwiseMulLaneAsm cfg.p)).r0
  let p3 := (runProgram { r0 := sA.r3, t0 := sB.r3 } (pointwiseMulLaneAsm cfg.p)).r0
  let sOut := runProgram { r0 := p0, r1 := p1, r2 := p2, r3 := p3 }
    (intt4AsmFermat cfg.p cfg.invFour cfg.invOmega4)
  ⟨sOut.r0, sOut.r1, sOut.r2, sOut.r3⟩

/-- Exact unreduced 4-point cyclic integer convolution `(a * b) mod (x^4 - 1)`. -/
def exactCyclicConv4Vec (a b : Vec4) : Vec4 :=
  ⟨a.x0 * b.x0 + a.x1 * b.x3 + a.x2 * b.x2 + a.x3 * b.x1,
   a.x0 * b.x1 + a.x1 * b.x0 + a.x2 * b.x3 + a.x3 * b.x2,
   a.x0 * b.x2 + a.x1 * b.x1 + a.x2 * b.x0 + a.x3 * b.x3,
   a.x0 * b.x3 + a.x1 * b.x2 + a.x2 * b.x1 + a.x3 * b.x0⟩

/--
4-channel Fermat-tower CRT-NTT cyclic convolution assembly pipeline on `MiniVM`:
runs `crtNtt4ChannelConvAsm` across `{5, 17, 257, 65537}` and reconstructs each
integer lane `< M_4` using compiled `garnerReconstruct4Asm`.
-/
def crtNtt4ConvAsmReconstruct (a b : Vec4) : Vec4 :=
  let c5 := crtNtt4ChannelConvAsm fermatNtt4Spec5 a b
  let c17 := crtNtt4ChannelConvAsm fermatNtt4Spec17 a b
  let c257 := crtNtt4ChannelConvAsm fermatNtt4Spec257 a b
  let c65537 := crtNtt4ChannelConvAsm fermatNtt4Spec65537 a b
  ⟨(runProgram { r0 := c5.x0, r1 := c17.x0, r2 := c257.x0, r3 := c65537.x0 }
      garnerReconstruct4Asm).r0,
   (runProgram { r0 := c5.x1, r1 := c17.x1, r2 := c257.x1, r3 := c65537.x1 }
      garnerReconstruct4Asm).r0,
   (runProgram { r0 := c5.x2, r1 := c17.x2, r2 := c257.x2, r3 := c65537.x2 }
      garnerReconstruct4Asm).r0,
   (runProgram { r0 := c5.x3, r1 := c17.x3, r2 := c257.x3, r3 := c65537.x3 }
      garnerReconstruct4Asm).r0⟩

/--
Single-channel MiniVM 4-point NTT convolution soundness for every valid
Fermat-tower configuration `cfg`.
-/
theorem crtNtt4ChannelConvAsm_sound (cfg : FermatNtt4Spec) (hcfg : cfg.Valid) (a b : Vec4) :
    crtNtt4ChannelConvAsm cfg a b = cyclicConv4 cfg.p a b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases hcfg with ⟨hp1, hw2, hwinv, h4inv⟩
  have hp0 : 0 < cfg.p := Nat.lt_trans Nat.zero_lt_one hp1
  have hwinv' : (cfg.omega4 * cfg.invOmega4) % cfg.p = 1 % cfg.p := by
    rw [hwinv, Nat.mod_eq_of_lt hp1]
  have h4inv' : (4 * cfg.invFour) % cfg.p = 1 % cfg.p := by
    rw [h4inv, Nat.mod_eq_of_lt hp1]
  dsimp [crtNtt4ChannelConvAsm]
  have hA := ntt4AsmFermat_sound cfg.p cfg.omega4
    { r0 := a0, r1 := a1, r2 := a2, r3 := a3 } a0 a1 a2 a3 rfl rfl rfl rfl
  have hB := ntt4AsmFermat_sound cfg.p cfg.omega4
    { r0 := b0, r1 := b1, r2 := b2, r3 := b3 } b0 b1 b2 b3 rfl rfl rfl rfl
  dsimp [State.r0, State.r1, State.r2, State.r3] at hA hB
  let sA := runProgram { r0 := a0, r1 := a1, r2 := a2, r3 := a3 }
    (ntt4AsmFermat cfg.p cfg.omega4)
  let sB := runProgram { r0 := b0, r1 := b1, r2 := b2, r3 := b3 }
    (ntt4AsmFermat cfg.p cfg.omega4)
  have hPeq :
      (⟨(runProgram { r0 := sA.r0, t0 := sB.r0 } (pointwiseMulLaneAsm cfg.p)).r0,
        (runProgram { r0 := sA.r1, t0 := sB.r1 } (pointwiseMulLaneAsm cfg.p)).r0,
        (runProgram { r0 := sA.r2, t0 := sB.r2 } (pointwiseMulLaneAsm cfg.p)).r0,
        (runProgram { r0 := sA.r3, t0 := sB.r3 } (pointwiseMulLaneAsm cfg.p)).r0⟩ : Vec4) =
      pointwiseMul4 cfg.p (ntt4 cfg.p cfg.omega4 ⟨a0, a1, a2, a3⟩)
        (ntt4 cfg.p cfg.omega4 ⟨b0, b1, b2, b3⟩) := by
    have hA0 : sA.r0 = (ntt4 cfg.p cfg.omega4 ⟨a0, a1, a2, a3⟩).x0 := congrArg Vec4.x0 hA
    have hA1 : sA.r1 = (ntt4 cfg.p cfg.omega4 ⟨a0, a1, a2, a3⟩).x1 := congrArg Vec4.x1 hA
    have hA2 : sA.r2 = (ntt4 cfg.p cfg.omega4 ⟨a0, a1, a2, a3⟩).x2 := congrArg Vec4.x2 hA
    have hA3 : sA.r3 = (ntt4 cfg.p cfg.omega4 ⟨a0, a1, a2, a3⟩).x3 := congrArg Vec4.x3 hA
    have hB0 : sB.r0 = (ntt4 cfg.p cfg.omega4 ⟨b0, b1, b2, b3⟩).x0 := congrArg Vec4.x0 hB
    have hB1 : sB.r1 = (ntt4 cfg.p cfg.omega4 ⟨b0, b1, b2, b3⟩).x1 := congrArg Vec4.x1 hB
    have hB2 : sB.r2 = (ntt4 cfg.p cfg.omega4 ⟨b0, b1, b2, b3⟩).x2 := congrArg Vec4.x2 hB
    have hB3 : sB.r3 = (ntt4 cfg.p cfg.omega4 ⟨b0, b1, b2, b3⟩).x3 := congrArg Vec4.x3 hB
    dsimp [pointwiseMulLaneAsm, runProgram, step, State.get, State.set, State.setPc,
      pointwiseMul4]
    rw [hA0, hA1, hA2, hA3, hB0, hB1, hB2, hB3]
  let p0 := (runProgram { r0 := sA.r0, t0 := sB.r0 } (pointwiseMulLaneAsm cfg.p)).r0
  let p1 := (runProgram { r0 := sA.r1, t0 := sB.r1 } (pointwiseMulLaneAsm cfg.p)).r0
  let p2 := (runProgram { r0 := sA.r2, t0 := sB.r2 } (pointwiseMulLaneAsm cfg.p)).r0
  let p3 := (runProgram { r0 := sA.r3, t0 := sB.r3 } (pointwiseMulLaneAsm cfg.p)).r0
  have hI := intt4AsmFermat_sound cfg.p cfg.invFour cfg.invOmega4
    { r0 := p0, r1 := p1, r2 := p2, r3 := p3 } p0 p1 p2 p3 rfl rfl rfl rfl
  rw [hI, hPeq]
  exact cyclic_conv4_ntt_generic cfg.p cfg.omega4 cfg.invFour cfg.invOmega4
    hp0 hw2 hwinv' h4inv' ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩

private theorem conv4_lane_lt_fermatTowerMod4 (u0 u1 u2 u3 v0 v1 v2 v3 : Nat)
    (hu0 : u0 ≤ 18918) (hu1 : u1 ≤ 18918) (hu2 : u2 ≤ 18918) (hu3 : u3 ≤ 18918)
    (hv0 : v0 ≤ 18918) (hv1 : v1 ≤ 18918) (hv2 : v2 ≤ 18918) (hv3 : v3 ≤ 18918) :
    u0 * v0 + u1 * v3 + u2 * v2 + u3 * v1 < CrtNtt.fermatTowerMod4 := by
  have p0 : u0 * v0 ≤ 18918 * 18918 := Nat.mul_le_mul hu0 hv0
  have p1 : u1 * v3 ≤ 18918 * 18918 := Nat.mul_le_mul hu1 hv3
  have p2 : u2 * v2 ≤ 18918 * 18918 := Nat.mul_le_mul hu2 hv2
  have p3 : u3 * v1 ≤ 18918 * 18918 := Nat.mul_le_mul hu3 hv1
  have hbound : 4 * (18918 * 18918) < CrtNtt.fermatTowerMod4 :=
    CrtNtt.fermat_tower_conv_bound_certs.1.2.1
  omega

/--
End-to-end 4-point CRT-NTT cyclic convolution assembly soundness on `MiniVM`:
under the sharp `CrtNttUniversal` wrap-around bound `B ≤ 18,918`, executing the
4 Fermat-tower channels (`5, 17, 257, 65537`) on `MiniVM` followed by compiled
`garnerReconstruct4Asm` recovers all 4 exact integer convolution coefficients
`< M_4 = 1,431,655,765` with ZERO wrap-around error.
-/
theorem crtNtt4ConvAsm_sound (a b : Vec4)
    (ha0 : a.x0 ≤ 18918) (ha1 : a.x1 ≤ 18918) (ha2 : a.x2 ≤ 18918) (ha3 : a.x3 ≤ 18918)
    (hb0 : b.x0 ≤ 18918) (hb1 : b.x1 ≤ 18918) (hb2 : b.x2 ≤ 18918) (hb3 : b.x3 ≤ 18918) :
    let c := crtNtt4ConvAsmReconstruct a b
    c = exactCyclicConv4Vec a b ∧
    c.x0 < CrtNtt.fermatTowerMod4 ∧ c.x1 < CrtNtt.fermatTowerMod4 ∧
    c.x2 < CrtNtt.fermatTowerMod4 ∧ c.x3 < CrtNtt.fermatTowerMod4 := by
  have h5 := crtNtt4ChannelConvAsm_sound fermatNtt4Spec5 fermatNtt4Spec5_valid a b
  have h17 := crtNtt4ChannelConvAsm_sound fermatNtt4Spec17 fermatNtt4Spec17_valid a b
  have h257 := crtNtt4ChannelConvAsm_sound fermatNtt4Spec257 fermatNtt4Spec257_valid a b
  have h65537 := crtNtt4ChannelConvAsm_sound fermatNtt4Spec65537 fermatNtt4Spec65537_valid a b
  have hl0 : (exactCyclicConv4Vec a b).x0 < CrtNtt.fermatTowerMod4 :=
    conv4_lane_lt_fermatTowerMod4 a.x0 a.x1 a.x2 a.x3 b.x0 b.x1 b.x2 b.x3
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have hl1 : (exactCyclicConv4Vec a b).x1 < CrtNtt.fermatTowerMod4 :=
    conv4_lane_lt_fermatTowerMod4 a.x0 a.x1 a.x2 a.x3 b.x1 b.x2 b.x3 b.x0
      ha0 ha1 ha2 ha3 hb1 hb2 hb3 hb0
  have hl2 : (exactCyclicConv4Vec a b).x2 < CrtNtt.fermatTowerMod4 :=
    conv4_lane_lt_fermatTowerMod4 a.x0 a.x1 a.x2 a.x3 b.x2 b.x3 b.x0 b.x1
      ha0 ha1 ha2 ha3 hb2 hb3 hb0 hb1
  have hl3 : (exactCyclicConv4Vec a b).x3 < CrtNtt.fermatTowerMod4 :=
    conv4_lane_lt_fermatTowerMod4 a.x0 a.x1 a.x2 a.x3 b.x3 b.x0 b.x1 b.x2
      ha0 ha1 ha2 ha3 hb3 hb0 hb1 hb2
  have hg0 : (runProgram
      { r0 := (crtNtt4ChannelConvAsm fermatNtt4Spec5 a b).x0,
        r1 := (crtNtt4ChannelConvAsm fermatNtt4Spec17 a b).x0,
        r2 := (crtNtt4ChannelConvAsm fermatNtt4Spec257 a b).x0,
        r3 := (crtNtt4ChannelConvAsm fermatNtt4Spec65537 a b).x0 }
      garnerReconstruct4Asm).r0 = (exactCyclicConv4Vec a b).x0 := by
    apply garnerReconstruct4Asm_sound _ _ hl0
    · exact congrArg Vec4.x0 h5
    · exact congrArg Vec4.x0 h17
    · exact congrArg Vec4.x0 h257
    · exact congrArg Vec4.x0 h65537
  have hg1 : (runProgram
      { r0 := (crtNtt4ChannelConvAsm fermatNtt4Spec5 a b).x1,
        r1 := (crtNtt4ChannelConvAsm fermatNtt4Spec17 a b).x1,
        r2 := (crtNtt4ChannelConvAsm fermatNtt4Spec257 a b).x1,
        r3 := (crtNtt4ChannelConvAsm fermatNtt4Spec65537 a b).x1 }
      garnerReconstruct4Asm).r0 = (exactCyclicConv4Vec a b).x1 := by
    apply garnerReconstruct4Asm_sound _ _ hl1
    · exact congrArg Vec4.x1 h5
    · exact congrArg Vec4.x1 h17
    · exact congrArg Vec4.x1 h257
    · exact congrArg Vec4.x1 h65537
  have hg2 : (runProgram
      { r0 := (crtNtt4ChannelConvAsm fermatNtt4Spec5 a b).x2,
        r1 := (crtNtt4ChannelConvAsm fermatNtt4Spec17 a b).x2,
        r2 := (crtNtt4ChannelConvAsm fermatNtt4Spec257 a b).x2,
        r3 := (crtNtt4ChannelConvAsm fermatNtt4Spec65537 a b).x2 }
      garnerReconstruct4Asm).r0 = (exactCyclicConv4Vec a b).x2 := by
    apply garnerReconstruct4Asm_sound _ _ hl2
    · exact congrArg Vec4.x2 h5
    · exact congrArg Vec4.x2 h17
    · exact congrArg Vec4.x2 h257
    · exact congrArg Vec4.x2 h65537
  have hg3 : (runProgram
      { r0 := (crtNtt4ChannelConvAsm fermatNtt4Spec5 a b).x3,
        r1 := (crtNtt4ChannelConvAsm fermatNtt4Spec17 a b).x3,
        r2 := (crtNtt4ChannelConvAsm fermatNtt4Spec257 a b).x3,
        r3 := (crtNtt4ChannelConvAsm fermatNtt4Spec65537 a b).x3 }
      garnerReconstruct4Asm).r0 = (exactCyclicConv4Vec a b).x3 := by
    apply garnerReconstruct4Asm_sound _ _ hl3
    · exact congrArg Vec4.x3 h5
    · exact congrArg Vec4.x3 h17
    · exact congrArg Vec4.x3 h257
    · exact congrArg Vec4.x3 h65537
  have hvec : crtNtt4ConvAsmReconstruct a b = exactCyclicConv4Vec a b := by
    dsimp [crtNtt4ConvAsmReconstruct]
    exact vec4_eq_intro _ _ hg0 hg1 hg2 hg3
  refine ⟨hvec, ?_, ?_, ?_, ?_⟩
  · rw [hvec]; exact hl0
  · rw [hvec]; exact hl1
  · rw [hvec]; exact hl2
  · rw [hvec]; exact hl3

-- =============================================================================
-- Part 5: Symbolic 8-Point Fermat-Tower NTT/INTT Assembly over {17, 257, 65537}
--         (Issue #79)
-- =============================================================================

/-- 8-point radix-2 DIT Stage 1: 4 x 2-point butterflies on bit-reversed pairs. -/
def dit8Stage1Asm (p : Nat) : List Instr :=
  butterfly2Asm p Reg.r0 Reg.r4 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r2 Reg.r6 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r1 Reg.r5 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r3 Reg.r7 Reg.t0 Reg.t1

/-- 8-point radix-2 DIT Stage 2: 2 x 4-point butterflies with twiddles `(1, w2)`. -/
def dit8Stage2Asm (p w2 : Nat) : List Instr :=
  butterfly2Asm p Reg.r0 Reg.r2 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r6 Reg.t0 p] ++
  butterfly2Asm p Reg.r4 Reg.r6 Reg.t0 Reg.t1 ++
  butterfly2Asm p Reg.r1 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r7 Reg.t0 p] ++
  butterfly2Asm p Reg.r5 Reg.r7 Reg.t0 Reg.t1

/-- 8-point radix-2 DIT Stage 3: 8-point butterfly with twiddles `(1, w1, w2, w3)`. -/
def dit8Stage3Asm (p w1 w2 w3 : Nat) : List Instr :=
  butterfly2Asm p Reg.r0 Reg.r1 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w1, Instr.mulModReg Reg.r5 Reg.t0 p] ++
  butterfly2Asm p Reg.r4 Reg.r5 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r3 Reg.t0 p] ++
  butterfly2Asm p Reg.r2 Reg.r3 Reg.t0 Reg.t1 ++
  [Instr.movImm Reg.t0 w3, Instr.mulModReg Reg.r7 Reg.t0 p] ++
  butterfly2Asm p Reg.r6 Reg.r7 Reg.t0 Reg.t1

/-- 8-point DIT final bit-order lane permutation `(r1 <-> r4, r3 <-> r6)`. -/
def dit8PermuteAsm : List Instr :=
  [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r4, Instr.movReg Reg.r4 Reg.t0,
   Instr.movReg Reg.t0 Reg.r3, Instr.movReg Reg.r3 Reg.r6, Instr.movReg Reg.r6 Reg.t0]

/--
Parametric 8-point radix-2 DIT butterfly skeleton modulo `p` with twiddle factors
`(w1, w2, w3)` over lane registers `(r0..r7)` and scratch `(t0, t1)`.
-/
def dit8Asm (p w1 w2 w3 : Nat) : List Instr :=
  dit8Stage1Asm p ++ dit8Stage2Asm p w2 ++ dit8Stage3Asm p w1 w2 w3 ++ dit8PermuteAsm

/-- Parametric 8-point forward NTT assembly program over `(r0..r7)`. -/
def ntt8AsmFermat (p w1 w2 w3 : Nat) : List Instr :=
  dit8Asm p w1 w2 w3

/-- Parametric 8-point inverse NTT assembly program over `(r0..r7)`. -/
def intt8AsmFermat (p inv8 iw1 iw2 iw3 : Nat) : List Instr :=
  dit8Asm p iw1 iw2 iw3 ++ [
    Instr.movImm Reg.t0 inv8,
    Instr.mulModReg Reg.r0 Reg.t0 p,
    Instr.mulModReg Reg.r1 Reg.t0 p,
    Instr.mulModReg Reg.r2 Reg.t0 p,
    Instr.mulModReg Reg.r3 Reg.t0 p,
    Instr.mulModReg Reg.r4 Reg.t0 p,
    Instr.mulModReg Reg.r5 Reg.t0 p,
    Instr.mulModReg Reg.r6 Reg.t0 p,
    Instr.mulModReg Reg.r7 Reg.t0 p
  ]

private theorem runProgram_twiddleModReg (p : Nat) (dst : Reg) (_hd0 : dst ≠ Reg.t0)
    (w : Nat) (s : State) :
    let s' := runProgram s [Instr.movImm Reg.t0 w, Instr.mulModReg dst Reg.t0 p]
    s'.get dst = (s.get dst * w) % p ∧
    ∀ r, r ≠ dst → r ≠ Reg.t0 → s'.get r = s.get r := by
  dsimp [runProgram, step]
  constructor
  · simp only [get_set_pc, get_set_same, get_set_other _ _ _ _ _hd0.symm]
  · intro r hrd hrt
    simp only [get_set_pc, get_set_other _ _ _ _ (Ne.symm hrd),
      get_set_other _ _ _ _ (Ne.symm hrt)]

private theorem runProgram_swapRegs (rA rB : Reg)
    (hAB : rA ≠ rB) (hAt : rA ≠ Reg.t0) (hBt : rB ≠ Reg.t0) (s : State) :
    let s' := runProgram s [Instr.movReg Reg.t0 rA, Instr.movReg rA rB, Instr.movReg rB Reg.t0]
    s'.get rA = s.get rB ∧
    s'.get rB = s.get rA ∧
    ∀ r, r ≠ rA → r ≠ rB → r ≠ Reg.t0 → s'.get r = s.get r := by
  dsimp [runProgram, step]
  refine ⟨?_, ?_, ?_⟩
  · simp only [get_set_pc, get_set_same,
      get_set_other _ _ _ _ hAB.symm, get_set_other _ _ _ _ hBt.symm]
  · simp only [get_set_pc, get_set_same,
      get_set_other _ _ _ _ hAt]
  · intro r hrA hrB hrt
    simp only [get_set_pc,
      get_set_other _ _ _ _ (Ne.symm hrA),
      get_set_other _ _ _ _ (Ne.symm hrB),
      get_set_other _ _ _ _ (Ne.symm hrt)]

private theorem runProgram_dit8Stage1Asm (p : Nat) (s : State) :
    let s' := runProgram s (dit8Stage1Asm p)
    s'.r0 = (CrtNtt.butterfly2 p s.r0 s.r4).1 ∧
    s'.r4 = (CrtNtt.butterfly2 p s.r0 s.r4).2 ∧
    s'.r2 = (CrtNtt.butterfly2 p s.r2 s.r6).1 ∧
    s'.r6 = (CrtNtt.butterfly2 p s.r2 s.r6).2 ∧
    s'.r1 = (CrtNtt.butterfly2 p s.r1 s.r5).1 ∧
    s'.r5 = (CrtNtt.butterfly2 p s.r1 s.r5).2 ∧
    s'.r3 = (CrtNtt.butterfly2 p s.r3 s.r7).1 ∧
    s'.r7 = (CrtNtt.butterfly2 p s.r3 s.r7).2 := by
  dsimp only [dit8Stage1Asm]
  simp only [List.append_assoc, runProgram_append]
  have hs1 := runProgram_butterfly2Asm p s Reg.r0 Reg.r4 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs1 with ⟨h1_0, h1_4, h1_p⟩
  generalize runProgram s (butterfly2Asm p Reg.r0 Reg.r4 Reg.t0 Reg.t1) = s1 at *
  have hs2 := runProgram_butterfly2Asm p s1 Reg.r2 Reg.r6 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs2 with ⟨h2_2, h2_6, h2_p⟩
  generalize runProgram s1 (butterfly2Asm p Reg.r2 Reg.r6 Reg.t0 Reg.t1) = s2 at *
  have hs3 := runProgram_butterfly2Asm p s2 Reg.r1 Reg.r5 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs3 with ⟨h3_1, h3_5, h3_p⟩
  generalize runProgram s2 (butterfly2Asm p Reg.r1 Reg.r5 Reg.t0 Reg.t1) = s3 at *
  have hs4 := runProgram_butterfly2Asm p s3 Reg.r3 Reg.r7 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs4 with ⟨h4_3, h4_7, h4_p⟩
  generalize runProgram s3 (butterfly2Asm p Reg.r3 Reg.r7 Reg.t0 Reg.t1) = s4 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s4.get Reg.r0 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide), h1_0]
    rfl
  · change s4.get Reg.r4 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide), h1_4]
    rfl
  · change s4.get Reg.r2 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide), h2_2,
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s4.get Reg.r6 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide), h2_6,
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s4.get Reg.r1 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide), h3_1,
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s4.get Reg.r5 = _
    rw [h4_p _ (by decide) (by decide) (by decide) (by decide), h3_5,
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s4.get Reg.r3 = _
    rw [h4_3,
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s4.get Reg.r7 = _
    rw [h4_7,
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h3_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h2_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide),
      h1_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl

private theorem runProgram_dit8Stage2Asm (p w2 : Nat) (s4 : State) :
    let s' := runProgram s4 (dit8Stage2Asm p w2)
    s'.r0 = (CrtNtt.butterfly2 p s4.r0 s4.r2).1 ∧
    s'.r2 = (CrtNtt.butterfly2 p s4.r0 s4.r2).2 ∧
    s'.r4 = (CrtNtt.butterfly2 p s4.r4 (((s4.r6) * w2) % p)).1 ∧
    s'.r6 = (CrtNtt.butterfly2 p s4.r4 (((s4.r6) * w2) % p)).2 ∧
    s'.r1 = (CrtNtt.butterfly2 p s4.r1 s4.r3).1 ∧
    s'.r3 = (CrtNtt.butterfly2 p s4.r1 s4.r3).2 ∧
    s'.r5 = (CrtNtt.butterfly2 p s4.r5 (((s4.r7) * w2) % p)).1 ∧
    s'.r7 = (CrtNtt.butterfly2 p s4.r5 (((s4.r7) * w2) % p)).2 := by
  dsimp only [dit8Stage2Asm]
  simp only [List.append_assoc, runProgram_append]
  have hs5 := runProgram_butterfly2Asm p s4 Reg.r0 Reg.r2 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs5 with ⟨h5_0, h5_2, h5_p⟩
  generalize runProgram s4 (butterfly2Asm p Reg.r0 Reg.r2 Reg.t0 Reg.t1) = s5 at *
  have ht6 := runProgram_twiddleModReg p Reg.r6 (by decide) w2 s5
  rcases ht6 with ⟨ht6_6, ht6_p⟩
  generalize runProgram s5 [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r6 Reg.t0 p] = s6 at *
  have hs7 := runProgram_butterfly2Asm p s6 Reg.r4 Reg.r6 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs7 with ⟨h7_4, h7_6, h7_p⟩
  generalize runProgram s6 (butterfly2Asm p Reg.r4 Reg.r6 Reg.t0 Reg.t1) = s7 at *
  have hs8 := runProgram_butterfly2Asm p s7 Reg.r1 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs8 with ⟨h8_1, h8_3, h8_p⟩
  generalize runProgram s7 (butterfly2Asm p Reg.r1 Reg.r3 Reg.t0 Reg.t1) = s8 at *
  have ht9 := runProgram_twiddleModReg p Reg.r7 (by decide) w2 s8
  rcases ht9 with ⟨ht9_7, ht9_p⟩
  generalize runProgram s8 [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r7 Reg.t0 p] = s9 at *
  have hs10 := runProgram_butterfly2Asm p s9 Reg.r5 Reg.r7 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs10 with ⟨h10_5, h10_7, h10_p⟩
  generalize runProgram s9 (butterfly2Asm p Reg.r5 Reg.r7 Reg.t0 Reg.t1) = s10 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s10.get Reg.r0 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), h5_0]
    rfl
  · change s10.get Reg.r2 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), h5_2]
    rfl
  · change s10.get Reg.r4 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide), h7_4,
      ht6_p _ (by decide) (by decide), ht6_6,
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s10.get Reg.r6 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide), h7_6,
      ht6_p _ (by decide) (by decide), ht6_6,
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s10.get Reg.r1 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide), h8_1,
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), ht6_p _ (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s10.get Reg.r3 = _
    rw [h10_p _ (by decide) (by decide) (by decide) (by decide),
      ht9_p _ (by decide) (by decide), h8_3,
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), ht6_p _ (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s10.get Reg.r5 = _
    rw [h10_5, ht9_p _ (by decide) (by decide), ht9_7,
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), ht6_p _ (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s10.get Reg.r7 = _
    rw [h10_7, ht9_p _ (by decide) (by decide), ht9_7,
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h8_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      h7_p _ (by decide) (by decide) (by decide) (by decide),
      ht6_p _ (by decide) (by decide), ht6_p _ (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide),
      h5_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl

private theorem runProgram_dit8Stage3Asm (p w1 w2 w3 : Nat) (s10 : State) :
    let s' := runProgram s10 (dit8Stage3Asm p w1 w2 w3)
    s'.r0 = (CrtNtt.butterfly2 p s10.r0 s10.r1).1 ∧
    s'.r1 = (CrtNtt.butterfly2 p s10.r0 s10.r1).2 ∧
    s'.r4 = (CrtNtt.butterfly2 p s10.r4 (((s10.r5) * w1) % p)).1 ∧
    s'.r5 = (CrtNtt.butterfly2 p s10.r4 (((s10.r5) * w1) % p)).2 ∧
    s'.r2 = (CrtNtt.butterfly2 p s10.r2 (((s10.r3) * w2) % p)).1 ∧
    s'.r3 = (CrtNtt.butterfly2 p s10.r2 (((s10.r3) * w2) % p)).2 ∧
    s'.r6 = (CrtNtt.butterfly2 p s10.r6 (((s10.r7) * w3) % p)).1 ∧
    s'.r7 = (CrtNtt.butterfly2 p s10.r6 (((s10.r7) * w3) % p)).2 := by
  dsimp only [dit8Stage3Asm]
  simp only [List.append_assoc, runProgram_append]
  have hs11 := runProgram_butterfly2Asm p s10 Reg.r0 Reg.r1 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs11 with ⟨h11_0, h11_1, h11_p⟩
  generalize runProgram s10 (butterfly2Asm p Reg.r0 Reg.r1 Reg.t0 Reg.t1) = s11 at *
  have ht12 := runProgram_twiddleModReg p Reg.r5 (by decide) w1 s11
  rcases ht12 with ⟨ht12_5, ht12_p⟩
  generalize runProgram s11 [Instr.movImm Reg.t0 w1, Instr.mulModReg Reg.r5 Reg.t0 p] = s12 at *
  have hs13 := runProgram_butterfly2Asm p s12 Reg.r4 Reg.r5 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs13 with ⟨h13_4, h13_5, h13_p⟩
  generalize runProgram s12 (butterfly2Asm p Reg.r4 Reg.r5 Reg.t0 Reg.t1) = s13 at *
  have ht14 := runProgram_twiddleModReg p Reg.r3 (by decide) w2 s13
  rcases ht14 with ⟨ht14_3, ht14_p⟩
  generalize runProgram s13 [Instr.movImm Reg.t0 w2, Instr.mulModReg Reg.r3 Reg.t0 p] = s14 at *
  have hs15 := runProgram_butterfly2Asm p s14 Reg.r2 Reg.r3 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs15 with ⟨h15_2, h15_3, h15_p⟩
  generalize runProgram s14 (butterfly2Asm p Reg.r2 Reg.r3 Reg.t0 Reg.t1) = s15 at *
  have ht16 := runProgram_twiddleModReg p Reg.r7 (by decide) w3 s15
  rcases ht16 with ⟨ht16_7, ht16_p⟩
  generalize runProgram s15 [Instr.movImm Reg.t0 w3, Instr.mulModReg Reg.r7 Reg.t0 p] = s16 at *
  have hs17 := runProgram_butterfly2Asm p s16 Reg.r6 Reg.r7 Reg.t0 Reg.t1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hs17 with ⟨h17_6, h17_7, h17_p⟩
  generalize runProgram s16 (butterfly2Asm p Reg.r6 Reg.r7 Reg.t0 Reg.t1) = s17 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s17.get Reg.r0 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), h11_0]
    rfl
  · change s17.get Reg.r1 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), h11_1]
    rfl
  · change s17.get Reg.r4 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide), h13_4,
      ht12_p _ (by decide) (by decide), ht12_5,
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s17.get Reg.r5 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide), h13_5,
      ht12_p _ (by decide) (by decide), ht12_5,
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s17.get Reg.r2 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide), h15_2,
      ht14_p _ (by decide) (by decide), ht14_3,
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), ht12_p _ (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s17.get Reg.r3 = _
    rw [h17_p _ (by decide) (by decide) (by decide) (by decide),
      ht16_p _ (by decide) (by decide), h15_3,
      ht14_p _ (by decide) (by decide), ht14_3,
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), ht12_p _ (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s17.get Reg.r6 = _
    rw [h17_6, ht16_p _ (by decide) (by decide), ht16_7,
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide), ht14_p _ (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), ht12_p _ (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl
  · change s17.get Reg.r7 = _
    rw [h17_7, ht16_p _ (by decide) (by decide), ht16_7,
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      h15_p _ (by decide) (by decide) (by decide) (by decide),
      ht14_p _ (by decide) (by decide), ht14_p _ (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      h13_p _ (by decide) (by decide) (by decide) (by decide),
      ht12_p _ (by decide) (by decide), ht12_p _ (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide),
      h11_p _ (by decide) (by decide) (by decide) (by decide)]
    rfl

private theorem runProgram_dit8PermuteAsm (s17 : State) :
    let s' := runProgram s17 dit8PermuteAsm
    s'.r0 = s17.r0 ∧ s'.r1 = s17.r4 ∧ s'.r2 = s17.r2 ∧ s'.r3 = s17.r6 ∧
    s'.r4 = s17.r1 ∧ s'.r5 = s17.r5 ∧ s'.r6 = s17.r3 ∧ s'.r7 = s17.r7 := by
  dsimp only [dit8PermuteAsm]
  have hcons :
      [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r4, Instr.movReg Reg.r4 Reg.t0,
       Instr.movReg Reg.t0 Reg.r3, Instr.movReg Reg.r3 Reg.r6, Instr.movReg Reg.r6 Reg.t0] =
      [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r4, Instr.movReg Reg.r4 Reg.t0] ++
      [Instr.movReg Reg.t0 Reg.r3, Instr.movReg Reg.r3 Reg.r6, Instr.movReg Reg.r6 Reg.t0] := rfl
  rw [hcons, runProgram_append]
  have hs18 := runProgram_swapRegs Reg.r1 Reg.r4 (by decide) (by decide) (by decide) s17
  rcases hs18 with ⟨h18_1, h18_4, h18_p⟩
  generalize runProgram s17
    [Instr.movReg Reg.t0 Reg.r1, Instr.movReg Reg.r1 Reg.r4, Instr.movReg Reg.r4 Reg.t0] = s18 at *
  have hs19 := runProgram_swapRegs Reg.r3 Reg.r6 (by decide) (by decide) (by decide) s18
  rcases hs19 with ⟨h19_3, h19_6, h19_p⟩
  generalize runProgram s18
    [Instr.movReg Reg.t0 Reg.r3, Instr.movReg Reg.r3 Reg.r6, Instr.movReg Reg.r6 Reg.t0] = s19 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s19.get Reg.r0 = s17.get Reg.r0
    rw [h19_p _ (by decide) (by decide) (by decide), h18_p _ (by decide) (by decide) (by decide)]
  · change s19.get Reg.r1 = s17.get Reg.r4
    rw [h19_p _ (by decide) (by decide) (by decide), h18_1]
  · change s19.get Reg.r2 = s17.get Reg.r2
    rw [h19_p _ (by decide) (by decide) (by decide), h18_p _ (by decide) (by decide) (by decide)]
  · change s19.get Reg.r3 = s17.get Reg.r6
    rw [h19_3, h18_p _ (by decide) (by decide) (by decide)]
  · change s19.get Reg.r4 = s17.get Reg.r1
    rw [h19_p _ (by decide) (by decide) (by decide), h18_4]
  · change s19.get Reg.r5 = s17.get Reg.r5
    rw [h19_p _ (by decide) (by decide) (by decide), h18_p _ (by decide) (by decide) (by decide)]
  · change s19.get Reg.r6 = s17.get Reg.r3
    rw [h19_6, h18_p _ (by decide) (by decide) (by decide)]
  · change s19.get Reg.r7 = s17.get Reg.r7
    rw [h19_p _ (by decide) (by decide) (by decide), h18_p _ (by decide) (by decide) (by decide)]

private theorem runProgram_dit8Asm (p w1 w2 w3 : Nat) (s : State) :
    let v : CrtNtt.Vec8 := ⟨s.r0, s.r1, s.r2, s.r3, s.r4, s.r5, s.r6, s.r7⟩
    let s' := runProgram s (dit8Asm p w1 w2 w3)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3, s'.r4, s'.r5, s'.r6, s'.r7⟩ : CrtNtt.Vec8) =
      CrtNtt.ntt8WithRoots p w1 w2 w3 v := by
  dsimp only [dit8Asm, CrtNtt.ntt8WithRoots]
  simp only [List.append_assoc, runProgram_append]
  have h1 := runProgram_dit8Stage1Asm p s
  rcases h1 with ⟨h1_0, h1_4, h1_2, h1_6, h1_1, h1_5, h1_3, h1_7⟩
  generalize runProgram s (dit8Stage1Asm p) = s4 at *
  have h2 := runProgram_dit8Stage2Asm p w2 s4
  rcases h2 with ⟨h2_0, h2_2, h2_4, h2_6, h2_1, h2_3, h2_5, h2_7⟩
  generalize runProgram s4 (dit8Stage2Asm p w2) = s10 at *
  have h3 := runProgram_dit8Stage3Asm p w1 w2 w3 s10
  rcases h3 with ⟨h3_0, h3_1, h3_4, h3_5, h3_2, h3_3, h3_6, h3_7⟩
  generalize runProgram s10 (dit8Stage3Asm p w1 w2 w3) = s17 at *
  have h4 := runProgram_dit8PermuteAsm s17
  rcases h4 with ⟨h4_0, h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7⟩
  generalize runProgram s17 dit8PermuteAsm = s19 at *
  rw [h4_0, h4_1, h4_2, h4_3, h4_4, h4_5, h4_6, h4_7]
  rw [h3_0, h3_1, h3_4, h3_5, h3_2, h3_3, h3_6, h3_7]
  rw [h2_0, h2_2, h2_4, h2_6, h2_1, h2_3, h2_5, h2_7]
  rw [h1_0, h1_4, h1_2, h1_6, h1_1, h1_5, h1_3, h1_7]

/-- Symbolic soundness of `ntt8AsmFermat` matching `CrtNtt.ntt8WithRoots`. -/
theorem ntt8AsmFermat_sound (p w1 w2 w3 : Nat) (s : State)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (h0 : s.r0 = x0) (h1 : s.r1 = x1) (h2 : s.r2 = x2) (h3 : s.r3 = x3)
    (h4 : s.r4 = x4) (h5 : s.r5 = x5) (h6 : s.r6 = x6) (h7 : s.r7 = x7) :
    let s' := runProgram s (ntt8AsmFermat p w1 w2 w3)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3, s'.r4, s'.r5, s'.r6, s'.r7⟩ : CrtNtt.Vec8) =
      CrtNtt.ntt8WithRoots p w1 w2 w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := by
  have h := runProgram_dit8Asm p w1 w2 w3 s
  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
  exact h

/-- Symbolic soundness of `intt8AsmFermat` matching `CrtNtt.intt8WithRoots`. -/
theorem intt8AsmFermat_sound (p inv8 iw1 iw2 iw3 : Nat) (s : State)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (h0 : s.r0 = x0) (h1 : s.r1 = x1) (h2 : s.r2 = x2) (h3 : s.r3 = x3)
    (h4 : s.r4 = x4) (h5 : s.r5 = x5) (h6 : s.r6 = x6) (h7 : s.r7 = x7) :
    let s' := runProgram s (intt8AsmFermat p inv8 iw1 iw2 iw3)
    (⟨s'.r0, s'.r1, s'.r2, s'.r3, s'.r4, s'.r5, s'.r6, s'.r7⟩ : CrtNtt.Vec8) =
      CrtNtt.intt8WithRoots p iw1 iw2 iw3 inv8 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := by
  have h := runProgram_dit8Asm p iw1 iw2 iw3 s
  rw [h0, h1, h2, h3, h4, h5, h6, h7] at h
  dsimp [intt8AsmFermat]
  rw [runProgram_append]
  generalize runProgram s (dit8Asm p iw1 iw2 iw3) = s1 at h ⊢
  rcases s1 with ⟨y0, y1, y2, y3, y4, y5, y6, y7, u0, u1, ipc⟩
  dsimp [runProgram, step, State.get, State.set, State.setPc]
  have hy0 : y0 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x0 :=
    congrArg CrtNtt.Vec8.x0 h
  have hy1 : y1 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x1 :=
    congrArg CrtNtt.Vec8.x1 h
  have hy2 : y2 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x2 :=
    congrArg CrtNtt.Vec8.x2 h
  have hy3 : y3 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x3 :=
    congrArg CrtNtt.Vec8.x3 h
  have hy4 : y4 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x4 :=
    congrArg CrtNtt.Vec8.x4 h
  have hy5 : y5 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x5 :=
    congrArg CrtNtt.Vec8.x5 h
  have hy6 : y6 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x6 :=
    congrArg CrtNtt.Vec8.x6 h
  have hy7 : y7 = (CrtNtt.ntt8WithRoots p iw1 iw2 iw3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x7 :=
    congrArg CrtNtt.Vec8.x7 h
  rw [hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7]
  rfl

/-- Parameter bundle for 8-point NTT/INTT over Fermat-tower primes `{17, 257, 65537}`. -/
structure FermatNtt8Spec where
  p : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  iw1 : Nat
  iw2 : Nat
  iw3 : Nat
  inv8 : Nat
  deriving DecidableEq, Repr

/-- Algebraic validity of an 8-point Fermat-tower primitive 8th-root configuration. -/
def FermatNtt8Spec.Valid (cfg : FermatNtt8Spec) : Prop :=
  1 < cfg.p ∧
  (cfg.w1 * cfg.w1) % cfg.p = cfg.w2 % cfg.p ∧
  (cfg.w1 * cfg.w2) % cfg.p = cfg.w3 % cfg.p ∧
  (cfg.w2 * cfg.w2 + 1) % cfg.p = 0 ∧
  (cfg.w1 * cfg.iw1) % cfg.p = 1 ∧
  (cfg.w2 * cfg.iw2) % cfg.p = 1 ∧
  (cfg.w3 * cfg.iw3) % cfg.p = 1 ∧
  (8 * cfg.inv8) % cfg.p = 1

/-- Canonical 8-point NTT parameters for `F_2 = 17` (`ω_8 = 9`). -/
def fermatNtt8Spec17 : FermatNtt8Spec :=
  { p := 17, w1 := 9, w2 := 13, w3 := 15, iw1 := 2, iw2 := 4, iw3 := 8, inv8 := 15 }

/-- Canonical 8-point NTT parameters for `F_3 = 257` (`ω_8 = 4`). -/
def fermatNtt8Spec257 : FermatNtt8Spec :=
  { p := 257, w1 := 4, w2 := 16, w3 := 64, iw1 := 193, iw2 := 241, iw3 := 253, inv8 := 225 }

/-- Canonical 8-point NTT parameters for `F_4 = 65537` (`ω_8 = 16`). -/
def fermatNtt8Spec65537 : FermatNtt8Spec :=
  { p := 65537, w1 := 16, w2 := 256, w3 := 4096,
    iw1 := 61441, iw2 := 65281, iw3 := 65521, inv8 := 57345 }

/-- All three Fermat-tower 8-point NTT parameter configurations (`{17, 257, 65537}`). -/
def fermatTowerNtt8Specs : List FermatNtt8Spec :=
  [fermatNtt8Spec17, fermatNtt8Spec257, fermatNtt8Spec65537]

theorem fermatNtt8Spec17_valid : fermatNtt8Spec17.Valid := by
  dsimp [FermatNtt8Spec.Valid, fermatNtt8Spec17]; decide

theorem fermatNtt8Spec257_valid : fermatNtt8Spec257.Valid := by
  dsimp [FermatNtt8Spec.Valid, fermatNtt8Spec257]; decide

theorem fermatNtt8Spec65537_valid : fermatNtt8Spec65537.Valid := by
  dsimp [FermatNtt8Spec.Valid, fermatNtt8Spec65537]; decide

/-- Decidable verification that all three Fermat-tower 8-point specs are valid. -/
theorem fermatTowerNtt8Specs_valid :
    ∀ cfg ∈ fermatTowerNtt8Specs, cfg.Valid := by
  intro cfg hmem
  dsimp [fermatTowerNtt8Specs] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact fermatNtt8Spec17_valid
  · rcases List.mem_cons.mp hmem with rfl | hmem
    · exact fermatNtt8Spec257_valid
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact fermatNtt8Spec65537_valid
      · contradiction

/-- Componentwise normalization of `CrtNtt.Vec8` modulo `p`. -/
def normVec8 (p : Nat) (v : CrtNtt.Vec8) : CrtNtt.Vec8 :=
  ⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p, v.x4 % p, v.x5 % p, v.x6 % p, v.x7 % p⟩

private theorem vec8_eq_intro (u v : CrtNtt.Vec8)
    (h0 : u.x0 = v.x0) (h1 : u.x1 = v.x1) (h2 : u.x2 = v.x2) (h3 : u.x3 = v.x3)
    (h4 : u.x4 = v.x4) (h5 : u.x5 = v.x5) (h6 : u.x6 = v.x6) (h7 : u.x7 = v.x7) :
    u = v := by
  cases u; cases v; simp only at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h1 h2 h3 h4 h5 h6 h7; rfl

private theorem butterfly2_pair_int (p u v : Nat) (hp : 0 < p) :
    (((CrtNtt.butterfly2 p u v).1 : Int) % (p : Int) = ((u : Int) + (v : Int)) % p) ∧
    (((CrtNtt.butterfly2 p u v).2 : Int) % (p : Int) = ((u : Int) - (v : Int)) % p) := by
  dsimp [CrtNtt.butterfly2]
  exact ⟨mod_add_congr_int p u v, mod_sub_congr_int p u v hp⟩

private theorem butterfly2_cancel_int (p u v : Nat) (hp : 0 < p)
    {a b : Int}
    (ha : (u : Int) % (p : Int) = a % (p : Int))
    (hb : (v : Int) % (p : Int) = b % (p : Int)) :
    (((CrtNtt.butterfly2 p u v).1 : Int) % (p : Int) = (a + b) % p) ∧
    (((CrtNtt.butterfly2 p u v).2 : Int) % (p : Int) = (a - b) % p) := by
  have h := butterfly2_pair_int p u v hp
  exact ⟨h.1.trans (emod_add_cancel ha hb), h.2.trans (emod_sub_cancel ha hb)⟩

private theorem butterfly2_inv_int (p u v : Nat) (hp : 0 < p)
    {a b : Int}
    (ha : (u : Int) % (p : Int) = (a + b) % (p : Int))
    (hb : (v : Int) % (p : Int) = (a - b) % (p : Int)) :
    (((CrtNtt.butterfly2 p u v).1 : Int) % (p : Int) = (2 * a) % p) ∧
    (((CrtNtt.butterfly2 p u v).2 : Int) % (p : Int) = (2 * b) % p) := by
  have h := butterfly2_cancel_int p u v hp ha hb
  exact ⟨h.1.trans (by congr 1; omega), h.2.trans (by congr 1; omega)⟩

private theorem natCast_inv_mul_int (p a b : Nat) (hab : (a * b) % p = 1 % p) :
    ((a : Int) * (b : Int)) % (p : Int) = 1 % (p : Int) := by
  rw [← natCast_mul_int, ← Int.natCast_emod, hab, Int.natCast_emod]; rfl

private theorem mul_cancel_inv_int {p : Int} {x a b inv : Int}
    (hx : x % p = (a * b) % p) (hi : (b * inv) % p = 1 % p) :
    (x * inv) % p = a % p := by
  calc (x * inv) % p
      = ((a * b) * inv) % p := emod_mul_cancel hx rfl
    _ = (a * (b * inv)) % p := by rw [Int.mul_assoc]
    _ = (a * 1) % p := emod_mul_cancel rfl hi
    _ = a % p := by rw [Int.mul_one]

private theorem butterfly2_scaled_inv (p U V u v : Nat) (hp : 0 < p) (k : Int)
    (hU : (U : Int) % (p : Int) = (k * (CrtNtt.butterfly2 p u v).1) % (p : Int))
    (hV : (V : Int) % (p : Int) = (k * (CrtNtt.butterfly2 p u v).2) % (p : Int)) :
    (((CrtNtt.butterfly2 p U V).1 : Int) % (p : Int) = ((2 * k) * (u : Int)) % (p : Int)) ∧
    (((CrtNtt.butterfly2 p U V).2 : Int) % (p : Int) = ((2 * k) * (v : Int)) % (p : Int)) := by
  have hb := butterfly2_pair_int p u v hp
  have h1 : (U : Int) % p = (k * ((u : Int) + (v : Int))) % p :=
    hU.trans (emod_mul_cancel rfl hb.1)
  have h2 : (V : Int) % p = (k * ((u : Int) - (v : Int))) % p :=
    hV.trans (emod_mul_cancel rfl hb.2)
  have hc := butterfly2_cancel_int p U V hp h1 h2
  constructor
  · refine hc.1.trans ?_
    have heq : k * ((u : Int) + (v : Int)) + k * ((u : Int) - (v : Int)) =
        (2 * k) * (u : Int) := by
      have h2 : (2 : Int) * k = k + k := by omega
      rw [Int.mul_add, Int.mul_sub, h2, Int.add_mul]; omega
    rw [heq]
  · refine hc.2.trans ?_
    have heq : k * ((u : Int) + (v : Int)) - k * ((u : Int) - (v : Int)) =
        (2 * k) * (v : Int) := by
      have h2 : (2 : Int) * k = k + k := by omega
      rw [Int.mul_add, Int.mul_sub, h2, Int.add_mul]; omega
    rw [heq]

private theorem butterfly2_scaled_mul_inv (p U V u v w inv : Nat) (hp : 0 < p) (k : Int)
    (hwinv : ((w : Int) * (inv : Int)) % (p : Int) = 1 % (p : Int))
    (hU : (U : Int) % (p : Int) = (k * (CrtNtt.butterfly2 p u ((v * w) % p)).1) % (p : Int))
    (hV : (V : Int) % (p : Int) = (k * (CrtNtt.butterfly2 p u ((v * w) % p)).2) % (p : Int)) :
    (((CrtNtt.butterfly2 p U V).1 : Int) % (p : Int) = ((2 * k) * (u : Int)) % (p : Int)) ∧
    (((((CrtNtt.butterfly2 p U V).2 * inv) % p : Nat) : Int) % (p : Int) =
      ((2 * k) * (v : Int)) % (p : Int)) := by
  have hinv := butterfly2_scaled_inv p U ((V : Nat)) u ((v * w) % p) hp k hU hV
  constructor
  · exact hinv.1
  · refine (mod_mul_congr_int p _ inv).trans ?_
    have hmul : (((CrtNtt.butterfly2 p U V).2 : Int)) % p = (((2 * k) * (v : Int)) * w) % p := by
      refine hinv.2.trans ?_
      exact (emod_mul_cancel rfl (mod_mul_congr_int p v w)).trans (by ac_rfl)
    exact mul_cancel_inv_int hmul hwinv

/-- Generic algebraic 8-point NTT/INTT invertibility over arbitrary moduli. -/
theorem intt8_ntt8_generic (p w1 w2 w3 iw1 iw2 iw3 inv8 : Nat)
    (hp : 0 < p)
    (hw12 : (w1 * w2) % p = w3 % p)
    (hi1 : (w1 * iw1) % p = 1 % p)
    (hi2 : (w2 * iw2) % p = 1 % p)
    (hi3 : (w3 * iw3) % p = 1 % p)
    (hi8 : (8 * inv8) % p = 1 % p)
    (v : CrtNtt.Vec8) :
    CrtNtt.intt8WithRoots p iw1 iw2 iw3 inv8 (CrtNtt.ntt8WithRoots p w1 w2 w3 v) =
      normVec8 p v := by
  have hw12i : ((w1 : Int) * (w2 : Int)) % (p : Int) = (w3 : Int) % (p : Int) := by
    rw [← natCast_mul_int, ← Int.natCast_emod, hw12, Int.natCast_emod]
  have hi1i := natCast_inv_mul_int p w1 iw1 hi1
  have hi2i := natCast_inv_mul_int p w2 iw2 hi2
  have hi3i := natCast_inv_mul_int p w3 iw3 hi3
  have hi8i := natCast_inv_mul_int p 8 inv8 hi8
  have hw3iw2 : ((w3 : Int) * (iw2 : Int)) % (p : Int) = (w1 : Int) % (p : Int) := by
    calc ((w3 : Int) * (iw2 : Int)) % p
        = (((w1 : Int) * w2) * iw2) % p := emod_mul_cancel hw12i.symm rfl
      _ = ((w1 : Int) * ((w2 : Int) * iw2)) % p := by rw [Int.mul_assoc]
      _ = ((w1 : Int) * 1) % p := emod_mul_cancel rfl hi2i
      _ = (w1 : Int) % p := by rw [Int.mul_one]
  dsimp [CrtNtt.intt8WithRoots, CrtNtt.ntt8WithRoots]
  -- Stage 1 of forward NTT
  let a0 := (CrtNtt.butterfly2 p v.x0 v.x4).1
  let a1 := (CrtNtt.butterfly2 p v.x0 v.x4).2
  let a2 := (CrtNtt.butterfly2 p v.x2 v.x6).1
  let a3 := (CrtNtt.butterfly2 p v.x2 v.x6).2
  let a4 := (CrtNtt.butterfly2 p v.x1 v.x5).1
  let a5 := (CrtNtt.butterfly2 p v.x1 v.x5).2
  let a6 := (CrtNtt.butterfly2 p v.x3 v.x7).1
  let a7 := (CrtNtt.butterfly2 p v.x3 v.x7).2
  -- Stage 2 of forward NTT
  let b0 := (CrtNtt.butterfly2 p a0 a2).1
  let b2 := (CrtNtt.butterfly2 p a0 a2).2
  let b1 := (CrtNtt.butterfly2 p a1 ((a3 * w2) % p)).1
  let b3 := (CrtNtt.butterfly2 p a1 ((a3 * w2) % p)).2
  let b4 := (CrtNtt.butterfly2 p a4 a6).1
  let b6 := (CrtNtt.butterfly2 p a4 a6).2
  let b5 := (CrtNtt.butterfly2 p a5 ((a7 * w2) % p)).1
  let b7 := (CrtNtt.butterfly2 p a5 ((a7 * w2) % p)).2
  -- Stage 3 of forward NTT
  let X0 := (CrtNtt.butterfly2 p b0 b4).1
  let X4 := (CrtNtt.butterfly2 p b0 b4).2
  let X1 := (CrtNtt.butterfly2 p b1 ((b5 * w1) % p)).1
  let X5 := (CrtNtt.butterfly2 p b1 ((b5 * w1) % p)).2
  let X2 := (CrtNtt.butterfly2 p b2 ((b6 * w2) % p)).1
  let X6 := (CrtNtt.butterfly2 p b2 ((b6 * w2) % p)).2
  let X3 := (CrtNtt.butterfly2 p b3 ((b7 * w3) % p)).1
  let X7 := (CrtNtt.butterfly2 p b3 ((b7 * w3) % p)).2
  -- Stage 1 of inverse NTT recovers 2 * b_k
  have hA01 := butterfly2_scaled_inv p X0 X4 b0 b4 hp 1
    (by rw [Int.one_mul]) (by rw [Int.one_mul])
  have hA23 := butterfly2_scaled_mul_inv p X2 X6 b2 b6 w2 iw2 hp 1 hi2i
    (by rw [Int.one_mul]) (by rw [Int.one_mul])
  have hA45 := butterfly2_scaled_inv p X1 X5 b1 ((b5 * w1) % p) hp 1
    (by rw [Int.one_mul]) (by rw [Int.one_mul])
  have hA67 := butterfly2_scaled_inv p X3 X7 b3 ((b7 * w3) % p) hp 1
    (by rw [Int.one_mul]) (by rw [Int.one_mul])
  have hA7iw : ((((CrtNtt.butterfly2 p X3 X7).2 * iw2) % p : Nat) : Int) % p =
      ((2 * (w1 : Int)) * (b7 : Int)) % p := by
    refine (mod_mul_congr_int p _ iw2).trans ?_
    have hm : (((CrtNtt.butterfly2 p X3 X7).2 : Int)) % p = ((2 * (b7 : Int)) * w3) % p := by
      refine hA67.2.trans ?_
      rw [Int.mul_one, Int.mul_assoc]
      exact emod_mul_cancel rfl (mod_mul_congr_int p b7 w3)
    calc ((((CrtNtt.butterfly2 p X3 X7).2 : Int)) * iw2) % p
        = (((2 * (b7 : Int)) * w3) * iw2) % p := emod_mul_cancel hm rfl
      _ = ((2 * (b7 : Int)) * ((w3 : Int) * iw2)) % p := by rw [Int.mul_assoc]
      _ = ((2 * (b7 : Int)) * w1) % p := emod_mul_cancel rfl hw3iw2
      _ = ((2 * (w1 : Int)) * (b7 : Int)) % p := by ac_rfl
  have hA5sc : (((CrtNtt.butterfly2 p X1 X5).2 : Nat) : Int) % p =
      ((2 * (w1 : Int)) * (b5 : Int)) % p := by
    refine hA45.2.trans ?_
    have hm : (2 * (1 : Int)) * ((b5 : Int) * (w1 : Int)) =
        (2 * (w1 : Int)) * (b5 : Int) := by ac_rfl
    exact (emod_mul_cancel rfl (mod_mul_congr_int p b5 w1)).trans (by rw [hm])
  -- Stage 2 of inverse NTT recovers 4 * a_k
  have hB02 := butterfly2_scaled_inv p _ _ a0 a2 hp 2 hA01.1 hA23.1
  have hB13 := butterfly2_scaled_inv p _ _ a4 a6 hp 2 hA01.2 hA23.2
  have hB46 := butterfly2_scaled_mul_inv p _ _ a1 a3 w2 iw2 hp 2 hi2i hA45.1 hA67.1
  have hB57 := butterfly2_scaled_inv p _ _ a5 ((a7 * w2) % p) hp (2 * w1) hA5sc hA7iw
  have hB5iw : (((((CrtNtt.butterfly2 p (CrtNtt.butterfly2 p X1 X5).2
      (((CrtNtt.butterfly2 p X3 X7).2 * iw2) % p)).1 * iw1) % p : Nat) : Int)) % p =
      (4 * (a5 : Int)) % p := by
    refine (mod_mul_congr_int p _ iw1).trans ?_
    have h4w1 : 2 * (2 * (w1 : Int)) = 4 * (w1 : Int) := by omega
    rw [h4w1] at hB57
    have hm : (4 * (w1 : Int)) * (a5 : Int) = (4 * (a5 : Int)) * (w1 : Int) := by ac_rfl
    exact mul_cancel_inv_int (hB57.1.trans (by rw [hm])) hi1i
  have hB7iw : (((((CrtNtt.butterfly2 p (CrtNtt.butterfly2 p X1 X5).2
      (((CrtNtt.butterfly2 p X3 X7).2 * iw2) % p)).2 * iw3) % p : Nat) : Int)) % p =
      (4 * (a7 : Int)) % p := by
    refine (mod_mul_congr_int p _ iw3).trans ?_
    have h4w1 : 2 * (2 * (w1 : Int)) = 4 * (w1 : Int) := by omega
    rw [h4w1] at hB57
    have hmul : (((CrtNtt.butterfly2 p (CrtNtt.butterfly2 p X1 X5).2
        (((CrtNtt.butterfly2 p X3 X7).2 * iw2) % p)).2 : Int)) % p =
        ((4 * (a7 : Int)) * w3) % p := by
      refine hB57.2.trans ?_
      have hs : ((4 * (w1 : Int)) * (((a7 * w2) % p : Nat) : Int)) % p =
          ((4 * (a7 : Int)) * ((w1 : Int) * w2)) % p := by
        calc ((4 * (w1 : Int)) * (((a7 * w2) % p : Nat) : Int)) % p
            = ((4 * (w1 : Int)) * ((a7 : Int) * w2)) % p :=
                emod_mul_cancel rfl (mod_mul_congr_int p a7 w2)
          _ = ((4 * (a7 : Int)) * ((w1 : Int) * w2)) % p := by ac_rfl
      exact hs.trans (emod_mul_cancel rfl hw12i)
    exact mul_cancel_inv_int hmul hi3i
  -- Stage 3 of inverse NTT recovers 8 * x_k
  have hY04 := butterfly2_scaled_inv p _ _ v.x0 v.x4 hp 4 hB02.1 hB46.1
  have hY15 := butterfly2_scaled_inv p _ _ v.x1 v.x5 hp 4 hB13.1 hB5iw
  have hY26 := butterfly2_scaled_inv p _ _ v.x2 v.x6 hp 4 hB02.2 hB46.2
  have hY37 := butterfly2_scaled_inv p _ _ v.x3 v.x7 hp 4 hB13.2 hB7iw
  have hfin : ∀ (res y : Nat) (k : Nat)
      (hy : (y : Int) % (p : Int) = (8 * (k : Int)) % (p : Int))
      (hres : res = (y * inv8) % p), res = k % p := by
    intro res y k hy hres
    have hmul : ((res : Int) % p) = (k : Int) % p := by
      rw [hres]
      refine (mod_mul_congr_int p y inv8).trans ?_
      calc ((y : Int) * inv8) % p
          = ((8 * (k : Int)) * inv8) % p := emod_mul_cancel hy rfl
        _ = ((k : Int) * (8 * (inv8 : Int))) % p := by ac_rfl
        _ = ((k : Int) * 1) % p := emod_mul_cancel rfl hi8i
        _ = (k : Int) % p := by rw [Int.mul_one]
    have hlt : res % p = res := by rw [hres]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)
    rw [← hlt]
    exact nat_mod_of_int_mod_eq p res k (k : Int) (by rw [hlt]; exact hmul) (mod_mod_congr_int p k)
  dsimp [normVec8]
  apply vec8_eq_intro
  · exact hfin _ _ v.x0 hY04.1 rfl
  · exact hfin _ _ v.x1 hY15.1 rfl
  · exact hfin _ _ v.x2 hY26.1 rfl
  · exact hfin _ _ v.x3 hY37.1 rfl
  · exact hfin _ _ v.x4 hY04.2 rfl
  · exact hfin _ _ v.x5 hY15.2 rfl
  · exact hfin _ _ v.x6 hY26.2 rfl
  · exact hfin _ _ v.x7 hY37.2 rfl

/--
Symbolic roundtrip invertibility of `ntt8AsmFermat` followed by `intt8AsmFermat`
across any valid Fermat-tower primitive-8th-root configuration `{17, 257, 65537}`
and all `x0..x7 < cfg.p`.
-/
theorem intt8_ntt8_asm_fermat_roundtrip (cfg : FermatNtt8Spec) (hcfg : cfg.Valid)
    (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (hx0 : x0 < cfg.p) (hx1 : x1 < cfg.p) (hx2 : x2 < cfg.p) (hx3 : x3 < cfg.p)
    (hx4 : x4 < cfg.p) (hx5 : x5 < cfg.p) (hx6 : x6 < cfg.p) (hx7 : x7 < cfg.p)
    (hr0 : s.r0 = x0) (hr1 : s.r1 = x1) (hr2 : s.r2 = x2) (hr3 : s.r3 = x3)
    (hr4 : s.r4 = x4) (hr5 : s.r5 = x5) (hr6 : s.r6 = x6) (hr7 : s.r7 = x7) :
    let s1 := runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)
    let s2 := runProgram s1 (intt8AsmFermat cfg.p cfg.inv8 cfg.iw1 cfg.iw2 cfg.iw3)
    (⟨s2.r0, s2.r1, s2.r2, s2.r3, s2.r4, s2.r5, s2.r6, s2.r7⟩ : CrtNtt.Vec8) =
      ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := by
  rcases hcfg with ⟨hp1, _, hw12, _, hi1, hi2, hi3, hi8⟩
  have hp0 : 0 < cfg.p := Nat.lt_trans Nat.zero_lt_one hp1
  dsimp
  have h1 := ntt8AsmFermat_sound cfg.p cfg.w1 cfg.w2 cfg.w3 s
    x0 x1 x2 x3 x4 x5 x6 x7 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have hr1' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r0 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x0 :=
    congrArg CrtNtt.Vec8.x0 h1
  have hr2' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r1 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x1 :=
    congrArg CrtNtt.Vec8.x1 h1
  have hr3' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r2 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x2 :=
    congrArg CrtNtt.Vec8.x2 h1
  have hr4' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r3 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x3 :=
    congrArg CrtNtt.Vec8.x3 h1
  have hr5' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r4 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x4 :=
    congrArg CrtNtt.Vec8.x4 h1
  have hr6' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r5 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x5 :=
    congrArg CrtNtt.Vec8.x5 h1
  have hr7' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r6 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x6 :=
    congrArg CrtNtt.Vec8.x6 h1
  have hr8' : (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)).r7 =
      (CrtNtt.ntt8WithRoots cfg.p cfg.w1 cfg.w2 cfg.w3 ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩).x7 :=
    congrArg CrtNtt.Vec8.x7 h1
  have h2 := intt8AsmFermat_sound cfg.p cfg.inv8 cfg.iw1 cfg.iw2 cfg.iw3
    (runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3))
    _ _ _ _ _ _ _ _ hr1' hr2' hr3' hr4' hr5' hr6' hr7' hr8'
  have hi1' : (cfg.w1 * cfg.iw1) % cfg.p = 1 % cfg.p := by
    rw [hi1, Nat.mod_eq_of_lt hp1]
  have hi2' : (cfg.w2 * cfg.iw2) % cfg.p = 1 % cfg.p := by
    rw [hi2, Nat.mod_eq_of_lt hp1]
  have hi3' : (cfg.w3 * cfg.iw3) % cfg.p = 1 % cfg.p := by
    rw [hi3, Nat.mod_eq_of_lt hp1]
  have hi8' : (8 * cfg.inv8) % cfg.p = 1 % cfg.p := by
    rw [hi8, Nat.mod_eq_of_lt hp1]
  have hgen := intt8_ntt8_generic cfg.p cfg.w1 cfg.w2 cfg.w3
    cfg.iw1 cfg.iw2 cfg.iw3 cfg.inv8 hp0 hw12 hi1' hi2' hi3' hi8'
    ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  have hnorm : normVec8 cfg.p ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ =
      ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := by
    dsimp [normVec8]
    rw [Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hx3,
      Nat.mod_eq_of_lt hx4, Nat.mod_eq_of_lt hx5, Nat.mod_eq_of_lt hx6, Nat.mod_eq_of_lt hx7]
  exact h2.trans (hgen.trans hnorm)

/-- Theorem (`MiniVM` Parametric 8-Point Fermat-Tower NTT/INTT Roundtrip Certificates):
All three Fermat-tower primitive-8th-root primes `{17, 257, 65537}` satisfy
`ntt8AsmFermat` / `intt8AsmFermat` symbolic roundtrip invertibility on `MiniVM`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermatTowerNtt8_asm_roundtrip_certs :
    ∀ cfg ∈ fermatTowerNtt8Specs,
      ∀ (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 : Nat),
        x0 < cfg.p → x1 < cfg.p → x2 < cfg.p → x3 < cfg.p →
        x4 < cfg.p → x5 < cfg.p → x6 < cfg.p → x7 < cfg.p →
        s.r0 = x0 → s.r1 = x1 → s.r2 = x2 → s.r3 = x3 →
        s.r4 = x4 → s.r5 = x5 → s.r6 = x6 → s.r7 = x7 →
        let s1 := runProgram s (ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)
        let s2 := runProgram s1 (intt8AsmFermat cfg.p cfg.inv8 cfg.iw1 cfg.iw2 cfg.iw3)
        (⟨s2.r0, s2.r1, s2.r2, s2.r3, s2.r4, s2.r5, s2.r6, s2.r7⟩ : CrtNtt.Vec8) =
          ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := by
  intro cfg hmem s x0 x1 x2 x3 x4 x5 x6 x7 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  exact intt8_ntt8_asm_fermat_roundtrip cfg (fermatTowerNtt8Specs_valid cfg hmem)
    s x0 x1 x2 x3 x4 x5 x6 x7 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7

end MiniVMNttBridge

-- end of file: leanasm/src/LeanAsm/MiniVMNttBridge.lean

