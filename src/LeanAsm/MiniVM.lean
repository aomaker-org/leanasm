-- Path: leanasm/src/LeanAsm/MiniVM.lean
-- A verified assembly instruction set and state machine evaluator with modular RNS opcodes.
-- Max Column: 100 Columns

namespace MiniVM

/-- Register identifiers for a 4-register virtual machine. -/
inductive Reg : Type
  | r0
  | r1
  | r2
  | r3
  deriving Repr, DecidableEq

/-- Machine state: register values and program counter. -/
structure State where
  r0 : Nat := 0
  r1 : Nat := 0
  r2 : Nat := 0
  r3 : Nat := 0
  pc : Nat := 0
  deriving Repr, DecidableEq

/-- Read a register value from the state. -/
def State.get (s : State) : Reg → Nat
  | Reg.r0 => s.r0
  | Reg.r1 => s.r1
  | Reg.r2 => s.r2
  | Reg.r3 => s.r3

/-- Write a value into a register in state. -/
def State.set (s : State) (r : Reg) (v : Nat) : State :=
  match r with
  | Reg.r0 => { s with r0 := v }
  | Reg.r1 => { s with r1 := v }
  | Reg.r2 => { s with r2 := v }
  | Reg.r3 => { s with r3 := v }

/-- Update program counter. -/
def State.setPc (s : State) (newPc : Nat) : State :=
  { s with pc := newPc }

/-- Assembly instruction set with modular arithmetic. -/
inductive Instr : Type
  | movImm (dst : Reg) (val : Nat)                 -- dst := val
  | movReg (dst : Reg) (src : Reg)                 -- dst := src
  | addReg (dst : Reg) (src : Reg)                 -- dst := dst + src
  | addImm (dst : Reg) (val : Nat)                 -- dst := dst + val
  | subReg (dst : Reg) (src : Reg)                 -- dst := dst - src
  | modImm (dst : Reg) (m : Nat)                   -- dst := dst % m
  | mulModReg (dst : Reg) (src : Reg) (m : Nat)    -- dst := (dst * src) % m
  deriving Repr, DecidableEq

/-- Single-step evaluation of an instruction. -/
def step (s : State) : Instr → State
  | Instr.movImm dst val => (s.set dst val).setPc (s.pc + 1)
  | Instr.movReg dst src => (s.set dst (s.get src)).setPc (s.pc + 1)
  | Instr.addReg dst src => (s.set dst (s.get dst + s.get src)).setPc (s.pc + 1)
  | Instr.addImm dst val => (s.set dst (s.get dst + val)).setPc (s.pc + 1)
  | Instr.subReg dst src => (s.set dst (s.get dst - s.get src)).setPc (s.pc + 1)
  | Instr.modImm dst m => (s.set dst (s.get dst % m)).setPc (s.pc + 1)
  | Instr.mulModReg dst src m => (s.set dst ((s.get dst * s.get src) % m)).setPc (s.pc + 1)

/-- Execute a sequence of instructions. -/
def runProgram (s : State) : List Instr → State
  | [] => s
  | i :: rest => runProgram (step s i) rest

-- =============================================================================
-- Formally Verified Theorems about the MiniVM
-- =============================================================================

/-- Theorem: Loading an immediate value into a register sets that register value. -/
theorem get_set_same (s : State) (r : Reg) (v : Nat) :
    (s.set r v).get r = v := by
  cases r <;> rfl

/-- Theorem: Setting register regA does not alter a distinct register regB. -/
theorem get_set_other (s : State) (regA regB : Reg) (v : Nat) (h : regA ≠ regB) :
    (s.set regA v).get regB = s.get regB := by
  cases regA <;> cases regB <;> first | contradiction | rfl

/-- Lemma: Changing the program counter does not affect register values. -/
theorem get_set_pc (s : State) (r : Reg) (newPc : Nat) :
    (s.setPc newPc).get r = s.get r := by
  cases r <;> rfl

/-- Theorem (Algebraic Commutativity): Adding two registers commutes. -/
theorem add_comm_equiv (s : State) (dst src : Reg) :
    (s.get dst + s.get src) = (s.get src + s.get dst) := by
  omega

/-- Theorem: Modular multiplication instruction evaluates correctly. -/
theorem mul_mod_reg_correct (s : State) (dst src : Reg) (m : Nat) :
    (step s (Instr.mulModReg dst src m)).get dst = (s.get dst * s.get src) % m := by
  dsimp [step]
  rw [get_set_pc]
  rw [get_set_same]

-- =============================================================================
-- Multi-Instruction Assembly Program for Garner Mixed-Radix CRT (gemweb019)
-- =============================================================================

/--
Garner mixed-radix reconstruction program:
Input registers: r1 = residue mod 7, r2 = residue mod 11, r3 = residue mod 13.
Computes x = v1 + v2 * 7 + v3 * 77 into r0 using bounded intermediate values.
-/
def garnerCrtProgram : List Instr := [
  -- Step 1: v1 = r1 % 7 (stored back in r1)
  Instr.modImm Reg.r1 7,
  -- Step 2: diff2 = (r2 + 11 - (v1 % 11)) % 11; v2 = (diff2 * 8) % 11
  Instr.addImm Reg.r2 11,
  Instr.subReg Reg.r2 Reg.r1,
  Instr.modImm Reg.r2 11,
  Instr.movImm Reg.r0 8,
  Instr.mulModReg Reg.r2 Reg.r0 11,
  -- Step 3: term = (v1 + v2 * 7) % 13 (stored in r0)
  Instr.movImm Reg.r0 7,
  Instr.mulModReg Reg.r0 Reg.r2 13,
  Instr.addReg Reg.r0 Reg.r1,
  Instr.modImm Reg.r0 13,
  -- Step 4: diff3 = (r3 + 13 - term) % 13; v3 = (diff3 * 12) % 13 (stored in r3)
  Instr.addImm Reg.r3 13,
  Instr.subReg Reg.r3 Reg.r0,
  Instr.modImm Reg.r3 13,
  Instr.movImm Reg.r0 12,
  Instr.mulModReg Reg.r3 Reg.r0 13,
  -- Step 5: x = v1 + v2 * 7 + v3 * 77 (accumulated into r0)
  Instr.movImm Reg.r0 77,
  Instr.mulModReg Reg.r0 Reg.r3 1001,
  Instr.movImm Reg.r3 7,
  Instr.mulModReg Reg.r3 Reg.r2 1001,
  Instr.addReg Reg.r0 Reg.r3,
  Instr.addReg Reg.r0 Reg.r1
]

/--
Theorem (MiniVM Garner CRT Concrete Soundness):
Executing `garnerCrtProgram` from initial state with residue inputs (r1=4, r2=4, r3=6)
halts with r0 = 851 (matching 23 * 37 = 851) and program counter pc = 21.
Proved constructively with ZERO axioms.
-/
theorem exec_garner_crt_sound :
    let sInit : State := { r0 := 0, r1 := 4, r2 := 4, r3 := 6, pc := 0 }
    let sFinal := runProgram sInit garnerCrtProgram
    sFinal.r0 = 851 ∧ sFinal.pc = 21 := by
  decide

end MiniVM

-- end of file: leanasm/src/LeanAsm/MiniVM.lean
