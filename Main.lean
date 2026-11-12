-- Path: leanasm/Main.lean
-- Interactive runner demonstrating MiniVM and Mathematical explorations.

import LeanAsm

open MiniVM
open Conjectures

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "   leanasm: Verified Assembly VM & Mathematical Demo      "
  IO.println "=========================================================="

  -- 1. MiniVM Assembly Program execution
  IO.println "\n[+] Part 1: MiniVM Assembly Execution"
  let initial : State := {}
  -- Program:
  --   movImm r0, 42
  --   movImm r1, 10
  --   addReg r0, r1
  --   subReg r0, r1
  let prog : List Instr := [
    Instr.movImm Reg.r0 42,
    Instr.movImm Reg.r1 10,
    Instr.addReg Reg.r0 Reg.r1,
    Instr.subReg Reg.r0 Reg.r1
  ]

  let finalState := runProgram initial prog
  IO.println s!"  Initial State : r0={initial.r0}, r1={initial.r1}, pc={initial.pc}"
  IO.println s!"  After Program : r0={finalState.r0}, r1={finalState.r1}, pc={finalState.pc}"
  IO.println "  Formal proof verified: (s.set r v).get r = v"

  -- 2. Conjectures & Collatz computation
  IO.println "\n[+] Part 2: Collatz Trajectory Exploration"
  for seed in [6, 11, 27] do
    let traj := collatzTrajectory seed 25
    IO.println s!"  Seed {seed} trajectory (first {traj.length} steps): {traj}"

  IO.println "\n[+] Formal theorems verified at build-time with Lean 4 kernel."
  IO.println "=========================================================="

-- end of file: leanasm/Main.lean
