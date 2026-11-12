-- Path: leanasm/Main.lean
-- Interactive runner demonstrating MiniVM, Conjectures, and Yang-Mills Lattice.

import LeanAsm

open MiniVM
open Conjectures
open YangMillsToy

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "   leanasm: Verified Assembly VM, Math & Yang-Mills Demo  "
  IO.println "=========================================================="

  -- 1. MiniVM Assembly Program execution
  IO.println "\n[+] Part 1: MiniVM Assembly Execution"
  let initial : State := {}
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

  -- 3. 4D Wilson Lattice Gauge Theory Simulation
  IO.println "\n[+] Part 3: 4D Yang-Mills Wilson Lattice Gauge Simulation"
  let origin : Point4 := ⟨0, 0, 0, 0⟩
  let vacConfig : GaugeConfig := fun _ => Z2.plusOne
  let vacP := plaquette vacConfig origin Dir.d0 Dir.d1
  let vacAct := plaquetteAction vacConfig origin Dir.d0 Dir.d1
  IO.println s!"  Vacuum Plaquette U_01(0) : {repr vacP}"
  IO.println s!"  Vacuum Plaquette Action S_P : {vacAct} (minimum energy state)"

  -- Fluctuating gauge link at link (origin, d0)
  let excitedConfig : GaugeConfig := fun l =>
    if l == ⟨origin, Dir.d0⟩ then Z2.minusOne else Z2.plusOne
  let excP := plaquette excitedConfig origin Dir.d0 Dir.d1
  let excAct := plaquetteAction excitedConfig origin Dir.d0 Dir.d1
  IO.println s!"  Excited Plaquette U_01(0): {repr excP}"
  IO.println s!"  Excited Plaquette Action S_P: {excAct} (positive excitation energy)"

  IO.println "\n[+] All theorems verified at build-time with the Lean 4 kernel."
  IO.println "=========================================================="

-- end of file: leanasm/Main.lean
