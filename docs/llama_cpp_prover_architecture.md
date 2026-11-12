<!-- Path: leanasm/docs/llama_cpp_prover_architecture.md -->
<!-- Max Column: 80 Columns -->

# llama.cpp Prover Integration Architecture

## Overview

This document specifies the architecture for pairing local quantized neural
prover models (`llama.cpp` / `llama-server`) with a stateful Lean 4 interactive
environment (`leanprover-community/repl` or `Pantograph`) for automated
theorem proving, verified assembly generation, and tactic search.

## Process Topology

```text
+------------------------------------+      HTTP POST /v1/chat/completions
|   Python Proof-Search Harness      | -------------------------------------> [ llama-server (GGUF) ]
|   (uv / asyncio / Best-First BFS)  | <-------------------------------------   DeepSeek-Prover-V2-7B
+------------------------------------+      Candidate tactics + logprobs        or Goedel-Prover-V2-8B
           |              ^
    stdin  |              | stdout
  (JSON)   v              | (JSON proofState / goals / errors)
+------------------------------------+
|   lake env /path/to/repl           |  <-- Inherits Lean 4 + Mathlib .oleans
+------------------------------------+
```

## Core Components

### 1. Local GGUF Prover Model (`llama.cpp`)
- **Server**: Run `llama-server` bound strictly to `127.0.0.1:8080`.
- **Target Weights**:
  - `DeepSeek-Prover-V2-7B` (`Q4_K_M` ~4.4GB or `Q8_0` ~7.5GB).
  - `Goedel-Prover-V2-8B` (`Q4_K_M`).
- **Inference Mode**:
  - Low-latency sampling with `--flash-attn on` and pinned thread count.
  - Optional GBNF grammar constraints for valid tactic syntax.

### 2. Stateful Lean 4 REPL
- **`leanprover-community/repl`**:
  - Compiled with the exact toolchain version in `lean-toolchain`.
  - Driven via stdin/stdout JSON lines protocol.
  - Stateful `proofState` handles allow backtracking and tree branching
    without re-elaborating earlier commands.

### 3. Orchestration Harness
- Coordinates best-first search (BFS) over tactic states.
- Rejects tactic candidates that emit elaboration errors.
- Confirms closed goals when `goals` count reaches zero.

### 4. Post-Proof Verification & Axiom Audit
- Splice completed proof back into source `.lean` file.
- Verify via `lake build` and external kernel check (`lake check`).
- Audit axioms using `#print axioms <name>` to ensure only standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) are relied upon, avoiding
  `sorryAx` or unsound escapes.

<!-- end of file: leanasm/docs/llama_cpp_prover_architecture.md -->
