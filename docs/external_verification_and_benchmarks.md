<!-- Path: leanasm/docs/external_verification_and_benchmarks.md -->
<!-- Max Column: 80 Columns -->

# External Verification Suites & Frontier Math Benchmarks

## Overview

Based on ingested research memos (`inbox/gemweb001.md`, `inbox/gemweb004.md`),
this document summarizes external kernel checkers, challenge comparison
standards, and milestone benchmark suites (such as OpenAI's 2026 formalization
drops and DeepMind's `formal-conjectures`).

## Key Verification Stack

| Layer | Tool | Role |
| :--- | :--- | :--- |
| **Toolchain Manager** | `elan` | Auto-switches pinned Lean versions per repository without conflict. |
| **Build Engine** | `lake` | Compiles modules and retrieves precompiled Mathlib `.olean` caches. |
| **Axiom Audit** | `#print axioms` | Verifies adherence to standard axioms (`propext`, `Classical.choice`, `Quot.sound`). |
| **Environment Exporter** | `lean4export` | Dumps elaborated Lean 4 environments for external checkers. |
| **External Kernel** | `nanoda_bin` / `comparator` | Replays proofs in an independent kernel isolated with `landrun`. |

## Reference Repositories & Formalization Drops (2026)

- **`openai/ten-proofs`** (`leanprover/lean4:v4.32.0`):
  10 mathematical and TCS milestones (e.g., Erdős #183 multicolor triangle
  Ramsey, Erdős #146 & #180, Sphere Packing) with `ComparatorChallenges/`.
- **`openai/NavierStokesAndEuler`** (`leanprover/lean4:v4.34.0-rc2`):
  3D Navier–Stokes and Euler blowup certificates.
- **`yang-mills-group/YM`** (Oct/Nov 2026):
  4D continuum pure Yang–Mills QFT scaling limit formalization with automated
  hash auditing and negative control replay (`scripts/verify.py`).
- **`google-deepmind/formal-conjectures`**:
  ~4,900 theorem statements, open conjectures, and frozen benchmark targets
  (`FC100OpenSet1.lean`, `FC100SolvedSet1.lean`).

## Verification Hygiene Checklist

1. **Precompiled Caches**: Always run `lake exe cache get` before compiling
   Mathlib-dependent trees to avoid compiling tens of thousands of files from scratch.
2. **Resource Constraints**: Limit concurrency with `LEAN_NUM_THREADS=2` or `4`
   during deep analysis elaboration to prevent OOM killer termination.
3. **Challenge Type Matching**: When evaluating provers, check that generated
   types match challenge declarations byte-for-byte using external checkers
   (`Comparator`) and that no `sorryAx` or `native_decide` escapes are present.

<!-- end of file: leanasm/docs/external_verification_and_benchmarks.md -->

---

## 4. OpenAI Family 003: Quasi-Riemann Hypothesis (QRH, Oct 6, 2026)

From `inbox/gemweb009.md` and `inbox/gemweb010.md`:
In `openai/math` under `lean/ComparatorChallenges/`, the Lean 4 challenges formalize
the $\theta = 7/8$ zero-free half-plane across three layers of $L$-functions:

1. **`QuasiRiemannHypothesis.lean`**:
   $$\forall s \in \mathbb{C}, \quad \operatorname{Re}(s) > \frac{7}{8} \land s \ne 1 \implies \zeta(s) \ne 0$$
   By functional equation reflection $\rho \leftrightarrow 1 - \bar{\rho}$, all
   non-trivial zeros lie in the symmetric strip $\operatorname{Re}(\rho) \in [1/8, 7/8]$,
   reducing the critical strip width by 75%.
2. **`DirichletSevenEighths.lean` & `SiegelZeros.lean`**:
   Generalizes $\theta = 7/8$ uniformly over all Dirichlet characters $\chi \pmod q$.
   Because $7/8$ is independent of the modulus $q$, it completely excludes real
   Siegel zeros in $\beta \in (7/8, 1)$.
3. **`HeckeSevenEighths.lean`**:
   Extends the zero-free region to finite-order Hecke $L$-functions over the
   Eisenstein field $\mathbb{Q}(\sqrt{-3})$.

### Reproduction Commands:
```bash
cd ~/src/openai-lean/math/lean
lake update
lake exe cache get
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
lake env comparator ComparatorChallenges/DirichletSevenEighths.json
```

<!-- end of file: leanasm/docs/external_verification_and_benchmarks.md -->
