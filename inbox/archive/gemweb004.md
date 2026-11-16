Between August and November 2026, OpenAI released several major Lean 4 formalization packages alongside independent verification suites (`Comparator` challenges, `landrun` sandboxing, `lean4export`, and `nanoda_bin`). Note that because each drop pins a different Lean 4 toolchain (`v4.32.0` vs. `v4.34.0-rc2` vs. the October/November 2026 Yang–Mills package), `elan` will automatically download and switch toolchains per directory without colliding.

---

### 1. The OpenAI Lean 4 Drops at a Glance

| Drop & Repository | Release Date | Pinned Toolchain | Key Formalized Targets & Structure |
| --- | --- | --- | --- |
| **`openai/ten-proofs`**<br>

<br>*(Ten Advances in Math & TCS)* | Aug 1, 2026 | `leanprover/lean4:v4.32.0` | 10 standalone modules (`SpherePacking.lean`, `NonSoficGroup.lean`, `ConnesRigidity.lean`, `MulticolorTriangleRamsey.lean` for Erdős #183, `CompactnessAndDegeneracy.lean` for Erdős #146 & #180, etc.) + `ComparatorChallenges/`. |
| **`openai/NavierStokesAndEuler`**<br>

<br>*(3D Blowup Certificates)* | Sep 8, 2026 | `leanprover/lean4:v4.34.0-rc2` | Forced 3D Navier–Stokes blowup on $\mathbb{R}^3$ and $\mathbb{R}^3/\mathbb{Z}^3$ (`NavierStokes/ComparatorSolution.lean`) and unforced 3D Euler singularity (`Euler/Solution.lean`), cross-checked against Formal Conjectures definitions. |
| **`yang-mills-group/OpenAI-YM-20261028`**<br>

<br>& **`yang-mills-group/YM`** | Oct 28 / Nov 10, 2026 | Pinned per package (`verification/tool-pins.json`) | 4D continuum pure Yang–Mills QFT scaling limit from Wilson lattice gauge theory (`YangMills.jointExistence`, `YMReview.Acceptance.combined_acceptance`) with automated `scripts/verify.py` replay. |
| **FrontierMath Erdős Disproofs**<br>

<br>*(e.g., `tadamcz/erdos1`, `tadamcz/erdos548`)* | Sep 2026 | Mathlib-pinned per repo | Autonomous resolutions found by pre-release GPT-6 Astra (`Challenge.lean` vs. `Solution.lean` verified via Comparator). |

---

### 2. End-to-End Verification Workflow (Starting with `openai/ten-proofs` & `NavierStokesAndEuler`)

Rather than building every multi-hour target globally (for example, a full clean rebuild of `NavierStokes` + `Euler` can run over 11,400 Lake jobs), fetch precompiled Mathlib `.olean` caches first, target single modules, and verify against the `ComparatorChallenges/` specifications.

1. **Clone and build openai/ten-proofs on a single target module:** Uses elan to auto-fetch Lean 4.32.0; build a single fast module like Erdős #183 before running build All.
```bash
mkdir -p ~/src/openai-lean && cd ~/src/openai-lean
git clone https://github.com/openai/ten-proofs.git
cd ten-proofs

# Fetch precompiled Mathlib .oleans so you don't recompile Mathlib from source
lake exe cache get

# Build a single self-contained module first (e.g., Erdős #183 multicolor triangle Ramsey)
lake build MulticolorTriangleRamsey

```


2. **Audit axioms and check for hidden sorry or native_decide shortcuts:** Confirms reliance solely on Lean's three standard foundational axioms.
Create a temporary scratch check (without polluting tracked files) using `lake env lean --stdin` so you inspect the exact kernel type and axiom footprint of the target declaration:

```bash
lake env lean --stdin <<'EOF'
import MulticolorTriangleRamsey
#check @MulticolorTriangleRamsey.erdos_183
#print axioms MulticolorTriangleRamsey.erdos_183
EOF

```

Verify that `#print axioms` prints strictly `[propext, Classical.choice, Quot.sound]` with no `sorryAx` or `Lean.ofReduceBool` (`native_decide`). Note that `grep -rn "sorry" .` will match the 42 intentional `sorry` placeholders inside `ComparatorChallenges/`—those are the unproved reference theorem statements that `Comparator` checks the solution types against.


3. **Run the Comparator challenge checker:** Requires landrun (Linux sandboxing), lean4export, and nanoda_bin on PATH.
`Comparator` exports the environment via `lean4export`, replays typechecking inside an independent external kernel (`nanoda_bin`) sandboxed with `landrun`, and verifies that the proved theorem's type matches the challenge declaration byte-for-byte:

```bash
# Run Comparator on the Erdős #183 challenge config inside ten-proofs
lake exe comparator ComparatorChallenges/I_MulticolorTriangleRamsey.json

```


4. **Clone and verify openai/NavierStokesAndEuler:** Pin LEAN_NUM_THREADS to your physical core count (e.g., 4) to prevent OOM thrashing on large PDE files.
```bash
cd ~/src/openai-lean
git clone https://github.com/openai/NavierStokesAndEuler.git
cd NavierStokesAndEuler

# Auto-switches to leanprover/lean4:v4.34.0-rc2 via lean-toolchain
lake exe cache get

# Build the statement/comparator definitions first (~8,764 jobs) before full solution modules
LEAN_NUM_THREADS=4 lake build NavierStokes.ComparatorDefinitions ComparatorChallenges.NavierStokes

# Build the Euler blowup solution and run Comparator
LEAN_NUM_THREADS=4 lake build Euler
lake exe comparator ComparatorChallenges/Euler.json

```


5. **Run the November 2026 Yang–Mills verification harness:** Includes built-in SHA-256 hash auditing, negative control tests, and Comparator replay.
The `yang-mills-group/YM` repository packages OpenAI's October 28, 2026 submission alongside an end-to-end verification script (`scripts/verify.py`) that checks input hashes, runs four negative controls, and replays `Comparator` on `YangMills.jointExistence`:

```bash
cd ~/src/openai-lean
git clone https://github.com/yang-mills-group/YM.git
cd YM/submissions/openai-20261028

# 1. Verify SHA-256 integrity of original submission bytes and upstream OS definitions
python3 scripts/verify.py integrity

# 2. Execute full build, axiom audit, negative controls, and Comparator replay
python3 scripts/verify.py all

```


---

### 3. Practical Caveats When Inspecting These Drops

* **Resource & RAM Budgeting:** While `ten-proofs` modules compile quickly once `lake exe cache get` finishes, `NavierStokesAndEuler` and `OpenAI-YM-20261028` elaborate deep analysis hierarchies. On a 12–16 GB RAM workstation, restrict `LEAN_NUM_THREADS=2` or `4` (and ensure swap is active) so parallel `lean` worker processes do not get killed by the OOM killer during peak tactic elaboration.
* **Statement Alignment vs. Kernel Validity:** `Comparator` guarantees that `Solution.lean` proves the exact type written in `Challenge.lean` without extra axioms. However, community audits (such as the DIU OS and structural audits on `NavierStokesAndEuler` and the Yang–Mills group's November 10 assessment) emphasize reading the `ComparatorDefinitions` file directly: for example, in `NavierStokesAndEuler`, Clay Statement (C) is proved via manufactured residual forcing with $u_0 \equiv 0$, and the Yang–Mills proof constructs the continuum Wightman QFT scaling limit without establishing uniqueness of the infinite-volume limit or a positive mass gap.
