In `openai/math` (Family `003`), the Lean 4 workspace lives under the `lean/` subdirectory. The files inside `lean/ComparatorChallenges/` contain only the unproved reference theorem signatures ending in `sorry` against standard Mathlib definitions, while the paired `.json` manifests point `Comparator` to the corresponding proved solution modules.

---

### 1. Exact Challenge Signatures in `openai/math`

Before running `lake build`, inspect the two challenge declarations directly:

* **`lean/ComparatorChallenges/QuasiRiemannHypothesis.lean`**:
```lean
import Mathlib

namespace OAI

theorem riemannZeta_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  sorry

end OAI

```


* **`lean/ComparatorChallenges/DirichletSevenEighths.lean`**:
```lean
import Mathlib

namespace OAI
namespace DirichletCharacter
open scoped _root_.DirichletCharacter

theorem LFunction_ne_zero_of_seven_eighths_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

end DirichletCharacter
end OAI

```



Both challenges rely directly on Mathlib's built-in `riemannZeta` and `DirichletCharacter.LFunction` without custom wrapper definitions.

---

### 2. Step-by-Step Commands to Clone, Inspect, Audit Axioms, and Run `Comparator`

Note that `openai/math` contains 700+ manuscripts and PDFs alongside `lean/`. If you only want the Lean 4 development without downloading every manuscript PDF, you can use a sparse checkout or full clone, apply the repo's dependency patches via `lake update`, and pull precompiled Mathlib `.olean` files.

1. **Clone openai/math and inspect the challenge files and JSON configs:** Uses elan to switch to the repository's pinned Lean 4.34.1 toolchain and fetches precompiled Mathlib .oleans.
```bash
mkdir -p ~/src/openai-lean && cd ~/src/openai-lean
git clone https://github.com/openai/math.git
cd math/lean

# Inspect the challenge statements and their paired JSON solution mappings
cat ComparatorChallenges/QuasiRiemannHypothesis.lean
cat ComparatorChallenges/QuasiRiemannHypothesis.json
cat ComparatorChallenges/DirichletSevenEighths.lean
cat ComparatorChallenges/DirichletSevenEighths.json

# Apply the repo's Mathlib compatibility patches and fetch cached .oleans
lake update
lake exe cache get

```


2. **Build the solution modules referenced by the Comparator JSON manifests:** Pin LEAN_NUM_THREADS to your physical core count (e.g., 4) to avoid OOM pressure on analytical modules.
Extract the `solution_module` names from `QuasiRiemannHypothesis.json` and `DirichletSevenEighths.json` and compile just those targets (plus their transitive dependencies) rather than building all 300+ modules in the repository:

```bash
# Read the target solution_module names from the challenge manifests
SOL_QRH=$(python3 -c 'import json; print(json.load(open("ComparatorChallenges/QuasiRiemannHypothesis.json"))["solution_module"])')
SOL_DIR=$(python3 -c 'import json; print(json.load(open("ComparatorChallenges/DirichletSevenEighths.json"))["solution_module"])')
echo "Building: $SOL_QRH and $SOL_DIR"

# Build both solution modules
LEAN_NUM_THREADS=4 lake build "$SOL_QRH" "$SOL_DIR"

```


3. **Run a non-destructive #print axioms and signature check via stdin:** Verifies type equality against Mathlib's riemannZeta / LFunction and checks for sorryAx or trustCompiler.
Pipe a verification snippet into `lake env lean --stdin` so you inspect the fully elaborated types and axiom footprints without modifying any tracked `.lean` files:

```bash
lake env lean --stdin <<EOF
import $SOL_QRH
import $SOL_DIR

#check @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re

#check @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
EOF

```

Confirm that both declarations list strictly `[propext, Classical.choice, Quot.sound]`—with no `sorryAx` or `Lean.ofReduceBool` / `Lean.trustCompiler`.


4. **Execute the Comparator external-kernel checks:** Requires comparator, landrun, and lean4export on PATH.
Run `comparator` inside `lake env` against both JSON manifests. `Comparator` exports the environment closure (~120,000+ declarations from Lean core and Mathlib through `OAI.NumberTheory`), replays typechecking in a network-isolated `landrun` sandbox, and verifies byte-for-byte signature match against the `sorry` challenge files:

```bash
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
lake env comparator ComparatorChallenges/DirichletSevenEighths.json

```


---

### 3. Optional: Enabling Second-Kernel (`nanoda`) Replay

Some JSON configurations in `openai/math/lean/ComparatorChallenges/` leave the external Rust typechecker (`nanoda_bin`) disabled by default (`"enable_nanoda": false`) so users without `nanoda_bin` installed can still run `comparator`. If you have `nanoda_bin` built and on your `PATH`, you can test a temporary copy of the config with `"enable_nanoda": true` in `/tmp` to verify the entire ~122,700-declaration closure against an independent Rust kernel:

```bash
python3 -c '
import json
cfg = json.load(open("ComparatorChallenges/QuasiRiemannHypothesis.json"))
cfg["enable_nanoda"] = True
json.dump(cfg, open("/tmp/QuasiRiemannHypothesis_nanoda.json", "w"), indent=2)
'
lake env comparator /tmp/QuasiRiemannHypothesis_nanoda.json

```

For a walkthrough of the `openai/math` repository layout, its Lean `ComparatorChallenges` directory, and how the Quasi-Riemann Hypothesis files are organized, see [OpenAI's Math Breakthrough Has a Problem](https://www.youtube.com/watch?v=NCo8yFuc18w).
