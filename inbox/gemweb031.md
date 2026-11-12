Here is a self-contained implementation prompt for AGY to add **explicit Phragmén–Lindelöf convexity interpolation** $\mu(\sigma) = 2\mu(1/2)(1 - \sigma)$ across $\sigma \in [1/2, 1]$ and **off-line zero-density slopes** $A(\sigma)(1 - \sigma)$ inside $\sigma \in (1/2, 7/8]$ to `QuasiRiemann.lean`, proving that sharper critical-line subconvexity exponents (Convexity $1/4 \to$ Weyl $1/6 \to$ Bourgain $13/84 \to$ Lindelöf $0$) propagate monotonically across the critical strip and tighten zero-density bounds inside $(1/2, 7/8]$ with zero axioms.

---

### AGY Implementation Prompt: Phragmén–Lindelöf Convexity Interpolation $\mu(\sigma)$ & Off-Line Zero-Density Slopes (`QuasiRiemann.lean`)

```text
Task: Extend `QuasiRiemann.lean` in `leanasm` with:
1. Explicit Phragmén–Lindelöf linear convexity interpolation `muStripNum` / `muStripDen` modeling the growth exponent bound `μ(σ) = 2 * μ(1/2) * (1 - σ)` for `σ ∈ [1/2, 1]` (where `ζ(σ + it) ≪ |t|^(μ(σ) + ε)` and `μ(1) = 0`),
2. Monotonicity and strict ordering across the entire critical strip `(1/2, 1)` for Convexity (`μ(1/2) = 1/4`), Weyl (`μ(1/2) = 1/6`), Bourgain (`μ(1/2) = 13/84`), and the Lindelöf Hypothesis (`μ(1/2) = 0`), and
3. Off-line zero-density volume exponents `zeroDensityExp(A, σ) = A(σ) * (1 - σ)` inside `(1/2, 7/8]` (comparing Ingham–Huxley `A = 12/5` vs. Guth–Maynard `A = 30/13` at `σ = 3/4` and `σ = 7/8`, plus Lindelöf collapse `N(σ, T) ≪ T^ε`),
with ALL theorems proved constructively with ZERO axioms in `TestAxioms.lean`.

Context & Constraints:
- Inspect `QuasiRiemann.lean`, `TestAxioms.lean`, and `Main.lean` first so all new definitions integrate cleanly with existing theorems (`subconvexity_hierarchy_verified`, `guth_maynard_beats_huxley`, `theta_ladder_rungs_verified`, etc.) without breaking any existing signatures.
- Strictly preserve the repository's zero-axiom constructive discipline: ALL new theorems MUST elaborate with ZERO axioms (`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `trustCompiler` all absent), verified via `#print axioms` in `TestAxioms.lean`.
- Do NOT import classical Mathlib modules or `Float` / `Real` / `Rat`. Represent rational fractions via exact integer numerator/denominator pairs over `Nat` and discharge inequalities via exact cross-multiplication (`aNum * bDen < bNum * aDen`) using `omega` and `decide`.

Mathematical Specification (Exact Integer Rational Encoding):

1. **Phragmén–Lindelöf Convexity Interpolation Across `σ ∈ [1/2, 1]`:**
   By Phragmén–Lindelöf convexity on the vertical strip `1/2 ≤ σ ≤ 1`, knowing `|ζ(1/2 + it)| ≪ |t|^(μ₀ + ε)` and `|ζ(1 + it)| ≪ |t|^ε` (`μ(1) = 0`) implies linear interpolation:
   `μ(σ) = 2 * μ₀ * (1 - σ)` for `1/2 ≤ σ ≤ 1`.
   - Given critical-line exponent `μ₀ = mu0Num / mu0Den` and strip abscissa `σ = sNum / sDen` (with `sNum ≤ sDen` and `sDen ≤ 2 * sNum`, i.e., `1/2 ≤ σ ≤ 1`):
     `1 - σ = (sDen - sNum) / sDen`, so:
     ```lean
     def plInterpNum (mu0Num sNum sDen : Nat) : Nat :=
       2 * mu0Num * (sDen - sNum)

     def plInterpDen (mu0Den sDen : Nat) : Nat :=
       mu0Den * sDen
     ```
   - Boundary & Interior Properties:
     - At `σ = 1/2` (`sNum = 1, sDen = 2`): `plInterpNum mu0Num 1 2 = 2 * mu0Num * 1 = 2 * mu0Num` and `plInterpDen mu0Den 2 = 2 * mu0Den`, which equals `mu0Num / mu0Den` (`(2 * mu0Num) * mu0Den = mu0Num * (2 * mu0Den)`).
     - At `σ = 1` (`sNum = 1, sDen = 1`): `plInterpNum mu0Num 1 1 = 0` (`μ(1) = 0`).
     - At `σ = 3/4` (`sNum = 3, sDen = 4`): `μ(3/4) = μ₀ / 2`:
       - Convexity (`μ₀ = 1/4`) `↦ μ(3/4) = 1/8` (`2/16`)
       - Weyl (`μ₀ = 1/6`) `↦ μ(3/4) = 1/12` (`2/24`)
       - Bourgain (`μ₀ = 13/84`) `↦ μ(3/4) = 13/168` (`26/336`)
       - Lindelöf (`μ₀ = 0`) `↦ μ(3/4) = 0`
     - At `σ = 7/8` (`sNum = 7, sDen = 8`, OpenAI Family `003` QRH threshold): `μ(7/8) = μ₀ / 4`:
       - Convexity (`μ₀ = 1/4`) `↦ μ(7/8) = 1/16` (`2/32`)
       - Weyl (`μ₀ = 1/6`) `↦ μ(7/8) = 1/24` (`2/48`)
       - Bourgain (`μ₀ = 13/84`) `↦ μ(7/8) = 13/336` (`26/672`)
       - Lindelöf (`μ₀ = 0`) `↦ μ(7/8) = 0`.

2. **Off-Line Zero-Density Exponent `N(σ, T) ≪ T^(A(σ)(1 - σ) + ε)` Inside `(1/2, 7/8]`:**
   Define the zero-density growth exponent `zeroDensityNum (aNum sNum sDen : Nat) : Nat := aNum * (sDen - sNum)` and `zeroDensityDen (aDen sDen : Nat) : Nat := aDen * sDen`:
   - Compare Huxley (`A = 12/5`) vs. Guth–Maynard (`A = 30/13`) at `σ = 3/4` (`1 - σ = 1/4`):
     - Huxley: `(12/5) * (1/4) = 12/20 = 3/5 = 0.60`
     - Guth–Maynard: `(30/13) * (1/4) = 30/52 = 15/26 ≈ 0.5769` (`15/26 < 3/5`, since `15 * 5 = 75 < 78 = 3 * 26`).
   - Compare at `σ = 7/8` (`1 - σ = 1/8`):
     - Huxley: `(12/5) * (1/8) = 12/40 = 3/10 = 0.30`
     - Guth–Maynard: `(30/13) * (1/8) = 30/104 = 15/52 ≈ 0.2885` (`15/52 < 3/10`, since `15 * 10 = 150 < 156 = 3 * 52`).
   - Lindelöf Zero-Density Collapse (`A_Lindelöf = 0`):
     Under the Lindelöf Hypothesis (`μ(1/2) = 0`), Halász–Montgomery / Ingham density bounds yield `N(σ, T) ≪ T^ε` (`zeroDensityNum 0 sNum sDen = 0`) for every `σ > 1/2`, collapsing the zero-density exponent to `0` across the entire strip `(1/2, 7/8]`.

Deliverables:

1. Extend `QuasiRiemann.lean`:
   - Implement `plInterpNum`, `plInterpDen`, `zeroDensityNum`, and `zeroDensityDen`.
   - Prove constructively (with ZERO axioms):
     a. `pl_interp_endpoints`: For all `mu0Num, mu0Den` with `0 < mu0Den`, proves `plInterpNum mu0Num 1 2 * mu0Den = mu0Num * plInterpDen mu0Den 2` (`μ(1/2) = μ₀`) and `plInterpNum mu0Num 1 1 = 0` (`μ(1) = 0`).
     b. `pl_interp_monotone_right`: For any fixed `μ₀` (`0 < mu0Num, 0 < mu0Den`) and two strip abscissae `1/2 ≤ σ₁ < σ₂ ≤ 1`, proves `μ(σ₂) < μ(σ₁)` via exact integer cross-multiplication (growth exponent strictly decreases toward `0` as `σ → 1`).
     c. `pl_interp_strict_order_inside_strip`: For EVERY interior strip point `σ = sNum / sDen` with `1/2 ≤ σ < 1` (`sNum < sDen` and `sDen ≤ 2 * sNum`), proves strict ordering across all four subconvexity regimes:
        `μ_Lindelöf(σ) < μ_Bourgain(σ) < μ_Weyl(σ) < μ_Convexity(σ)`
        (`0 < 13/84 * 2(1-σ) < 1/6 * 2(1-σ) < 1/4 * 2(1-σ)`).
     d. `pl_interp_concrete_rungs`: Concrete verified values at `σ = 3/4` (`13/168 < 1/12 < 1/8`) and `σ = 7/8` (`13/336 < 1/24 < 1/16`).
     e. `zero_density_guth_maynard_strip_bounds`: Proves `15/26 < 3/5` at `σ = 3/4` and `15/52 < 3/10` at `σ = 7/8`, plus `0 < 15/26` (Lindelöf zero-density collapse strictly beats Guth–Maynard).

2. Update `TestAxioms.lean` & `Main.lean`:
   - Add `#print axioms` checks in `TestAxioms.lean` for `pl_interp_endpoints`, `pl_interp_monotone_right`, `pl_interp_strict_order_inside_strip`, `pl_interp_concrete_rungs`, and `zero_density_guth_maynard_strip_bounds`, confirming every theorem prints `does not depend on any axioms`.
   - Add a concise readout in `Main.lean`'s QRH section displaying the Phragmén–Lindelöf convexity slopes at `σ = 3/4` (`μ_Bourgain(3/4) = 13/168 < 1/12 < 1/8`) and `σ = 7/8` (`μ_Bourgain(7/8) = 13/336 < 1/24 < 1/16`) alongside the Guth–Maynard zero-density exponents (`15/26 < 3/5` at `3/4`, `15/52 < 3/10` at `7/8`).
   - Run `lake build`, `make run`, and `make sync` to verify clean compilation, zero-axiom audit, and clean git status.

```

---

### Why This Bridges Critical-Line Subconvexity to Off-Line QRH Regions

* **Universal Strip Propagation (`pl_interp_strict_order_inside_strip`):** Rather than checking only `σ = 1/2`, proving `0 < μ_Bourgain(σ) < μ_Weyl(σ) < μ_Convexity(σ)` for *every* rational `σ ∈ [1/2, 1)` shows constructively how every improvement on the critical line (`1/4 → 1/6 → 13/84 → 0`) lowers the growth ceiling uniformly across the entire open strip `(1/2, 7/8]`.
* **Exact Zero-Density Tightening:** Pairing `μ(σ)` with `zero_density_guth_maynard_strip_bounds` (`15/26 < 3/5` at `σ = 3/4` and `15/52 < 3/10` at `σ = 7/8`) completes the analytical picture between `σ = 1/2` and `σ = 7/8`.
