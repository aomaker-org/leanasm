# Repository Issues Digest (aomaker-org/leanasm)

## Issue #9: chore(Makefile): align help text hyphen for build-incremental target
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-13T22:45:14Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/issues/9

### Description

Track low-severity formatting nit noted by Copilot review on PR #7:
- Reference: https://github.com/aomaker-org/leanasm/pull/7#discussion_r4569368613
- Location: `Makefile` line 21 (`@echo "  make build-incremental- Build all modules incrementally; fail if slice incomplete"`)

`make build-incremental` reaches column 24 where `-` is aligned for lines 18–31, leaving no space before `-`. Widen the help column padding across the `help` target lines so all `-` separators have consistent spacing.

---

## Issue #11: feat(minivm): compile F_17 forward & inverse NTT butterflies to MiniVM assembly with zero-axiom soundness
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-13T23:28:47Z
- **Labels**: enhancement
- **URL**: https://github.com/aomaker-org/leanasm/issues/11

### Description

## Goal & Architectural Context
Bridge the high-level modular algebra in `src/LeanAsm/NttArithmetic.lean` (`nttButterfly2`, `inttButterfly2`, `ntt4`, `intt4`) down to concrete opcode sequences in `src/LeanAsm/MiniVM.lean` (`MiniVM.Reg`, `MiniVM.State`, `MiniVM.Instr`, `MiniVM.step`, `MiniVM.runProgram`), proving that emitted `MiniVM` assembly programs preserve the exact $\mathbb{F}_{17}$ NTT algebraic invariants without register clobbering or `Nat` subtraction underflow.

### Existing Codebase Anchors
- **`src/LeanAsm/MiniVM.lean`**: 4-register machine (`Reg.r0`, `Reg.r1`, `Reg.r2`, `Reg.r3`, plus `pc : Nat`) with 7 opcodes (`movImm`, `movReg`, `addReg`, `addImm`, `subReg`, `modImm`, `mulModReg`), evaluated via `MiniVM.step` and `MiniVM.runProgram`. Precedent multi-instruction verified program: `garnerCrtProgram` / `exec_garner_crt_sound`.
- **`src/LeanAsm/NttArithmetic.lean`**: `p = 17`, `invTwo = 9`, `nttButterfly2 (x0 x1 : Nat) (modP := 17)` computing `((x0 + x1) % 17, (x0 + 17 - (x1 % 17)) % 17)`, `inttButterfly2` scaling each output by `invTwo = 9` mod `17`, plus `omega4 = 13`, `invOmega4 = 4`, `invFour = 13`, `ntt4`, `intt4`, and `ntt_butterfly2_sound_all_pairs`.

## Technical Deliverables
1. **Emit Forward & Inverse 2-Point $\mathbb{F}_{17}$ Butterfly Programs (`ntt2AsmF17`, `intt2AsmF17`):**
   - Represent `(a, b)` in `(r0, r1)` using `r2, r3` as non-clobbering scratch registers (same pattern as `garnerCrtProgram`).
   - Implement forward 2-point butterfly: `(a, b) ↦ ((a + b) % 17, (a + 17 - b) % 17)` using explicit `+ 17` bias (`addImm` before `subReg`) so unsigned `Nat` register subtraction (`subReg`) never underflows when `a < b`.
   - Implement inverse 2-point butterfly (`intt2AsmF17`) with modular scaling by `invTwo = 9` via `movImm` + `mulModReg ... 17`.
2. **End-to-End Execution Soundness & Roundtrip Invertibility:**
   - Prove `ntt2AsmF17_sound` and `intt2AsmF17_sound`: for all `a, b < 17` ($17^2 = 289$ states), `MiniVM.runProgram` matches `NttArithmetic.nttButterfly2 a b` and `NttArithmetic.inttButterfly2 a b` on the output registers (and advances `pc` to the expected program length).
   - Prove `intt2_ntt2_asm_F17_roundtrip`: composing `ntt2AsmF17 ++ intt2AsmF17` (or sequential `runProgram`) recovers `(a, b)` across all `a, b < 17`.
3. **(Stretch / Optional) 4-Point $\mathbb{F}_{17}$ NTT Assembly Routine (`ntt4AsmF17` / `intt4AsmF17`):**
   - Compose verified 2-point butterflies with twiddle multiplication ($\omega_4 = 13$ / inverse $4 \bmod 17$, or conjugate choice $4$ / $13 \bmod 17$ with $4^{-1} \equiv 13 \pmod{17}$ as in `ntt4`/`intt4`) to emit and verify a full 4-point $\mathbb{F}_{17}$ NTT/INTT assembly routine.
   - *Design note:* `MiniVM.State` currently provides 4 registers (`r0..r3`), so either in-place 4-lane scheduling without a 5th temporary or extending `MiniVM` (e.g., extra scratch registers / state fields) should be evaluated cleanly without breaking existing `MiniVM` proofs.
4. **Axiom Audit & CLI Integration:**
   - Add `#print axioms` checks for the new theorems in `tests/TestAxioms.lean`.
   - Showcase the verified `MiniVM` NTT assembly execution in `Main.lean`.

## Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` shows only `[propext, Quot.sound]` or `[]`).
- All modified `.lean` files adhere to `<= 120` chars/line with intact `-- Path:` headers and footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.
- Work implemented on a dedicated feature branch and merged via PR.

---

## Issue #16: feat(qrh): constructive Dirichlet L^2 diagonal dominance & explicit de la Vallee Poussin zero-free region
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T00:18:14Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/16

### Description

## Overview

Formalize constructive Dirichlet-polynomial $L^2$ diagonal-dominance bounds and an explicit de la Vallée Poussin asymptotic zero-free region $\sigma > 1 - c_{\text{dvp}} / \ln(t)$ for all $t \ge t_0$ in the `QuasiRiemann` hierarchy, with **zero `Classical.choice`** and **zero `sorryAx`**.

## Architectural & Incremental Build Plan

- Create a dedicated submodule [`src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean`](src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean) in `namespace QuasiRiemann`.
- Import `LeanAsm.QuasiRiemann` inside `AsymptoticZfr.lean` to reuse the existing `QRat` engine (`src/LeanAsm/QuasiRiemann.lean#L2414-L2519`), `lnInterval36` (`#L3741`) / `ln_table_1_to_64_valid` (`#L3784`), `lnInterval72` (`#L4899`), `doubleAngleCosSin72` (`#L5006`), and mollifier regime definitions (`#L703-L779`).
- Import `LeanAsm.QuasiRiemann.AsymptoticZfr` in [`src/LeanAsm.lean`](src/LeanAsm.lean) rather than editing `src/LeanAsm/QuasiRiemann.lean`, avoiding circular imports and preserving the existing 5,336-line `QuasiRiemann.olean` cache so `make build-incremental` compiles the new module in seconds.

## Technical Deliverables

### 1. Constructive Dyadic-Octave Logarithm Envelope (`octaveLnUpper36`)
- Bound $\ln(t)$ constructively for any integer height $t \ge 2$ via its binary bit-length / octave bracket $2^k \le t < 2^{k+1}$ (`Nat.log2 t = k`), giving:
  $$\ln(t) \le (k + 1) \cdot \ln(2)$$
  backed by `(lnInterval36 2).hi` from `src/LeanAsm/QuasiRiemann.lean` (certified by `ln_table_1_to_64_valid`), with no `Real.log` or `Float`.
- Prove positivity, monotonicity in $t$, and exact `QRat` cross-multiplication compatibility for `(Nat.log2 t + 1)` octave bounds.

### 2. Explicit de la Vallée Poussin Asymptotic Zero-Free Region
- **3–4–1 Trigonometric Positivity & Log-Derivative Inequality:**
  - Formalize the algebraic identity `3 + 4 c + (2 c^2 - 1) = 2 * (1 + c)^2 ≥ 0` over `Int` and `QRat` (`|c| ≤ 1`, representing $\cos \theta$ and $\cos 2\theta = 2\cos^2\theta - 1$, aligning with `doubleAngleCosSin72`), and lift to the non-negative Dirichlet cosine sum inequality for $3 \left(-\frac{\zeta'}{\zeta}(\sigma_0)\right) + 4 \operatorname{Re}\left(-\frac{\zeta'}{\zeta}(\sigma_0 + i t)\right) + \operatorname{Re}\left(-\frac{\zeta'}{\zeta}(\sigma_0 + 2 i t)\right) \ge 0$ ($\sigma_0 > 1$).
- **Constructive Zero-Repulsion & Explicit `c_dvp` Derivation:**
  - Combine the pole upper bound $-\frac{\zeta'}{\zeta}(1 + \delta) \le \frac{1}{\delta} + C_{\text{pole}}$, the $2t$-growth bound $\operatorname{Re}\left(-\frac{\zeta'}{\zeta}(1 + \delta + 2 i t)\right) \le A_2 \ln(2t)$, and the zero-repulsion bound $\operatorname{Re}\left(-\frac{\zeta'}{\zeta}(1 + \delta + i t)\right) \le -\frac{1}{1 + \delta - \beta} + A_1 \ln(t)$ at a hypothetical zero $\beta + i t$.
  - Derive an explicit positive rational constant `c_dvp : QRat` (e.g. `1/56` or `1/60`) and height threshold `t_0 ≥ 4` proving `dvp_asymptotic_zero_free_region`: for every $t \ge t_0$, any zero $\beta + i t$ satisfies:
    $$\beta \le 1 - \frac{c_{\text{dvp}}}{(\text{Nat.log2 } t + 1) \cdot \ln_2^{\text{hi}}},$$
    certifying an unconditional zero-free region extending as $t \to \infty$.

### 3. Constructive Dirichlet-Polynomial $L^2$ Diagonal-Dominance & Montgomery–Vaughan Sandwich
- Formalize finite Dirichlet polynomials $D(t) = \sum_{n=1}^N a_n n^{-i t}$ over `QRat` coefficients with diagonal energy `dirichletDiagEnergy N a := ∑_{n=1}^N a_n^2`.
- Prove the elementary rational logarithmic spacing bound:
  - `dirichlet_log_ratio_lower`: `∀ m n, 1 ≤ m → m < n → (n - m : QRat) / n ≤ ln(n/m)` (via rational/harmonic comparison `(n - m) / n ≤ ...` compatible with `lnInterval36` / `QRat`), and
  - `dirichlet_offdiag_sum_bound`: pairwise off-diagonal interference envelope $\sum_{m \ne n} \frac{|a_m a_n|}{|\ln(n/m)|}$.
- Prove `dirichlet_l2_diagonal_dominance_sandwich`: for any window length $H \ge 4 N^2$, any certified mean-square approximation satisfying the Montgomery–Vaughan off-diagonal envelope obeys:
  $$\frac{1}{2} \sum_{n=1}^N a_n^2 \le M_2(D; T, H) \le \frac{3}{2} \sum_{n=1}^N a_n^2$$
  over `QRat`, and instantiate it explicitly on both:
  1. the unweighted zeta polynomial ($a_n = 1$), and
  2. alternating Möbius-style mollifier coefficients ($a_n \in \{-1, 0, 1\}$).

### 4. Axiom Audit & CLI Output
- Add `#print axioms` checks in [`tests/TestAxioms.lean`](tests/TestAxioms.lean) for all new `QuasiRiemann` theorems in `AsymptoticZfr.lean`.
- Update [`Main.lean`](Main.lean#L78-L151) Part 5 output to report the explicit de la Vallée Poussin constant `c_dvp` and the certified Dirichlet $L^2$ diagonal-dominance sandwich bounds.

## Acceptance Criteria
- [ ] Zero `Classical.choice` and zero `sorryAx` across all new theorems (at most `[propext, Quot.sound]` or `[]`).
- [ ] All modified/created `.lean` files adhere to `<= 120` chars per line (target `<= 100` in `AsymptoticZfr.lean`) with `-- Path:` headers and `-- end of file:` footers.
- [ ] `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #17: refactor(qrh): extract UltraDeep72.lean submodule and derive twoPiInterval72 from PiChudnovsky
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T00:30:43Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/17

### Description

## Motivation & Architectural Context

Part 15 of [`src/LeanAsm/QuasiRiemann.lean`](src/LeanAsm/QuasiRiemann.lean#L4328-L5336) currently embeds ~1,008 lines of 72-digit interval arithmetic (`ScaledInterval72`), 72-digit prime-table synthesis (`ln 1..128`), and the `N = 128` 2D zero-free rectangle sweeper down to `σ = 0.501` inside a single 5,336-line module. Extracting Part 15 into a dedicated `.olean`-checkpointed submodule `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` will:

1. Significantly reduce incremental `.olean` build time and peak RSS memory pressure on both `core12` and `core11`.
2. Close the end-to-end formal provenance chain:
   `192-digit CRT-NTT -> Chudnovsky 100-digit pi -> twoPiInterval72 -> σ = 0.501 2D QRH rectangles & Collatz spectral beat bounds`
   by replacing the duplicate Machin `rawArctan72` series with `LeanAsm.PiChudnovsky`'s already-certified `10^105` $\pi$ bracket (`piLower105`, `piUpper105`, `pi_105_bracket_valid`).

---

## Codebase Integration Points

- **Source Part 15:** `src/LeanAsm/QuasiRiemann.lean` (lines 4328–5336): `natMul192ViaCrtNtt`, `intMul192ViaCrtNtt`, `ScaledInterval72`, `mulInterval72`, `mulInterval72_sound`, `artanhTaylor72`, `rawArctan72`, `arctanTaylor72`, `twoPiInterval72`, `lnInterval72`, `ln_table_1_to_128_valid`, `taylorExpNegInterval72`, `taylorCosInterval72`, `taylorSinInterval72`, `n128PowNegUpperFromSigma72`, `n128_pow_neg_sigma72_sound`, `eulerMaclaurinB2TailRect2D_N128`, `buildRect2DCertN128`, `buildRect2DCertN128_implies_valid`, `sweepRectangles2DN128`, `sweepRectangles2DN128_all_valid`, `ultra_deep_rects_down_to_0501_certified`.
- **Shared Helpers in `QuasiRiemann.lean`:** Part 15 currently relies on file-local definitions/lemmas in `QuasiRiemann.lean` (such as `ediv_mul_le_self`, `floorDiv_le_ceilDiv_gen`, `int_mul_sign_cases`, `corner_bounds`, `foldNatStep`, `EntriesTree`, `isValidRectTreeN64`, `isValidRectTreeN64_sound`, `DirichletRect2DCert`, `IsValidRect2DCert`, `totalCertifiedAreaScaled12`, `ScaledInterval`). Expose/unprivatize or relocate shared helpers cleanly so `UltraDeep72.lean` can `import LeanAsm.QuasiRiemann` without circular imports.
- **Pi Source:** `src/LeanAsm/PiChudnovsky.lean` (`piLower105`, `piUpper105`, `pi_105_bracket_valid`; note `PiChudnovsky` does NOT import `QuasiRiemann`, so importing `LeanAsm.PiChudnovsky` + `LeanAsm.QuasiRiemann` in `UltraDeep72.lean` is acyclic).
- **Downstream Callers:**
  - `src/LeanAsm/CollatzQrhBridge.lean` (`ScaledInterval72`, `lnInterval72`, `twoPiInterval72`, `linearFormLn2Ln3Interval72`, `collatzBeatPeriodUpper72`, `collatz_qrh_phase_beat_72_verified` — will need `import LeanAsm.QuasiRiemann.UltraDeep72` unless re-exported, and verify all `decide +kernel` checks remain fast).
  - `src/LeanAsm.lean` (export `LeanAsm.QuasiRiemann.UltraDeep72`).
  - `tests/TestAxioms.lean` (Part 14 & Part 16 axiom checks around lines 284–312).
  - `Main.lean` (lines 44, 51–56, 143–150 referencing `QuasiRiemann.lnInterval72`, `sweepRectangles2DN128`, `ScaledInterval72`).

---

## Technical Deliverables

### 1. Extract `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- Create `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` in `namespace QuasiRiemann` containing the extracted Part 15 definitions and theorems (`ScaledInterval72`, `mulInterval72`, `artanhTaylor72`, `lnInterval72`, `ln_table_1_to_128_valid`, `n128PowNegUpperFromSigma72`, `eulerMaclaurinB2TailRect2D_N128`, `buildRect2DCertN128`, `sweepRectangles2DN128`, `ultra_deep_rects_down_to_0501_certified`, etc.).
- Export `LeanAsm.QuasiRiemann.UltraDeep72` from `src/LeanAsm.lean`.
- Update downstream imports in `src/LeanAsm/CollatzQrhBridge.lean`, `tests/TestAxioms.lean`, and `Main.lean` cleanly (keeping `namespace QuasiRiemann` so no downstream symbol names or signatures break).
- Remove dead/superseded Machin `rawArctan72` and `arctanTaylor72` code from `QuasiRiemann.lean` / `UltraDeep72.lean`.

### 2. Derive `twoPiInterval72` Directly from `PiChudnovsky`
- Import `LeanAsm.PiChudnovsky` in `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`.
- Define `twoPiInterval72 : ScaledInterval72` (and backing `twoPiRaw72` / `twoPiRaw72Lit` if retained for fast `decide +kernel` reduction) by projecting `[2 * PiChudnovsky.piLower105, 2 * PiChudnovsky.piUpper105]` from `10^105` down to `10^72`:
  - `lo := (2 * PiChudnovsky.piLower105) / 10^33`
  - `hi := (2 * PiChudnovsky.piUpper105 + 10^33 - 1) / 10^33`
- Prove constructively (ZERO `Classical.choice`, ZERO `sorryAx`):
  - `twoPiInterval72_valid : twoPiInterval72.lo ≤ twoPiInterval72.hi`
  - `twoPiInterval72_from_chudnovsky_sound`: exact integer bracketing linking `twoPiInterval72` directly to `PiChudnovsky.pi_105_bracket_valid`, proving:
    - `twoPiInterval72.lo * 10 ^ 33 ≤ 2 * (PiChudnovsky.piLower105 : Int)`
    - `2 * (PiChudnovsky.piUpper105 : Int) ≤ twoPiInterval72.hi * 10 ^ 33`
- Ensure `ultra_deep_rects_down_to_0501_certified` and `CollatzQrhBridge.collatz_qrh_phase_beat_72_verified` verify cleanly against the Chudnovsky-derived `twoPiInterval72`.

### 3. Axiom Audits & CLI Verification
- Add `#print axioms` checks in `tests/TestAxioms.lean` for `QuasiRiemann.twoPiInterval72_valid` and `QuasiRiemann.twoPiInterval72_from_chudnovsky_sound` alongside all migrated `UltraDeep72` theorems (`natMul192ViaCrtNtt_eq_mul`, `mulInterval72_sound`, `ln_table_1_to_128_valid`, `n128_pow_neg_sigma72_sound`, `buildRect2DCertN128_implies_valid`, `sweepRectangles2DN128_all_valid`, `ultra_deep_rects_down_to_0501_certified`), confirming zero `Classical.choice` and zero `sorryAx`.
- Verify `Main.lean` output (including `ultra_deep_rects_down_to_0501_certified` and `CollatzQrhBridge` 72-digit beat bounds) remains intact and passes `make sync`.

---

## Acceptance Criteria
- [ ] **Zero Non-Constructive Axioms:** Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- [ ] **Formatting & Headers:** All `.lean` files adhere to `<= 120` chars per line (keep `<= 100` in submodules following `QuasiRiemann.lean`/`CollatzQrhBridge.lean` style) with intact `-- Path:` headers and `-- end of file:` footers.
- [ ] **Build & Sync Clean:** `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly with zero warnings or errors.


---

## Issue #19: chore: address actionable Copilot review comments from PRs #12, #14, and #18
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T01:33:00Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/19

### Description

## Overview
Audit of Copilot automated PR reviews across PRs #1–#18 on `main` (`6abcc8b`).

Most earlier findings were already resolved in PRs #4, #6, and #10, and several Lean tactic flags in PRs #7, #14, and #15 (`CrtMulBridge.lean:59`, `FiniteFieldRH.lean:436`, `WeilZetaBridge.lean:32,38,66`) are false positives verified as typechecking cleanly by Lean 4 CI. The items below are the **remaining actionable findings** on `main` that should be addressed.

---

## Actionable Items

### 1. Zero-pad 36-digit fractional printout for `ln16` (`PR #18`, `Main.lean:155`)
- **Current behavior:** `Main.lean` prints `{ln16 / 10^36}.{ln16 % 10^36}` directly. While `octaveLnUpper36 16` happens to start its fractional part with `4`, any 36-digit fixed-point value whose fractional remainder has leading zeros would print an ambiguous/incorrect decimal string.
- **Action:** Pad `toString (ln16 % 10^36)` with leading `'0'`s to width 36 (analogous to `pad128` right above it in `Main.lean`, or via a shared `padZeros (width : Nat) (n : Nat) : String` helper).

### 2. Clarify or wire `QRat.reduce` documentation vs `Repr QRat` (`PR #18`, `src/LeanAsm/QuasiRiemann/Rat.lean:16-43`)
- **Current behavior:** `QRat.reduce` states *"Reduce a `QRat` by `Nat.gcd` for canonical display"*, but `Repr QRat` (defined above it on lines 16–18) does not call `QRat.reduce` and there are no callers elsewhere in the codebase.
- **Action:** Either clarify in `QRat.reduce`'s docstring that it is an explicit/manual normalization helper (and note `Repr QRat` prints raw `(num/den)` to keep `#eval`/proof outputs unreduced unless normalized), **or** move `instance : Repr QRat` below `QRat.reduce` and normalize via `q.reduce` (checking `Main.lean` CLI output snapshots remain accurate).

### 3. Decouple `AsymptoticZfr` from `QuasiRiemann.lean` to preserve `.olean` cache (`PR #18`, `src/LeanAsm/QuasiRiemann.lean:8`)
- **Current behavior:** `QuasiRiemann.lean` imports `LeanAsm.QuasiRiemann.AsymptoticZfr` so `ln2Upper36Scaled_eq_lnInterval36_hi` and `octaveLnUpper36_bounds_lnInterval36` can live at the bottom of `QuasiRiemann.lean` and be re-exported by `QuasiRiemann`. Any edit to `AsymptoticZfr.lean` therefore invalidates the large `QuasiRiemann.olean` (~157s rebuild) and downstream `CollatzQrhBridge`.
- **Action:** Move `ln2Upper36Scaled_eq_lnInterval36_hi` and `octaveLnUpper36_bounds_lnInterval36` into a small dedicated bridge module (e.g. `src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean`) that imports both `LeanAsm.QuasiRiemann` and `LeanAsm.QuasiRiemann.AsymptoticZfr` (re-exported via `src/LeanAsm.lean`), and remove `import LeanAsm.QuasiRiemann.AsymptoticZfr` from `src/LeanAsm/QuasiRiemann.lean`. (Update `tests/TestAxioms.lean` Part 19 references if namespace/module changes.)

### 4. Clarify constant derivative in `genus2DerivF5` (`PR #12`, `src/LeanAsm/FiniteFieldRH.lean:75-83`)
- **Current behavior:** `genus2DerivF5 x` computes `(5 : Fin 5) * (x * x * x * x) - 1`, where `(5 : Fin 5) = 0` reduces definitionally to `-1`.
- **Action:** Prove an explicit lemma `genus2DerivF5_eq_neg_one : ∀ x : Fin 5, genus2DerivF5 x = -1` (or clarify the definition/docstring) so the `5 x^4 ≡ 0 (mod 5)` reduction is explicitly documented and proved rather than implicit.

### 5. Align / strengthen `FiniteFieldRH` L-value & Jacobian docstrings (`PR #14`, `src/LeanAsm/FiniteFieldRH.lean:484-528`)
- **Current behavior:**
  - `genus2_L_at_1_eq_71_div_25` proves `genus2LNumAtInv5 = 1775 ∧ 1775 * 25 = 71 * 625 ∧ 1775 > 0`, while its docstring talks about `L(C, 1) = 71/25` and analytic rank `0`.
  - `genus2_jacobian_order_71_prime` proves bounded trial-division non-divisibility (`2 ≤ d → d * d ≤ 71 → 71 % d ≠ 0`), and `genus2_basepoint_generates_jacobian` proves `onGenus2CurveF5 0 1 ∧ (1 : Fin 5) ≠ 0`, while their docstrings describe cyclic order `71` / generation consequences.
- **Action:** Either strengthen `genus2_L_at_1_eq_71_div_25` (or add a companion theorem) to express the exact rational equivalence in `QRat` (`QRat.eqv (QRat.mk' genus2LNumAtInv5 625) (QRat.mk' 71 25)`), and tighten the docstrings on lines 484–525 to clearly separate what is formally verified in Lean (`Prop` statement) from the classical/algebraic mathematical interpretation.

---

## Triage Reference (False Positives / Already Resolved)
Not tracked above because they are already fixed on `main` (`6abcc8b`) or verified invalid by Lean 4 CI:
- PRs #2, #3, #4, #5, #6, #7 (`Makefile:21` fixed in #10; `Div QRat`/`(a / b)`/`foldRawPair` fixed or absent; `inbox/` formatting handled in #6).
- PR #7 (`CrtMulBridge.lean:59`), PR #14 (`FiniteFieldRH.lean:436`), PR #15 (`WeilZetaBridge.lean:32,38,66`): typecheck cleanly in Lean 4 CI without errors.

---

## Verification Acceptance Criteria
- `make build-incremental` passes cleanly (`0` errors, all modules cached/up-to-date).
- `lake env lean tests/TestAxioms.lean` passes with zero `Classical.choice` and zero `sorryAx` on any added/updated theorems.
- `make sync` passes cleanly.

---

## Issue #22: docs(finite-field-rh): align genus2_L_at_1 docstrings with formal theorem statements
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T02:36:27Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/22

### Description

Copilot review finding on `src/LeanAsm/FiniteFieldRH.lean` (around lines 492 and 535 for `genus2_L_at_1_eq_71_div_25` and `genus2_L_at_1_qrat`):

- The docstrings claim that the theorems formally establish nonvanishing ($L(J/\mathbb{F}_5, 1) \neq 0$) / analytic rank `0`, whereas their formal Lean theorem types establish cleared-denominator integer equalities (`genus2LNumAtInv5 = 1775`, `1775 * 25 = 71 * 625`), positivity (`1775 > 0`), and `QRat.eqv` (`71 / 25`).
- Reword both docstrings so the formal claim describes strictly the proved Lean propositions, with any analytic-rank-0 interpretation placed in an explicitly marked parenthetical mathematical remark.

---

## Issue #24: feat(finite-field-rh): formalize Cantor-Mumford Jacobian group law on J(C)(F_5) and prove exact order 71
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T02:50:03Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/24

### Description

Formalize Cantor's Mumford divisor composition and reduction on the Jacobian `J(C)(F_5)` of the genus-2 hyperelliptic curve `C : y^2 = x^5 - x + 1` in `src/LeanAsm/Genus2Jacobian.lean`, constructively verifying `71 * [P_0 - ∞] = 0` and exact prime order `71` with ZERO `Classical.choice` and ZERO `sorryAx`.

## Context
`src/LeanAsm/FiniteFieldRH.lean` already certifies:
- `onGenus2CurveF5 (x y : Fin 5)` (`y^2 = x^5 - x + 1`),
- `cardJacobianGenus2F5 = 71` (`genus2_jacobian_order_eq_71`),
- primality of `71` (`genus2_jacobian_order_71_prime`), and
- basepoint `P_0 = (0, 1)` on `C(F_5)` (`genus2_basepoint_generates_jacobian`).

Currently, the claim that `[P_0 - ∞]` generates `J(C)(F_5) ≅ Z/71Z` rests on the abstract Weil point-count identity `#J(C)(F_5) = 71` together with `[P_0 - ∞] ≠ 0`. This issue constructs the explicit Mumford divisor group law and verifies the `71`-element cyclic group structure directly inside `Fin 5[x]`.

## Technical Deliverables

1. **Univariate Polynomial Arithmetic over `F_5` (`PolyF5`):**
   - Represent polynomials over `Fin 5` as canonical trimmed coefficient lists (`List (Fin 5)`).
   - Implement `polyAdd`, `polySub`, `polyMul`, `polyDivMod` (monic/nonzero Euclidean division), `polyGcd`, and extended Euclidean algorithm `polyXgcd` over `Fin 5`.
   - Prove soundness constructively (`polyDivMod_sound`, `polyXgcd_bezout`).

2. **Reduced Mumford Divisors & Cantor's Composition/Reduction Algorithm:**
   - Define `MumfordDivisor` `(u, v : PolyF5)` with computable invariant `isReducedMumford u v`: `u` is monic, `deg(u) <= 2`, `deg(v) < deg(u)` (with `(u, v) = (1, 0)` as the identity `MumfordDivisor.zero` / `0_J`), and `u` divides `v^2 - (x^5 - x + 1)` in `Fin 5[x]`.
   - Implement `cantorAdd (D1 D2 : MumfordDivisor) : MumfordDivisor` (generalized CRT composition via `polyXgcd`, followed by Cantor reduction steps `u' := monic((f - v^2) / u)` and `v' := (-v) mod u'` until `deg(u') <= 2`) and `cantorNeg`, plus double-and-add scalar multiplication `cantorSmul (n : Nat) (D : MumfordDivisor) : MumfordDivisor`.
   - Prove `cantorAdd_preserves_reduced` and `cantorSmul_preserves_reduced` constructively (`ZERO Classical.choice`, `ZERO sorryAx`).

3. **Exact Order `71` & Group Law Verification for `P_0 = (0, 1)`:**
   - Define the base divisor `D0 : MumfordDivisor` corresponding to `[P_0 - ∞]` (`u(x) = x`, `v(x) = 1`), and prove `D0_is_reduced : isReducedMumford D0.u D0.v`.
   - Constructively prove via kernel evaluation (`decide`):
     - `jacobian_D0_order_71 : cantorSmul 71 D0 = MumfordDivisor.zero`
     - `jacobian_D0_primitive : ∀ k : Nat, 1 ≤ k → k ≤ 70 → cantorSmul k D0 ≠ MumfordDivisor.zero`
     - `jacobian_group_axioms_on_orbit`: associativity, commutativity, identity, and inverse laws verified constructively across the full `71`-element cyclic orbit `{cantorSmul k D0 | k < 71}`, providing an independent group-theoretic proof that `J(C)(F_5) ≅ Z/71Z`.

4. **Module Export, Axiom Audit & CLI Output:**
   - Export `LeanAsm.Genus2Jacobian` in `src/LeanAsm.lean`.
   - Add `#print axioms` checks in `tests/TestAxioms.lean` (Part 21) confirming zero `Classical.choice` and zero `sorryAx`.
   - Update `Main.lean` Part 7 CLI output to report the explicit Cantor–Mumford verification `71 * [P_0 - ∞] = 0` on `J(C)(F_5)`.

## Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` reports only `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All `.lean` files stay within 120 characters per line with intact `-- Path:` headers and `-- end of file:` footers (and 80 columns for any `.md` docs).
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #26: feat(collatz): constructive Steiner-Simons-de Weger cycle-length and minimum-element bounds up to (485, 306)
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T04:09:18Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/26

### Description

## Overview

Extend [`src/LeanAsm/CollatzQrhBridge.lean`](src/LeanAsm/CollatzQrhBridge.lean) with constructive Steiner–Simons–de Weger Collatz cycle-length and minimum-element bounds derived from the certified `log_2(3)` continued-fraction convergent ladder up through `(485, 306)` (and `powViaCrtNtt192` / `linearFormLn2Ln3Interval72`), with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Context in Codebase

[`src/LeanAsm/CollatzQrhBridge.lean`](src/LeanAsm/CollatzQrhBridge.lean) already provides:
- `powViaCrtNtt192` and `powViaCrtNtt192_eq_pow`
- `expectedGap485` and `collatz_convergent_485_306_separation_certified` covering `(8, 5)`, `(19, 12)`, `(65, 41)`, `(84, 53)`, `(306, 193)`, and `(485, 306)`
- `linearFormLn2Ln3Interval72`, `linearFormLn2Ln3Interval72_sound`, `linearFormLn2Ln3AbsLower72`, and `linearFormLn2Ln3AbsLower72_sound`
- `baker_effective_measure_485_306_verified` (`scale71 < linearFormLn2Ln3AbsLower72 k m * (m * m : Int)` across the 6 convergents)
- `collatz_485_306_cycle_denominator_certified`

## Technical Deliverables (`src/LeanAsm/CollatzQrhBridge.lean`)

1. **Constructive Collatz Cycle Equation & Minimum-Element Inequality (`collatz_cycle_min_element_lower_bound`):**
   - Model a valid `m`-odd-step Collatz cycle schedule via positive halving counts `a_0, ..., a_{m-1} ≥ 1` with cumulative shifts `s_j = ∑_{r=0}^{j-1} a_r` (`s_0 = 0`, `s_m = k = ∑ a_r`) and cycle equation `n_min * (2^k - 3^m) = ∑_{j=0}^{m-1} 3^{m - 1 - j} * 2^{s_j}` where `2^k > 3^m`.
   - Prove constructively by induction on `m` (`s_j ≥ j` and geometric sum identity `∑_{j=0}^{m-1} 3^{m - 1 - j} * 2^j = 3^m - 2^m`) that every valid positive Collatz cycle satisfies:
     ```
     n_min * (2^k - 3^m) ≥ 3^m - 2^m
     ```

2. **Steiner 1-Cycle Exclusion Across Certified Upper Convergents (`steiner_1cycle_excluded_at_convergents`):**
   - Prove that for a Steiner 1-cycle (`a_0 = ... = a_{m-2} = 1`, `a_{m-1} = k - m + 1`), equality holds: `n_min * (2^k - 3^m) = 3^m - 2^m`, requiring `(2^k - 3^m) ∣ (3^m - 2^m)`.
   - Using `powViaCrtNtt192`, constructively certify `(2^{p_n} - 3^{q_n}) ∤ (3^{q_n} - 2^{q_n})` at every certified upper convergent `(p_n, q_n) ∈ {(8, 5), (65, 41), (306, 193), (485, 306)}`, ruling out Steiner 1-cycles at all four convergents.

3. **Explicit Convergent `n_min` Thresholds (`collatz_convergent_nmin_lower_bounds`):**
   - Using `powViaCrtNtt192` and `collatz_cycle_min_element_lower_bound`, certify explicit integer lower bounds `n_min ≥ ⌈(3^{q_n} - 2^{q_n}) / (2^{p_n} - 3^{q_n})⌉` for any cycle realizing the convergent exponent pairs `(8, 5)` (`n_min ≥ 17`), `(65, 41)` (`n_min ≥ 87`), `(306, 193)` (`n_min ≥ 14`), and `(485, 306)` (`n_min ≥ 978`).

4. **Simons–de Weger Cycle-Length Barrier Through `(485, 306)` (`collatz_cycle_length_lower_bound_306`):**
   - Prove the cycle odd-step product upper inequality `2^k * n_min^m ≤ (3 * n_min + 1)^m` (from `2^{a_j} * x_{j+1} = 3 * x_j + 1 ≤ x_j * (3 + 1/n_min)` over all odd cycle elements `x_j ≥ n_min`), and extend the 72-digit linear-form measure (`baker_effective_measure_485_306_verified` / `linearFormLn2Ln3AbsLower72`) to hold uniformly across all `1 ≤ m ≤ 306` with `2^k > 3^m` (`|k ln 2 - m ln 3| * m > 1/10`, hence also `|k ln 2 - m ln 3| * m^2 > 1/10`).
   - Combine the constructive cycle inequality with `e^x - 1 ≥ x` / `ln(1 + t) ≤ t` (or equivalent constructive rational/integer inequalities over `1 ≤ m ≤ 306`) to prove:
     - Any nontrivial positive Collatz cycle with `2 ≤ m ≤ 306` odd steps must satisfy `n_min < 10 * m^2 ≤ 936,360` (note `10 * 306^2 = 936,360`).
     - Contrapositively, any nontrivial positive Collatz cycle with `n_min ≥ 936,360` must have at least `m ≥ 307` odd steps and `K = k + m ≥ 793` total steps (since `2^486 < 3^307 < 2^487`, `k + m ≥ 794 ≥ 793`).

5. **Axiom Audit & CLI Output:**
   - Add `#print axioms` checks in `tests/TestAxioms.lean` for all new `CollatzQrhBridge` theorems (`ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 2 CLI output to display the certified Steiner 1-cycle exclusions and the `n_min ≥ 936,360 ⇒ m ≥ 307` (`K ≥ 793`) cycle-length barrier.

## Acceptance Criteria

- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All `.lean` files adhere to at most 120 characters per line with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #28: feat(euler): constructive Fermat-prime tower {5, 17, 257, 65537} Euler product non-vanishing across the critical strip
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T04:21:14Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/28

### Description

## Summary

Extend `src/LeanAsm/EulerFactorNonVanishing.lean` from single-prime reverse-triangle bounds (`local_euler_factor_nonvanishing` and `list_euler_product_nonvanishing`) to constructive, finite-Euler-product non-vanishing lower bounds for the Fermat-prime CRT-NTT tower `{5, 17, 257, 65537}` across the critical strip (`sigma = 1/2`, `sigma = 3/4`, `sigma = 1`), with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Module DAG Note (Avoid Cyclic Imports)

- `src/LeanAsm/WeilZetaBridge.lean` already imports `LeanAsm.EulerFactorNonVanishing` (line 7), so `EulerFactorNonVanishing.lean` **must not** import `LeanAsm.WeilZetaBridge`.
- Replicate or factor any self-contained integer reverse-triangle / product-of-squares helpers (following the cleared-denominator integer pattern of `weil_denom_factor1_nonvanishing` / `weil_denom_product_lower_bound`) directly inside `EulerFactorNonVanishing.lean` (or a leaf helper module imported by both).
- Note the CRT-NTT tower linkage: `src/LeanAsm/CrtNtt.lean` uses `{5, 17}` (and `257`), while `src/LeanAsm/CrtNttUniversal.lean` uses `{17, 257, 65537}`. Keep `EulerFactorNonVanishing.lean` lightweight (avoid heavy `decide` dependencies) and cross-reference those moduli explicitly.

## Arithmetic Clarification on the Fermat-Prime Tower Product

> **Telescoping Fermat Identity Check:**
> Because $2^{32} - 1 = (2 - 1)(2 + 1)(2^2 + 1)(2^4 + 1)(2^8 + 1)(2^{16} + 1) = 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$:
> - `fermatTowerPrimes := [5, 17, 257, 65537]` ($F_1, F_2, F_3, F_4$) satisfies
>   `fermatTowerPrimes.prod = 1431655765` and `3 * fermatTowerPrimes.prod = 2^32 - 1 = 4294967295`.
> - Including $F_0 = 3$ (`[3, 5, 17, 257, 65537]`, already used in `fermat_tower_euler_nonvanishing_concrete`) gives `[3, 5, 17, 257, 65537].prod = 2^32 - 1 = 4294967295`.
> - For `fermatTowerPrimes = [5, 17, 257, 65537]`, the totient product is
>   `∏ (p - 1) = 4 * 16 * 256 * 65536 = 2^30 = 1073741824`.

## Technical Deliverables (in `src/LeanAsm/EulerFactorNonVanishing.lean`)

1. **Fermat-Prime Tower Moduli & Telescoping Product Identity (`fermat_tower_product_eq_2pow32_sub_1`):**
   - Define `fermatTowerPrimes : List Nat := [5, 17, 257, 65537]` ($F_1, F_2, F_3, F_4$).
   - Prove constructively (linked to the Fermat telescoping identity `(2 - 1) * ∏_{k=0}^{n-1} (2^{2^k} + 1) = 2^{2^n} - 1`):
     - `fermatTowerPrimes.prod = 1431655765` and `3 * fermatTowerPrimes.prod = 2^32 - 1 = 4294967295`,
     - `[3, 5, 17, 257, 65537].prod = 2^32 - 1 = 4294967295`,
     - `(fermatTowerPrimes.map (· - 1)).prod = 2^30 = 1073741824`.

2. **Inductive Finite Euler Product Norm Lower Bound (`euler_product_finite_norm_lower_bound`):**
   - Model each local complex factor $1 - p^{-s}$ in cleared-denominator integer coordinates as `(d_p - zx_p, -zy_p)` over `d_p > 0` where `zx_p^2 + zy_p^2 = rNum_p^2` with `0 < rNum_p < d_p` (representing rational modulus envelope `r_p = rNum_p / d_p \in (0, 1)`).
   - Lift the single-factor reverse triangle inequality `|1 - z_p|^2 = (d_p - zx_p)^2 + zy_p^2 >= (d_p - rNum_p)^2 > 0` inductively over any finite list of factors to:
     - `0 < ∏ (d_p - rNum_p)^2 <= ∏ ((d_p - zx_p)^2 + zy_p^2)`.

3. **Fermat-Tower Specialization (`fermat_tower_euler_product_nonvanishing`):**
   - Specialize `euler_product_finite_norm_lower_bound` to the 4-prime tower `fermatTowerPrimes = [5, 17, 257, 65537]` for any positive rational modulus envelopes `(rNum_p / d_p)` with `0 < rNum_p < d_p`, yielding the explicit strictly positive 4-factor lower bound.

4. **Critical-Strip Certified Rational Lower Bounds (`fermat_tower_euler_product_strip_certs`):**
   Prove constructive cleared-denominator rational inequalities (plus norm-envelope admissibility `r_p >= p^{-\sigma}` cleared as integer powers) for:
   - **`sigma = 1/2` (`r_5 = 1/2, r_17 = 1/4, r_257 = 1/16, r_65537 = 1/256`, where `rNum_p^2 * p >= d_p^2`):**
     - `∏ (1 - r_p) = (1/2) * (3/4) * (15/16) * (255/256) = 11475 / 32768`,
     - `(11475 / 32768)^2 = 131675625 / 1073741824 > 1 / 9` (`9 * 11475^2 > 32768^2`).
   - **`sigma = 3/4` (`r_5 = 3/10, r_17 = 1/8, r_257 = 1/64, r_65537 = 1/4096`, where `rNum_p^4 * p^3 >= d_p^4`):**
     - `∏ (1 - r_p) = (7/10) * (7/8) * (63/64) * (4095/4096) = 2528253 / 4194304`,
     - `(2528253 / 4194304)^2 > 1 / 3` (`3 * 2528253^2 > 4194304^2`).
   - **`sigma = 1` (`r_p = 1 / p` for `p ∈ [5, 17, 257, 65537]`):**
     - `∏ (1 - 1/p) = 2^30 / 1431655765 = 3 * 2^30 / (2^32 - 1)`,
     - `(1073741824 / 1431655765)^2 > 9 / 16 > 1 / 16` (and with `F_0 = 3` included, `(2^31 / (2^32 - 1))^2 > 1 / 4 > 1 / 16`).

5. **Axiom Audit & CLI Integration:**
   - Add `#print axioms` checks for all new `EulerFactorNonVanishing` theorems in `tests/TestAxioms.lean`, verifying ZERO `Classical.choice` and ZERO `sorryAx`.
   - Update `Main.lean` Part 8 (`Prime-Tower Local Euler Factor Non-Vanishing (RNS ↔ QRH)`) — and cross-reference Part 6 (`Residue Number System (RNS) & Chinese Remainder Theorem (CRT)`) — to print the certified `{5, 17, 257, 65537}` Euler product non-vanishing bounds at `sigma = 1/2`, `3/4`, and `1`.

## Acceptance Criteria

- [ ] All `.lean` lines <= 120 characters, with intact `-- Path:` headers and `-- end of file:` footers.
- [ ] `make build-incremental` succeeds with all targets green.
- [ ] `lake env lean tests/TestAxioms.lean` reports zero `Classical.choice` and zero `sorryAx` for all new theorems.
- [ ] `make sync` passes cleanly.


---

## Issue #29: feat(qrh): high-height 2D zero-free rectangles at t ~ 10^12 via PiChudnovsky twoPiInterval72 phase reduction
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T04:25:33Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/29

### Description

## Summary

Extend `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` with certified high-height 2D zero-free rectangles for the truncated Dirichlet zeta polynomial $\zeta_N(s) = \sum_{n=1}^N n^{-s}$ ($N \le 128$) at heights $t \sim 10^{12}$ using `PiChudnovsky`-derived `twoPiInterval72` modulo-$2\pi$ phase reduction, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Mathematical & Architectural Context

- At height $t \approx 10^{12}$ and $n \le 128$, reducing $t \ln n$ modulo $2\pi$ multiplies the 1-ULP (`hi - lo = 1` at `10^{72}`) width of `twoPiInterval72` by the quotient $k \approx t \ln n / (2\pi) \lesssim 7.73 \times 10^{11}$. Because `twoPiInterval72` is projected directly from `PiChudnovsky`'s certified $10^{105}$ bracket (`twoPiInterval72_from_chudnovsky_sound`), modulo-$2\pi$ quotient wrapping adds less than $10^{12} \le 10^{13}$ ULP at $10^{72}$ scale (**$< 10^{-59}$ radians**, 59+ decimal digits of wrapping precision), avoiding the catastrophic phase-wrapping loss of IEEE 754 `Float64` (`t * eps ~ 1.1e-4` rad).
- **Precision Attribution Note:** `lnInterval72 n` has table width up to `5000` ULPs at `10^{72}` (`ValidLnBound72`), so `t * width(lnInterval72 n)` contributes up to `5 * 10^{15}` ULPs at $t \sim 10^{12}$ ($< 10^{-56}$ rad, still 56+ digits). The deliverables below distinguish the `< 10^{13}` (`< 10^{-59}` rad) `twoPiInterval72` quotient-wrapping error bound from the full `t * lnInterval72 n` product width (`<= 6 * 10^{15}` at `10^{72}`, `< 10^{-56}` rad).
- **Rect Scope Note:** `InRemainingUnknownRect2D` in `src/LeanAsm/QuasiRiemann.lean` enforces `tHi6 < 10^12` ($t < 10^6$), and the Euler–Maclaurin $B_2$ tail scales as $O(t^2 N^{-\sigma-1})$. Therefore, high-height $t \sim 10^{12}$ ($tLo6 \sim 10^{18}$) certification targets the **truncated Dirichlet polynomial** $\zeta_N(s) = \sum_{n=1}^N n^{-s}$ ($N \le 128$) directly via a dedicated high-height 2D rect predicate (`IsValidDirichletRect2DN128`) without `InRemainingUnknownRect2D`'s $t < 10^6$ cap.

## Technical Deliverables (in `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`)

1. **High-Height Modulo-$2\pi$ Phase-Reduction Precision Certificate (`high_height_phase_reduction_1e12`):**
   - Expose constructive phase reduction `reducePhaseModTwoPi72 (t72 ln72 : ScaledInterval72) : ScaledInterval72` composing `mulInterval72 t72 ln72` with `reduceModTwoPiCentered72` (backed by `twoPiInterval72` / `twoPiInterval72_from_chudnovsky_sound`).
   - Prove constructively (`high_height_phase_reduction_1e12`):
     - For any input phase bracket `xIv` with `xIv.hi - xIv.lo <= 5 * 10^12` and $|x| \le (10^{12} + 10) \cdot 5$, reducing `xIv` modulo `twoPiInterval72` yields quotient $|k| \le 8 \times 10^{11}$, `twoPiInterval72`-induced wrapping expansion `|k| * (twoPiInterval72.hi - twoPiInterval72.lo) < 10^{12}`, and reduced interval width `<= 10^{13}` at scale `10^{72}` (`< 10^{-59}` radians), linked explicitly to `twoPiInterval72_from_chudnovsky_sound`.
     - Specialize to `reducePhaseModTwoPi72` at point $t \in [10^{12}, 10^{12} + 10]$ with `lnInterval72 n` ($1 \le n \le 128$), proving `reducePhaseModTwoPi72` preserves soundness and maintains width `<= 6 * 10^{15}` at `10^{72}` (`< 10^{-56}` rad).

2. **Constructive 2D Dirichlet Partial-Sum Certifier (`buildDirichletRect2DCertN128`, `sweepDirichletRectangles2DN128`):**
   - Define a 2D rectangle certificate type / validity predicate `IsValidDirichletRect2DN128` for $\zeta_N(s) = \sum_{n=1}^N n^{-s}$ ($N \le 128$) over $[\sigma_0, \sigma_1] \times [t_0, t_1]$ using `reducePhaseModTwoPi72`, 72-digit cosine/sine/exp Taylor brackets (`taylorCosInterval72`, `taylorSinInterval72`, `taylorExpNegInterval72`), and termwise interval/Lipschitz oscillation bounds ($|\nabla \zeta_N(s)| \le \sum_{n=2}^N (\ln n) n^{-\sigma_0}$).
   - Implement `buildDirichletRect2DCertN128` and `sweepDirichletRectangles2DN128` (parameterized cleanly with `*Core` + CRT-NTT `rawMul72Crt` / fast `*Lit` equivalence just like `buildRect2DCertN128` / `sweepRectangles2DN128`).
   - Prove `isValidDirichletRect2DN128_sound` so the formal theorem statement directly establishes non-vanishing across all `(σ, t)` in the certified 2D rectangle (`∀ σ t, σ_0 ≤ σ ≤ σ_1 → t_0 ≤ t ≤ t_1 → ... ≠ 0` / positive lower bound on `Re(ζ_N(σ + i t))` or `|ζ_N(σ + i t)|²`).

3. **Certified High-Height 2D Zero-Free Rectangles Near $t = 10^{12}$ (`high_height_dirichlet_rects_1e12_certified`):**
   - Certify positive-area 2D boxes $[\sigma_0, \sigma_1] \times [t_0, t_1]$ near $t = 10^{12}$ (including phase-alignment windows around $t \approx 10^{12} + 6.1$ spanning $\sigma \in [0.501, 0.750]$, such as `[0.501, 0.750] × [10^12 + 6.08, 10^12 + 6.12]`, `[0.501, 0.550] × [10^12 + 6.05, 10^12 + 6.15]`, and `[0.600, 0.750] × [10^12 + 6.00, 10^12 + 6.20]`, where $\operatorname{Re}(\zeta_{128}(s)) > 1.49 > 0$ uniformly across each rectangle).
   - Prove `high_height_dirichlet_rects_1e12_certified`, verifying non-empty swept list, exact count, strictly positive total 2D area `Δσ · Δt > 0`, and coverage down to $\sigma = 0.501$ at $t \ge 10^{12}$.

4. **Axiom Audit & CLI Integration:**
   - Add `#print axioms` checks in `tests/TestAxioms.lean` for `high_height_phase_reduction_1e12`, `isValidDirichletRect2DN128_sound`, and `high_height_dirichlet_rects_1e12_certified`, confirming **ZERO `Classical.choice`** and **ZERO `sorryAx`**.
   - Update `Main.lean` Part 5 CLI output to display the certified $t \sim 10^{12}$ `twoPiInterval72` phase-precision bound ($< 10^{-59}$ rad wrapping precision) and certified high-height 2D zero-free rectangles for $\zeta_{128}(s)$.

## Acceptance Criteria

- [ ] Zero `Classical.choice` and zero `sorryAx` (`#print axioms` shows at most `propext`, `Quot.sound`, or empty).
- [ ] All `.lean` lines <= 120 characters, with intact `-- Path:` headers and `-- end of file:` footers.
- [ ] `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.


---

## Issue #32: refactor(euler): replace brittle tuple projections in fermat_tower_euler_product_strip_certs
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T05:24:20Z
- **Labels**: enhancement, ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/32

### Description

### Context
In PR #30 (`Closes #28`), Copilot left a low-severity maintainability suggestion on [`src/LeanAsm/EulerFactorNonVanishing.lean` (lines 425–427)](https://github.com/aomaker-org/leanasm/pull/30#discussion_r4571508614):

> The tuple projections from `strip_three_quarters_admissible` (`h.2.2.2...`) are very brittle: any small change to that lemma’s conjunction structure will break this proof and it’s hard to review. Destructure the conjunction with `rcases` and reassemble the needed sub-conjunctions with named hypotheses.

### Notes & Scope
- **Primary site (`src/LeanAsm/EulerFactorNonVanishing.lean` lines 425–427)**:
  - In `fermat_tower_euler_product_strip_certs`, replace `h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2` from `strip_three_quarters_admissible` with explicit `rcases` destructuring and named hypotheses (or align `strip_three_quarters_admissible` directly with the exported sub-conjunctions).
- **Adjacent site (`src/LeanAsm/EulerFactorNonVanishing.lean` lines 428–430)**:
  - Similarly replace `h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2` from `strip_one_admissible` with named `rcases` bindings (or `simpa using ...`).
- **Verification**:
  - Keep all `.lean` lines `≤ 120` characters with intact headers/footers.
  - Verify with `make build-incremental`, `lake env lean tests/TestAxioms.lean` (ZERO `Classical.choice`, ZERO `sorryAx`), and `make sync`.

---

## Issue #34: feat(weil): constructive genus-2 Hasse-Weil functional equation and completed zeta symmetry in WeilZetaBridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T05:40:00Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/34

### Description

## Summary

Extend `src/LeanAsm/WeilZetaBridge.lean` with constructive, zero-axiom (`ZERO Classical.choice`, `ZERO sorryAx`) proofs of the genus-2 Hasse-Weil functional equation, the Weil zeta functional equation, and critical-line reflection symmetry and reality for the smooth genus-2 curve
$$C : y^2 = x^5 - x + 1 \quad\text{over } \mathbb{F}_5.$$

## Context & Existing Symbols

- `src/LeanAsm/FiniteFieldRH.lean`:
  - `genus2FrobPoly`, `genus2FrobHomog`, and `genus2_frob_poly_functional_eq` (`genus2FrobHomog (5 * d) n = 25 * genus2FrobHomog n d`)
  - `genus2LPoly (T : Int) := 1 + 5 * T + 15 * T ^ 2 + 25 * T ^ 3 + 25 * T ^ 4`
  - `genus2_L_poly_eq_recip_frob` and `genus2LNumAtInv5` (`= 1775`)
- `src/LeanAsm/WeilZetaBridge.lean`:
  - Cleared-denominator integer/Gaussian-rational coordinate proofs (`d, tx, ty`) for `genus2_L_poly_quad_factor_id`, `weil_denom_factor1_nonvanishing`, `weil_denom_factor2_nonvanishing`, `genus2_L_poly_lower_bound_off_half`, and `weil_zeta_punctured_strip_regular_and_nonzero`
- `src/LeanAsm/QuasiRiemann/Rat.lean`: `QuasiRiemann.QRat` exact rational arithmetic

## Technical Deliverables (in `src/LeanAsm/WeilZetaBridge.lean`)

1. **Cleared-Denominator $L$-Polynomial Reciprocity (`genus2_L_poly_functional_eq`)**
   - Formalize the reciprocal polynomial transform $T^4 L_C(1 / (5T))$ in cleared-denominator algebraic form over `Int` / `QRat` (and Gaussian coordinates `(tx + i ty) / d`), proving constructively:
     $$25 T^4 \, L_C\!\left(\frac{1}{5T}\right) = L_C(T)$$
     for all nonzero $T$ on $C : y^2 = x^5 - x + 1$.

2. **Weil Zeta Rational Functional Equation (`genus2_weil_zeta_functional_eq`)**
   - Combine `genus2_L_poly_functional_eq` with the denominator identity
     $$\left(1 - \frac{1}{5T}\right)\left(1 - \frac{1}{T}\right) = \frac{(1 - T)(1 - 5T)}{5 T^2}$$
     to prove constructively in cleared-denominator form:
     $$5 T^2 \, Z\!\left(C/\mathbb{F}_5, \frac{1}{5T}\right) = Z(C/\mathbb{F}_5, T)$$
     for all $T \notin \{0, 1, 1/5\}$.

3. **Completed Zeta Reflection $\Xi_C(1 - s) = \Xi_C(s)$ & Critical-Line Reality (`genus2_completed_zeta_reflection`)**
   - Define the completed genus-2 zeta numerator/quotient $\Xi_C(s) = 5^s Z(C/\mathbb{F}_5, 5^{-s})$ over cleared-denominator integer/rational (and Gaussian `(tx, ty, d)`) coordinates `(u, v)` modeling `(5^{-s}, 5^{-(1-s)})` subject to $u \cdot v = 1/5$.
   - Prove constructively via cleared-denominator cross-multiplication on $u v = 1/5$:
     - **Reflection symmetry:** $\Xi_C(1 - s) = \Xi_C(s)$.
     - **Critical-line reality:** On $\operatorname{Re}(s) = 1/2$ (where $5 (tx^2 + ty^2) = d^2$, i.e. $\overline{u} = 1/(5u) = v$), the imaginary part of $\Xi_C(1/2 + i t)$ vanishes identically (`completedZetaImagPart = 0`).

4. **Axiom Audit & CLI Integration**
   - Add `#print axioms` checks in `tests/TestAxioms.lean` covering all new `WeilZetaBridge` theorems (strictly `ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 7 (or Part 7/8) CLI output to report the verified genus-2 Hasse–Weil functional equation $25 T^4 L_C(1/(5T)) = L_C(T)$ and critical-line reality of $\Xi_C(1/2 + i t)$.

## Acceptance Criteria

- ZERO `Classical.choice` and ZERO `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All `.lean` lines adhere to at most 120 characters with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #36: feat(qrh): constructive rational zero-density-to-QRH descent bridge in ZeroDensityBridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T07:04:43Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/36

### Description

### Summary
Create `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` (in `namespace QuasiRiemann`) formalizing a constructive rational zero-density-to-QRH descent bridge linking $A(\sigma)$ zero-density exponents, subconvexity/Lindelöf exponents $\mu(\sigma)$, and QRH thresholds $\theta \in \{3/4, 7/8, 11/12, 47/48\}$ to explicit zero-free strip bounds and Chebyshev prime-counting remainder gaps—with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

### Context (Existing Codebase Hooks)
- `src/LeanAsm/QuasiRiemann/Rat.lean`: constructive `QRat` (`num : Int`, `den : Nat`, `den_pos : 0 < den`, `QRat.eqv`, `<`, `≤`, `QRat.div`).
- `src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean`: `cDvp`, `dvpThresholdT0` (`16`), `dvp_asymptotic_zero_free_region`, `octaveLnUpper36QRat`, and `dirichlet_l2_diagonal_dominance_sandwich`.
- `src/LeanAsm/QuasiRiemann.lean`: `zeroDensityHuxley` (`12/5`), `zeroDensityGuthMaynard` (`30/13`), `zeroDensityIngham` (`3`), `zeroDensityHypothesis` (`2`), `zeroDensityExponentAt`, `guth_maynard_strictly_improves_huxley`, `qrhThresholdFromMollifier`.
- `src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean`: pattern for bridging `LeanAsm.QuasiRiemann` and `LeanAsm.QuasiRiemann.AsymptoticZfr` cleanly.

### Technical Deliverables

1. **Rational Zero-Density & Subconvexity Exponent Model (`ZeroDensitySpec`, `SubconvexitySpec`)** in `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`:
   - Define `ZeroDensitySpec` and `SubconvexitySpec` over `QRat` / cleared-denominator integer arithmetic without real-number axioms, modeling zero-density exponents $A(\sigma) = p/q > 0$ (representing $N(\sigma, T) \ll T^{A(\sigma)(1 - \sigma)}$) and Lindelöf/subconvexity exponents $\mu(\sigma)$.
   - Provide cleared-denominator cross-multiplication and monotonicity helpers relating $A(\sigma)(1 - \sigma)$ across rational inputs.

2. **Constructive Ingham / Huxley / Guth–Maynard Benchmark Certificates (`qrh_zero_density_benchmark_certs`)**:
   - Certify exact rational comparisons at $\sigma = 3/4$:
     - Ingham benchmark $A(3/4) = 8/3 \implies A(3/4)(1 - 3/4) = 2/3$ (in addition to compatibility with `zeroDensityIngham = 3`, $A(3/4)(1 - 3/4) = 3/4$),
     - Huxley $A(3/4) = 12/5 \implies A(3/4)(1 - 3/4) = 3/5$,
     - Guth–Maynard $A(3/4) = 30/13 \implies A(3/4)(1 - 3/4) = 15/26$.
   - Prove the strict improvement chain $15/26 < 3/5 < 2/3$ constructively (along with explicit `QRat.eqv` witness equalities and savings).

3. **Zero-Density-to-QRH Strip & Chebyshev Remainder Descent (`zero_density_implies_qrh_threshold`, `qrh_theta_ladder_certs`)**:
   - Prove constructively (`zero_density_implies_qrh_threshold`) that if $A(\sigma)(1 - \sigma) < 1$ for admissible $\sigma > \theta$ (cleared-denominator condition for sub-linear zero count growth above threshold $\theta$), then no nontrivial zero satisfying the admissibility predicate can violate the QRH density threshold above $\theta$.
   - Certify (`qrh_theta_ladder_certs`) the exact rational QRH threshold ladder:
     $$\theta \in \{3/4, 7/8, 11/12, 47/48\}, \quad \frac{3}{4} < \frac{7}{8} < \frac{11}{12} < \frac{47}{48} < 1,$$
     together with exact Chebyshev remainder exponent gaps:
     $$1 - \theta \in \{1/4, 1/8, 1/12, 1/48\} \quad (1/48 < 1/12 < 1/8 < 1/4).$$
   - Bridge cleanly with `AsymptoticZfr.dvp_asymptotic_zero_free_region` (e.g., comparing the asymptotic de la Vallée Poussin zero-free boundary $1 - c_{\mathrm{dvp}}/\ln(t)$ with the uniform QRH strip thresholds $\theta$ at high heights / linking `dirichlet_l2_diagonal_dominance_sandwich`).

4. **Module Export, Axiom Audit & CLI Output**:
   - Export `LeanAsm.QuasiRiemann.ZeroDensityBridge` in `src/LeanAsm.lean`.
   - Add `#print axioms` checks in `tests/TestAxioms.lean` covering all new theorems in `QuasiRiemann.ZeroDensityBridge` (`ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 5 CLI output to display the certified rational zero-density benchmark chain ($15/26 < 3/5 < 2/3$) and the QRH threshold ladder $\theta \in \{3/4, 7/8, 11/12, 47/48\}$ with gaps $\{1/4, 1/8, 1/12, 1/48\}$.

### Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All `.lean` files adhere to at most 120 characters per line with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #38: feat(euler): constructive cyclotomic Fermat-tower Dedekind zeta Euler factor non-vanishing
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T07:20:46Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/38

### Description

### Summary
Extend `src/LeanAsm/EulerFactorNonVanishing.lean` (`namespace EulerFactorNonVanishing`) with constructive non-vanishing lower bounds for splitting prime ideal Euler factors in the 2-power cyclotomic extensions $\mathbb{Q}(\zeta_{2^{2^k}})$ over the Fermat-prime tower $\{5, 17, 257, 65537\}$, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

### Context (Existing Codebase Hooks)
- `src/LeanAsm/EulerFactorNonVanishing.lean`:
  - `fermatNumber` (`F_k = 2^(2^k) + 1`), `fermatTowerPrimes` (`[5, 17, 257, 65537]`), `fermat_tower_product_eq_2pow32_sub_1`.
  - `EulerLocalFactorSpec`, `ValidEulerLocalFactorSpec`, `local_euler_disk_nonvanishing`, `euler_product_finite_norm_lower_bound`, `fermat_tower_euler_product_nonvanishing`, and `fermat_tower_euler_product_strip_certs`.
- `src/LeanAsm/CrtNttUniversal.lean`: CRT-NTT over `{17, 257, 65537}`.
- `tests/TestAxioms.lean` (Part 23) & `Main.lean` (Part 6).

### Technical Deliverables (in `src/LeanAsm/EulerFactorNonVanishing.lean`)

1. **Complete Splitting Arithmetic of Fermat Primes in $\mathbb{Q}(\zeta_{2^{2^k}})$ (`fermat_prime_cyclotomic_splitting_deg`):**
   - Define the cyclotomic degree / splitting multiplicity $g_k = \varphi(2^{2^k}) = 2^{2^k - 1}$ (`fermatCyclotomicSplittingDeg`).
   - Prove constructively for every $k \ge 1$ that $F_k \equiv 1 \pmod{2^{2^k}}$ (`fermatNumber k % 2 ^ (2 ^ k) = 1`), showing residue degree $f = 1$, $F_k - 1 = 2 g_k$, and complete splitting into $g_k$ prime ideals of norm $N(\mathfrak{p}) = F_k$.
   - Certify concrete splitting multiplicities $(g_1, g_2, g_3, g_4) = (2, 8, 128, 32768)$ and total prime ideal count $2 + 8 + 128 + 32768 = 32{,}906$.

2. **Power-Lifted Cyclotomic Local Euler Factor Lower Bound (`cyclotomic_split_euler_factor_nonvanishing`):**
   - Prove constructively by induction on multiplicity $g \ge 1$ that if a single-prime local factor satisfies `ValidEulerLocalFactorSpec f` (`0 < (d - rNum)^2 ≤ (d - zx)^2 + zy^2`), then the completely split cyclotomic Euler factor $\prod_{\mathfrak{p} \mid p} (1 - N(\mathfrak{p})^{-s}) = (1 - p^{-s})^g$ satisfies the cleared-denominator squared-modulus bound:
     $$0 < (d - r_{\mathrm{Num}})^{2g} \le ((d - z_x)^2 + z_y^2)^g$$
     (representing $\prod_{\mathfrak{p} \mid p} |1 - N(\mathfrak{p})^{-s}|^2 \ge (1 - r_p)^{2g} > 0$).

3. **Fermat-Tower Cyclotomic Dedekind Euler Product Certificates (`fermat_tower_dedekind_euler_strip_certs`):**
   - Instantiate `cyclotomic_split_euler_factor_nonvanishing` across the Fermat-prime tower $(F_1, F_2, F_3, F_4) = (5, 17, 257, 65537)$ with splitting multiplicities $(g_1, g_2, g_3, g_4) = (2, 8, 128, 32768)$ in $\mathbb{Q}(\zeta_{2^{2^k}})$ across $\sigma = 1/2$, $\sigma = 3/4$, and $\sigma = 1$.
   - Certify strictly positive rational lower bounds (in cleared-denominator form, without expensive huge literal exponentiations—using inductive / modular ratio certificates or fast exponentiation bounds so kernel verification stays fast):
     - Uniform $\sigma = 1$ Bernoulli / $e$-envelope comparison confirming $(1 - 1/F_k)^{2 g_k} = (1 - 1/F_k)^{F_k - 1} > 1/3 > 0$ (and hence $(1 - 1/257)^{256} > 1/3$, $(1 - 1/65537)^{65536} > 1/3$ stay bounded away from zero uniformly as $k$ grows, giving explicit positive joint rational lower bounds across all 4 cyclotomic levels at $\sigma \in \{1/2, 3/4, 1\}$).

4. **Axiom Audit & CLI Output:**
   - Add Part 27 `#print axioms` checks in `tests/TestAxioms.lean` covering all new theorems in `EulerFactorNonVanishing` (`ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 6 CLI output to display the Fermat-tower cyclotomic splitting multiplicities $(2, 8, 128, 32768)$ (sum $32{,}906$) and Dedekind Euler factor non-vanishing certificates.

### Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All `.lean` files adhere to at most 120 characters per line with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #40: feat(qrh): constructive Chebyshev remainder envelopes across benchmark scales in ZeroDensityBridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T07:39:05Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/40

### Description

## Goal
Extend `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` with constructive, cleared-denominator Chebyshev prime-counting remainder envelopes $|\psi(x) - x| \le C \cdot x^\theta (\ln x)^2$ across benchmark scales $x = 10^{12k}$ and the QRH threshold ladder $\theta \in \{3/4, 7/8, 11/12, 47/48\}$, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Context
`src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` already defines `chebyshevGap (θ : QRat) := QRat.ofInt 1 - θ`, proves `chebyshevGap_pos_of_lt_one` and `chebyshevGap_antitone`, and certifies in `qrh_theta_ladder_certs` that $\theta \in \{3/4, 7/8, 11/12, 47/48\}$ satisfies $1 - \theta \in \{1/4, 1/8, 1/12, 1/48\}$ strictly left of the de la Vallée Poussin boundary. What is missing is an exact integer-power Chebyshev remainder model translating those QRH exponents into concrete $|\psi(x) - x|$ envelopes and relative error / savings certificates at large powers of $10$.

## Technical Deliverables (in `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`)

1. **Explicit Chebyshev Remainder Model (`ChebyshevRemainderSpec`, `qrhRemainderBoundAtTenPow`)**
   - Model explicit Chebyshev remainder envelopes $|\psi(x) - x| \le C \cdot x^\theta (\ln x)^2$ at powers of ten $x = 10^{12 k}$ ($k \ge 1$) using exact `Nat` / `QRat` exponents with zero real-number or floating-point axioms:
     - When `θ.den ∣ 12 * k` and `0 < θ.num`, define the exact integer exponent `e = (12 * k * θ.num.natAbs) / θ.den` so $x^\theta = 10^e$ is an exact power of $10$ (`qrh_exact_tenPow_exponent`).
     - Specifically:
       - At $k = 1$ ($x = 10^{12}$): $q \in \{4, 12\}$ gives exact exponents $10^9$ ($\theta = 3/4$) and $10^{11}$ ($\theta = 11/12$); note $8 \nmid 12$ ($12 \cdot 7/8 = 21/2$), so $\theta = 7/8$ uses the ceiling exponent $\lceil 12 \cdot 7/8 \rceil = 11$ (or restricts exact integer powers to $2 \mid k$).
       - At $k = 2$ ($x = 10^{24}$): $q \in \{4, 8, 12\}$ gives exact exponents $10^{18}, 10^{21}, 10^{22}$.
       - At $k = 3$ ($x = 10^{36}$): $q \in \{4, 12\}$ gives exact exponents $10^{27}, 10^{33}$ ($8 \nmid 36$, ceiling $32$ if included for $7/8$).
       - At $k = 4$ ($x = 10^{48}$): $q \in \{4, 8, 12, 48\}$ gives exact exponents $10^{36}, 10^{42}, 10^{44}, 10^{47}$.
     - Use the conservative rational logarithmic envelope $(\ln 10^{12k})^2 \le (28 k)^2$ (since $12 \ln 10 < 12 \cdot (7/3) = 28$) with explicit prefactor $C = 1$ (and general `C : Nat` in `ChebyshevRemainderSpec`).
     - Keep large powers (`10^e`) in symbolic `Nat.pow` form in theorem statements/proofs (avoiding literal 300+ digit expansion in the Lean kernel).

2. **Monotonicity & Relative Savings Across the $\theta$ Ladder (`chebyshev_remainder_mono_theta`, `qrh_chebyshev_savings_1e24`)**
   - Prove constructively via `Nat.pow_le_pow_right` that for $1/2 \le \theta_1 \le \theta_2 < 1$ and divisible scale $x = 10^{12k}$ ($k \ge 1$), the QRH remainder envelope scales monotonically with $\theta$ and achieves exact power-of-ten relative savings factor $10^{12k(\theta_2 - \theta_1)}$ (`10^e₂ = 10^e₁ * 10^(e₂ - e₁)`).
   - Certify concrete relative savings:
     - At $x = 10^{24}$ ($k = 2$): $\theta = 3/4$ improves upon $\theta = 7/8$ by $10^3 = 1{,}000$ and upon $\theta = 11/12$ by $10^4 = 10{,}000$.
     - At $x = 10^{48}$ ($k = 4$): $\theta = 3/4$ improves upon $\theta = 47/48$ by $10^{11}$.

3. **Explicit Numerical Remainder Certificates (`qrh_chebyshev_benchmark_certs`)**
   - Certify the exact symbolic remainder envelopes `10^e * (28 * k)^2` across $k \in \{1, 2, 3, 4\}$ (`(28k)^2 ∈ {784, 3136, 7056, 12544}`).
   - Prove strict sub-linear relative error `(28 * k)^2 * 10 < 10^(12 * k - e)` (i.e. relative error `< 10^-1`) wherever $(28k)^2$ is strictly dominated by the $10^{12k(1-\theta)}$ saving:
     - At benchmark scales $x \in \{10^{24}, 10^{36}\}$ for $\theta = 3/4$ (`31360 < 10^6` and `70560 < 10^9`), and at $x = 10^{48}$ for $\theta \in \{3/4, 7/8\}$ (`125440 < 10^12` and `125440 < 10^6`). *(Note: at small $k$, $\theta = 11/12$ at $k \le 4$ or $\theta = 47/48$ at $k = 4$ have savings $10^{1..4} < 10 \cdot (28k)^2$, whereas for $k = 1, \theta = 3/4$ we get $< 1$ via `784 < 1000`; include the minimal all-rung asymptotic crossover scale $k = 28$, i.e. $x = 10^{336}$, where `10 * 784^2 = 6146560 < 10^7`, certifying $< 10^{-1}$ simultaneously across ALL four rungs $\theta \in \{3/4, 7/8, 11/12, 47/48\}$.)*

4. **Axiom Audit & CLI Output**
   - Add `#print axioms` checks in `tests/TestAxioms.lean` for all new `ZeroDensityBridge` theorems (`ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 5 CLI output to display the certified Chebyshev remainder savings across $x = 10^{24}$ and $x = 10^{48}$ (plus the $x = 10^{336}$ universal `< 10^-1` crossover).

## Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All modified `.lean` files adhere to $\le 120$ characters per line with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #42: feat(crt): constructive Garner mixed-radix CRT and convolution wrap-around bounds over {5, 17, 257, 65537}
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T07:49:56Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/42

### Description

## Goal
Extend `src/LeanAsm/CrtNttUniversal.lean` with constructive Garner mixed-radix CRT reconstruction over the 4-prime Fermat tower $\{5, 17, 257, 65537\}$, 31-bit dynamic-range certificates linked to `EulerFactorNonVanishing.fermatTowerPrimes`, and sharp NTT convolution wrap-around safety bounds for transform lengths $N \in \{4, 8, 16\}$, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Context
- `src/LeanAsm/CrtNttUniversal.lean` currently proves universal 16-point NTT invertibility/convolution over $\{17, 257, 65537\}$ and 3-prime CRT-NTT integer multiplication over $\{5, 17, 257\}$ / $\{17, 257, 65537\}$ (with base-1000 limb arithmetic up to 192 digits).
- `src/LeanAsm/EulerFactorNonVanishing.lean` defines `fermatTowerPrimes = [5, 17, 257, 65537]` and proves `fermat_tower_product_eq_2pow32_sub_1` (`fermatTowerPrimes.prod = 1431655765`, `3 * fermatTowerPrimes.prod = 2^32 - 1`).
- Adding `import LeanAsm.EulerFactorNonVanishing` in `src/LeanAsm/CrtNttUniversal.lean` is acyclic (`EulerFactorNonVanishing` depends only on `RnsArithmetic`).

## Technical Deliverables (in `src/LeanAsm/CrtNttUniversal.lean`)

1. **Fermat-Tower Dynamic Range & 31-Bit Embedding (`fermat_tower_crt_modulus_bounds`)**
   - Define `fermatTowerMod4 : Nat := 5 * 17 * 257 * 65537` (`= 1431655765`).
   - Prove constructively:
     - `fermatTowerMod4 = EulerFactorNonVanishing.fermatTowerPrimes.prod` (via `EulerFactorNonVanishing.fermat_tower_product_eq_2pow32_sub_1`),
     - `3 * fermatTowerMod4 = 2 ^ 32 - 1` (`4294967295`),
     - `2 ^ 30 < fermatTowerMod4 ∧ fermatTowerMod4 < 2 ^ 31` (clean 31-bit unsigned embedding without 32-bit overflow).

2. **Constructive Garner Mixed-Radix Reconstruction (`garnerReconstruct4`, `garnerReconstruct4_sound`)**
   - Define sequential mixed-radix Garner reconstruction over $(p_1, p_2, p_3, p_4) = (5, 17, 257, 65537)$ with certified modular inverses:
     - $c_{12} = 5^{-1} \bmod 17 = 7$ (`(5 * 7) % 17 = 1`),
     - $c_{123} = (5 \cdot 17)^{-1} \bmod 257 = 127$ (`(85 * 127) % 257 = 1`),
     - $c_{1234} = (5 \cdot 17 \cdot 257)^{-1} \bmod 65537 = 32767$ (`(21845 * 32767) % 65537 = 1`),
     computing:
     - $v_1 = r_1 \bmod 5$,
     - $v_2 = ((r_2 + 17 - v_1 \bmod 17) \cdot 7) \bmod 17$,
     - $x_{12} = v_1 + 5 \cdot v_2$,
     - $v_3 = ((r_3 + 257 - x_{12} \bmod 257) \cdot 127) \bmod 257$,
     - $x_{123} = x_{12} + 85 \cdot v_3$,
     - $v_4 = ((r_4 + 65537 - x_{123} \bmod 65537) \cdot 32767) \bmod 65537$,
     - `garnerReconstruct4 r1 r2 r3 r4 = x_{123} + 21845 * v_4`.
   - Prove `garnerReconstruct4_lt` (`garnerReconstruct4 r1 r2 r3 r4 < fermatTowerMod4`) and `garnerReconstruct4_sound`:
     for every $x < \text{fermatTowerMod4}$,
     `garnerReconstruct4 (x % 5) (x % 17) (x % 257) (x % 65537) = x`
     without $O(M_4^2)$ intermediate big-modulus multiplications.

3. **Sharp Convolution Wrap-Around Safety Certificates (`ntt_convolution_no_wraparound`, `fermat_tower_conv_bound_certs`)**
   - Prove `ntt_convolution_no_wraparound`: for any transform length $N$ and any index-bounded coefficient sequences `a b : Nat → Nat` satisfying `∀ i < N, a i ≤ B` and `∀ j < N, b j ≤ B`, every sum of $N$ pairwise products $a_i \cdot b_j$ is bounded above by $N \cdot B^2$, and if $N \cdot B^2 < \text{fermatTowerMod4}$ then each raw convolution coefficient $c$ satisfies `c < fermatTowerMod4` and is recovered identically by `garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c` (and specialize cleanly to `Vec16` / `exactIntCyclicConv16` or convolution fold sums).
   - Prove `fermat_tower_conv_bound_certs` certifying the sharp maximum single-limb bounds:
     - $N = 4$: $B \le 18{,}918$ (`4 * 18918^2 = 1431562896 < M_4 < 4 * 18919^2 = 1431714244`),
     - $N = 8$: $B \le 13{,}377$ (`8 * 13377^2 = 1431553032 < M_4 < 8 * 13378^2 = 1431767072`),
     - $N = 16$: $B \le 9{,}459$ (`16 * 9459^2 = 1431562896 < M_4 < 16 * 9460^2 = 1431865600`).

4. **Axiom Audit & CLI Output**
   - Add Part 29 `#print axioms` checks in `tests/TestAxioms.lean` for all new `CrtNttUniversal` theorems (`ZERO Classical.choice`, `ZERO sorryAx`).
   - Update `Main.lean` Part 10 CLI output to display the certified 4-prime Garner mixed-radix inverses `(7, 127, 32767)` and sharp wrap-around-safe limb limits `B ≤ 18918 / 13377 / 9459` for `N = 4 / 8 / 16`.

## Acceptance Criteria
- Zero `Classical.choice` and zero `sorryAx` (`#print axioms` limited to `[]`, `[propext]`, or `[propext, Quot.sound]`).
- All modified `.lean` files adhere to $\le 120$ characters per line with intact `-- Path:` headers and `-- end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #45: feat(provenance): unified zero-axiom provenance theorem and README architecture audit
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T08:24:08Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/45

### Description

## Motivation
Across Issues #11–#42 and PRs #1–#44, `leanasm` has grown into a 26-module verified library spanning `MiniVM` assembly, `F_17` NTT execution, 192-digit Fermat-tower Garner CRT-NTT arithmetic, 100-digit Chudnovsky `pi`, 2D analytic zero-free regions / QRH / Chebyshev envelopes, Collatz Diophantine barriers, and genus-2 Hasse–Weil / BSD / Cantor–Mumford Jacobian certificates—while [`README.md`](README.md) still describes only the original 2-module starter layout (`Conjectures.lean` and `MiniVM.lean`).

This issue adds a top-level constructive synthesis module `src/LeanAsm/ProvenanceSummary.lean` tying together the headline zero-axiom theorems across all 11 CLI parts into a single master theorem `LeanAsm.leanasm_full_provenance_certified`, audits its full transitive axiom closure in `tests/TestAxioms.lean`, surfaces it in `Main.lean`, and brings `README.md` up to date with the full 27-module architecture.

## Technical Deliverables

1. **Top-Level Synthesis Module (`src/LeanAsm/ProvenanceSummary.lean`, exported in `src/LeanAsm.lean`):**
   - Import the core domain modules: `LeanAsm.MiniVM`, `LeanAsm.MiniVMNttBridge`, `LeanAsm.Conjectures`, `LeanAsm.YangMillsToy`, `LeanAsm.YangMillsQ8`, `LeanAsm.QuasiRiemann`, `LeanAsm.QuasiRiemann.UltraDeep72`, `LeanAsm.QuasiRiemann.AsymptoticZfr`, `LeanAsm.QuasiRiemann.AsymptoticZfrBridge`, `LeanAsm.QuasiRiemann.ZeroDensityBridge`, `LeanAsm.RnsArithmetic`, `LeanAsm.FiniteFieldRH`, `LeanAsm.Genus2Jacobian`, `LeanAsm.EulerFactorNonVanishing`, `LeanAsm.WeilZetaBridge`, `LeanAsm.NttArithmetic`, `LeanAsm.CrtNtt`, `LeanAsm.CrtNttUniversal`, `LeanAsm.CollatzQrhBridge`, and `LeanAsm.PiChudnovsky`.
   - Define and prove `LeanAsm.leanasm_full_provenance_certified : Prop` as a single closed conjunction synthesizing headline theorems across all 11 CLI parts (universally quantifying parameterized soundness theorems such as `MiniVMNttBridge.ntt2AsmF17_sound`, `MiniVMNttBridge.ntt4AsmF17_sound`, `MiniVMNttBridge.intt4_ntt4_asm_F17_roundtrip`, `CrtNtt.garnerReconstruct4_sound`, `CrtNtt.karatsubaCrtNttMul192_universal_sound`), including:
     - **Part 1 (`MiniVM` & `MiniVMNttBridge`):** `MiniVM.exec_garner_crt_sound`, 2-pt (`289` states) and 4-pt (`83,521` states) `F_17` NTT assembly soundness & roundtrip.
     - **Part 2 (`Conjectures` & `CollatzQrhBridge`):** `Conjectures.collatz_one_reaches_one`, `CollatzQrhBridge.collatz_no_exact_power_resonance`, `CollatzQrhBridge.baker_effective_measure_485_306_verified`, `CollatzQrhBridge.collatz_cycle_length_lower_bound_306`.
     - **Parts 3–4 (`YangMillsToy` & `YangMillsQ8`):** `YangMillsToy.plaquette_action_gauge_invariant` and `YangMillsQ8.q8_trace_conjugation_invariant`.
     - **Part 5 (`QuasiRiemann`, `UltraDeep72`, `AsymptoticZfr`, `ZeroDensityBridge`):** `QuasiRiemann.qrh_full_descent_chain_certified`, `QuasiRiemann.ultra_deep_rects_down_to_0501_certified`, `QuasiRiemann.high_height_dirichlet_rects_1e12_certified`, `QuasiRiemann.dvp_asymptotic_zero_free_region`, `QuasiRiemann.dirichlet_l2_zeta_and_mobius_certs`, `QuasiRiemann.zero_density_and_dvp_combined_region`, `QuasiRiemann.qrh_chebyshev_savings_certs`, `QuasiRiemann.qrh_chebyshev_benchmark_certs`.
     - **Parts 6 & 8 (`RnsArithmetic` & `EulerFactorNonVanishing`):** `RnsArithmetic.garner_mul_concrete_soundness`, `EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs`, `EulerFactorNonVanishing.fermat_tower_dedekind_euler_strip_certs`.
     - **Part 7 (`FiniteFieldRH`, `Genus2Jacobian`, `WeilZetaBridge`):** `FiniteFieldRH.hasse_weil_riemann_hypothesis`, `FiniteFieldRH.genus2_frob_negative_discriminants`, `FiniteFieldRH.genus2_L_at_1_qrat`, `Genus2Jacobian.jacobian_group_axioms_on_orbit`, `WeilZetaBridge.weil_zeta_punctured_strip_regular_and_nonzero`, `WeilZetaBridge.genus2_completed_zeta_reflection`.
     - **Parts 9–10 (`NttArithmetic` & `CrtNttUniversal`):** `NttArithmetic.cyclic_conv4_ntt_universal_F17`, `CrtNtt.karatsubaCrtNttMul192_universal_sound`, `CrtNtt.fermat_tower_crt_modulus_bounds`, `CrtNtt.garnerReconstruct4_sound`, `CrtNtt.fermat_tower_conv_bound_certs`.
     - **Part 11 (`PiChudnovsky`):** `PiChudnovsky.pi_105_traps_all_chudnovsky_truncations` and `PiChudnovsky.pi_100_digits_certified`.
   - Note: Re-exporting via `import LeanAsm.ProvenanceSummary` in `src/LeanAsm.lean` makes it immediately available to `Main.lean` and `tests/TestAxioms.lean`.

2. **Master Axiom Audit (`tests/TestAxioms.lean` Part 31):**
   - Add Part 31 `#print axioms LeanAsm.leanasm_full_provenance_certified` (plus any component summary theorems) confirming strictly `[propext, Quot.sound]` (or empty), with **ZERO `Classical.choice`** and **ZERO `sorryAx`** across the entire transitive dependency cone.

3. **CLI Summary & Repository Documentation (`Main.lean` & `README.md`):**
   - Update `Main.lean` footer / summary output to report the unified `LeanAsm.leanasm_full_provenance_certified` verification status.
   - Update `README.md` (respecting max 80 columns for markdown/text and intact header/footer) with:
     - Full **27-module architecture overview** (`src/LeanAsm.lean`, 17 modules in `src/LeanAsm/` including `ProvenanceSummary.lean`, 3 in `src/LeanAsm/PiChudnovsky/`, 5 in `src/LeanAsm/QuasiRiemann/`, plus `Main.lean`).
     - **CLI Parts 1–11 summary** matching `Main.lean`.
     - **Zero-axiom verification workflow** (`make build-incremental`, `lake env lean tests/TestAxioms.lean`, `make sync`).
     - **Module-by-module theorem inventory table** linking modules to namespaces and flagship theorems.

## Acceptance Criteria
- `LeanAsm.leanasm_full_provenance_certified` compiles with ZERO `Classical.choice` and ZERO `sorryAx` across its full transitive dependency cone.
- All `.lean` files satisfy `<= 120` chars/line and `.md` files satisfy `<= 80` chars/line, with intact `Path:` headers and `end of file:` footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly on the final commit.

---

## Issue #49: feat(qrh): constructive short-interval prime bounds and rational exponent ladder in ShortIntervalPrimes.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T19:38:27Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/49

### Description

## Goal

Add `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` (exported from `src/LeanAsm.lean`) extending our `v1.0.0` (`1ed68c0`) QRH $\theta = 7/8$ and $\theta = 3/4$ Chebyshev remainder envelopes and zero-density bounds in [`ZeroDensityBridge.lean`](src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean) to constructive short-interval prime guarantees $\psi(x + h) - \psi(x)$, maximal prime-gap bounds $p_{n+1} - p_n \le h$, and the rational short-interval exponent ladder

$$\frac{1}{2} < \frac{17}{30} < \frac{7}{12} < \frac{2}{3} < \frac{3}{4} < \frac{7}{8} < 1$$

with **ZERO** `Classical.choice` and **ZERO** `sorryAx`.

## Context

On `main` (`1ed68c0`, `v1.0.0`):
- `src/LeanAsm/QuasiRiemann.lean` defines `QRat` zero-density slopes (`zeroDensityHypothesis`, `zeroDensityGuthMaynard`, `zeroDensityHuxley`, `zeroDensityIngham`) and `primeGapExponent` (`1/2 < 17/30 < 7/12 < 2/3`).
- `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` defines `ChebyshevRemainderSpec`, `qrhRemainderBoundAtTenPow`, `tenPowThetaExactExp`, `tenPowThetaCeilExp`, `chebyshevLogEnv`, `chebyshevLogSqEnv`, `qrhThresholdThreeQuarters`, `qrhThresholdSevenEighths`, and certifies `qrh_theta_ladder_certs` and `qrh_chebyshev_benchmark_certs` (including the all-rung $x = 10^{336}$ crossover).
- `src/LeanAsm/ProvenanceSummary.lean` bundles Part 5 certificates into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified`, which feeds `LeanAsm.leanasm_full_provenance_certified`.

What is missing is the constructive bridge from Chebyshev remainder envelopes $|\psi(x) - x| \le E(x, \theta)$ to short-interval prime existence $\vartheta(x + h) - \vartheta(x) > 0$, contrapositive prime-gap bounds, and the unified density-to-QRH short-interval exponent ladder.

## Technical Deliverables

### 1. New Module `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` (exported in `src/LeanAsm.lean`)

- **Imports & Reuse**:
  - Import `LeanAsm.QuasiRiemann.ZeroDensityBridge` (namespace `QuasiRiemann`) and reuse its cleared-denominator `QRat` arithmetic, `ChebyshevRemainderSpec`, `qrhRemainderBoundAtTenPow`, and `qrhThresholdThreeQuarters` / `qrhThresholdSevenEighths` definitions.
- **`ShortIntervalChebyshevSpec` & `HasGuaranteedPrime`**:
  - Define `ShortIntervalChebyshevSpec` capturing the interval parameters:
    - `thetaNum : Nat`
    - `thetaDen : Nat`
    - `xScaleExp : Nat`
    - `hScaleExp : Nat`
    - `errUpper : Nat`
    - `primePowerCorr : Nat`
    (plus any structural positivity invariants needed, e.g. `0 < thetaDen`, `thetaNum < thetaDen`).
  - Define `HasGuaranteedPrime (spec : ShortIntervalChebyshevSpec) : Prop := 2 * spec.errUpper + spec.primePowerCorr < 10 ^ spec.hScaleExp` (with a `Decidable` instance where helpful), certifying $\vartheta(x + h) - \vartheta(x) > 0$ and hence at least one prime in $[x, x + h]$.
- **Differenced Chebyshev Bounds (`short_interval_psi_diff_bound`)**:
  - Prove `short_interval_psi_diff_bound` deriving differenced Chebyshev bounds $|\psi(x + h) - \psi(x) - h| \le 2 E(2x, \theta)$ from `ChebyshevRemainderSpec` for $1 \le h \le x$ (in exact integer/cleared-denominator form without real-number axioms), showing how $|\psi(x + h) - (x + h)| \le E(2x, \theta)$ and $|\psi(x) - x| \le E(2x, \theta)$ imply $|\psi(x + h) - \psi(x) - h| \le 2 E(2x, \theta)$, and subtracting the prime-power correction yields $\vartheta(x + h) - \vartheta(x) > 0$ under `HasGuaranteedPrime`.
- **Short-Interval Positivity Witnesses & Maximal Prime-Gap Bounds**:
  - Prove `qrh_short_interval_positivity_certs` certifying exact cleared-denominator scale witnesses where `HasGuaranteedPrime` holds across:
    - $\theta = 7/8$: $x = 10^{336}, h = 10^{308}$ (with `xScaleExp = 336`, `hScaleExp = 308`, matching `qrh_chebyshev_benchmark_certs` $k = 28$ where $x^{7/8} = 10^{294}$);
    - $\theta = 3/4$: $x = 10^{168}, h = 10^{140}$ (matching $x^{3/4} = 10^{126}$);
    - $\theta = 1/2$ (RH benchmark): $x = 10^{168}, h = 10^{98}$ (matching $x^{1/2} = 10^{84}$).
  - Note: Avoid unfolding $10^{336}$ / $10^{308}$ directly in kernel reduction; use power-of-ten factoring lemmas analogous to `tenPow_rel_err_lt_inv10` in `ZeroDensityBridge.lean` so compilation stays fast and clean under `exponentiation.threshold`.
  - Prove contrapositive maximal prime-gap bounds `qrh_maximal_prime_gap_bound` showing that if no prime lies in $(x, x + h]$ (or $[x, x + h]$) then `¬ HasGuaranteedPrime`, yielding $p_{n+1} - p_n \le h$ from `HasGuaranteedPrime`.
- **Rational Short-Interval Exponent Ladder**:
  - Define `shortIntervalDensityExponent (aNum aDen : Nat) : QRat` representing the Huxley–Hoheisel exponent $1 - 1/A = 1 - a_{\text{den}} / a_{\text{num}}$ (consistent with `QuasiRiemann.primeGapExponent`).
  - Prove `short_interval_density_ladder_strict` certifying in cleared-denominator `QRat` arithmetic:
    $$\frac{1}{2} < \frac{17}{30}\text{ (Guth–Maynard)} < \frac{7}{12}\text{ (Huxley)} < \frac{2}{3}\text{ (Ingham)} < \frac{3}{4}\text{ (QRH } 3/4\text{)} < \frac{7}{8}\text{ (QRH } 7/8\text{)} < 1$$
    alongside the exact gap differences:
    - $7/12 - 17/30 = 1/60$
    - $7/8 - 17/30 = 37/120$.

### 2. Provenance Integration, Axiom Audit, CLI & Documentation

- **`src/LeanAsm.lean`**:
  - Export `import LeanAsm.QuasiRiemann.ShortIntervalPrimes`.
- **`src/LeanAsm/ProvenanceSummary.lean`**:
  - Import `LeanAsm.QuasiRiemann.ShortIntervalPrimes` and wire the headline short-interval theorem(s) into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`).
- **`tests/TestAxioms.lean` (Part 32)**:
  - Add Part 32 `#print axioms` checks confirming all new `ShortIntervalPrimes` headline theorems (and updated `quasiRiemann_provenance_certified` / `leanasm_full_provenance_certified`) depend strictly on `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO** `Classical.choice`, **ZERO** `sorryAx`).
- **`Main.lean` (Part 5)**:
  - Update Part 5 CLI output to display the short-interval prime positivity scales ($\theta = 7/8$ at $10^{336}/10^{308}$, $\theta = 3/4$ at $10^{168}/10^{140}$, $\theta = 1/2$ at $10^{168}/10^{98}$) and the `1/2 < 17/30 < 7/12 < 2/3 < 3/4 < 7/8 < 1` exponent ladder.
- **`README.md`**:
  - Add `QR/ShortIntervalPrimes.lean` to the module inventory table (updating module counts accordingly) and update the Part 5 summary, keeping `README.md` strictly at $\le 80$ columns with intact `-- Path:` / `<!-- end of file: ... -->` markers.

## Acceptance Criteria

- **Zero Axioms**: `#print axioms` for every new theorem in `ShortIntervalPrimes` and `LeanAsm.leanasm_full_provenance_certified` is limited strictly to `[]`, `[propext]`, or `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
- **Formatting & Hygiene**: All `.lean` files adhere to $\le 120$ characters per line, `README.md` adheres to $\le 80$ characters per line, and every modified/added file has intact `-- Path:` / `# Path:` headers and `-- end of file:` / `<!-- end of file: -->` footers.
- **Verification**: `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly with 0 errors and 0 warnings.


---

## Issue #51: feat(qrh): Fermat-tower arithmetic-progression short-interval primes and sub-3/4 QRH ladder
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T19:51:08Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/51

### Description

## Goal

Extend `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` with:
1. Constructive arithmetic-progression (AP) short-interval prime guarantees modulo the Fermat-tower primes $\{5, 17, 257, 65537\}$ (linked directly to `src/LeanAsm/EulerFactorNonVanishing.lean`).
2. Sub-$3/4$ QRH threshold rungs (`2/3`, `5/8`, `9/16`) extending the cleared-denominator short-interval ladder `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` with exact positivity scales.

All proofs must depend strictly on `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO** `Classical.choice`, **ZERO** `sorryAx`) and build with **0 warnings**.

## Context

On `main` (`42724e5`):
- `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` defines `ShortIntervalChebyshevSpec`, `HasGuaranteedPrime`, `qrhRemainderBoundAtTwoTenPow`, `short_interval_psi_diff_bound`, `qrh_short_interval_positivity_certs` ($\theta = 7/8$ at $(10^{336}, 10^{308})$, $\theta = 3/4$ at $(10^{168}, 10^{140})$, $\theta = 1/2$ at $(10^{168}, 10^{98})$), `qrh_maximal_prime_gap_bound`, and `short_interval_density_ladder_strict`.
- `src/LeanAsm/EulerFactorNonVanishing.lean` defines `fermatNumber`, `fermatTowerPrimes` (`[5, 17, 257, 65537]`), `fermat_tower_product_eq_2pow32_sub_1`, `FermatTowerStripCert`, and `fermat_tower_euler_product_strip_certs`.
- `src/LeanAsm/ProvenanceSummary.lean` bundles Part 5 into `ShortIntervalPrimesProp` inside `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified`.

## Technical Deliverables

### 1. Fermat-Tower AP Short-Interval Envelopes (`src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`)

- **Imports & Reuse**:
  - Import `LeanAsm.EulerFactorNonVanishing` alongside `LeanAsm.QuasiRiemann.ZeroDensityBridge`.
  - Reuse `EulerFactorNonVanishing.fermatTowerPrimes` (`[5, 17, 257, 65537]`) and `EulerFactorNonVanishing.FermatTowerStripCert`.
- **`ApShortIntervalSpec` & `HasGuaranteedApPrime`**:
  - Define `ApShortIntervalSpec` extending `ShortIntervalChebyshevSpec` with modulus `q : Nat`, totient `phiQ : Nat` (and positivity/validity invariants such as `0 < phiQ`, `phiQ < q`).
  - Define the AP prime-existence predicate:
    `HasGuaranteedApPrime (s : ApShortIntervalSpec) : Prop := s.phiQ * (2 * s.base.errUpper + s.base.primePowerCorr) < 10 ^ s.base.hScaleExp`
    (with a `Decidable` instance), certifying $\vartheta(x + h; q, a) - \vartheta(x; q, a) > 0$ for every reduced residue class $a \bmod q$ with $\gcd(a, q) = 1$.
  - Prove a general AP differenced Chebyshev bridge lemma (`ap_short_interval_psi_diff_bound`) showing constructively (without `Classical.choice`) that `HasGuaranteedApPrime` forces `0 < thetaApXH - thetaApX` whenever `|φ(q) * ψ(y; q, a) - y| ≤ φ(q) * errUpper` at `x` and `x + h` and the AP prime-power correction is at most `primePowerCorr`.
- **`fermat_tower_ap_short_interval_certs`**:
  - Certify `HasGuaranteedApPrime` for every modulus $q \in \{5, 17, 257, 65537\}$ ($\varphi(F_k) = F_k - 1 \in \{4, 16, 256, 65536\}$, absorbing $\varphi(65537) = 65536 < 10^5$) under both:
    - $\theta = 7/8$ (`shortIntervalQrh78Spec` scale $x = 10^{336}, h = 10^{308}$), and
    - $\theta = 3/4$ (`shortIntervalQrh34Spec` scale $x = 10^{168}, h = 10^{140}$),
    while also recording compatibility with `EulerFactorNonVanishing.fermatTowerPrimes` and `EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs`.

### 2. Sub-3/4 QRH Rungs (`2/3`, `5/8`, `9/16`) (`src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`)

- Define exact `QRat` threshold constants (`qrhThresholdTwoThirds := QRat.mk' 2 3`, `qrhThresholdFiveEighths := QRat.mk' 5 8`, `qrhThresholdNineSixteenths := QRat.mk' 9 16`) and benchmark `ShortIntervalChebyshevSpec` witnesses at exact `(xScaleExp, hScaleExp)` scales (using symbolic power-of-ten factoring with `set_option exponentiation.threshold 2000 in` where needed so compilation has zero warnings).
- Prove `sub_three_quarters_qrh_ladder_certs` certifying:
  1. Strict `QRat` chain `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` (plus `chebyshevGap` ordering).
  2. Exact `HasGuaranteedPrime` positivity witnesses at minimal certified scales `(xScaleExp, hScaleExp)` for each sub-$3/4$ rung $\theta \in \{2/3, 5/8, 9/16\}$ (matching exact `tenPowThetaCeilExp` exponents and `primePowerCorr > 2 * sqrt(2x) * ln(2x)`).

### 3. Provenance, Axiom Audit, CLI & Documentation

- **`src/LeanAsm/ProvenanceSummary.lean`**:
  - Wire `fermat_tower_ap_short_interval_certs` and `sub_three_quarters_qrh_ladder_certs` (and `ap_short_interval_psi_diff_bound`) into `ShortIntervalPrimesProp` / `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`).
- **`tests/TestAxioms.lean` (Part 33)**:
  - Add Part 33 `#print axioms` checks confirming every new theorem in `ShortIntervalPrimes` (and updated `quasiRiemann_provenance_certified` / `leanasm_full_provenance_certified`) depends strictly on `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO** `Classical.choice`, **ZERO** `sorryAx`).
- **`Main.lean` (Part 5) & `README.md`**:
  - Update `Main.lean` Part 5 CLI output to display the Fermat-tower AP short-interval prime certificates (`q ∈ {5, 17, 257, 65537}`, `θ ∈ {3/4, 7/8}`) and the `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` sub-3/4 QRH ladder.
  - Update `README.md` (keeping all lines at most 80 characters) to document Part 33 and the new `ShortIntervalPrimes` headline theorems.

## Acceptance Criteria

- **Zero Axioms & Zero Warnings**: `#print axioms` for every new theorem and `LeanAsm.leanasm_full_provenance_certified` shows zero `Classical.choice` and zero `sorryAx`; `make build-incremental` emits 0 errors and 0 warnings (`set_option exponentiation.threshold 2000 in` scoped where needed).
- **Formatting & Hygiene**: All `.lean` files adhere to $\le 120$ characters per line and `README.md` adheres to $\le 80$ characters per line, with intact `-- Path:` / `# Path:` headers and `-- end of file:` / `<!-- end of file: -->` footers.
- **Verification**: `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.


---

## Issue #53: feat(minivm): parametric 4-prime Fermat-tower NTT and Garner CRT assembly compilation
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T20:01:37Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/53

### Description

## Summary

Extend `src/LeanAsm/MiniVMNttBridge.lean` from single-modulus $\mathbb{F}_{17}$ 4-point NTT/INTT compilation to:
1. Parametric 4-point NTT/INTT `MiniVM` assembly compilation (`ntt4Asm` / `intt4Asm`) certified symbolically across all four Fermat-tower primes `(p, ω₄) ∈ {(5, 2), (17, 4), (257, 16), (65537, 256)}` (matching `CrtNttUniversal.lean` / `NttArithmetic.lean`),
2. Compiled 4-channel Garner mixed-radix CRT reconstruction (`garnerReconstruct4Asm`) over moduli `(5, 17, 257, 65537)` (`M₄ = 1,431,655,765`) with precomputed inverses `(7, 127, 32767)` on `MiniVM`, and
3. An end-to-end 4-point CRT-NTT cyclic convolution assembly bridge theorem (`crtNtt4ConvAsm_sound`) closing the vertical loop between `MiniVM.lean`, `CrtNttUniversal.lean`, and `src/LeanAsm/PiChudnovsky/CrtMulBridge.lean` with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

---

## Context & Existing Building Blocks

- [`src/LeanAsm/MiniVM.lean`](src/LeanAsm/MiniVM.lean): Defines `Reg` (`r0, r1, r2, r3, t0, t1`), `State`, `Instr` (`movImm`, `movReg`, `addReg`, `addImm`, `subReg`, `modImm`, `mulModReg`), `runProgram`, `runProgram_append`, and 2-channel `garnerCrtProgram`.
- [`src/LeanAsm/MiniVMNttBridge.lean`](src/LeanAsm/MiniVMNttBridge.lean): Defines `ntt4AsmF17`, `intt4AsmF17`, `ntt4AsmF17_sound`, and `intt4_ntt4_asm_F17_roundtrip` over $\mathbb{F}_{17}$ using `NttArithmetic.Vec4`, `NttArithmetic.ntt4`, and `NttArithmetic.intt4`.
- [`src/LeanAsm/CrtNttUniversal.lean`](src/LeanAsm/CrtNttUniversal.lean): Defines `fermatTowerMod4` (`5 * 17 * 257 * 65537 = 1431655765`), `garnerReconstruct4`, `garnerReconstruct4_lt`, `garnerReconstruct4_sound`, `convPairSum`, `ntt_convolution_no_wraparound`, and `fermat_tower_conv_bound_certs` (wrap-around bound `B ≤ 18918` for `N = 4`).
- [`src/LeanAsm/PiChudnovsky/CrtMulBridge.lean`](src/LeanAsm/PiChudnovsky/CrtMulBridge.lean): Consumes `CrtNttUniversal` for base-1000 CRT-NTT arithmetic.
- [`src/LeanAsm/ProvenanceSummary.lean`](src/LeanAsm/ProvenanceSummary.lean): Defines `MiniVmProvenance`, `miniVm_provenance_certified`, and `leanasm_full_provenance_certified`.
- [`tests/TestAxioms.lean`](tests/TestAxioms.lean): Part 30 audits `MiniVMNttBridge.*`; Part 31 audits `*_provenance_certified`; Parts 32–33 audit `ShortIntervalPrimes`. Next audit section is **Part 34**.

---

## Deliverables

### 1. Parametric 4-Point Fermat-Tower NTT/INTT Compilation (`src/LeanAsm/MiniVMNttBridge.lean`)
- Parameterize `butterfly2`, swap, twiddle, `dit4Asm`, `ntt4Asm`, and `intt4Asm` over `(p w : Nat)` / `(p inv4 invW : Nat)` (keeping existing `ntt4AsmF17` / `intt4AsmF17` APIs intact and unbreaking).
- Define a bundled parameter record or table (e.g., `FermatNtt4Params`) covering all four Fermat-tower primes $F_k = 2^{2^k} + 1$ ($k \in \{1, 2, 3, 4\}$) with canonical $4$-th roots $\omega_4 = 2^{2^{k-1}}$ ($\omega_4^2 \equiv -1 \pmod{F_k}$):
  - `(p = 5,     ω₄ = 2,   invW = 3,     inv4 = 4)`
  - `(p = 17,    ω₄ = 4,   invW = 13,    inv4 = 13)`
  - `(p = 257,   ω₄ = 16,  invW = 241,   inv4 = 193)`
  - `(p = 65537, ω₄ = 256, invW = 65281, inv4 = 49153)`
- Define `ntt4AsmFermat (p w : Nat)` and `intt4AsmFermat (p inv4 invW : Nat)` (and/or parameterized `ntt4Asm` / `intt4Asm`).
- Prove **symbolic** soundness and roundtrip invertibility over arbitrary `a b c d : Nat` with `a < p`, `b < p`, `c < p`, `d < p` (no brute-force enumeration, since $65537^4$ states is infeasible):
  - `ntt4AsmFermat_sound` matching `NttArithmetic.ntt4 p w ⟨a, b, c, d⟩`
  - `intt4AsmFermat_sound` matching `NttArithmetic.intt4 p inv4 invW ⟨a, b, c, d⟩`
  - `intt4_ntt4_asm_fermat_roundtrip` across all four Fermat-tower parameter tuples `{(5, 2, 3, 4), (17, 4, 13, 13), (257, 16, 241, 193), (65537, 256, 65281, 49153)}`.

### 2. Compiled 4-Channel Garner CRT Reconstruction & End-to-End Convolution Bridge
- Import `LeanAsm.CrtNttUniversal` in `src/LeanAsm/MiniVMNttBridge.lean` (or share cleanly without circular imports).
- Define `garnerReconstruct4Asm : List MiniVM.Instr` compiling `CrtNtt.garnerReconstruct4` for moduli `(5, 17, 257, 65537)` and precomputed mixed-radix inverses `(7, 127, 32767)` onto `MiniVM` (taking residues `(r0, r1, r2, r3)` in registers `(r0, r1, r2, r3)` using scratch `(t0, t1)` and existing `MiniVM.Instr` operations such as `modImm`, `addImm`, `subReg`, `mulModReg` with `CrtNtt.fermatTowerMod4`, outputting the reconstructed value in `r0`).
- Prove `garnerReconstruct4Asm_sound`: for any initial state `s` with `s.r0 = x % 5`, `s.r1 = x % 17`, `s.r2 = x % 257`, `s.r3 = x % 65537` and `x < CrtNtt.fermatTowerMod4` (`1,431,655,765`) (or equivalently `r0 < 5, r1 < 17, r2 < 257, r3 < 65537` matching `CrtNtt.garnerReconstruct4 r0 r1 r2 r3`), `(MiniVM.runProgram s garnerReconstruct4Asm).r0 = CrtNtt.garnerReconstruct4 ... = x`.
- Prove `crtNtt4ConvAsm_sound`: end-to-end 4-point CRT-NTT cyclic convolution assembly bridge theorem showing that running the 4 Fermat-tower `MiniVM` channels `(ntt4AsmFermat → pointwise mod p → intt4AsmFermat)` on normalized 4-vectors `a, b` with coefficients `≤ 18,918` (`B ≤ 18918` from `CrtNtt.fermat_tower_conv_bound_certs`) and passing each resulting residue lane into `garnerReconstruct4Asm` recovers the exact integer 4-point cyclic convolution coefficient `< M₄` (`1,431,655,765`) with zero wrap-around error.

### 3. Provenance Wiring, Axiom Audit, CLI & Documentation
- **`src/LeanAsm/ProvenanceSummary.lean`**: Extend `MiniVmProvenance` and `miniVm_provenance_certified` (and transitively `leanasm_full_provenance_certified`) to include the parametric 4-prime `ntt4AsmFermat` / `intt4AsmFermat` roundtrip, `garnerReconstruct4Asm_sound`, and `crtNtt4ConvAsm_sound`.
- **`tests/TestAxioms.lean`**: Add **Part 34** checking `#print axioms` on all newly added parametric NTT, `garnerReconstruct4Asm_sound`, `crtNtt4ConvAsm_sound`, and `miniVm_provenance_certified` / `leanasm_full_provenance_certified` (confirming zero `Classical.choice` and zero `sorryAx`).
- **`Main.lean`**: Update Part 1 CLI summary output to report the 4-prime parametric NTT/INTT assembly & compiled 4-channel Garner CRT bridge checks.
- **`README.md`**: Document the parametric Fermat-tower MiniVM NTT & 4-channel Garner CRT assembly guarantees (respecting `README.md` max **80 columns** and header/footer tags).

---

## Acceptance Criteria

- [ ] **Zero `Classical.choice`**, **zero `sorryAx`**, **zero compiler warnings**.
- [ ] Line width & format rules (`AI.md` / `AGENTS.md`):
  - `.lean` files: max **120 chars/line**, with `-- Path:` header and `-- end of file:` footer intact.
  - `README.md`: max **80 chars/line**, with `# Path:` header and `<!-- end of file: -->` footer intact.
- [ ] No `/dev/null` redirection and no silent error suppression (`|| true`, etc.) in any script or verification step.
- [ ] All checks pass cleanly on a dedicated feature branch from `main`:
  - `make build-incremental`
  - `lake env lean tests/TestAxioms.lean`
  - `lake exe leanasm` (or project test/CLI run)
  - `make sync`


---

## Issue #55: feat(collatz): higher log_2(3) convergent gaps (1054, 665) and constructive predecessor-tree density bounds
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T20:26:49Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/55

### Description

## Overview

Extend [`src/LeanAsm/CollatzQrhBridge.lean`](https://github.com/aomaker-org/leanasm/blob/main/src/LeanAsm/CollatzQrhBridge.lean) on `main` (`87a5fe6`) with:
1. Higher continued-fraction convergent gaps for $\log_2 3$ at the 318-digit convergent `(k, m) = (1054, 665)` bracketing `(485, 306)` and pushing the constructive Simons–de Weger cycle-length barrier from `m >= 307` (`K >= 793`) to `m >= 666` (`k >= 1055`, `K >= 1721`).
2. Constructive inverse Collatz predecessor trees (`collatzPredecessors`, `collatzPredTree`), backward-to-forward soundness into `Conjectures.iterate Conjectures.collatzStep`, and cleared-denominator predecessor-density growth certificates (`PredecessorDensitySpec`, `collatz_pred_tree_growth_certs`).

All proofs must maintain **ZERO `Classical.choice`**, **ZERO `sorryAx`**, and **ZERO compiler warnings**.

## Background & Existing Context

- `src/LeanAsm/CollatzQrhBridge.lean` currently verifies convergent gaps up to `(485, 306)` (`collatz_convergent_485_306_separation_certified`), Steiner 1-cycle exclusions (`steiner_1cycle_excluded_at_convergents`), and `collatz_cycle_length_lower_bound_306` (`n_min >= 936,360 => 307 <= m, 487 <= k, 793 <= k + m`).
- `src/LeanAsm/Conjectures.lean` defines `collatzStep`, `iterate`, and `CollatzReachesOne`.
- `src/LeanAsm/ProvenanceSummary.lean` bundles Part 2 theorems in `CollatzProvenance` / `collatz_provenance_certified`.
- `tests/TestAxioms.lean` audits Parts 1–34; `Main.lean` Part 2 displays verified Collatz–QRH metrics.

## Technical Deliverables

### 1. Higher Convergent Bracket `(1054, 665)` & Raised Cycle Barrier (`src/LeanAsm/CollatzQrhBridge.lean`)
- **318-digit Diophantine gap & bracket:**
  - Scope `set_option exponentiation.threshold 2000 in` where needed for evaluating `2 ^ 1054`, `3 ^ 665`, `2 ^ 1055`, and `3 ^ 666`.
  - Prove `convergent_1054_665_gap_pos : 2 ^ 1054 < 3 ^ 665 ∧ 0 < 3 ^ 665 - 2 ^ 1054` (exact 313-digit separation between 318-digit powers).
  - Prove `log2_3_convergent_bracket_665` certifying `2 ^ 1054 < 3 ^ 665`, `3 ^ 306 < 2 ^ 485`, and the cleared-denominator convergent bracket `1054 * 306 < 485 * 665` (`322524 < 322525`, i.e., `1054 / 665 < log_2(3) < 485 / 306`).
- **Steiner 1-cycle exclusion at `(1054, 665)`:**
  - Prove `steiner_1cycle_excluded_1054_665`, ruling out:
    - `(k, m) = (1054, 665)` directly for any `CollatzOddCycle 665` (since `2 ^ 1054 < 3 ^ 665` contradicts `collatz_odd_cycle_gap_pos`), and
    - the minimal upper pair `(k, m) = (1055, 665)` via `¬ ((2 ^ 1055 - 3 ^ 665) ∣ (3 ^ 665 - 2 ^ 665))` and `steiner_1cycle_divides`.
- **Simons–de Weger barrier pushed to `m >= 666`:**
  - Prove `simons_de_weger_barrier_665` extending the conditional barrier over `1 <= m <= 665` (using the `n_min >= 936,360` verification floor and `2 ^ 1054 < 3 ^ 665 < 3 ^ 666`, `2 ^ 1055 < 3 ^ 666`) so any non-trivial `CollatzOddCycle m` (`1 <= m`) with `936360 <= c.nMin` satisfies:
    - `666 <= m` odd steps,
    - `1055 <= cycleShift c.a m` halvings (note `2 ^ 1055 < 3 ^ 666` even yields `1056 <= cycleShift c.a m`), and
    - `1721 <= cycleShift c.a m + m` total steps.

### 2. Constructive Predecessor-Tree Cardinality & Cleared-Denominator Density Bounds (`src/LeanAsm/CollatzQrhBridge.lean`)
- **Inverse Collatz operator & depth-`d` tree:**
  - Define `collatzPredecessors (n : Nat) : List Nat`, returning `[2 * n, (n - 1) / 3]` when `n % 6 = 4 && 1 < (n - 1) / 3`, else `[2 * n]` (or empty when `n = 0`).
  - Define `collatzPredTree (d root : Nat) : List Nat` (exact depth-`d` inverse frontier via `collatzPredecessors`, using `flatMap`).
- **Soundness & mod-6 branching:**
  - Prove `collatzPredTree_sound`: for every `d` and `x ∈ collatzPredTree d 1`, `Conjectures.iterate Conjectures.collatzStep d x = 1`.
  - Prove `collatz_mod6_branching`: classifying single-step predecessor multiplicity (`2` vs `1`) modulo `6`.
- **Cleared-denominator density benchmarks:**
  - Define `PredecessorDensitySpec` capturing `expNum`, `expDen`, `depth`, `treeCard`, and cleared-denominator comparison fields benchmarking finite-depth inverse tree growth against the trivial halving spine (`treeCard > depth + 1`, e.g., at `d = 14..20` where depth-14 gives `18 > 15` and depth-20 gives `72 > 21`) and against the rational exponent ladder `3/4 < 84/100` (Krasikov–Lagarias) `< 9/10` (Mazur) `< 1`.
  - Prove `collatz_pred_tree_growth_certs`.

### 3. Provenance Integration, Axiom Audit, CLI & Docs
- Wire `convergent_1054_665_gap_pos`, `log2_3_convergent_bracket_665`, `steiner_1cycle_excluded_1054_665`, `simons_de_weger_barrier_665`, `collatzPredTree_sound`, and `collatz_pred_tree_growth_certs` into `CollatzProvenance` / `collatz_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
- Add **Part 35** `#print axioms` audits in `tests/TestAxioms.lean` confirming ZERO `Classical.choice` and ZERO `sorryAx` (`[]`, `[propext]`, or `[propext, Quot.sound]`).
- Update `Main.lean` Part 2 output to display the `(1054, 665)` convergent gap, `m >= 666` (`K >= 1721`) barrier, and constructive predecessor-tree density metrics.
- Update `README.md` (max 80 columns, updating Part 2 and Parts 1–35 references).

## Acceptance Criteria
- Zero `Classical.choice`, zero `sorryAx`, zero compiler warnings.
- Every `.lean` file at most 120 characters per line; `README.md` at most 80 characters per line; intact `-- Path:` / `-- end of file:` headers and footers.
- `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` exit `0` cleanly.

---

## Issue #57: feat(qrh): higher-truncation 2D zero-free rectangles via 4-prime CRT-NTT precision engine
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T20:44:26Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/57

### Description

## Summary

Extend `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` and `src/LeanAsm/QuasiRiemann.lean` from the existing `N = 128` (`σ ≥ 0.501`, `t ~ 10^12`) 2D zero-free rectangle certificates to higher-truncation (`N = 256` and `N = 512`) 2D zero-free rectangle certificates pushing closer to the critical line (`σ = 0.5005 = 1/2 + 1/2000` and `σ = 0.50025 = 1/2 + 1/4000`) at ultra-high heights (`t ~ 10^12` and `t ~ 10^18`), powered by the 192-digit 4-prime `{5, 17, 257, 65537}` CRT-NTT multiplication and phase-reduction engine (`PiChudnovsky.CrtMulBridge` / `CrtNttUniversal`), with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

---

## Existing Foundation to Build On

- `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`:
  - 72-digit fixed-point engine (`scale72 = 10^72`, `scale66 = 10^66`, `ScaledInterval72`), `twoPiInterval72`, `lnInterval72` (`ln_table_1_to_128_valid`), `reducePhaseModTwoPi72`, and `high_height_phase_reduction_1e12`.
  - Existing `N = 128` 2D sweepers & certificates: `IsValidDirichletRect2DN128`, `dirichletGradBoundScaled6`, `sweepRectangles2DN128`, `sweepDirichletRectangles2DN128`, `ultra_deep_rects_down_to_0501_certified` (`σ ∈ [0.501, 0.875]`), and `high_height_dirichlet_rects_1e12_certified` (`t ~ 10^12`).
- `src/LeanAsm/QuasiRiemann.lean`:
  - `DirichletRect2DCert`, `InRemainingUnknownRect2D`, `IsValidRect2DCert`, and Lipschitz step / minimum norm-squared bounds (`complexIntervalMinNormSq`).
- `src/LeanAsm/PiChudnovsky/CrtMulBridge.lean` & `src/LeanAsm/CrtNttUniversal.lean`:
  - Exact 192-digit multiplication `natMul192ViaCrtNtt` / `intMul192ViaCrtNtt` (`natMul192ViaCrtNtt_eq_mul`, `intMul192ViaCrtNtt_eq_mul`) over the four Fermat-tower primes `{5, 17, 257, 65537}`.

---

## Scope & Required Deliverables

### 1. Higher-Truncation (`N = 256` and `N = 512`) Spec & Tail Error Bounds
In `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (and supporting helpers in `src/LeanAsm/QuasiRiemann.lean` as needed):
- Define a unified specification structure `HighTruncZeroFreeRectSpec` (covering `σ`, truncation order `N ∈ {128, 256, 512}`, height range `[tLo, tHi]`, lower-bound margin `delta_N`, Euler–Maclaurin remainder/tail bound `E_tail`, and CRT-NTT/truncation error `eps_crt`) together with the constructive non-vanishing invariant:
  - `HasCertifiedNonVanishing : E_tail + eps_crt < delta_N`.
- Prove `euler_maclaurin_tail_shrinks_with_N`: an exact cleared-denominator / computable monotonic decay theorem across `N ∈ {128, 256, 512}` demonstrating that doubling `N` strictly tightens the Euler–Maclaurin `B_2` tail remainder envelope, enabling verified 2D rectangles down to `σ = 0.5005` (`1/2 + 1/2000`, `sLo6 = 500500`) and `σ = 0.50025` (`1/2 + 1/4000`, `sLo6 = 500250` or matching sub-micro-grid scaled representation).
  - *Note*: If representing `0.50025` (`1/2 + 1/4000`), use exact cleared-denominator or finer scaled coordinates (e.g. `10^-7` or rational `Nat`/`Rat`) alongside `10^-6` compatibility where needed rather than truncating `500250` improperly.

### 2. High-Precision Phase Reduction up to `N = 512` & `t ~ 10^18`
In `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`:
- Extend certified `ln` enclosures (`lnInterval72` / rational or `10^-72` interval table, leveraging multiplicative relations `ln(a * b) = ln a + ln b` plus certified prime enclosures up to `512` to keep the file compact and kernel-fast).
- Define and prove `crtNtt_phase_reduction_512_sound`: using the 192-digit CRT-NTT engine (`PiChudnovsky.CrtMulBridge.natMul192ViaCrtNtt` / `intMul192ViaCrtNtt` and `twoPiInterval72`), certify that the phase reduction `t * ln n mod 2π` across `n ≤ 512` at both `t ~ 10^12` and `t ~ 10^18` achieves interval width `< 10^-60` radians (in `10^-72` ULP units, width `< 10^12` ULPs—tight enough for `t ~ 10^18 * 10^-72` margin).

### 3. Certified 2D Zero-Free Rectangles (`(σ = 0.5005, N = 256, t ~ 10^12)` & `(σ = 0.50025, N = 512, t ~ 10^18)`)
In `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (and `src/LeanAsm/QuasiRiemann.lean` if extending generic rect predicates):
- Construct concrete verified 2D sub-rectangle certificate grids and sweepers for:
  - `(σ = 0.5005, N = 256, t ~ 10^12)`
  - `(σ = 0.50025, N = 512, t ~ 10^18)`
- Prove `crtNtt_highTrunc_2d_zero_free_rect` (and concrete certified rectangle theorems): using cleared-denominator Lipschitz derivative / gradient bounds (`dirichletGradBoundScaled6` or exact higher-precision gradient envelope) over each sub-rectangle, establish `|ζ_N(σ + it)| > 0` across the full continuous 2D sub-rectangles without `Classical.choice` or `sorryAx`.

### 4. Top-Level Provenance, Axiom Audit, CLI & Documentation
- **`src/LeanAsm/ProvenanceSummary.lean`**: Wire the new higher-truncation `HighTruncZeroFreeRectSpec`, `euler_maclaurin_tail_shrinks_with_N`, `crtNtt_phase_reduction_512_sound`, and `crtNtt_highTrunc_2d_zero_free_rect` certificates into `QuasiRiemannProvenance` and `quasiRiemann_provenance_certified`.
- **`tests/TestAxioms.lean`**: Add **Part 36** `#print axioms` checks covering all new exported theorems, plus `LeanAsm.quasiRiemann_provenance_certified` and `LeanAsm.leanasm_full_provenance_certified`.
- **`Main.lean`**: Extend **Part 5** (`Quasi-Riemann Hypothesis`) CLI summary output to print the `N = 256` (`σ = 0.5005`, `t ~ 10^12`) and `N = 512` (`σ = 0.50025`, `t ~ 10^18`) phase-reduction precision and 2D rectangle certificates computed live via the CRT-NTT engine.
- **`README.md`**: Update the QRH / UltraDeep72 section and provenance summary (`≤ 80` columns).

---

## Acceptance Criteria
- **Zero Non-Constructive Axioms**: All new definitions/theorems and `quasiRiemann_provenance_certified` / `leanasm_full_provenance_certified` use **ZERO `Classical.choice`** and **ZERO `sorryAx`** (verified via `lake env lean tests/TestAxioms.lean`).
- **Formatting & Repo Governance (`AI.md` / `AGENTS.md`)**:
  - Zero Lean compiler warnings (`0 warnings`); use `set_option exponentiation.threshold 2000 in` locally if large base-exponent powers trigger threshold warnings.
  - `.lean` files: max `120` chars/line; `README.md`: max `80` chars/line; preserve repository file path headers and `-- end of file:` / `<!-- end of file: ... -->` footers.
- **Verification**:
  - `make build-incremental` succeeds with exit code `0` and `0` warnings.
  - `lake env lean tests/TestAxioms.lean` succeeds with `0` warnings and shows only `[propext, Lean.ofReduceBool, Lean.trustCompiler]` / `[propext, quot.mk, Lean.ofReduceBool, Lean.trustCompiler]` (no `Classical.choice`, no `sorryAx`).
  - `make sync` succeeds cleanly.

---

## Issue #59: feat(langlands): GL(1) Artin factorization and MiniVM 4-point NTT character orthogonality in ArtinFermatBridge.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T22:22:52Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/59

### Description

## Summary

Create `src/LeanAsm/ArtinFermatBridge.lean` (exported from `src/LeanAsm.lean`) connecting $\mathrm{GL}(1)$ Artin factorization of Fermat-tower cyclotomic Euler factors over $\mathbb{Q}(\zeta_{F_k})$ ($F_k \in \{5, 17, 257, 65537\}$) in `LeanAsm.EulerFactorNonVanishing` to `MiniVM` 4-point NTT character orthogonality in `LeanAsm.NttArithmetic` and `LeanAsm.MiniVMNttBridge`, verified constructively with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Motivation & Existing Foundations

The repository already formalizes both sides independently:
- **`src/LeanAsm/EulerFactorNonVanishing.lean`**:
  - `fermatTowerPrimes := [5, 17, 257, 65537]` ($F_1 \dots F_4$), `fermatNumber`, `fermat_prefix_prod_eq`
  - `FermatTowerStripCert` / `fermat_tower_euler_product_strip_certs`
  - `CyclotomicSplitFactorSpec`, `cyclotomicProdMarginPow`, `cyclotomicProdNormPow`, `cyclotomicProdDenPow`, `cyclotomic_euler_product_lower_bound`, and `fermat_tower_dedekind_euler_strip_certs`
- **`src/LeanAsm/NttArithmetic.lean`**:
  - `Vec4`, `ntt4 (p w : Nat) (v : Vec4) : Vec4`, `intt4 (p inv4 invW : Nat) (X : Vec4) : Vec4`, `cyclicConv4`
- **`src/LeanAsm/MiniVMNttBridge.lean`**:
  - `FermatNtt4Spec` (`p`, `omega4`, `invOmega4`, `invFour`, `.Valid` proving `omega4^2 + 1 ≡ 0`, `omega4 * invOmega4 ≡ 1`, `4 * invFour ≡ 1 mod p`)
  - `fermatNtt4Spec5` `(5, 2, 3, 4)`, `fermatNtt4Spec17` `(17, 4, 13, 13)`, `fermatNtt4Spec257` `(257, 16, 241, 193)`, `fermatNtt4Spec65537` `(65537, 256, 65281, 49153)`, `fermatTowerNtt4Specs`, `fermatTowerNtt4Specs_valid`
  - `ntt4AsmFermat_sound`, `intt4AsmFermat_sound`, `intt4_ntt4_asm_fermat_roundtrip`, `fermatTowerNtt4_asm_roundtrip_certs`

This issue unifies the Langlands/cyclotomic $\mathrm{GL}(1)$ character decomposition of Fermat-tower local Euler factors with executable `MiniVM` 4-point NTT arithmetic.

## Technical Specification

### 1. New Module: `src/LeanAsm/ArtinFermatBridge.lean`
Export `LeanAsm.ArtinFermatBridge` from `src/LeanAsm.lean`, importing `LeanAsm.EulerFactorNonVanishing`, `LeanAsm.NttArithmetic`, and `LeanAsm.MiniVMNttBridge`:

1. **Fermat-Tower Character Specification (`ArtinFermatCharacterSpec`)**:
   - Capture $F_k = 2^{2^k} + 1 \in \{5, 17, 257, 65537\}$, totient degree $\varphi(F_k) = F_k - 1 = 2^{2^k} \in \{4, 16, 256, 65536\}$, and order-4 character generator $\omega_4 \in \{2, 4, 16, 256\}$ ($\omega_4^2 \equiv -1 \pmod{F_k}$, matching `MiniVMNttBridge.FermatNtt4Spec`).
   - Include decidable/constructive validity predicates and concrete instances for $F_1=5, F_2=17, F_3=257, F_4=65537$.

2. **Split Euler Factor Artin Collapse (`artin_split_euler_factor_collapse`)**:
   - Link `EulerFactorNonVanishing.FermatTowerStripCert` and `fermat_tower_dedekind_euler_strip_certs` for completely split primes $p \equiv 1 \pmod{F_k}$ (where every Artin character satisfies $\chi(p) = 1$) to $(1 - T)^{\varphi(F_k)}$ (`g = \varphi(F_k)` in `CyclotomicSplitFactorSpec`) and certify positive cleared-denominator Euler factor evaluations / non-vanishing lower bounds.

3. **Order-4 Cyclotomic Factorization (`artin_order4_cyclotomic_factorization`)**:
   - Certify $\prod_{j=0}^{3}(1 - \omega_4^j T) \equiv 1 - T^4 \pmod{F_k}$ constructively for all $(F_k, \omega_4) \in \{(5, 2), (17, 4), (257, 16), (65537, 256)\}$ (using cleared polynomial/coefficient congruences mod $F_k$).

4. **$\mathrm{GL}(1)$ Artin Transform = `NttArithmetic.ntt4` (`artin_char_transform_eq_ntt4`)**:
   - Define the 4-element $\mathrm{GL}(1)$ Artin Fourier transform $\hat{v}_j = \sum_{i=0}^{3} \chi_j(g^i) v_i \pmod{F_k}$ where $\chi_j(g^i) = \omega_4^{i j} \bmod F_k$, and prove it equals `NttArithmetic.ntt4 F_k \omega_4 v` across $(F_k, \omega_4) \in \{(5, 2), (17, 4), (257, 16), (65537, 256)\}$ (and universally over valid `FermatNtt4Spec`).

5. **MiniVM Character Orthogonality (`artin_char_orthogonality_minivm`)**:
   - Compose `MiniVMNttBridge.ntt4AsmFermat_sound` and `MiniVMNttBridge.intt4_ntt4_asm_fermat_roundtrip` (`fermatTowerNtt4_asm_roundtrip_certs`) to certify the discrete orthogonality identity
     $$\frac{1}{4}\sum_{j=0}^{3}\chi_j(g^i)\chi_j(g^{-m}) \equiv \delta_{i,m} \pmod{F_k}$$
     end-to-end inside `MiniVM` assembly execution for all four Fermat-tower primes.

### 2. Integration & Governance Updates
- **`src/LeanAsm.lean`**: Export `LeanAsm.ArtinFermatBridge`.
- **`src/LeanAsm/ProvenanceSummary.lean`**: Thread the certified Artin–Fermat theorems into `LeanAsm.leanasm_full_provenance_certified` (via `EulerRnsProvenance`, `CrtNttProvenance`, or a dedicated conjunct preserving existing components).
- **`tests/TestAxioms.lean`**: Add **Part 37** with `#print axioms` audits for all new theorems in `ArtinFermatBridge` plus `LeanAsm.leanasm_full_provenance_certified`, confirming only `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO `Classical.choice`**, **ZERO `sorryAx`**).
- **`Main.lean`**: Print a concise CLI summary demonstrating `ArtinFermatBridge` (`F_k ∈ {5, 17, 257, 65537}`, $\omega_4 \in \{2, 4, 16, 256\}$, and `MiniVM` 4-point NTT orthogonality check).
- **`README.md`**: Document `src/LeanAsm/ArtinFermatBridge.lean` in the Module Inventory and update `TestAxioms.lean` coverage to Parts 1–37 (strictly $\le 80$ columns).

## Acceptance Criteria
- **Zero-Axiom Purity**: `#print axioms` on every new theorem and `LeanAsm.leanasm_full_provenance_certified` reports ZERO `Classical.choice` and ZERO `sorryAx`.
- **Zero Warnings**: Clean compilation (`set_option exponentiation.threshold 2000 in` where needed for $F_4 = 65537$ / large powers).
- **Formatting & Governance**:
  - `.lean` lines $\le 120$ chars; `.md` lines $\le 80$ chars.
  - Mandatory `-- Path: leanasm/...` header and `-- end of file: leanasm/...` footer on all created/modified files.
  - `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #60: feat(langlands): GL(2) elliptic modularity Eichler-Shimura trace equality and Ramanujan bounds in EllipticModularityBridge.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T22:23:36Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/60

### Description

## Summary

Create `src/LeanAsm/EllipticModularityBridge.lean` (exported from `src/LeanAsm.lean`) verifying $\mathrm{GL}(2)$ elliptic curve modularity via Eichler–Shimura Hecke–Frobenius trace equality $c_p(f_{11}) = p + 1 - \#E_{11a1}(\mathbb{F}_p)$ for the conductor-$11$ modular curve
$$E_{11a1} : y^2 + y = x^3 - x^2 - 10x - 20$$
and its Dedekind eta-product weight-$2$ cusp form
$$f_{11}(\tau) = \eta(\tau)^2 \eta(11\tau)^2 = q \prod_{n \ge 1} (1 - q^n)^2 (1 - q^{11n})^2 = \sum_{n \ge 1} c_n(f_{11})\, q^n \in S_2(\Gamma_0(11)),$$
alongside cleared-denominator Hasse–Weil / Ramanujan–Petersson bounds, local $\mathrm{GL}(2)$ Euler-factor positivity, and Hecke multiplicativity, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations

- **`src/LeanAsm/FiniteFieldRH.lean`**:
  - Point-counting pattern (`isPointOnCurve`, `countAffinePoints`, `totalProjectivePoints`, `frobeniusTrace`, `hasse_weil_riemann_hypothesis`) certifying $a_p^2 \le 4p$ constructively with zero axioms.
- **`src/LeanAsm/WeilZetaBridge.lean`**:
  - Cleared-denominator quadratic local Euler-factor conventions and non-vanishing proofs (`genus2_L_poly_quad_factor_id`, `weil_denom_factor1_nonvanishing`, `weil_denom_factor2_nonvanishing`, `weil_denom_product_lower_bound`).

## Technical Specification

### 1. New Module: `src/LeanAsm/EllipticModularityBridge.lean`
Export `LeanAsm.EllipticModularityBridge` from `src/LeanAsm.lean`, importing `LeanAsm.FiniteFieldRH` and `LeanAsm.WeilZetaBridge` (or aligning directly with their cleared-denominator local Euler-factor conventions):

1. **Computable Weight-$2$ Cusp Form $f_{11}(\tau) = \eta(\tau)^2 \eta(11\tau)^2$**:
   - Implement exact integer truncated power-series / polynomial multiplication (e.g., `Array Int` or `List Int`) up to degree $100$ for
     $$q \prod_{n=1}^{100} (1 - q^n)^2 \prod_{m=1}^{9} (1 - q^{11m})^2 = \sum_{n=1}^{100} c_n(f_{11})\, q^n.$$
   - Expose `heckeCoeff11 (n : Nat) : Int` returning the $n$-th Fourier coefficient $c_n(f_{11})$ (verified by `decide` in kernel-checked integer arithmetic).

2. **Computable Point Count & Frobenius Trace for $E_{11a1}$**:
   - Implement exact affine solution counting modulo $p$ for $y^2 + y \equiv x^3 - x^2 - 10x - 20 \pmod p$ over $x, y \in \{0, \dots, p-1\}$ (`ec11a1PointCount (p : Nat) : Nat`, adding `1` for the point at infinity $\mathcal{O}$).
   - Define the Frobenius trace `ec11a1FrobTrace (p : Nat) : Int := (p : Int) + 1 - (ec11a1PointCount p : Int)` (matching $a_p(E_{11a1}) = p + 1 - \#E_{11a1}(\mathbb{F}_p)$).

3. **Eichler–Shimura Hecke–Frobenius Trace Equality (`eichler_shimura_trace_eq_11a1`)**:
   - Prove in kernel-checked integer arithmetic that $c_p(f_{11}) = a_p(E_{11a1})$ across all $24$ good primes $p \le 97$:
     `[2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]`,
     plus the bad-reduction multiplicative coefficient $c_{11}(f_{11}) = 1$.

4. **$\mathrm{GL}(2)$ Ramanujan–Petersson Temperedness & Local Euler-Factor Positivity (`hasse_weil_ramanujan_11a1_certs`)**:
   - Certify $a_p(E_{11a1})^2 \le 4p$ (negative discriminant $\Delta_p = a_p(E_{11a1})^2 - 4p \le 0$, and strictly $< 4p$ for prime $p$) across all $24$ good primes $p \le 97$.
   - Prove cleared-denominator positivity of the local $\mathrm{GL}(2)$ Euler factor quadratic form:
     $$\forall u\, v : \mathbb{Z},\quad 0 < v \implies 0 < v^2 - a_p(E_{11a1})\, u v + p\, u^2$$
     (via $4(v^2 - a_p u v + p u^2) = (2v - a_p u)^2 + (4p - a_p^2) u^2 > 0$) across all $24$ good primes $p \le 97$.

5. **Hecke Algebra Multiplicativity (`hecke_multiplicativity_11a1_certs`)**:
   - Certify Hecke eigenvalue multiplicativity $c_{mn}(f_{11}) = c_m(f_{11}) c_n(f_{11})$ for coprime $m, n \ge 1$ with $mn \le 100$ (e.g., all coprime pairs `m, n ≥ 2` with `m * n ≤ 100`, plus `c_1 = 1`).
   - Certify the prime-square Hecke relation $c_{p^2}(f_{11}) = c_p(f_{11})^2 - p$ for the good primes $p \in \{2, 3, 5, 7\}$.

### 2. Provenance Integration, Axiom Audit, CLI & Documentation
- **`src/LeanAsm.lean`**: Export `LeanAsm.EllipticModularityBridge`.
- **`src/LeanAsm/ProvenanceSummary.lean`**: Wire the headline `EllipticModularityBridge` theorems (`eichler_shimura_trace_eq_11a1`, `hasse_weil_ramanujan_11a1_certs`, `hecke_multiplicativity_11a1_certs`) into `LeanAsm.leanasm_full_provenance_certified`.
- **`tests/TestAxioms.lean`**: Add a new sequential `#print axioms` section confirming all new `EllipticModularityBridge` theorems and `LeanAsm.leanasm_full_provenance_certified` audit strictly to `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO `Classical.choice`**, **ZERO `sorryAx`**).
- **`Main.lean`**: Update CLI output (e.g., under Part 7 or a clear sub-section) to display the $E_{11a1}$ Eichler–Shimura Hecke–Frobenius trace matches ($p \le 97$), Ramanujan bounds $a_p^2 \le 4p$, and Hecke multiplicativity checks.
- **`README.md`**: Document `src/LeanAsm/EllipticModularityBridge.lean` and update the `TestAxioms.lean` coverage summary (strictly $\le 80$ characters per line).

## Acceptance Criteria
- **Zero-Axiom Purity**: Zero `Classical.choice`, zero `sorryAx`.
- **Zero Warnings**: Clean build with zero compiler warnings.
- **Formatting & Governance**:
  - All `.lean` files $\le 120$ chars/line; `README.md` $\le 80$ chars/line.
  - Intact `-- Path: leanasm/...` headers and `-- end of file: leanasm/...` footers.
  - `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #61: feat(langlands): GSp(4) to SO(5) functorial Euler factor lift and Selberg / Kim-Sarnak exponent ladder in GSp4FunctorialityBridge.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T22:24:36Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/61

### Description

## Summary

Create `src/LeanAsm/GSp4FunctorialityBridge.lean` (exported from `src/LeanAsm.lean`) formalizing the $\mathrm{GSp}(4) \to \mathrm{SO}(5)$ functorial lift of the genus-$2$ curve $C : y^2 = x^5 - x + 1$ over $\mathbb{F}_5$ alongside the Langlands symmetric-power / Selberg / Kim–Sarnak Ramanujan exponent ladder ($0 < 7/64 < 1/9 < 1/5 < 1/4 < 1/2$), proved constructively with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations

- **`src/LeanAsm/Genus2Jacobian.lean`**:
  - Cantor–Mumford group law on $J(C)(\mathbb{F}_5)$ (`jacobian_D0_order_71`, `jacobian_group_axioms_on_orbit`) proving $|J(C)(\mathbb{F}_5)| = 71$.
- **`src/LeanAsm/FiniteFieldRH.lean`**:
  - Point counts `#C(F_5) = 11`, `#C(F_25) = 31` (`genus2_N1_eq_11`, `genus2_N2_eq_31`), Frobenius polynomial $L_C(T) = 1 + 5T + 15T^2 + 25T^3 + 25T^4$ (`genus2LPoly`, corresponding to Spin parameters $q = 5$, $a_1 = -\mathrm{tr}(\mathrm{Frob}) = -5$, $a_2 = 15$ since `genus2TraceA1 = 5 = -a_1`), $L_C(1) = 71/25$ (`genus2_L_at_1_eq_71_div_25`), and finite-field RH (`genus2_real_trace_bounds`, `genus2_frob_negative_discriminants`).
- **`src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`** & **`src/LeanAsm/QuasiRiemann/Rat.lean`**:
  - Constructive `QRat` arithmetic and rational exponent ladder pattern (`qrh_theta_ladder_certs`).

## Technical Specification

### 1. New Module: `src/LeanAsm/GSp4FunctorialityBridge.lean`
Export `LeanAsm.GSp4FunctorialityBridge` from `src/LeanAsm.lean`, importing `LeanAsm.Genus2Jacobian`, `LeanAsm.FiniteFieldRH` (for `genus2LPoly` / trace data), and `LeanAsm.QuasiRiemann.ZeroDensityBridge`:

1. **$\mathrm{GSp}(4) \to \mathrm{SO}(5)$ Standard Euler-Factor Lift (`gsp4StandardEulerPoly`, `gsp4_std_functional_equation`)**:
   - Given a cleared-denominator degree-$4$ $\mathrm{GSp}(4)$ Spin Euler polynomial
     $$L_{\mathrm{spin}}(T) = 1 - a_1 T + a_2 T^2 - q a_1 T^3 + q^2 T^4,$$
     define the cleared-denominator degree-$5$ $\mathrm{PGSp}(4) \cong \mathrm{SO}(5)$ Standard Euler polynomial (corresponding to $\bigwedge^2 V_\ell(J(C)) \otimes \mathrm{sim}^{-1}$):
     $$\begin{aligned}
     q \cdot L_{\mathrm{std}}(T) &= (1 - T)\bigl(q - (a_2 - 2q)T + (a_1^2 - 2a_2 + 2q)T^2 - (a_2 - 2q)T^3 + q T^4\bigr) \\
     &= q - (a_2 - q)T + (a_1^2 - a_2)T^2 - (a_1^2 - a_2)T^3 + (a_2 - q)T^4 - q T^5.
     \end{aligned}$$
   - Prove the polynomial factorization identity matching the two expressions, the exact $\mathrm{SO}(5)$ anti-palindromic functional equation
     $$T^5 (q \cdot L_{\mathrm{std}}(1/T)) = -(q \cdot L_{\mathrm{std}}(T))$$
     (cleared in homogenized / cleared-denominator form for all $T \neq 0$ or as exact reversed-coefficient negation), and the simple-pole cuspidality / trivial-character zero $L_{\mathrm{std}}(1) = 0$ for all $(q, a_1, a_2) \in \mathbb{Z}^3$.

2. **Genus-$2$ Curve $C/\mathbb{F}_5$ $\mathrm{SO}(5)$ Lift & Unit-Circle Ramanujan Temperedness (`genus2_f5_so5_cyclotomic_lift`, `genus2_f5_so5_ramanujan_tempered`)**:
   - Specialize to $(q, a_1, a_2) = (5, -5, 15)$ (aligning with `FiniteFieldRH.genus2LPoly T = 1 + 5T + 15T^2 + 25T^3 + 25T^4` and `Genus2Jacobian`'s $71$-element Jacobian).
   - Prove the exact cleared-denominator polynomial factorization:
     $$5 \cdot L_{\mathrm{std}}(T) = 5(1 - T)(1 - T + T^2 - T^3 + T^4) = 5(1 - T)\Phi_{10}(T).$$
   - Certify that $(1 - T)\Phi_{10}(T) \mid 1 - T^{10}$, establishing constructively that all five eigenvalues of the $\mathrm{SO}(5)$ Frobenius lift are $10$-th roots of unity on the unit circle $|T| = 1$ (including checking concrete evaluation / $10$-th root annihilation).

3. **Langlands Symmetric-Power ($\mathrm{Sym}^k$) & Selberg / Kim–Sarnak Exponent Ladder (`kim_sarnak_ramanujan_ladder_strict`, `selberg_laplacian_eigenvalue_ladder`)**:
   - Using `QuasiRiemann.QRat` (via `ZeroDensityBridge`), certify in cleared-denominator rational arithmetic the $\mathrm{GL}(2)$ Ramanujan–Petersson exponent descent across Langlands symmetric-power lifts:
     $$0 < \frac{7}{64} < \frac{1}{9} < \frac{1}{5} < \frac{1}{4} < \frac{1}{2}$$
     (`Selberg / Ramanujan < Kim–Sarnak Sym^4 < Kim–Shahidi Sym^3 < Gelbart–Jacquet Sym^2 < Selberg 1/4 < Convexity 1/2`).
   - Define `selbergLambda1 (θ : QRat) : QRat := 1/4 - θ * θ` and prove the ascending Selberg Laplacian bottom-eigenvalue ladder:
     $$\frac{3}{16} < \frac{21}{100} < \frac{77}{324} < \frac{975}{4096} < \frac{1}{4},$$
     certifying the exact spectral improvement $\frac{975}{4096} - \frac{77}{324} = \frac{127}{331{,}776}$ from $\mathrm{Sym}^3$ to $\mathrm{Sym}^4$.

### 2. Provenance Integration, Axiom Audit, CLI & Documentation
- **`src/LeanAsm.lean`**: Export `LeanAsm.GSp4FunctorialityBridge`.
- **`src/LeanAsm/ProvenanceSummary.lean`**: Wire the headline `GSp4FunctorialityBridge` theorems (`gsp4_std_functional_equation`, `genus2_f5_so5_cyclotomic_lift`, `genus2_f5_so5_ramanujan_tempered`, `kim_sarnak_ramanujan_ladder_strict`, `selberg_laplacian_eigenvalue_ladder`) into `LeanAsm.leanasm_full_provenance_certified`.
- **`tests/TestAxioms.lean`**: Add a new sequential `#print axioms` section confirming all new `GSp4FunctorialityBridge` theorems and `LeanAsm.leanasm_full_provenance_certified` audit strictly to `[]`, `[propext]`, or `[propext, Quot.sound]` (**ZERO `Classical.choice`**, **ZERO `sorryAx`**).
- **`Main.lean`**: Update CLI output to report the $\mathrm{GSp}(4) \to \mathrm{SO}(5)$ Euler-factor lift for $C/\mathbb{F}_5$ ($5(1-T)\Phi_{10}(T)$) and the Selberg / Kim–Sarnak functoriality ladder.
- **`README.md`**: Document `src/LeanAsm/GSp4FunctorialityBridge.lean` and update the `TestAxioms.lean` coverage summary (strictly $\le 80$ characters per line).

## Acceptance Criteria
- **Zero-Axiom Purity**: Zero `Classical.choice`, zero `sorryAx`.
- **Zero Warnings**: Clean compilation with zero warnings.
- **Formatting & Governance**:
  - All `.lean` files $\le 120$ chars/line; `README.md` $\le 80$ chars/line.
  - Intact `-- Path: leanasm/...` headers and `-- end of file: leanasm/...` footers.
  - `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` pass cleanly.

---

## Issue #65: feat(port): audit 21 pure constructive openai-20261028 files and port verified discrete/algebraic lemmas
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-14T23:55:44Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/65

### Description

## Summary

Audit all **21** pure constructive `.lean` files identified in `docs/openai-20261028/LEAN_TOC.json` (`leanasm_pure_constructive = true`, zero `Classical` / `noncomputable`, zero `Real` / `Complex` / `Filter` / `Asymptotics`, zero `sorry`, zero custom `axiom` declarations), document every file in `docs/openai-20261028/CONSTRUCTIVE_AUDIT.md`, and port the verified discrete/lattice/gauge-algebra theorems into `src/LeanAsm/ConstructiveOpenaiBridge.lean` with ZERO `Classical.choice`, ZERO `sorryAx`, and ZERO warnings.

## Classification of All 21 Pure Constructive Files

1. **Category A — Substantive Discrete Lattice & Gauge Algebra (4 files, 57 declarations — Ported):**
   - `provenance/lgt/LGT/GaugeField/Connection.lean` (`74` lines, `8` decls): `GaugeConnection`, `AsymGaugeConnection`, `plaquetteHolonomy`, `asymPlaquetteHolonomy`, `GaugeTransform`, `AsymGaugeTransform`, `gaugeTransformConnection`, `holonomy_gauge_covariant`.
   - `submission/YM/Lattice/Faces.lean` (`145` lines, `20` decls): `PlaqAxes`, `Face`, `ordered`, `rotate`, `rotate_inv`, `transform`, `faceValue`, `face_gauge`, `rev_rev`, `oriented`, `stop_oriented`, `oriented_swap`, `oriented_next`, `price_flip`, `atFace`, `price_shift_pos`, `lower`, `send`, `injective_send`, `send_price`.
   - `submission/YM/Lattice/Foliation.lean` (`108` lines, `14` decls): `layers`, `slab`, `box_iff_layers`, `card_layers`, `slab_iff`, `update_box`, `lower_pin`, `step_between`, `slab_update_image`, `slab_sum`, `axis_orthogonal`, `square_corners`, `axis_route_support`, `carry_succ`.
   - `submission/YM/Lattice/Route.lean` (`62` lines, `15` decls): `reverse_append`, `reverse_straight`, `axisRoute_append`, `axisRoute_reverse`, `rev_range`, `backward`, `backward_back`, `backOrder`, `back_axes`, `back_route`, `indexRoute`, `sendOrder`, `sendOrder_inv`, `orderEquiv`, `send_route`.
2. **Category B — Lean 4 Metaprogramming / Elaborator Helper (1 file, 4 decls — Reference Only):**
   - `submission/YM/UVExtension/Orchard/Barrel.lean` (`71` lines, `4` decls: `agingName`, `ferment`, `wine`, `store` + `vintage` command elaborator).
3. **Category C — Orchard `vintage` Derivation Scripts (6 files, 0 Lean decls — Scripts Only):**
   - `Apple.lean`, `Muesli.lean`, `Pours.lean`, `Shears.lean`, `Tarts.lean`, `Vanilla.lean` under `submission/YM/UVExtension/Orchard/`.
4. **Category D — Audits, Entrypoint Wrappers, Stubs & Comparator Controls (10 files, 5 decls — Structural/Trivial):**
   - `checks/AxiomAudit.lean`, `submission/verification/Inventory.lean`, `submission/verification/Usage.lean` (`auditModule`), `submission/Solution.lean` (`YangMills.jointExistence`), `submission/YM.lean`, `provenance/lgt/LGT/GaugeField/Holonomy.lean`, `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean`, plus 3 `verification/controls/*/Solution.lean` (`reference`, `comparatorSmoke`).

## Technical Deliverables

- `docs/openai-20261028/CONSTRUCTIVE_AUDIT.md` ($\le 80$ chars/line): Complete classification table and portability notes across all 21 files.
- `src/LeanAsm/ConstructiveOpenaiBridge.lean` (exported in `src/LeanAsm.lean`, $\le 120$ chars/line, pure `Nat`/`Int`/`List` + `YangMillsQ8.Q8`):
  - **4D Lattice Walks & Signed Routes** (`Route.lean` / `Faces.lean`): `straightWalk_stop`, `reverse_straightWalk`, `axisRoute_append`, `axisRoute_reverse`, `axisRoute_support`, `squareWalk_corners`, `PlaqAxes.rotate_inv`, `Face.injective_send`.
  - **Finite Box Layers & Slab Sum Foliation** (`Foliation.lean`): `layerRange_length` (`2 * r + 1`), `boxSites_length` (`(2 * r + 1)^4`), `lower_pin_mem`, `step_between_mem`, `slab_sum_foliation` (constructively decomposing finite sums over 4D pinned slabs across axis layers).
  - **Gauge-Covariant Plaquette Holonomy & Class-Function Trace Invariance** (`Connection.lean` / `Faces.lean` / `Foliation.carry_succ`): constructive `LatticeGroup` (instantiated concretely for `YangMillsQ8.Q8` and `Int`/`Z2`), proving `carry_succ_transport`, `holonomy_gauge_covariant`, `face_gauge_covariant`, `oriented_swap_transport`, `oriented_next_transport`, `classFn_price_flip`, `classFn_price_shift_pos`, `classFn_send_price`, and non-abelian `q8_plaquette_holonomy_gauge_invariant` / `q8_send_price_trace_invariant`.
- `src/LeanAsm/ProvenanceSummary.lean`: Wire the headline `ConstructiveOpenaiBridge` theorems into `YangMillsProvenance` / `yangMills_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`).
- `tests/TestAxioms.lean`: Add **Part 41** `#print axioms` checks confirming `[propext, Quot.sound]` / `[]` / `[propext]` (ZERO `Classical.choice`, ZERO `sorryAx`).
- `Main.lean` & `README.md`: Update CLI Part 4 output and `README.md` ($\le 80$ cols, documenting Parts 1–41).

---

## Issue #68: feat(qrh): parametric QRH ladder and Kim-Sarnak coupling in ParametricQrhLadder.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T00:46:46Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/68

### Description

## Summary

Create `src/LeanAsm/QuasiRiemann/ParametricQrhLadder.lean` (exported from `src/LeanAsm.lean`) linking `LeanAsm.QuasiRiemann.ZeroDensityBridge`, `LeanAsm.QuasiRiemann.ShortIntervalPrimes`, and `LeanAsm.GSp4FunctorialityBridge` with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations (`main` `d96e3d9`)
- `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`: `ZeroDensitySpec`, `zdHuxley` (`12/5`), `zdGuthMaynard` (`30/13`), `zdDensityHypothesis` (`2`), `chebyshevGap`, `zero_density_implies_qrh_threshold`, `qrh_chebyshev_savings_certs`.
- `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`: `ShortIntervalChebyshevSpec`, `shortIntervalDensityExponent`, `short_interval_psi_diff_bound`, `sub_three_quarters_qrh_ladder_certs` (`9/16 < 5/8 < 2/3 < 3/4 < 7/8`).
- `src/LeanAsm/GSp4FunctorialityBridge.lean`: `thetaKimSarnakSym4` (`7/64`), `thetaKimShahidiSym3` (`1/9`), `thetaGelbartJacquetSym2` (`1/5`), `thetaSelberg` (`1/4`), `selbergLambda1`, `kim_sarnak_ramanujan_ladder_strict`.

## Technical Specification
1. **Parametric Specification (`ParametricQrhSpec`)**:
   - Define inductive binary-ladder QRH exponents `θ(k) = (2^k + 1) / 2^(k+1)` (`k = 1 => 3/4`, `k = 2 => 5/8`, `k = 3 => 9/16`, `k = 4 => 17/32`, `k = 5 => 33/64`, strictly descending toward `1/2`), dual mollifier/strip ascent `ϑ(k) = 1 - 1 / 2^(k+1) ↑ 1`, and cleared-denominator `QRat` monotonicity theorems (`∀ k, 1/2 < θ(k+1) ∧ θ(k+1) < θ(k)`).
2. **Comparison Against Huxley (`7/12`) & Guth–Maynard (`17/30`)**:
   - Prove the strict `QRat` ordering across `θ(k)` and short-interval zero-density exponents (`shortIntervalDensityExponent 30 13 = 17/30 < shortIntervalDensityExponent 12 5 = 7/12 < 5/8 = θ(2)` and `θ(4) = 17/32 < 17/30`).
3. **Kim–Sarnak Spectral Tightening (`thetaKimSarnakSym4 = 7/64`)**:
   - Constructively tie `GSp4FunctorialityBridge.thetaKimSarnakSym4` (`7/64`), `selbergLambda1`, and off-diagonal spectral damping (`7/64 < 1/9 < 1/5 < 1/4`) to shifted prime-gap exponents and `ShortIntervalChebyshevSpec` remainder margins.
4. **Integration & Verification**:
   - Export `LeanAsm.QuasiRiemann.ParametricQrhLadder` in `src/LeanAsm.lean`, integrate into `ProvenanceSummary.lean`, add an axiom audit Part in `tests/TestAxioms.lean`, update `Main.lean` + `README.md`, and verify 0 errors, 0 warnings, and 0 `Classical.choice` / `sorryAx`.


---

## Issue #69: feat(qrh): higher-truncation N=256,512 rational contraction bridge from UltraDeep72 to ZeroDensityBridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T00:46:47Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/69

### Description

## Summary

Extend `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` and `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` so higher-truncation (`N ∈ {256, 512}`) 4-prime CRT-NTT Cauchy–Lipschitz 2D rectangles use general rational contraction ratios `qNum / qDen < 1` and export certified strip widths back to `ZeroDensityBridge`, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations (`main` `d96e3d9`)
- `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`: `CauchyBoxLowerBoundSpec`, `cauchy_box_interior_nonvanishing`, `NestedBox2D`, `telescoping_squeezing_chain` (currently hardcoded to factor `1/2`: `2 * drifts (i + 1) ≤ drifts i`), `highTruncSpec_1e12_N256`, `highTruncSpec_1e18_N512`, `dirichletGradBoundScaled6_512`, `telescoping_box_contraction_cert` (`σ = 0.50025 = 1/2 + 1/4000` at `t ~ 10^18`).
- Candidate abstractions from `docs/openai-20261028/LEAN_TOC.json`: `YM.Extension.UV.Tail.improve` (`(1/3)^w + ...`), `YM.Extension.UV.Holo.on_smaller_ball` (`M / (r - δ)`), `YM.UVExtension.Pier.zeroFree` (`r/3` survival).

## Technical Specification
1. **Rational-Ratio Telescoping (`rational_telescoping_squeezing_chain`)**:
   - Generalize `telescoping_squeezing_chain` in `UltraDeep72.lean` from fixed halving (`2 * drifts (i + 1) ≤ drifts i`) to arbitrary cleared-denominator rational contraction `qDen * drifts (i + 1) ≤ qNum * drifts i` with `0 < qNum < qDen` (e.g., `1/3`, `2/5`), preserving interior Cauchy lower bounds across `k` nested `NestedBox2D` steps.
2. **Radius-Shrinkage & Derivative Gate (`UltraDeep72.lean`)**:
   - Port the cleared-denominator integer analog of `Holo.on_smaller_ball` (`M / (r - δ)`) and explicit 4-prime CRT-NTT error-budget guarantees for `dirichletGradBoundScaled6_512` across `N ∈ {256, 512}` down to `σ = 0.50025` at `t ~ 10^18`.
3. **Strip-Width Export to `ZeroDensityBridge.lean`**:
   - Import `LeanAsm.QuasiRiemann.UltraDeep72` (or wire a clean `HighTruncStripBridge` interface without cyclic imports) so certified `N ∈ {256, 512}` 2D rectangle widths at `σ = 0.50025` combine with `zero_density_and_dvp_combined_region` into a unified `ZeroDensityBridge` theorem.
4. **Integration & Verification**:
   - Wire into `ProvenanceSummary.lean`, add an axiom audit Part in `tests/TestAxioms.lean`, update `Main.lean` / `README.md`, and verify 0 errors, 0 warnings, and 0 `Classical.choice` / `sorryAx`.


---

## Issue #70: feat(langlands): GL(1) Artin character-twisted short-interval prime bounds in ArtinShortIntervalBridge.lean
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T00:46:49Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/70

### Description

## Summary

Create `src/LeanAsm/ArtinShortIntervalBridge.lean` (exported from `src/LeanAsm.lean`) linking `LeanAsm.ArtinFermatBridge`, `LeanAsm.MiniVMNttBridge`, `LeanAsm.EulerFactorNonVanishing`, and `LeanAsm.QuasiRiemann.ShortIntervalPrimes` to certify character-twisted `ψ(x; χ_4)` and Fermat-tower `{5, 17, 257, 65537}` residue-class short-interval prime positivity, with **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations (`main` `d96e3d9`)
- `src/LeanAsm/ArtinFermatBridge.lean`: `ArtinFermatCharacterSpec`, `artinFermatTowerSpecs`, `artin_split_euler_factor_collapse`, `artin_char_transform_eq_ntt4`, `artin_char_orthogonality_minivm`.
- `src/LeanAsm/MiniVMNttBridge.lean`: `FermatNtt4Spec`, `fermatTowerNtt4_asm_roundtrip_certs`.
- `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`: `ApShortIntervalSpec`, `ApShortIntervalSpec.HasGuaranteedApPrime`, `ap_short_interval_psi_diff_bound`, `fermat_tower_ap_short_interval_certs` (`fermatAp78Spec`, `fermatAp34Spec` for `q ∈ {5, 17, 257, 65537}`).

## Technical Specification
1. **Character-Twisted Specification (`ArtinTwistedShortIntervalSpec`)**:
   - Pair `ShortIntervalPrimes.ApShortIntervalSpec` with `ArtinFermatBridge.ArtinFermatCharacterSpec` across `F_k ∈ {5, 17, 257, 65537}`, enforcing `q = spec.fermatPrime` and order-4 character decomposition `ψ(x; q, a)` via `MiniVM` 4-point NTT orthogonality (`artin_char_orthogonality_minivm`).
2. **Orthogonality-to-Positivity Bridge (`artin_twisted_ap_short_interval_pos`)**:
   - Prove constructively in cleared integer arithmetic that uniform bounds on character-twisted Chebyshev errors `φ(q) * ψ(x; χ_4^r)` (`r ∈ {0, 1, 2, 3}`, with trivial character `r = 0` carrying the main term `x`) imply `ap_short_interval_psi_diff_bound` positivity `0 < ϑ(x + h; q, a) - ϑ(x; q, a)` across every reduced class mod `F_k`.
3. **Beyond-7/8 Fermat-Tower Certificates**:
   - Instantiate concrete certificates for `θ ∈ {7/8, 3/4, 2/3, 5/8}` across `{5, 17, 257, 65537}`, demonstrating explicit scale pairs `(xScaleExp, hScaleExp)` where prime existence holds for every quartic character coset.
4. **Integration & Verification**:
   - Export `LeanAsm.ArtinShortIntervalBridge` in `src/LeanAsm.lean`, integrate into `ProvenanceSummary.lean`, add an axiom audit Part in `tests/TestAxioms.lean`, update `Main.lean` + `README.md`, and verify 0 errors, 0 warnings, and 0 `Classical.choice` / `sorryAx`.


---

## Issue #71: feat(qrh): constructive dyadic-shell and discrete Abel summation-by-parts bridge in ShortIntervalPrimes
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T00:46:51Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/71

### Description

## Summary

Extend `LeanAsm.ConstructiveOpenaiBridge` (`slab_sum_foliation`) and `LeanAsm.QuasiRiemann.ShortIntervalPrimes` with constructive `[M, M * 2^k)` dyadic-shell decomposition and discrete Abel summation-by-parts identities, using **ZERO `Classical.choice`** and **ZERO `sorryAx`**.

## Existing Foundations (`main` `d96e3d9`)
- `src/LeanAsm/ConstructiveOpenaiBridge.lean`: `listSum`, `listSum_flatMap`, `slabSites`, `slab_sum_foliation` (pure constructive `List`-based summation over finite index boxes).
- `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`: `ShortIntervalChebyshevSpec`, `short_interval_psi_diff_bound`, `qrh_short_interval_positivity_certs`, `sub_three_quarters_qrh_ladder_certs`.
- Candidate abstractions from `docs/openai-20261028/LEAN_TOC.json`: `YM.Contacts.Harvest.geometric_dyadic`, `YM.EveryPhase.Light.dyadic`, `YM.RemainderComparison.Placement.Decimates.summation`, and `YM.RG08.Flat.KStep.KContraction`.

## Technical Specification
1. **Constructive Discrete Abel Summation-by-Parts (`abel_summation_by_parts_list`)**:
   - Define finite `List`-backed summation helpers (`rangeSum a M N`, partial sums `S(k) = ∑_{n ≤ k} a n`) in `Int` / `QRat` without `Finset` or `Classical`, proving:
     `∑_{n=M+1}^{N} a(n) w(n) = (A(N) - A(M)) w(N) + ∑_{k=M+1}^{N-1} (A(k) - A(M)) (w(k) - w(k + 1))`.
2. **Monotone Weight Envelope Bound**:
   - For non-increasing positive integer/rational weights (`0 ≤ w(N) ≤ ... ≤ w(M+1)`) and uniform Chebyshev partial-sum remainder `|A(k) - k| ≤ E`, derive explicit tight upper bounds on weighted prime/Chebyshev sums (`∑ a_n / log n` or `ψ` to `ϑ` conversion envelopes).
3. **Dyadic Shell Decomposition `[M, M * 2^k)` (`dyadic_shell_sum_partition`)**:
   - Mirror `slab_sum_foliation` over dyadic intervals `[M * 2^j, M * 2^(j+1))` (`j < k`), proving additive partition invariance and tightening the prime-power / remainder bounds used in `ShortIntervalPrimes.short_interval_psi_diff_bound`.
4. **Integration & Verification**:
   - Wire into `ShortIntervalPrimes.lean` (and `ProvenanceSummary.lean`), add an axiom audit Part in `tests/TestAxioms.lean`, update `Main.lean` + `README.md`, and verify 0 errors, 0 warnings, and 0 `Classical.choice` / `sorryAx`.


---

## Issue #78: feat(qrh): closed-loop dyadic-Abel rungs k=5,6 and variational mollifier bridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T02:47:56Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/78

### Description

Part of the v1.3.0 roadmap (`docs/ROADMAP_V1_3_0.md`).

### Scope
- Create `src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean` (and export in `src/LeanAsm.lean`).
- Couple `DyadicAbelBridge` (`abel_monotone_weight_envelope_qrat`, `InvSqrtTailGateSpec`) with `ParametricQrhLadder` to unlock rungs `k = 5` (`θ = 33/64` at `[10^192, +10^108]`) and `k = 6` (`θ = 65/128` at `[10^384, +10^206]`).
- Formalize two-piece `QRat` variational mollifier optimization `P(u) = c_1 u + c_2 u^2` strictly beating linear mollifiers with cleared-denominator quadratic certificates.
- Wire into `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean` (**Part 47**).

### Constraints
- Zero Mathlib, zero `Classical.choice`, zero `sorryAx`, zero warnings.
- Preserve `<= 120` chars/line (`.lean`), `<= 80` chars/line (`.md`), and `-- Path:` / `-- end of file:` markers.

---

## Issue #79: feat(qrh): split UltraDeep72 for build performance, N=1024,2048 contraction to sigma=0.5000625, and MiniVM 8-pt NTT
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T02:47:59Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/79

### Description

Part of the v1.3.0 roadmap (`docs/ROADMAP_V1_3_0.md`).

### Scope
- **Split `UltraDeep72.lean` for incremental build performance** (currently `4,683` lines / `271.55s` single-module build): factor into focused submodules (e.g., `UltraDeep72Core.lean`, `UltraDeep90.lean`, `UltraDeep108.lean` / contraction module) re-exported by `UltraDeep72.lean` so existing imports remain compatible while Lake compiles slices in parallel.
- Extend `PiChudnovsky` to 108-digit `twoPiInterval108`.
- Certify `N = 1024` (`σ = 0.500125`, `t ~ 10^24`) and `N = 2048` (`σ = 0.5000625`, `t ~ 10^30`) rational box contractions (Part 20) and export `certifiedStrip05000625_N2048` into `ZeroDensityBridge` Part 8.
- Prove symbolic `MiniVM` 8-point NTT/INTT assembly soundness `ntt8AsmFermat_sound` in `MiniVMNttBridge.lean`.
- Wire into `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean` (**Part 48**).

### Constraints
- Zero Mathlib, zero `Classical.choice`, zero `sorryAx`, zero warnings.
- Preserve `<= 120` chars/line (`.lean`), `<= 80` chars/line (`.md`), and `-- Path:` / `-- end of file:` markers.

---

## Issue #80: feat(langlands): unified GL(1) x GL(2) -> GSp(4) Rankin-Selberg and Hecke short-interval bridge
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T02:48:01Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/80

### Description

Part of the v1.3.0 roadmap (`docs/ROADMAP_V1_3_0.md`).

### Scope
- Create `src/LeanAsm/LanglandsRankinSelbergBridge.lean` (and export in `src/LeanAsm.lean`).
- Link `EllipticModularityBridge` (`E_{11a1}` / `f_{11}`), `ArtinShortIntervalBridge` (`χ_4`), and `GSp4FunctorialityBridge` (`GSp(4) -> SO(5)`).
- Prove cleared-denominator Rankin-Selberg `L_p(s, f_{11} x χ_4)` and `Sym^2(f_{11})` Euler factor non-vanishing across `p <= 97`, `GL(2) x GL(2) -> GSp(4)` reciprocal-polynomial embedding, and Hecke-weighted short-interval Abel bounds.
- Wire into `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean` (**Part 49**).

### Constraints
- Zero Mathlib, zero `Classical.choice`, zero `sorryAx`, zero warnings.
- Preserve `<= 120` chars/line (`.lean`), `<= 80` chars/line (`.md`), and `-- Path:` / `-- end of file:` markers.

---

## Issue #81: feat(crt): 5-prime Proth/Solinas NTT tower P_5 = 15*2^27+1 and Dedekind strip bounds
- **Status**: CLOSED
- **Author**: @fekerr
- **Created**: 2026-11-15T02:48:03Z
- **Labels**: ready
- **URL**: https://github.com/aomaker-org/leanasm/issues/81

### Description

Part of the v1.3.0 roadmap (`docs/ROADMAP_V1_3_0.md`).

### Scope
- Create `src/LeanAsm/ProthNttTowerBridge.lean` (and export in `src/LeanAsm.lean`).
- Extend `{5, 17, 257, 65537}` with 31-bit NTT prime `P_5 = 2,013,265,921 = 15 * 2^27 + 1` (`M_5 > 2^61`).
- Prove 5-channel Garner CRT reconstruction (`garnerReconstruct5Asm_sound`) and 5-prime Dedekind Euler strip bounds in `EulerFactorNonVanishing`.
- Wire into `ProvenanceSummary.lean`, `Main.lean`, and `tests/TestAxioms.lean` (**Part 50**).

### Constraints
- Zero Mathlib, zero `Classical.choice`, zero `sorryAx`, zero warnings.
- Preserve `<= 120` chars/line (`.lean`), `<= 80` chars/line (`.md`), and `-- Path:` / `-- end of file:` markers.

---

## Issue #86: chore(audit): track local Qwen + DeepSeek codebase audit & follow-up TODOs
- **Status**: OPEN
- **Author**: @fekerr
- **Created**: 2026-11-16T00:59:39Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/issues/86

### Description

Tracking issue for the local Ollama (`qwen2.5-coder:7b` + `deepseek-prover:7b`) codebase audit pipeline merged in #85 (`88f3b64`).

- Actionable hygiene & docstring TODOs: [`docs/local_audit_todo.md`](docs/local_audit_todo.md)
- Hardware & architecture notes: [`docs/local_llm_brainstorming.md`](docs/local_llm_brainstorming.md)
- Runner: `./local/audit/usingQwenPlusDeepseek.sh` ([`local/auditor.py`](local/auditor.py))

# LeanAsm Local Qwen + DeepSeek Run Checklist

Workspace: `leanasm` (`feature/ollama-local-config`, base `79fd1e6`, 43 modules)

## Completed Calibration & Baseline Runs

- [x] **Local environment & SDK runner setup** — `config_env` toggles,
  `.venv` (`google-antigravity==0.1.23`), [``local/agent.py``](local/agent.py),
  [``local/prover_orchestrator.py``](local/prover_orchestrator.py)
- [x] **Trial 1: SDK tool-calling baseline** (`audit_20261115_222959`,
  `LeanAsm.QuasiRiemann.Rat`) — diagnosed CPU-only execution (`0.0 MB` VRAM,
  `4835.05 MB` CPU spill, `176.09 s`, `61.91%` of 4k ctx in schemas,
  `tool_calls=[]`)
- [x] **Trial 2: Wrapper deterministic smoke test** (`audit_20261115_223721`,
  `LeanAsm.QuasiRiemann.Rat`) — `--deterministic-only --no-check-axioms`,
  `0.152 s`, `exit=0`
- [x] **Trial 3: Direct Qwen + DeepSeek run** (`audit_20261115_223726`,
  `LeanAsm.QuasiRiemann.Rat`) — `358.335 s` (`lake` `144.66 ms`, Qwen `103.08 s`
  at `5.38 tok/s`, DeepSeek `254.96 s` incl. `36.86 s` load swap at `3.78 tok/s`);
  flagged DeepSeek prompt echoing & `10887.87 MB` peak concurrent RAM
- [x] **Trial 4: Refined DeepSeek prompt (`--prover-only`)**
  ([``report.md``](logs/traces/audit_20261115_224523/report.md),
  `LeanAsm.QuasiRiemann.Rat`) — `203.507 s`, `load=36.62 ms`, `3.85 tok/s`,
  `6052.82 MB` CPU spill, structured PASS bullets without echoing source
- [x] **Remote node git sync (`core11`)** — `git pull --ff-only origin main`
  on `core11` (`LAPTOP-5JODI0MG`) updated `bf33c60..79fd1e6`

---

## Upcoming Tooling & Pipeline Runs

### Phase A: Fast Full-Repo Deterministic Baseline (~seconds, no LLM/SSD load)

- [x] **Run 1: Full 43-module deterministic + axiom baseline**
  ([``report.md``](logs/traces/audit_20261115_225111/report.md),
  `10.254 s`) — `44/44` `lake` checks passed (`failures=0`,
  `tests/TestAxioms.lean` `exit=0` in `3363.44 ms`), `0` `sorry`/`axiom` across
  all 43 modules; flagged `LeanAsm.MiniVMNttBridge` missing footer (`Y/N`) and
  `>100` col lines across several files (notably `UltraDeep108Tables` `633`,
  `UltraDeep90` `106`, `Main` `58`).

### Phase B: Anti-SSD-Thrash & Thermal Enhancements (`local/auditor.py`)

- [x] **Implement `--two-phase`, `--cooldown-secs`, `--num-threads`,
  `--prover-base-url`** in [``local/auditor.py``](local/auditor.py)
  (and docs in [``local/AUDITOR.md``](local/AUDITOR.md)
  / [``local/audit/README.md``](local/audit/README.md))
  — verified `py_compile`, line limits, and mocked two-server HTTP tests for
  two-phase execution order, `options.num_thread`, `--cooldown-secs`, and
  `--budget-secs` + `--resume` (`TWO_PHASE_AND_RESUME_MOCK_TESTS_PASSED`).

### Phase C: Small-Module Direct Batch (`11/11` complete, `<= 8 KB`)

Fits inside default `--num-ctx 4096 --max-source-chars 8000` with no truncation:

- [x] `LeanAsm.QuasiRiemann.UltraDeep72` (17 lines, 674 B) — audited in
  [``audit_20261115_225555``](logs/traces/audit_20261115_225555/report.md)
  (`--two-phase`: Qwen `20.97 s`, DeepSeek `109.35 s` warm `load=92.94 ms`)
- [x] `LeanAsm.QuasiRiemann.AsymptoticZfrBridge` (31 lines, 1,308 B) — audited
  in [``audit_20261115_230538``](logs/traces/audit_20261115_230538/report.md)
  (`--two-phase`: Qwen `52.26 s` PASS, DeepSeek `85.44 s` warm `94.16 ms` PASS)
- [x] `LeanAsm.Conjectures` (48 lines, 1,378 B) — audited in
  [``audit_20261115_225555``](logs/traces/audit_20261115_225555/report.md)
  (`--two-phase`: Qwen `55.80 s`, DeepSeek `151.34 s` incl. `32.13 s` swap)
- [x] `LeanAsm` (42 lines, 1,550 B) — audited in
  [``audit_20261115_232106``](logs/traces/audit_20261115_232106/report.md)
  (`--qwen-only`: `61.72 s` PASS, `ctx=15.87%`)
- [x] `LeanAsm.PiChudnovsky.Sqrt10005` (79 lines, 3,054 B) — audited in
  [``audit_20261115_230538``](logs/traces/audit_20261115_230538/report.md)
  (`--two-phase`: Qwen `126.91 s` PASS, DeepSeek `141.02 s` early-EOS 13 tok)
- [x] `LeanAsm.QuasiRiemann.UltraDeep108` (58 lines, 3,132 B) — audited in
  [``audit_20261115_232106``](logs/traces/audit_20261115_232106/report.md)
  (`--qwen-only`: `114.77 s` PASS, `ctx=38.28%`)
- [x] `LeanAsm.YangMillsQ8` (136 lines, 3,790 B) — audited in
  [``audit_20261115_230538``](logs/traces/audit_20261115_230538/report.md)
  (`--two-phase`: Qwen `141.06 s` PASS, DeepSeek `148.63 s` warm `32.02 ms`)
- [x] `LeanAsm.QuasiRiemann.Rat` (124 lines, 4,323 B) — audited in Trials 3 & 4
- [x] `LeanAsm.RnsArithmetic` (150 lines, 4,812 B) — audited in
  [``audit_20261115_232106``](logs/traces/audit_20261115_232106/report.md)
  (`--qwen-only`: `130.69 s` PASS, `ctx=50.0%`)
- [x] `LeanAsm.YangMillsToy` (158 lines, 5,399 B) — audited in
  [``audit_20261115_232106``](logs/traces/audit_20261115_232106/report.md)
  (`--qwen-only`: `133.46 s` PASS, `ctx=46.56%`)
- [x] `LeanAsm.MiniVM` (186 lines, 6,452 B) — audited in
  [``audit_20261115_232106``](logs/traces/audit_20261115_232106/report.md)
  (`--qwen-only`: `221.29 s` PASS, `ctx=58.54%`)

### Phase D: Medium Modules (`6/12` complete, 8 KB–35 KB)

- [x] `LeanAsm.QuasiRiemann.UltraDeep108Eval` (186 lines, 9,772 B) — audited
  in [``audit_20261115_235957``](logs/traces/audit_20261115_235957/report.md)
  (`--qwen-only 8K`: `400.37 s` PASS, `ctx=57.37%`)
- [x] `LeanAsm.PiChudnovsky` (211 lines, 10,398 B) — audited in
  [``audit_20261115_235957``](logs/traces/audit_20261115_235957/report.md)
  (`--qwen-only 8K`: `341.17 s` PASS, `ctx=54.68%`)
- [x] `LeanAsm.PiChudnovsky.CrtMulBridge` (246 lines, 11,199 B) — audited in
  [``audit_20261115_235957``](logs/traces/audit_20261115_235957/report.md)
  (`--qwen-only 8K`: `381.76 s` PASS, `ctx=62.35%`)
- [x] `LeanAsm.GSp4FunctorialityBridge` (335 lines, 16,560 B) — audited in
  [``audit_20261116_003840``](logs/traces/audit_20261116_003840/report.md)
  (`--qwen-only 4K` smart slice: `221.88 s` PASS, `ctx=74.12%`)
- [x] `LeanAsm.QuasiRiemann.UltraDeep108N1024` (470 lines, 23,158 B) — audited
  in [``audit_20261116_003840``](logs/traces/audit_20261116_003840/report.md)
  (`--qwen-only 4K` smart slice: `294.90 s` PASS, `ctx=94.17%`)
- [x] `LeanAsm.FiniteFieldRH` (548 lines, 23,377 B) — audited in
  [``audit_20261116_003840``](logs/traces/audit_20261116_003840/report.md)
  (`--qwen-only 4K` smart slice: `242.88 s` PASS, `ctx=74.44%`)
- [ ] `LeanAsm.QuasiRiemann.MollifierVariationalBridge` (517 lines, 24,703 B)
- [ ] `LeanAsm.PiChudnovsky.ChudnovskySeries` (547 lines, 25,588 B)
- [ ] `LeanAsm.EllipticModularityBridge` (605 lines, 28,103 B)
- [ ] `Main` (453 lines, 30,800 B)
- [ ] `LeanAsm.QuasiRiemann.UltraDeep108N2048` (607 lines, 31,836 B)
- [ ] `LeanAsm.QuasiRiemann.ParametricQrhLadder` (601 lines, 32,209 B)

### Phase E: Large Modules (>35 KB, sliced via `--budget-secs` + `--resume`)

20 remaining modules (`AsymptoticZfr`, `DyadicAbelBridge`, `ShortIntervalPrimes`,
`ZeroDensityBridge`, `ArtinFermatBridge`, `ArtinShortIntervalBridge`,
`CollatzQrhBridge`, `ConstructiveOpenaiBridge`, `CrtNtt`, `CrtNttUniversal`,
`EulerFactorNonVanishing`, `Genus2Jacobian`, `MiniVMNttBridge`, `NttArithmetic`,
`ProvenanceSummary`, `QuasiRiemann`, `UltraDeep108Tables`, `UltraDeep72Core`,
`UltraDeep90`, `WeilZetaBridge`) — run in resumable slices once Phase B/C
numbers tell us comfortable batch sizes and chunked context limits.

### Phase F: Optional Distributed Experiment (`core11` + `core12`)

- [ ] Configure `core11` Windows Ollama + AC stay-awake (optional)
- [ ] Test split Qwen (`core12`) + DeepSeek (`core11` via `--prover-base-url`)

### Phase G: Final `agy` Review & Repo Polish

- [x] Inspect consolidated findings across completed reports in
  [``docs/local_audit_todo.md``](docs/local_audit_todo.md)
- [x] Run `make sync`, commit (`1a70d9b`), open & merge PR `#85` to `main`
  (`88f3b64`)

### Phase H: Future Local Utilities (Zero `agy` Token Usage)

- [ ] **Live heartbeat / trace viewer script**: Python CLI reading
  `events.jsonl`, `checkpoint.json`, and Ollama `/api/ps` + `server.log`
  snippets during long unattended runs
- [ ] **Local subrepo reviewer / summarizer for
  [``subrepos/YM/submissions/openai-20261028``](subrepos/YM/submissions/openai-20261028)**:
  (`9,564` Lean files / `100,680` declarations indexed in `LEAN_TOC.json`
  with `782` QRH 7/8 matches in `QRH_7_8_CANDIDATES.md`) — filter false
  positives and generate structured porting overviews offline overnight without
  spending `agy` quota


---

