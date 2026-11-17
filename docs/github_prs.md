# Repository Pull Requests Digest (aomaker-org/leanasm)

## PR #1: feat(ntt): Universal 4/8/16-Point CRT-NTT & 96/192-Digit Karatsuba Multipliers
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/ntt-universal-theorems` -> `main`
- **Created**: 2026-11-13T18:09:09Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/1

### Description

## Summary

Implements and formally verifies a constructive, zero-`Classical.choice` / zero-`sorryAx` hierarchy of universal Number Theoretic Transform (NTT), Chinese Remainder Theorem (CRT-NTT) big-integer multiplication, and two-tier Karatsuba-over-CRT-NTT multipliers in Lean 4 (4.35.0):

1. **Universal 4-Point NTT Algebraic Soundness (`F_5` & `F_17`)**
   - Formalized universal inversion and cyclic convolution theorems (`NttArithmetic.intt4_ntt4_universal_F5`, `ntt4_intt4_universal_F5`, `cyclic_conv4_ntt_universal_F5`, and `F17` counterparts) in `src/LeanAsm/NttArithmetic.lean`.

2. **Universal 8-Point NTT Soundness (`F_17` & `F_257`)**
   - Formalized universal inversion and cyclic convolution over `F_17` and `F_257` (`CrtNtt.intt8_ntt8_universal_F17`, `ntt8_intt8_universal_F17`, `cyclic_conv8_ntt_universal_F17`, and `F257` counterparts) in `src/LeanAsm/CrtNtt.lean`.

3. **Universal 16-Point NTT & End-to-End 48-Digit CRT-NTT Big-Integer Multiplier**
   - Added `src/LeanAsm/CrtNttUniversal.lean` (exported from `src/LeanAsm.lean`) proving universal 16-point NTT inversion and cyclic convolution over Fermat primes `F_17`, `F_257`, and `F_65537`.
   - Proved universal exactness of the 3-channel Garner CRT-NTT 48-digit big-integer multiplier: `CrtNtt.crtNttBigMulVec8_universal_sound` and `CrtNtt.crtNttBigMul_universal_sound` (`< 10^24` operands, `< 10^48` products).

4. **96-Digit 2×2 Karatsuba-over-CRT-NTT Multiplier (`karatsubaCrtNttMul96`)**
   - Built a 3-call Karatsuba tier over `crtNttBigMulVec8` using carry-safe 8-limb decomposition (`splitVec16_eval`, `addVec8WithCarry_sound`) and `karatsuba_algebraic_identity`.
   - Proved `karatsubaCrtNttMul96_normalized`, `karatsubaCrtNttMul96_universal_sound` (`∀ A, B < 10^48`), and `karatsuba_96_digit_max_verified` (`(10^48 - 1)^2`).

5. **192-Digit Two-Tier 2×2 Karatsuba-over-CRT-NTT Multiplier (`karatsubaCrtNttMul192`)**
   - Layered a second 2×2 Karatsuba tier (`Vec32` → `Vec64`) over `karatsubaCrtNttMul96` (9 underlying CRT-NTT calls vs. 16 schoolbook) with 32-limb ripple carry/borrow (`addVec32WithCarry_sound`, `subVec32WithBorrow_sound`).
   - Proved `karatsubaCrtNttMul192_normalized`, `karatsubaCrtNttMul192_universal_sound` (`∀ A, B < 10^96`), and `karatsuba_192_digit_max_verified` (`(10^96 - 1)^2`).

6. **CLI Demo, Axiom Audits & Inbox Archives**
   - Updated `Main.lean` Part 9 & Part 10 CLI output to exercise and report the 48-digit, 96-digit, and 192-digit boundary products and universal theorems.
   - Added `#print axioms` checks in `tests/TestAxioms.lean` confirming all new theorems depend at most on `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`).
   - Preserved spec prompts in `inbox/gemweb041.md`–`gemweb043.md`, `inbox/NttArithmetic.lean`, and `inbox/workspace_ro.txt`.

## Verification

- `lake build` (via `make sync`): `Build completed successfully (30 jobs).`
- `lake env lean tests/TestAxioms.lean`: Exited `0`; all added universal NTT, CRT-NTT, and Karatsuba theorems verified with `[propext, Quot.sound]` only (no `Classical.choice`, no `sorryAx`).
- `lake exe leanasm` (via `make sync`): Exited `0`; verified concrete 48-digit, 96-digit (`(10^48 - 1)^2`), and 192-digit (`(10^96 - 1)^2`) outputs.
- Line length audit: zero lines > 120 characters across `src/LeanAsm/CrtNttUniversal.lean`, `tests/TestAxioms.lean`, `Main.lean`, and `src/LeanAsm.lean`.

---

## PR #2: feat(qrh): Constructive QRat {A,B}* Exponent-Pair Engine, Guth-Maynard (30/13) & Mollifier Descent
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-vdc-mollifier-descent` -> `main`
- **Created**: 2026-11-13T18:38:21Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/2

### Description

## Summary

Implements and formally verifies a constructive, zero-`Classical.choice` / zero-`sorryAx` rational engine for van der Corput `{A, B}*` exponent-pair orbits, Guth–Maynard (`30/13`) vs. classical Huxley (`12/5`) / Ingham (`3`) zero-density comparisons, and constructive mollifier length descent (`11/12 → 7/8 → 5/6 → 3/4 → 1/2`) in Lean 4 (4.35.0):

1. **Constructive Rational Arithmetic (`QRat`) & `{A, B}*` Exponent-Pair Engine (`src/LeanAsm/QuasiRiemann.lean`)**
   - Added dependency-free `QRat` (`num : Int`, `den : Nat`, `0 < den`) with decidable `eqv`, `<`, `≤`, and arithmetic (`+`, `-`, `*`, `/`, `reduce`).
   - Implemented `RatExpPair`, `vdcProcessA`, `vdcProcessB`, and `criticalLineMu`.
   - Proved `vdcProcessA_preserves_valid`, `vdcProcessB_preserves_valid`, `vdcProcessB_involutive`, and `vdc_classic_orbit_chain` tracking `(0,1) → B(0,1)=(1/2,1/2) → AB=(1/6,2/3) → A²B=(1/14,11/14) → BA²B=(2/7,4/7) → ABA²B=(1/9,13/18)` with `criticalLineMu` bounds (`1/6 < 5/28 < 1/4` and `p5.k < p2.k < p1.k`).

2. **Guth–Maynard (`30/13`) vs. Huxley (`12/5`) & Ingham (`3`) Zero-Density Comparisons**
   - Added `zeroDensityIngham` (`3`), `zeroDensityHuxley` (`12/5`), `zeroDensityGuthMaynard` (`30/13`), `zeroDensityHypothesis` (`2`), `zeroDensityExponentAt`, and `primeGapExponent`.
   - Proved `guth_maynard_strictly_improves_huxley` and `guth_maynard_prime_gap_threshold` (`17/30 < 7/12 < 2/3` and `3/130` savings at `σ = 3/4`).

3. **Constructive Mollifier Descent & Cross-Domain Collatz Synchronization**
   - Defined `qrhThresholdFromMollifier` (`1 - ϑ/2`) and proved `mollifier_descent_monotone`, `mollifier_beyond_quarter_beats_seven_eighths`, `mollifier_one_third_yields_five_sixths`, `mollifier_one_half_yields_three_quarters`, and `qrh_full_descent_chain_certified`.
   - Synchronized the Collatz–QRH ladder in `src/LeanAsm/CollatzQrhBridge.lean` via `collatz_qrh_mollifier_descent_synchronized`.

4. **CLI Demo, Axiom Audits & Inbox Archival**
   - Updated `Main.lean` Part 5 CLI output to display the `{A,B}*` `QRat` orbit (`ABA²B=((1/9), (13/18))`), Guth–Maynard `30/13` vs. Huxley `12/5` comparison (`θ_p (17/30) < (7/12)`), and mollifier descent chain (`11/12 → 7/8 → 5/6 → 3/4 → 1/2`).
   - Added Part 5b `#print axioms` checks in `tests/TestAxioms.lean` covering all 12 new theorems (`vdcProcessA_preserves_valid` through `collatz_qrh_mollifier_descent_synchronized`).
   - Preserved `inbox/gemweb044.md`.

## Verification

- `lake build` (and `make sync`): `Build completed successfully (30 jobs).` with zero warnings and zero errors.
- `lake env lean tests/TestAxioms.lean`: Exited `0`; all Part 5b theorems depend only on `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`).
- `lake exe leanasm` (via `make sync`): Exited `0`.
- Line length audit: zero lines `> 120` chars across `Main.lean`, `src/LeanAsm/CollatzQrhBridge.lean`, `src/LeanAsm/QuasiRiemann.lean`, and `tests/TestAxioms.lean`.


---

## PR #3: feat(qrh): ScaledInterval36 (10^36) via CRT-NTT & N=64 2D Sweeper down to σ = 0.505
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/scaled-interval36-n64-sweeper` -> `main`
- **Created**: 2026-11-13T19:14:53Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/3

### Description

## Summary

Implements and formally verifies `inbox/gemweb045.md`: a constructive, zero-`Classical.choice` / zero-`sorryAx` **36-digit fixed-point engine (`10^36`) backed by verified 96-digit CRT-NTT Karatsuba multiplication**, together with **36-digit transcendental evaluators** and an **ultra-deep `N = 64` 2D zero-free rectangle sweeper** reaching down to `σ = 0.505` in Lean 4 (`4.35.0`):

1. **CRT-NTT 96-Digit Arithmetic Bridge & `ScaledInterval36` (`src/LeanAsm/QuasiRiemann.lean`)**
   - Bridged `CrtNtt.karatsubaCrtNttMul96` (`3`-call Karatsuba over 3-channel Fermat NTTs) into arbitrary `Nat`/`Int` products via `natMul96ViaCrtNtt`, `natMul96ViaCrtNtt_eq_mul`, `intMul96ViaCrtNtt`, and `intMul96ViaCrtNtt_eq_mul`.
   - Defined `ScaledInterval36` (`[lo / 10^36, hi / 10^36]`), `mulInterval36`, `toScaled6From36`, and proved constructive interval soundness `mulInterval36_sound` directly from `CrtNtt.karatsubaCrtNttMul96_universal_sound` and `mul_mem_corners_left` / `mul_mem_corners_right` without `Classical.choice`.

2. **Constructive 36-Digit Transcendental Interval Evaluators (`10^36` scale)**
   - Implemented 36-digit Taylor / Machin-like evaluators: `artanhTaylor36`, `arctanTaylor36`, `twoPiInterval36`, `reduceModTwoPiCentered36`, and `lnInterval36` across `1 ≤ n ≤ 64`.
   - Proved `ln_table_1_to_64_valid` certifying `ValidLnBound36` for all integers `1 ≤ n ≤ 64`.
   - Implemented outward 36-digit exponential and trigonometric evaluators: `taylorExpNegInterval36`, `taylorCosInterval36`, and `taylorSinInterval36` (using argument scaling `256` + `8` squarings for `exp(-y)` and `2` + double-angle identity for `cos/sin`).

3. **`N = 64` Ultra-Deep 2D Zero-Free Rectangle Sweeper (`σ` down to `0.505`)**
   - Defined `n64PowNegUpperFromSigma36`, proved monotonicity/soundness `n64_pow_neg_sigma36_sound`, and defined the second-order Euler–Maclaurin remainder `eulerMaclaurinB2TailRect2D_N64`.
   - Implemented `EntriesTree` (depth-6 balanced tree reduction matching `evalDirichletPolyInterval`) together with `buildRect2DCertN64`, `sweepRectangles2DN64`, and the 7-rectangle grid `ultraDeepStripRectGrid2D_N64` spanning `[0.505, 0.507] × ...` through `[0.520, 0.522]`.
   - Proved `buildRect2DCertN64_implies_valid`, `sweepRectangles2DN64_all_valid`, and `ultra_deep_rects_down_to_0505_certified` (7/7 certified 2D rectangles down to `σ = 0.505`, total certified area `Δσ·Δt = 0.140000000`).

4. **CLI Demo, Axiom Audits & Inbox Archival**
   - Updated `Main.lean` Part 2 (`lnInterval36 64` synthesis) and Part 5 (`ScaledInterval36` `(10^36)^2` CRT-NTT check and `N=64 Ultra-Deep 2D` summary).
   - Added Part 11 `#print axioms` checks in `tests/TestAxioms.lean` covering all 7 required theorems (`natMul96ViaCrtNtt_eq_mul`, `mulInterval36_sound`, `ln_table_1_to_64_valid`, `n64_pow_neg_sigma36_sound`, `buildRect2DCertN64_implies_valid`, `sweepRectangles2DN64_all_valid`, `ultra_deep_rects_down_to_0505_certified`).
   - Preserved `inbox/gemweb045.md`.

## Verification

- `lake build` (and `make sync`): `Build completed successfully (30 jobs).` with zero errors and zero warnings.
- `lake env lean tests/TestAxioms.lean`: Exited `0`; `n64_pow_neg_sigma36_sound` depends on no axioms (`[]`) and the remaining Part 11 theorems depend only on `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`).
- `make run` / `lake exe leanasm` (via `make sync`): Exited `0`, verifying `(10^36)^2`, `(ln 64)·10^36`, and 7/7 `N = 64` 2D rectangles with total area `0.140000000`.
- Line length & header/footer audit: zero lines `> 120` chars across `src/LeanAsm/QuasiRiemann.lean`, `tests/TestAxioms.lean`, and `Main.lean`.

---

## PR #4: fix(qrh): safe QRat division API (div / div? / divOrZero) & markdown formatting
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `fix/qrat-safe-div-pr2` -> `main`
- **Created**: 2026-11-13T19:28:53Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/4

### Description

## Summary

Resolves both Copilot review findings raised on [PR #2](https://github.com/aomaker-org/leanasm/pull/2):

1. **Safe / Checked `QRat` Division API (`src/LeanAsm/QuasiRiemann.lean`)** — addresses [comment r4567249815](https://github.com/aomaker-org/leanasm/pull/2#discussion_r4567249815):
   - Replaced total `QRat.div` (which silently returned `0` on division by zero) and removed the global `instance : Div QRat` so unguarded `a / b` expressions cannot mask `/ 0` bugs.
   - Exposed proof-carrying `QRat.div (a b : QRat) (hb : b.num ≠ 0) : QRat` and safe partial `QRat.div? (a b : QRat) : Option QRat`.
   - Made total fallback explicit via `QRat.divOrZero (a b : QRat) : QRat` (used only in unguarded compatibility wrappers like `vdcProcessA` and `primeGapExponent`, while adding `primeGapExponentChecked` / `primeGapExponent?` and switching `criticalLineMu` and `qrhThresholdFromMollifier` directly to checked `QRat.div` with `by decide`).
   - Proved `qrat_div_mul_cancel` (`(QRat.div a b hb * b) ≃ a`), `qrat_div?_zero`, `qrat_div?_eq_some`, and `qrat_divOrZero_eq_div`, with `#print axioms` verification in `tests/TestAxioms.lean`.

2. **Directive 04 Markdown Formatting (`inbox/gemweb044.md`, `inbox/gemweb045.md`)** — addresses [comment r4567249893](https://github.com/aomaker-org/leanasm/pull/2#discussion_r4567249893):
   - Added `# Path:` headers and `<!-- end of file: ... -->` footers and wrapped all lines to `≤ 80` columns.

## Verification

- `lake build` (and `make sync`): `Build completed successfully (30 jobs).` with zero errors and zero warnings.
- `lake env lean tests/TestAxioms.lean`: Exited `0`; `qrat_div_mul_cancel` depends only on `[propext, Quot.sound]` and `qrat_div?_zero`, `qrat_div?_eq_some`, `qrat_divOrZero_eq_div` depend only on `[propext]` (zero `Classical.choice`, zero `sorryAx`).
- Line length audit: zero lines `> 120` chars in `src/LeanAsm/QuasiRiemann.lean` and `tests/TestAxioms.lean`; zero lines `> 80` chars in `inbox/gemweb044.md` and `inbox/gemweb045.md`.

---

## PR #5: feat(collatz-qrh): high-convergent log₂(3) gaps & CRT-NTT |2^k - 3^m| bounds
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/collatz-convergent-crt-ntt-gaps` -> `main`
- **Created**: 2026-11-13T19:35:32Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/5

### Description

## Summary

Ingests `inbox/gemweb046.md`, extending `src/LeanAsm/CollatzQrhBridge.lean` with CRT-NTT-backed multi-digit exponentiation and 36-digit certified Diophantine lower bounds on `|k · ln 2 - m · ln 3|` across high-denominator convergents of `log₂(3)` through `(306, 193)`:

1. **CRT-NTT Exponentiation & Exact Power Separations (`src/LeanAsm/CollatzQrhBridge.lean`)**
   - Implemented `powViaCrtNtt96` using `QuasiRiemann.natMul96ViaCrtNtt` (`karatsubaCrtNttMul96_universal_sound`) and proved `powViaCrtNtt96_eq_pow`.
   - Certified exact multi-digit gaps `|2^k - 3^m|` across `(8, 5)`, `(19, 12)`, `(65, 41)`, `(84, 53)`, and 93-digit `(306, 193)` (`collatz_convergent_powers_separation_certified`).

2. **36-Digit Certified Linear Forms & Baker-Type Irrationality Measure**
   - Built `linearFormLn2Ln3Interval36` and `linearFormLn2Ln3AbsLower36` from certified `lnInterval36 2` and `lnInterval36 3`, proving `linearFormLn2Ln3Interval36_sound` and `linearFormLn2Ln3AbsLower36_sound`.
   - Proved `baker_effective_measure_verified`: `linearFormLn2Ln3AbsLower36 k m > 0` and `|k · ln 2 - m · ln 3| · m² > 1/10` (`> 10^35` at `10^36` scale) across all five convergents through `m = 193`.

3. **Collatz Cycle Gap & QRH Spectral Beat Period Bridge**
   - Proved `collatz_cycle_requires_positive_gap` connecting positive integer cycles `n0 * 2^k = n0 * 3^m + rhs` to `powViaCrtNtt96 2 k - powViaCrtNtt96 3 m`.
   - Added safe checked beat-period upper bound `collatzBeatPeriodUpper36 : Nat → Nat → Option Nat` (no zero-fallback division), proved `collatzBeatPeriodUpper36_sound` and `collatz_qrh_phase_beat_lower_bound` (showing `Δt ≤ 89` for `(306, 193)`).

4. **CLI Output, Axiom Audits & Inbox Formatting**
   - Updated `Main.lean` Part 2 output to display CRT-NTT `|2^306 - 3^193|` and the `(306, 193)` linear-form lower bound and spectral beat bound.
   - Added Part 12 `#print axioms` checks in `tests/TestAxioms.lean` and formatted `inbox/gemweb046.md` with Directive 04 header/footer.

## Verification

- `lake build` & `make sync`: `Build completed successfully (30 jobs).` with zero errors and zero warnings.
- `lake env lean tests/TestAxioms.lean`: Exited `0`; all 8 Part 12 theorems use at most `[propext, Quot.sound]` (zero `Classical.choice`, zero `sorryAx`).
- `lake exe leanasm`: Exited `0`, verifying `|2^306 - 3^193|` (91 digits) and `|306 ln2 - 193 ln3|·10^36 ≥ 70865538398094242390698440154536530`.

---

## PR #6: chore: clean up Copilot review nits and add gemweb047/gemweb048 stubs
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `fix/copilot-nits-and-stubs` -> `main`
- **Created**: 2026-11-13T19:42:53Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/6

### Description

## Summary
- Remove unused `foldRawPair` helper with identical `if/else` branches in `src/LeanAsm/QuasiRiemann.lean` (PR #3 Copilot nit).
- Clarify `qrat_div_mul_cancel` docstring to use `QRat.eqv (QRat.div a b hb * b) a` instead of `(a / b) * b` syntax (PR #4 Copilot nit).
- Fix unclosed inline-code bold spans (`sorryAx**`) and enforce 80-column wrapping across `inbox/gemweb044.md`, `inbox/gemweb045.md`, and `inbox/gemweb046.md` (PR #4 Copilot nits).
- Add `inbox/gemweb047.md` and `inbox/gemweb048.md` stubs linking to the corresponding prompt line ranges in `inbox/gemweb046.md`.

## Verification
- `lake build` completed successfully (30 jobs).
- `lake env lean tests/TestAxioms.lean` passed with zero `Classical.choice` and zero `sorryAx`.
- `make sync` completed and verified workspace state.

---

## PR #7: feat(pi): constructive 100-digit Chudnovsky pi via CRT-NTT and interruptible incremental builds
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/pi-chudnovsky-100` -> `main`
- **Created**: 2026-11-13T22:20:08Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/7

### Description

## Summary
- Implement constructive 100-digit Chudnovsky $\pi$ engine (`LeanAsm.PiChudnovsky`) backed by `karatsubaCrtNttMul192` from `CrtNttUniversal.lean`, decomposed into `.olean`-checkpointed submodules (`CrtMulBridge`, `Sqrt10005`, `ChudnovskySeries`, and `PiChudnovsky`).
- Certify all 100 decimal digits of $\pi$ (`pi_100_digits_certified`, `pi_105_bracket_valid`, universal truncation soundness `pi_105_traps_all_chudnovsky_truncations`, `chudnovsky_alternating_decreasing`, `sqrt10005_scaled110_certified`) with zero `Classical.choice` and zero `sorryAx`.
- Add Part 13 axiom checks to `tests/TestAxioms.lean` and Part 11 summary output to `Main.lean`.
- Add interruptible ~15-minute `.olean`-checkpointed build driver `tools/incremental_build.py` and `Makefile` targets (`build-chunk`, `build-incremental`, `build-status`).

## Verification
- `make build-incremental` (`[+] All targets up to date.`)
- `lake env lean tests/TestAxioms.lean` (zero `Classical.choice`, zero `sorryAx`)
- `make sync` (exit 0)

---

## PR #8: feat(qrh): 72-digit CRT-NTT interval engine & N=128 2D sweeper to σ=0.501 (gemweb048)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-n128-scaled72` -> `main`
- **Created**: 2026-11-13T22:37:31Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/8

### Description

## Summary
- Implement `ScaledInterval72` (scale `10^72`) in `src/LeanAsm/QuasiRiemann.lean` backed by `natMul192ViaCrtNtt` / `intMul192ViaCrtNtt` (`LeanAsm.PiChudnovsky.CrtMulBridge.natMul192ViaCrtNtt`, proved constructively via `karatsubaCrtNttMul192_universal_sound` with zero `Classical.choice` or `sorryAx`).
- Add `mulInterval72`, `mulInterval72_sound`, `artanhTaylor72`, `arctanTaylor72`, `twoPiInterval72`, `reduceModTwoPiCentered72`, `taylorExpNegInterval72`, `taylorCosInterval72`, and `taylorSinInterval72`.
- Extend pure-rational prime logarithm synthesis (`lnInterval72`, `ValidLnBound72`, `ln_table_1_to_128_valid`) to all integers `1 ≤ n ≤ 128`.
- Implement the `N = 128` 2D continuous zero-free rectangle sweeper down to `σ = 0.501` (`n128PowNegUpperFromSigma72`, `n128_pow_neg_sigma72_sound`, `eulerMaclaurinB2TailRect2D_N128`, `buildRect2DCertN128`, `sweepRectangles2DN128`, `buildRect2DCertN128_implies_valid`, `sweepRectangles2DN128_all_valid`, `ultra_deep_rects_down_to_0501_certified` — certifying 7/7 rectangles with `Δσ·Δt = 0.000140000000`).
- Add `#print axioms` audit entries in `tests/TestAxioms.lean` and update `Main.lean` Part 2 and Part 5 CLI output.

## Verification
- `make build-incremental` (`+LeanAsm.QuasiRiemann` built in 146.66s)
- `lake env lean tests/TestAxioms.lean` (zero `Classical.choice`, zero `sorryAx`)
- `make sync` (passes cleanly)

---

## PR #10: chore(Makefile): align help text hyphen spacing
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `fix/makefile-help-align` -> `main`
- **Created**: 2026-11-13T23:26:24Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/10

### Description

Closes #9

Fixes Copilot formatting nit from PR #7 (`discussion_r4569368613`) by padding the `make help` column so `make build-incremental` has a space before `-` and every `-` separator aligns cleanly.

## Verification
- Verified `make help` alignment locally

---

## PR #12: feat(finite-field-rh): smooth genus-2 curve C/F_5 Riemann Hypothesis (gemweb051)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/finite-field-rh-genus2` -> `main`
- **Created**: 2026-11-13T23:37:57Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/12

### Description

## Summary
- Extend `src/LeanAsm/FiniteFieldRH.lean` with exact point counting and Frobenius Riemann Hypothesis verification on the smooth genus-2 hyperelliptic curve $C : y^2 = x^5 - x + 1$ over $\mathbb{F}_5$:
  - Construct $\mathbb{F}_{25} \cong \mathbb{F}_5[\alpha]/(\alpha^2 - 2)$ as `F25`, verify smoothness (`genus2_curve_smooth_F5`: `f'(x) = -1 ≠ 0`), and prove `#C(F_5) = 11` (`genus2_N1_eq_11`) and `#C(F_25) = 31` (`genus2_N2_eq_31`) by constructive enumeration.
  - Derive Frobenius coefficients `a_1 = 5`, `a_2 = 15` (`genus2_weil_traces_verified`, verifying Newton–Girard identities and genus-2 Hasse–Weil bound `25 ≤ 80`) and `genus2FrobPoly(X) = X^4 + 5X^3 + 15X^2 + 25X + 25`.
  - Prove the palindromic functional equation (`genus2_frob_poly_functional_eq`) and the `Q(√5)` splitting identity `4 * P_frob(X) = (2 X^2 + 5 X + 10)^2 - 5 X^2` (`genus2_frob_poly_quad_factor_id`).
  - Prove constructively with zero `Classical.choice` or `sorryAx` that both reciprocal eigenvalue sums `u_{1,2} = (5 ± √5)/2` satisfy `u_i^2 < 20` (`genus2_real_trace_bounds`) and strictly negative discriminants `Δ_i = u_i^2 - 20 < 0` (`genus2_frob_negative_discriminants`), proving `|α_i|^2 = 5` (`Re(s) = 1/2`).
- Add `#print axioms` checks in `tests/TestAxioms.lean` and display genus-2 RH results in `Main.lean` Part 7.

## Verification
- `make build-incremental` (`+LeanAsm.FiniteFieldRH` built in `1.46s`)
- `lake env lean tests/TestAxioms.lean` (`Forbidden axioms: []`, zero `Classical.choice`, zero `sorryAx`)
- `make sync` (passes cleanly)

---

## PR #13: feat(collatz): 192-digit CRT-NTT (485, 306) gap & 72-digit Baker bounds (gemweb052)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/collatz-192-crt-ntt-485-306` -> `main`
- **Created**: 2026-11-13T23:44:35Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/13

### Description

## Summary
- Extend `src/LeanAsm/CollatzQrhBridge.lean` with 192-digit CRT-NTT exponentiation (`powViaCrtNtt192`, proved equal to `base ^ exp` via `PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul`) and certify exact power gaps through the 146-digit principal convergent `(485, 306)` (`2^485 > 3^306`, exact 144-digit difference `expectedGap485`).
- Add 72-digit linear form enclosures `linearFormLn2Ln3Interval72` and `linearFormLn2Ln3AbsLower72` backed by `QuasiRiemann.lnInterval72`, with universal soundness (`linearFormLn2Ln3Interval72_sound`, `linearFormLn2Ln3AbsLower72_sound`) and effective irrationality measure certification across all six convergents through `(485, 306)` (`baker_effective_measure_485_306_verified`).
- Prove the `(485, 306)` cycle denominator bound (`collatz_485_306_cycle_denominator_certified`) and sharp 72-digit spectral beat-period upper bounds (`collatzBeatPeriodUpper72`, `collatzBeatPeriodUpper72_sound`, `collatz_qrh_phase_beat_72_verified`, `beat ≤ 6147`).
- Add `#print axioms` checks in `tests/TestAxioms.lean` and display the `(485, 306)` gap and 72-digit Baker bound in `Main.lean` Part 2.

## Verification
- `make build-incremental` (`+LeanAsm.CollatzQrhBridge` built in `1.06s`)
- `lake env lean tests/TestAxioms.lean` (zero `Classical.choice`, zero `sorryAx`)
- `make sync` (passes cleanly)

---

## PR #14: feat(FiniteFieldRH): genus-2 Weil L(C, 1) = 71/25 & Jacobian order 71
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/genus2-weil-l-jacobian` -> `main`
- **Created**: 2026-11-14T00:02:56Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/14

### Description

Implements gemweb053 for C : y^2 = x^5 - x + 1 over F_5 in src/LeanAsm/FiniteFieldRH.lean with zero Classical.choice and zero sorryAx:
- Reciprocal Weil L-polynomial genus2LPoly, cleared numerator genus2LNumAtInv5 = 1775, and Jacobian order cardJacobianGenus2F5 = 71.
- Constructive proofs of genus2_L_poly_eq_recip_frob, genus2_zeta_rational_identity (mod T^3), genus2_L_at_1_eq_71_div_25 (analytic rank 0), genus2_bsd_finite_field_identity, genus2_jacobian_order_eq_71, genus2_jacobian_order_71_prime, and genus2_basepoint_generates_jacobian.
- Axiom checks in tests/TestAxioms.lean (Part 17, zero Classical.choice/sorryAx) and Part 7 CLI output in Main.lean.

---

## PR #15: feat(WeilZetaBridge): unify genus-2 Weil zeta & Euler-factor strip bounds
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/weil-zeta-euler-bridge` -> `main`
- **Created**: 2026-11-14T00:10:07Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/15

### Description

Implements gemweb054 bridging src/LeanAsm/FiniteFieldRH.lean and src/LeanAsm/EulerFactorNonVanishing.lean in src/LeanAsm/WeilZetaBridge.lean with zero Classical.choice and zero sorryAx:
- Constructive local Euler-factor denominator bounds weil_denom_factor1_nonvanishing, weil_denom_factor2_nonvanishing, and weil_denom_product_lower_bound.
- Global Frobenius off-half lower bound genus2_L_poly_lower_bound_off_half, quadratic factorization genus2_L_poly_quad_factor_id, and explicit strip certs genus2_L_poly_explicit_strip_certs (sigma = 1/4, 3/4, 1).
- Unified punctured-strip regularity & non-vanishing theorem weil_zeta_punctured_strip_regular_and_nonzero.
- Wired into src/LeanAsm.lean, Part 18 of tests/TestAxioms.lean (zero Classical.choice / sorryAx), and Part 7 of Main.lean.

---

## PR #18: feat(qrh): constructive DVP zero-free region & Dirichlet L^2 diagonal dominance
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-asymptotic-zfr` -> `main`
- **Created**: 2026-11-14T01:23:39Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/18

### Description

## Summary
Formalizes constructive dyadic-octave logarithm bounds, an explicit de la Vallée Poussin asymptotic zero-free region ($c_{\text{dvp}} = 1/56$ for $t \ge 16$), and constructive Dirichlet-polynomial $L^2$ diagonal dominance / Montgomery–Vaughan sandwich bounds with zero `Classical.choice` and zero `sorryAx`.

Closes #16

## Changes
- **[`src/LeanAsm/QuasiRiemann/Rat.lean`](src/LeanAsm/QuasiRiemann/Rat.lean)**: Extracted constructive `QRat` type and core exact rational arithmetic so both `QuasiRiemann.lean` and `AsymptoticZfr.lean` share a single `.olean`-cached definition.
- **[`src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean`](src/LeanAsm/QuasiRiemann/AsymptoticZfr.lean)**:
  - Part 1: Constructive dyadic-octave log envelope (`octaveLnUpper36`, `octaveLnUpper36QRat`, `octave_bracket_pow2`, `octaveLnUpper36_pos`, `octaveLnUpper36_mono`, `ln2Upper36_envelope_certs`).
  - Part 2: Explicit 3-4-1 trigonometric positivity (`trig_341_identity`, `trig_341_positivity`, `trig_341_positivity_qrat`, `trig_341_dirichlet_weighted_sum_nonneg`) and constructive de la Vallée Poussin asymptotic zero-free region (`cDvp = 1/56`, `dvpThresholdT0 = 16`, `dvp_asymptotic_zero_free_region`).
  - Part 3: Constructive Dirichlet-polynomial $L^2$ diagonal dominance & Montgomery–Vaughan sandwich (`dirichletDiagEnergy`, `dirichlet_log_ratio_lower`, `dirichlet_offdiag_sum_bound`, `dirichlet_offdiag_envelope_le_half_diag`, `dirichlet_l2_diagonal_dominance_sandwich`, `dirichlet_l2_zeta_and_mobius_certs`).
- **[`src/LeanAsm/QuasiRiemann.lean`](src/LeanAsm/QuasiRiemann.lean)** & **[`src/LeanAsm.lean`](src/LeanAsm.lean)**: Re-export `Rat` and `AsymptoticZfr` cleanly and link `ln2Upper36Scaled_eq_lnInterval36_hi` + `octaveLnUpper36_bounds_lnInterval36` directly to `(lnInterval36 2).hi`.
- **[`tests/TestAxioms.lean`](tests/TestAxioms.lean)**: Part 19 `#print axioms` checks across all 16 new/bridge theorems (strictly `[propext, Quot.sound]` or zero axioms; zero `Classical.choice` and zero `sorryAx`).
- **[`Main.lean`](Main.lean)**: Added Part 5 CLI output for `c_dvp = 1/56` ($t \ge 16$) and the Zeta/Mobius Dirichlet $L^2$ sandwich bounds.

## Verification
- `make build-incremental`: all 44 jobs succeeded, all 21 modules cached/up-to-date.
- `lake env lean tests/TestAxioms.lean`: all checks passed with zero `Classical.choice` and zero `sorryAx`.
- `make sync`: clean build & executable test passed.

---

## PR #20: chore: address actionable Copilot review comments from PRs #12, #14, and #18
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `chore/copilot-review-followups` -> `main`
- **Created**: 2026-11-14T01:39:50Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/20

### Description

Closes #19

## Summary
- **Zero-pad 36-digit `ln16` printout (`Main.lean`)**: Added `private def padZeros (width n : Nat) : String` helper and updated `pad128` and `padLn16` so fractional printouts preserve leading zeros (`ln_hi(16) = 3.465735902799726547086160607290883110`).
- **Clarify `QRat.reduce` vs `Repr QRat` docstrings (`src/LeanAsm/QuasiRiemann/Rat.lean`)**: Documented that `Repr QRat` prints `num/den` without automatic GCD reduction, and clarified `QRat.reduce` as the explicit manual reduction helper.
- **Decouple `AsymptoticZfr` from `QuasiRiemann.lean` (`src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean`)**: Moved `ln2Upper36Scaled_eq_lnInterval36_hi` and `octaveLnUpper36_bounds_lnInterval36` into a dedicated `LeanAsm.QuasiRiemann.AsymptoticZfrBridge` module re-exported via `src/LeanAsm.lean`, removing the reverse import from `QuasiRiemann.lean` while preserving exact `QuasiRiemann.*` theorem names. Resolved `scale36Int` ownership cleanly in `QuasiRiemann.lean`.
- **Clarify constant derivative in `genus2DerivF5` (`src/LeanAsm/FiniteFieldRH.lean`)**: Added `genus2DerivF5_eq_neg_one : ∀ x : Fin 5, genus2DerivF5 x = -1` and updated docstrings on `genus2DerivF5` and `genus2_curve_smooth_F5`.
- **Align `FiniteFieldRH` L-value & Jacobian docstrings (`src/LeanAsm/FiniteFieldRH.lean`)**: Imported `LeanAsm.QuasiRiemann.Rat`, proved `genus2_L_at_1_qrat` (`QRat.eqv` between `(genus2LNumAtInv5, 625)` and `(71, 25)`), and tightened docstrings to accurately describe the proved invariants.
- **Axiom audits (`tests/TestAxioms.lean`)**: Added Part 20 `#print axioms` checks for `FiniteFieldRH.genus2DerivF5_eq_neg_one` and `FiniteFieldRH.genus2_L_at_1_qrat`.

## Verification
- `make build-incremental`: succeeded cleanly
- `lake env lean tests/TestAxioms.lean`: 286 axiom checks passed with zero `Classical.choice` and zero `sorryAx`
- `make sync`: succeeded cleanly

---

## PR #21: refactor(qrh): extract UltraDeep72 and derive twoPiInterval72 from PiChudnovsky
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `refactor/qrh-ultradeep72` -> `main`
- **Created**: 2026-11-14T02:30:29Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/21

### Description

Closes #17

## Summary
- Extracted Part 15 (72-digit CRT-NTT engine, `lnInterval72`, `twoPiInterval72`, and N=128 ultra-deep 2D strip certification) from `src/LeanAsm/QuasiRiemann.lean` into `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` inside `namespace QuasiRiemann`.
- Exposed shared interval/tree helpers (`ediv_mul_le_self`, `floorDiv_le_ceilDiv_gen`, `int_mul_sign_cases`, `corner_bounds`, `foldNatStep`, `EntriesTree`, `EntriesTree.toList`, `isValidRectTreeN64`, `isValidRectTreeN64_sound`) from `QuasiRiemann.lean` for reuse in `UltraDeep72.lean`, and imported `LeanAsm.QuasiRiemann.Rat` and `LeanAsm.PiChudnovsky`.
- Removed dead Machin helpers (`rawArctan72`, `arctanTaylor72`) and derived `twoPiRaw72` / `twoPiInterval72` directly from `PiChudnovsky.piLower105` and `PiChudnovsky.piUpper105` scaled down by `scale33Nat = 10 ^ 33`, proving `twoPiInterval72_valid` and `twoPiInterval72_from_chudnovsky_sound` with ZERO `Classical.choice` and ZERO `sorryAx`.
- Exported `LeanAsm.QuasiRiemann.UltraDeep72` in `src/LeanAsm.lean`, updated `src/LeanAsm/CollatzQrhBridge.lean` imports/proofs, and added `#print axioms` checks for `twoPiInterval72_valid` and `twoPiInterval72_from_chudnovsky_sound` in `tests/TestAxioms.lean`.

## Verification
- `make build-incremental`: passed (`48 jobs`)
- `lake env lean tests/TestAxioms.lean`: passed (`288` axiom lines, `0` `Classical.choice` / `sorryAx`)
- `make sync`: passed (`48 jobs`, Lean executable ran cleanly)

---

## PR #23: docs(finite-field-rh): align genus2_L_at_1 docstrings with formal theorem statements
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `docs/finite-field-rh-docstrings` -> `main`
- **Created**: 2026-11-14T02:40:36Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/23

### Description

Closes #22

## Summary
- Reworded the docstrings on `FiniteFieldRH.genus2_L_at_1_eq_71_div_25` and `FiniteFieldRH.genus2_L_at_1_qrat` in `src/LeanAsm/FiniteFieldRH.lean` so the formal claim states strictly what the Lean theorem types prove (`genus2LNumAtInv5 = 1775`, `1775 * 25 = 71 * 625`, `1775 > 0`, and `QuasiRiemann.QRat.eqv` to `71 / 25`).
- Moved the nonvanishing / analytic-rank-0 interpretation into an explicitly marked parenthetical `(mathematical remark: ...)`.

## Verification
- `make build-incremental`: passed (`46 jobs`, all targets up to date)
- `lake env lean tests/TestAxioms.lean`: passed (`286` axiom lines, `0` `sorryAx` / `Classical.choice`)
- `make sync`: passed (`46 jobs`, Lean executable ran cleanly)

---

## PR #25: feat(finite-field-rh): formalize Cantor-Mumford Jacobian group law and prove order 71
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/genus2-jacobian` -> `main`
- **Created**: 2026-11-14T04:00:01Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/25

### Description

## Summary
- Added `src/LeanAsm/Genus2Jacobian.lean` implementing trimmed `PolyF5` arithmetic over `Fin 5` (`polyDivMod_sound`, `polyXgcd_bezout`), `MumfordDivisor`, `isReducedMumford`, Cantor composition and reduction (`cantorCompose`, `cantorReduceAux`, `cantorAdd`, `cantorNeg`, `cantorSmul`), `cantorAdd_preserves_reduced`, `cantorSmul_preserves_reduced`, `D0 = ⟨[0, 1], [1]⟩` (`D0_is_reduced`), `jacobian_D0_order_71`, `jacobian_D0_primitive`, and `jacobian_group_axioms_on_orbit` via an exhaustive candidate classification (`candidateDivisors`) and sliced `decide +kernel` verification of the 71×71 Cayley table (`orbitAt_cayley`).
- Exported `LeanAsm.Genus2Jacobian` in `src/LeanAsm.lean`.
- Updated Part 7 CLI output in `Main.lean` to display `Cantor-Mumford Group Law  : 71 * [P_0 - ∞] = 0 on J(C)(F_5) (zero=true)`.
- Added Part 21 `#print axioms` checks in `tests/TestAxioms.lean` verifying ZERO `Classical.choice` and ZERO `sorryAx` (only `[propext]` and `[propext, Quot.sound]`).

## Verification
- `make build-incremental`: passed (50 jobs)
- `lake env lean tests/TestAxioms.lean`: passed (zero `Classical.choice`, zero `sorryAx`)
- `make sync`: passed

Closes #24

---

## PR #27: feat(collatz): constructive Steiner-Simons-de Weger cycle bounds up to (485, 306)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/collatz-cycle-bounds` -> `main`
- **Created**: 2026-11-14T04:17:41Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/27

### Description

## Summary
- Extended `src/LeanAsm/CollatzQrhBridge.lean` with constructive Steiner–Simons–de Weger cycle bounds through `(485, 306)`:
  - `CollatzOddCycle`, `cycleShift`, `cycleRhs`, `collatz_odd_cycle_linear_eq`, `collatz_odd_cycle_gap_pos`, `collatz_cycle_min_element_lower_bound`, and `collatz_odd_cycle_min_element_lower_bound` (`n_min * (2^k - 3^m) ≥ 3^m - 2^m`).
  - `steiner_1cycle_divides` and `steiner_1cycle_excluded_at_convergents` ruling out Steiner 1-cycles at `(8, 5)`, `(65, 41)`, `(306, 193)`, and `(485, 306)` via `powViaCrtNtt192`.
  - `collatz_convergent_nmin_lower_bounds` certifying explicit ceiling thresholds `n_min ≥ 17`, `87`, `14`, and `978` at `(8, 5)`, `(65, 41)`, `(306, 193)`, and `(485, 306)`.
  - `collatz_odd_cycle_product_bound`, `collatz_linear_form_uniform_306`, and `collatz_cycle_length_lower_bound_306` proving `nMin < 10 * m^2 ≤ 936,360` for `1 ≤ m ≤ 306` and contrapositively `nMin ≥ 936,360 ⇒ m ≥ 307`, `k ≥ 487`, and `K = k + m ≥ 793`.
- Added Part 22 `#print axioms` checks in `tests/TestAxioms.lean` confirming ZERO `Classical.choice` and ZERO `sorryAx` (`[propext]` and `[propext, Quot.sound]` only).
- Updated Part 2 CLI output in `Main.lean` to display the Steiner 1-cycle exclusions and Simons–de Weger cycle-length barrier.

## Verification
- `make build-incremental`: passed (`50` jobs, `Build completed successfully`)
- `lake env lean tests/TestAxioms.lean`: passed (`312` lines, zero `Classical.choice`, zero `sorryAx`)
- `make sync`: passed (`50` jobs + CLI binary execution)

Closes #26

---

## PR #30: feat(euler): constructive Fermat-prime tower {5,17,257,65537} Euler product non-vanishing
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/fermat-tower-euler-product` -> `main`
- **Created**: 2026-11-14T04:32:49Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/30

### Description

## Summary

- Extended `src/LeanAsm/EulerFactorNonVanishing.lean` with constructive Fermat-prime tower `{5, 17, 257, 65537}` Euler product non-vanishing bounds across the critical strip (`σ = 1/2`, `σ = 3/4`, `σ = 1`):
  - `fermatNumber`, `fermatPrefixProd`, `fermatTowerPrimes`, `fermatAllPrimes`, `fermat_prefix_prod_eq` ($\prod_{k=0}^{n-1} (2^{2^k}+1) = 2^{2^n}-1$), and `fermat_tower_product_eq_2pow32_sub_1` (`∏{5,17,257,65537} = 1431655765`, `3 * ∏ = 2^32 - 1 = 4294967295`, `[3,5,17,257,65537].prod = 2^32 - 1`, `∏(p-1) = 2^30 = 1073741824`).
  - `EulerLocalFactorSpec`, `ValidEulerLocalFactorSpec`, `local_euler_disk_nonvanishing`, `euler_product_finite_norm_lower_bound`, and `fermat_tower_euler_product_nonvanishing` proving `0 < ∏ (d_p - rNum_p)^2 ≤ ∏ ((d_p - zx_p)^2 + zy_p^2)` for arbitrary local factors inside `|z_p| ≤ r_p < 1`.
  - `fermat_tower_euler_product_strip_certs` plus universal local-factor disk corollaries `fermat_tower_sigma_half_lower_bound` (`> 1/9`), `fermat_tower_sigma_three_quarters_lower_bound` (`> 1/3`), and `fermat_tower_sigma_one_lower_bound` (`> 9/16 > 1/16`).
- Added Part 23 `#print axioms` checks in `tests/TestAxioms.lean` confirming **ZERO `Classical.choice`** and **ZERO `sorryAx`** (`[]` and `[propext, Quot.sound]` only).
- Updated Part 6 CLI output in `Main.lean` to display the `{5,17,257,65537}` product/totient identities and critical-strip Euler product lower bounds.

## Verification

- `make build-incremental`: passed (`50` jobs, `Build completed successfully`)
- `lake env lean tests/TestAxioms.lean`: passed (zero `Classical.choice`, zero `sorryAx`)
- `make sync`: passed (`50` jobs + CLI binary execution)

Closes #28


---

## PR #31: feat(qrh): high-height 2D zero-free rectangles at t ~ 10^12 via PiChudnovsky twoPiInterval72 phase reduction
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-high-height-1e12` -> `main`
- **Created**: 2026-11-14T05:13:34Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/31

### Description

Closes #29

### Summary
- Extended `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (Part 16) with constructive 72-digit `twoPiInterval72` phase reduction at high heights `t ∈ [10^12, 10^12 + 10]` (`1 ≤ n ≤ 128`):
  - `reducePhaseModTwoPi72` and `reduceModTwoPiCentered72_sound`
  - `high_height_phase_reduction_1e12`: links `PiChudnovsky` `10^105` bracket (`twoPiInterval72.hi - twoPiInterval72.lo = 1` ULP at scale `10^72`, `< 10^-59` rad wrapping expansion `≤ 10^13` ULP) and bounds the `lnInterval72 n` table-width product to `≤ 6 * 10^15` ULP (`< 10^-56` rad)
  - `InHighHeightRect2D`, `IsValidDirichletRect2DN128`, `dirichletGradBoundScaled6`, `isValidHighDirichletTreeN128`, `isValidHighDirichletTreeN128_sound`, `buildDirichletRect2DCertN128`, `sweepDirichletRectangles2DN128`, `isValidDirichletRect2DN128_sound`, `buildDirichletRect2DCertN128_implies_valid`, `sweepDirichletRectangles2DN128_all_valid`
  - `high_height_dirichlet_rects_1e12_certified`: certifies 5 pairwise `t`-disjoint 2D zero-free rectangles for `ζ_128(s)` near `t = 10^12 + 6.1` spanning `σ ∈ [0.501, 0.750]` with total Lebesgue area `6970000000 / 10^12 = 0.006970000000`
- Added Part 24 `#print axioms` audit in `tests/TestAxioms.lean` confirming ZERO `Classical.choice` and ZERO `sorryAx` across all 323 lines of axiom checks.
- Updated Part 5 CLI output in `Main.lean` to print the `t ~ 10^12` `PiChudnovsky` phase reduction precision and high-height `ζ_128` 2D zero-free rectangle sweep summary.

### Verification
- `make build-incremental`: 50 jobs built cleanly
- `lake env lean tests/TestAxioms.lean`: 323 lines verified, ZERO `Classical.choice`, ZERO `sorryAx`
- `make sync`: full build & executable CLI output verified
- Line length check: all `.lean` files ≤ 120 chars with intact headers/footers

---

## PR #33: fix(qrh): address PR #31 Copilot review comments in UltraDeep72
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `fix/pr31-ultradeep72-cleanup` -> `main`
- **Created**: 2026-11-14T05:33:49Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/33

### Description

Addresses both Copilot review comments from PR #31 in `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`:
- Remove the unused `have hmul` binding in `reduceModTwoPiRaw72With_ordered`.
- Align the docstring of `isValidDirichletRect2DN128_sound` with what the theorem formally states (`InHighHeightRect2D`, `r.entries.length ≤ 128`, and positivity for enclosed `terms` under `TermWitnessesEnclosed` and `zetaPartialEvalScaled12`).

Verified with `make build-incremental`, `lake env lean tests/TestAxioms.lean`, and `make sync` (50 jobs, zero `Classical.choice` / `sorryAx`).

---

## PR #35: feat(weil): constructive genus-2 Hasse-Weil functional equation and completed zeta symmetry
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/genus2-functional-eq` -> `main`
- **Created**: 2026-11-14T05:53:13Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/35

### Description

Closes #34

### Summary
- Extended `src/LeanAsm/WeilZetaBridge.lean` with constructive, zero-`Classical.choice`, zero-`sorryAx` proofs for the genus-2 curve $C : y^2 = x^5 - x + 1$ over $\mathbb{F}_5$:
  1. **Cleared-denominator $L$-polynomial reciprocity** (`genus2_L_poly_functional_eq`): homogenized integer, `QRat`, and Gaussian `Int × Int` proofs of $25 T^4 L_C(1/(5T)) = L_C(T)$.
  2. **Weil zeta functional equation** (`genus2_weil_zeta_functional_eq`): cleared-denominator proofs (Gaussian `Int × Int` and integer/rational forms, with denominator non-vanishing) of $5 T^2 Z(C/\mathbb{F}_5, 1/(5T)) = Z(C/\mathbb{F}_5, T)$ for $T \notin \{0, 1, 1/5\}$.
  3. **Completed zeta reflection & critical-line reality** (`genus2_completed_zeta_reflection`): reflection symmetry $\Xi_C(1 - s) = \Xi_C(s)$ on $(u, v)$ satisfying $5 u v = d_u d_v$, vanishing of `completedZetaImagPart u d = 0` on the critical line $\operatorname{Re}(s) = 1/2$ ($5 \, \mathrm{gNormSq}(u) = d^2$), and exact witness `completedZetaImagPart (1, 2) 5 = 0`.
- Added `#print axioms` verification in `tests/TestAxioms.lean` (Part 25) confirming `[propext, Quot.sound]` only (zero `Classical.choice`, zero `sorryAx`).
- Updated `Main.lean` Part 7 CLI output to report the Hasse–Weil functional equations and `Im Ξ_C((1+2i)/5) = 0`.

### Verification
- `make build-incremental`: `+LeanAsm` (24 jobs) built cleanly.
- `lake env lean tests/TestAxioms.lean`: all three new `WeilZetaBridge` theorems depend only on `[propext, Quot.sound]`.
- `make sync`: `lake build` (50 jobs) + CLI executable passed cleanly.

---

## PR #37: feat(qrh): constructive rational zero-density-to-QRH descent bridge in ZeroDensityBridge
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-zero-density-bridge` -> `main`
- **Created**: 2026-11-14T07:12:17Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/37

### Description

Closes #36

### Summary
- Created `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` (`namespace QuasiRiemann`) with constructive, zero-`Classical.choice`, zero-`sorryAx` formalizations over `QRat` / cleared-denominator integers:
  1. **Models & Cleared-Denominator Lemmas:** `ZeroDensitySpec`, `SubconvexitySpec`, `chebyshevGap`, `sublinearAt_iff_exponent_lt_one`, `exponent_mono_sigma`, `exponent_mono_slope`, `sublinearAt_mono_right`, `muAt_endpoints`, `muAt_antitone`, `chebyshevGap_pos_of_lt_one`, and `chebyshevGap_antitone`.
  2. **Benchmark Certificates (`qrh_zero_density_benchmark_certs`):** certifies $A(3/4)(1 - 3/4)$ for Guth–Maynard (`15/26`), Huxley (`3/5`), and Ingham (`2/3`), strict ordering `1/2 < 15/26 < 3/5 < 2/3 < 3/4` with `3/130` savings, and critical-line subconvexity exponents `μ(1/2) ∈ {0, 13/84, 1/6, 1/4}`.
  3. **Zero-Density-to-QRH Descent & DVP Bridge:** `zero_density_implies_qrh_threshold`, `cDvp_div_octaveLnUpper36_le_inv168`, `qrh_theta_ladder_certs` (`3/4 < 7/8 < 11/12 < 47/48 < 1` with Chebyshev gaps `{1/4, 1/8, 1/12, 1/48}` and strict tightening relative to `AsymptoticZfr` DVP boundary for all `t ≥ dvpThresholdT0`), and `zero_density_and_dvp_combined_region`.
- Exported `LeanAsm.QuasiRiemann.ZeroDensityBridge` in `src/LeanAsm.lean`.
- Added Part 26 `#print axioms` checks in `tests/TestAxioms.lean`.
- Updated `Main.lean` Part 5 CLI output to display the certified zero-density exponents at `σ = 3/4` and QRH `θ` ladder.

### Verification
- Line-length check (`> 120` chars): `[]` across all 4 added/modified `.lean` files.
- `make build-incremental`: passed (25 modules, exit code `0`).
- `lake env lean tests/TestAxioms.lean`: all Part 26 theorems depend only on `[propext]` or `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
- `make sync`: `Build completed successfully (52 jobs)` and executable Parts 1–11 ran cleanly (exit code `0`).

---

## PR #39: feat(euler): constructive cyclotomic Fermat-tower Dedekind zeta Euler factor non-vanishing
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/cyclotomic-dedekind-euler` -> `main`
- **Created**: 2026-11-14T07:31:36Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/39

### Description

Closes #38

## Summary
- **Cyclotomic splitting in `src/LeanAsm/EulerFactorNonVanishing.lean`:**
  - Added `fermatCyclotomicSplittingDeg`, `fermatTowerSplittingDegs` (`[2, 8, 128, 32768]`), and `fermat_prime_cyclotomic_splitting_deg`, constructively proving $F_k = 2^{2^k} + 1 \equiv 1 \pmod{2^{2^k}}$ for all $k \ge 1$ with splitting multiplicities $(2, 8, 128, 32768)$ and total ideal sum $32{,}906$.
- **Inductive Dedekind Euler factor & tower non-vanishing:**
  - Added `cyclotomic_split_euler_factor_nonvanishing`, `CyclotomicSplitFactorSpec`, `cyclotomicProdMarginPow`, `cyclotomicProdNormPow`, `cyclotomicProdDenPow`, and `cyclotomic_euler_product_lower_bound` lifting local cleared-denominator Euler disk lower bounds to splitting multiplicity $g \ge 1$ and finite ideal products.
  - Added `fermat_sigma_one_uniform_quarter_bound` (uniform $(1 - 1/F_k)^{2g_k} > 1/4$ via elementary Bernoulli induction `bernoulli_sub_pow_nat`) and `fermat_tower_dedekind_euler_strip_certs` certifying non-vanishing across $(5, 17, 257, 65537)$ with multiplicities $(2, 8, 128, 32768)$ at $\sigma \in \{1/2, 3/4, 1\}$ in symbolic exponent form (plus $> 1/256$ uniform tower bound at $\sigma = 1$).
- **Axiom Audit & CLI:**
  - Added Part 27 `#print axioms` checks in `tests/TestAxioms.lean` confirming only `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
  - Updated `Main.lean` Part 6 CLI output to display splitting multiplicities `(2, 8, 128, 32768)` (`sum = 32906`) and Dedekind strip non-vanishing across $\sigma \in \{1/2, 3/4, 1\}$.

## Verification
- Max line length check (`> 120` chars): `[]` across all 3 modified files
- `make build-incremental`: passed (25 jobs)
- `lake env lean tests/TestAxioms.lean`: passed (all 5 new Part 27 theorems depend only on `[propext, Quot.sound]`)
- `make sync`: passed (52 build jobs, Parts 1–11 CLI output verified)

---

## PR #41: feat(qrh): constructive Chebyshev remainder envelopes across benchmark scales
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/qrh-chebyshev-envelopes` -> `main`
- **Created**: 2026-11-14T07:44:12Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/41

### Description

Closes #40

## Summary
- **Chebyshev remainder model in `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean`:**
  - Added `ChebyshevRemainderSpec`, `chebyshevLogEnv` (`28k`), `chebyshevLogSqEnv` (`(28k)^2`), `tenPowThetaExactExp`, `tenPowThetaCeilExp`, `tenPowGapExp`, `tenPowThetaCeilExp_eq_exact`, `tenPowThetaExactExp_lt_scale`, and `qrhRemainderBoundAtTenPow`.
  - Proved `chebyshev_remainder_mono_theta` and `qrh_chebyshev_savings_certs` certifying monotonicity across $1/2 \le \theta_1 \le \theta_2 < 1$ and exact power-of-ten relative savings $10^3$ ($\theta=3/4$ vs. $7/8$ at $x=10^{24}$), $10^4$ ($\theta=3/4$ vs. $11/12$ at $x=10^{24}$), and $10^{11}$ ($\theta=3/4$ vs. $47/48$ at $x=10^{48}$).
  - Proved `tenPow_rel_err_lt_inv10` and `qrh_chebyshev_benchmark_certs` certifying concrete symbolic envelopes $10^e \cdot (28k)^2$ across $x \in \{10^{12}, 10^{24}, 10^{36}, 10^{48}\}$, strict sub-linear relative error ($< 1$ at $(10^{12}, 3/4)$ and $< 10^{-1}$ at $(10^{24}, 3/4), (10^{36}, 3/4), (10^{48}, \{3/4, 7/8\})$), and the minimal all-rung $< 10^{-1}$ crossover at $x = 10^{336}$ ($k = 28$) simultaneously across all four rungs $\theta \in \{3/4, 7/8, 11/12, 47/48\}$.
- **Axiom Audit & CLI:**
  - Added Part 28 `#print axioms` checks in `tests/TestAxioms.lean` confirming only `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
  - Updated `Main.lean` Part 5 CLI output to display the certified Chebyshev remainder savings across $x = 10^{24}$, $x = 10^{48}$, and the $x = 10^{336}$ all-rung crossover.

## Verification
- Max line length check: `[]` (`> 120` chars and `> 100` chars) across all 3 modified files
- `make build-incremental`: passed (25 jobs)
- `lake env lean tests/TestAxioms.lean`: passed (all 6 new Part 28 theorems depend only on `[propext, Quot.sound]`)
- `make sync`: passed (52 build jobs, Parts 1–11 CLI output verified)

---

## PR #43: feat(crt): constructive Garner mixed-radix CRT and convolution wrap-around bounds over {5, 17, 257, 65537}
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/crt-garner-wraparound` -> `main`
- **Created**: 2026-11-14T07:56:49Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/43

### Description

Closes #42

## Summary
- **Fermat-tower 4-prime CRT & Garner reconstruction in `src/LeanAsm/CrtNttUniversal.lean`:**
  - Linked `LeanAsm.EulerFactorNonVanishing` and proved `fermat_tower_crt_modulus_bounds`: $M_4 = 5 \cdot 17 \cdot 257 \cdot 65537 = 1{,}431{,}655{,}765 = \text{fermatTowerPrimes.prod}$, $3 M_4 = 2^{32} - 1$, and $2^{30} < M_4 < 2^{31}$.
  - Added `garner5_17_257`, `garnerReconstruct4`, `garner_4ch_inverses_sound`, `garnerReconstruct4_lt`, and `garnerReconstruct4_sound` proving sequential mixed-radix CRT roundtrip for all $x < M_4$ using $(c_{12}, c_{123}, c_{1234}) = (7, 127, 32{,}767)$.
  - Added `convPairSum`, `ntt_convolution_no_wraparound`, and `fermat_tower_conv_bound_certs` proving $N \cdot B^2$ convolution bounds and sharp wrap-around safety for $N = 4$ ($B \le 18{,}918$), $N = 8$ ($B \le 13{,}377$), and $N = 16$ ($B \le 9{,}459$).
- **Axiom Audit & CLI:**
  - Added Part 29 `#print axioms` checks in `tests/TestAxioms.lean` confirming only `[]` or `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
  - Updated `Main.lean` Part 10 CLI output with the certified 4-prime Garner inverses and sharp wrap-around limits.

## Verification
- Max line length check (`> 120` chars): `[]` across all 3 modified files
- `make build-incremental`: passed
- `lake env lean tests/TestAxioms.lean`: passed (all 6 new Part 29 theorems depend only on `[]` or `[propext, Quot.sound]`)
- `make sync`: passed (52 build jobs, Parts 1–11 CLI output verified)

---

## PR #44: feat(minivm): verified 2-point and 4-point F_17 NTT assembly programs (#11)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/minivm-f17-ntt` -> `main`
- **Created**: 2026-11-14T08:20:04Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/44

### Description

## Summary
- Extended `MiniVM` (`src/LeanAsm/MiniVM.lean`) with scratch registers `t0, t1` and sequential composition lemma `runProgram_append`.
- Added `src/LeanAsm/MiniVMNttBridge.lean` (exported via `src/LeanAsm.lean`) implementing:
  - `butterfly2AsmF17`, `ntt2AsmF17`, `intt2AsmF17` over `(r0, r1)` using `(r2, r3)`, explicit `+ 17` bias before `subReg`, and `invTwo = 9` mod `17`, with symbolic soundness and roundtrip proofs (`ntt2AsmF17_sound`, `intt2AsmF17_sound`, `intt2_ntt2_asm_F17_roundtrip`) across all `289` states.
  - `dit4AsmF17`, `ntt4AsmF17`, `intt4AsmF17` over `(r0, r1, r2, r3)` using `(t0, t1)`, `omega4 = 13`, `invOmega4 = 4`, and `invFour = 13`, with symbolic soundness and roundtrip proofs (`ntt4AsmF17_sound`, `intt4AsmF17_sound`, `intt4_ntt4_asm_F17_roundtrip`) across all `83,521` states.
- Added Part 30 `#print axioms` checks in `tests/TestAxioms.lean` confirming zero `Classical.choice` and zero `sorryAx`.
- Updated Part 1 CLI output in `Main.lean` to showcase compiled `MiniVM` 2-point and 4-point NTT/INTT execution.

## Verification
- `make build-incremental` passed (all 26 Lean modules / 54 build jobs)
- `lake env lean tests/TestAxioms.lean` passed (Part 30 depends only on `[propext, Quot.sound]`)
- `make sync` passed cleanly (Parts 1–11 executable output verified)

Closes #11

---

## PR #46: refactor(euler): replace brittle tuple projections with named strip cert structures (#32)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `refactor/euler-strip-cert-struct` -> `main`
- **Created**: 2026-11-14T08:33:04Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/46

### Description

## Summary
- Replaced brittle positional tuple projections (`.2.2.2...`) in `EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs` with explicit `Prop`-valued structures in `src/LeanAsm/EulerFactorNonVanishing.lean`:
  - `StripHalfCert` (`σ = 1/2`, bound `> 1/9`)
  - `StripThreeQuartersCert` (`σ = 3/4`, bound `> 1/3`)
  - `StripOneCert` (`σ = 1`, bounds `> 9/16 > 1/16` and `> 1/4` with `F_0 = 3`)
  - `FermatTowerStripCert` bundling `.half`, `.threeQuarters`, and `.one`.
- Preserved all existing bounds, cyclotomic splitting certificates (`fermat_tower_dedekind_euler_strip_certs`), and zero-axiom guarantees.

## Verification
- Checked line lengths (`<= 120` chars) and intact `Path:` / `end of file:` comments in `src/LeanAsm/EulerFactorNonVanishing.lean`.
- `make build-incremental` passed across all 26 Lean modules (54 build jobs).
- `lake env lean tests/TestAxioms.lean` passed (`EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs` depends on ZERO axioms).
- `make sync` passed cleanly (all 54 build jobs and Parts 1–11 CLI output verified).

Closes #32

---

## PR #47: refactor(euler): reuse fsHalf/fs34/fsOne binders in fermat_tower_dedekind_euler_strip_certs
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `refactor/euler-dedekind-binders` -> `main`
- **Created**: 2026-11-14T08:45:39Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/47

### Description

## Summary
Addresses Copilot's review comment from PR #39 (`discussion_r4572293439`) on `src/LeanAsm/EulerFactorNonVanishing.lean`:
- Reused the introduced `fsHalf`, `fs34`, and `fsOne` `let` binders directly when applying `cyclotomic_euler_product_lower_bound` inside `fermat_tower_dedekind_euler_strip_certs`, eliminating the duplicated 4-element `CyclotomicSplitFactorSpec` list construction across all three strip branches.
- Replaced `fermat_4_cyclotomic_valid` with the shared per-element helper `cyclotomic_factor_valid`.
- Kept all theorem types and zero-axiom guarantees intact.

## Verification
- Checked line lengths (`<= 120` chars) and intact `Path:` / `end of file:` comments in `src/LeanAsm/EulerFactorNonVanishing.lean`.
- `make build-incremental` passed across all 26 Lean modules (54 build jobs).
- `lake env lean tests/TestAxioms.lean` passed (`EulerFactorNonVanishing.fermat_tower_dedekind_euler_strip_certs` depends strictly on `[propext, Quot.sound]`, zero `Classical.choice`, zero `sorryAx`).
- `make sync` passed cleanly (54 build jobs and Parts 1–11 CLI output verified).

---

## PR #48: feat(provenance): unified zero-axiom provenance theorem and README architecture audit
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/provenance-summary-audit` -> `main`
- **Created**: 2026-11-14T09:02:43Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/48

### Description

Implements aomaker-org/leanasm#45.

## Summary
- Added `src/LeanAsm/ProvenanceSummary.lean` (exported by `src/LeanAsm.lean`) uniting headline zero-axiom theorems across all 11 CLI parts into component provenance certificates (`miniVm_provenance_certified`, `collatz_provenance_certified`, `yangMills_provenance_certified`, `quasiRiemann_provenance_certified`, `eulerRns_provenance_certified`, `finiteFieldWeil_provenance_certified`, `crtNtt_provenance_certified`, `chudnovskyPi_provenance_certified`) and the master conjunction `LeanAsm.leanasm_full_provenance_certified`.
- Added Part 31 axiom audit in `tests/TestAxioms.lean` verifying the full transitive closure depends strictly on `[propext, Quot.sound]` (0 `Classical.choice`, 0 `sorryAx`).
- Updated `Main.lean` to reference and report `LeanAsm.leanasm_full_provenance_certified`.
- Updated `README.md` (<= 80 columns) with the 27-module theorem inventory, CLI Parts 1-11 overview, and zero-axiom verification workflow.

## Verification
- `make build-incremental`: 27 modules / 56 build jobs completed cleanly.
- `lake env lean tests/TestAxioms.lean`: all 372 output lines audited cleanly with 0 `Classical.choice` and 0 `sorryAx`.
- `make sync`: built and executed all Parts 1-11 cleanly.

Closes #45

---

## PR #50: feat(qrh): constructive short-interval prime bounds and rational exponent ladder
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/short-interval-primes` -> `main`
- **Created**: 2026-11-14T19:46:19Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/50

### Description

## Summary

Implements constructive short-interval prime guarantees, contrapositive maximal prime-gap bounds, and the rational short-interval exponent ladder extending our QRH Chebyshev remainder envelopes and zero-density bounds (`ZeroDensityBridge.lean`).

Closes #49

### Changes
- **`src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`** (exported from `src/LeanAsm.lean`):
  - Defines `ShortIntervalChebyshevSpec` (`thetaNum`, `thetaDen`, `xScaleExp`, `hScaleExp`, `errUpper`, `primePowerCorr`) and decidable `ShortIntervalChebyshevSpec.HasGuaranteedPrime` (`2 * s.errUpper + s.primePowerCorr < 10 ^ s.hScaleExp`).
  - Defines `qrhRemainderBoundAtTwoTenPow` and proves `qrhRemainderBoundAtTenPow_le_twoTenPow`.
  - Proves `short_interval_psi_diff_bound` and `short_interval_spec_guarantees_theta_pos` deriving differenced Chebyshev bounds `|ψ(x + h) - ψ(x) - h| ≤ 2 * E(2x, θ)` and `ϑ(x + h) - ϑ(x) > 0` for `1 ≤ h ≤ x` without `Classical.choice` or `sorryAx`.
  - Proves `qrh_maximal_prime_gap_bound` giving the contrapositive prime-gap bound `pNext - pCurr ≤ 10 ^ hScaleExp`.
  - Proves `qrh_short_interval_positivity_certs` (with `set_option exponentiation.threshold 2000`) certifying `HasGuaranteedPrime` at `θ = 7/8` (`10^336, +10^308`), `θ = 3/4` (`10^168, +10^140`), and `θ = 1/2` (`10^168, +10^98`).
  - Defines `shortIntervalDensityExponent`, proves compatibility with `QuasiRiemann.primeGapExponent`, and proves `short_interval_density_ladder_strict` certifying `1/2 < 17/30 < 7/12 < 2/3 < 3/4 < 7/8 < 1` alongside exact gaps `7/12 - 17/30 = 1/60` and `7/8 - 17/30 = 37/120`.
- **`src/LeanAsm/ProvenanceSummary.lean`**:
  - Adds `ShortIntervalPrimesProp` into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`).
- **`tests/TestAxioms.lean`**:
  - Adds Part 32 `#print axioms` checks verifying all new `ShortIntervalPrimes` theorems audit strictly to `[propext]` or `[propext, Quot.sound]` (ZERO `Classical.choice`, ZERO `sorryAx`).
- **`Main.lean` & `README.md`**:
  - Updates Part 5 CLI output with short-interval prime positivity scales and the `1/2 < 17/30 < 7/12 < 2/3 < 3/4 < 7/8 < 1` ladder.
  - Updates `README.md` (≤ 80 columns) for the 28-module inventory.

### Verification
- `make build-incremental`: passed (28/28 modules, 0 errors, 0 warnings).
- `lake env lean tests/TestAxioms.lean`: passed (0 `Classical.choice`, 0 `sorryAx`, 0 warnings).
- `make sync`: passed cleanly (`git status` clean after commit).


---

## PR #52: feat(qrh): Fermat-tower arithmetic-progression short-interval primes and sub-3/4 QRH ladder
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/fermat-ap-short-intervals` -> `main`
- **Created**: 2026-11-14T19:55:30Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/52

### Description

## Summary

Extends `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` with Fermat-tower arithmetic-progression short-interval prime guarantees (`{5, 17, 257, 65537}`) and sub-`3/4` QRH threshold rungs (`2/3`, `5/8`, `9/16`).

Closes #51

### Changes
- **`src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`**:
  - Imports `LeanAsm.EulerFactorNonVanishing` alongside `LeanAsm.QuasiRiemann.ZeroDensityBridge`.
  - Defines `ApShortIntervalSpec` (extending `ShortIntervalChebyshevSpec` with `q`, `phiQ`) and decidable `ApShortIntervalSpec.HasGuaranteedApPrime` (`phiQ * (2 * errUpper + primePowerCorr) < 10 ^ hScaleExp`).
  - Proves `ap_short_interval_psi_diff_bound` constructively showing `HasGuaranteedApPrime` implies `ϑ(x + h; q, a) - ϑ(x; q, a) > 0` for every reduced residue class `a mod q`.
  - Proves `fermat_tower_ap_short_interval_certs` linking `EulerFactorNonVanishing.fermatTowerPrimes` (`[5, 17, 257, 65537]`, `φ(F_k) ∈ {4, 16, 256, 65536}`) and `EulerFactorNonVanishing.FermatTowerStripCert` to `HasGuaranteedApPrime` under both `θ = 7/8` (`10^336, +10^308`) and `θ = 3/4` (`10^168, +10^140`).
  - Defines `qrhThresholdTwoThirds`, `qrhThresholdFiveEighths`, `qrhThresholdNineSixteenths` and proves `sub_three_quarters_qrh_ladder_certs` certifying `1/2 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8 < 1` (and reversed `chebyshevGap` chain) plus minimal `HasGuaranteedPrime` scales `(24, 21)`, `(24, 20)`, and `(48, 32)`.
- **`src/LeanAsm/ProvenanceSummary.lean`**:
  - Wires `fermat_tower_ap_short_interval_certs`, `ap_short_interval_psi_diff_bound`, and `sub_three_quarters_qrh_ladder_certs` into `ShortIntervalPrimesProp` / `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`).
- **`tests/TestAxioms.lean`**:
  - Adds Part 33 `#print axioms` checks confirming `[propext, Quot.sound]` (`0 Classical.choice`, `0 sorryAx`).
- **`Main.lean` & `README.md`**:
  - Updates Part 5 CLI output and `README.md` (≤ 80 columns) for Part 33 and the new `ShortIntervalPrimes` certificates.

### Verification
- `make build-incremental`: passed (28/28 modules, 0 errors, 0 warnings).
- `lake env lean tests/TestAxioms.lean`: passed (0 `Classical.choice`, 0 `sorryAx`, 0 warnings).
- `make sync`: passed cleanly.


---

## PR #54: feat(minivm): parametric 4-prime Fermat-tower NTT/INTT & Garner CRT assembly
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/minivm-fermat-crt-ntt` -> `main`
- **Created**: 2026-11-14T20:18:22Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/54

### Description

Closes #53

### Summary
- Extended `src/LeanAsm/MiniVMNttBridge.lean` with parametric 4-point NTT/INTT assembly compilers (`ntt4AsmFermat`, `intt4AsmFermat`) across Fermat-tower prime configurations `{5, 17, 257, 65537}` with symbolic soundness (`ntt4AsmFermat_sound`, `intt4AsmFermat_sound`) and roundtrip proofs (`intt4_ntt4_asm_fermat_roundtrip`, `fermatTowerNtt4_asm_roundtrip_certs`).
- Compiled 4-channel Garner mixed-radix CRT reconstruction (`garnerReconstruct4Asm`) over moduli `(5, 17, 257, 65537)` and inverses `(7, 127, 32767)`, proving `garnerReconstruct4Asm_sound` matching `CrtNtt.garnerReconstruct4_sound` (`< M_4 = 1,431,655,765`).
- Added end-to-end 4-point CRT-NTT cyclic convolution assembly bridge (`crtNtt4ChannelConvAsm_sound`, `crtNtt4ConvAsm_sound`) under the sharp bound `B <= 18,918`.
- Wired all new theorems into `MiniVmProvenance` / `miniVm_provenance_certified` in `src/LeanAsm/ProvenanceSummary.lean`, added Part 34 `#print axioms` audits in `tests/TestAxioms.lean`, and updated `Main.lean` Part 1 CLI output and `README.md`.

### Verification
- `make build-incremental`: passed (0 warnings, all targets up to date)
- `lake env lean tests/TestAxioms.lean`: passed (392 axiom lines, 0 `Classical.choice`, 0 `sorryAx`, 0 warnings)
- `make sync`: passed (full build & executable demo succeeded)

---

## PR #56: feat(collatz): higher log_2(3) convergent gaps (1054, 665) & predecessor-tree density
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/collatz-convergents-density` -> `main`
- **Created**: 2026-11-14T20:34:28Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/56

### Description

Closes #55

### Summary
- **318-Digit Convergent Gap & Bracket (`src/LeanAsm/CollatzQrhBridge.lean`)**:
  - Proved `convergent_1054_665_gap_pos` (`2 ^ 1054 < 3 ^ 665 ∧ 0 < 3 ^ 665 - 2 ^ 1054`, 313-digit separation).
  - Proved `log2_3_convergent_bracket_665` (`1054 * 306 < 485 * 665`, certifying `1054 / 665 < log_2(3) < 485 / 306`).
  - Proved `steiner_1cycle_excluded_1054_665` excluding both `(1054, 665)` directly (gap violation `2 ^ 1054 < 3 ^ 665`) and `(1055, 665)` via `¬ ((2 ^ 1055 - 3 ^ 665) ∣ (3 ^ 665 - 2 ^ 665))`.
- **Simons–de Weger Cycle Barrier (`src/LeanAsm/CollatzQrhBridge.lean`)**:
  - Proved `simons_de_weger_barrier_665`: under `936,360 <= c.nMin`, any non-trivial `CollatzOddCycle m` satisfies `666 <= m` odd steps, `1055 <= cycleShift c.a m` halvings, and `1721 <= cycleShift c.a m + m` total steps.
- **Constructive Predecessor-Tree & Density Bounds (`src/LeanAsm/CollatzQrhBridge.lean`)**:
  - Defined computable `collatzPredecessors` and `collatzPredTree`, proved backward-to-forward soundness `collatzPredTree_sound` into `Conjectures.iterate Conjectures.collatzStep`, and proved `collatz_mod6_branching`.
  - Defined `PredecessorDensitySpec` and proved `collatz_pred_tree_growth_certs` certifying exact depth cardinalities (`14 -> 18 > 15`, `15 -> 24 > 16`, `20 -> 72 > 21`) and cleared-denominator power-law comparisons against `3/4 < 84/100 < 9/10 < 1`.
- **Provenance, Axiom Audit, CLI & Docs**:
  - Wired all new theorems into `CollatzProvenance` / `collatz_provenance_certified` in `src/LeanAsm/ProvenanceSummary.lean` and Part 35 of `tests/TestAxioms.lean`.
  - Updated `Main.lean` Part 2 CLI output and `README.md` (`<= 80` cols).

### Verification
- `make build-incremental`: passed (0 warnings, all 28 modules up to date)
- `lake env lean tests/TestAxioms.lean`: passed (402 axiom lines, 0 `Classical.choice`, 0 `sorryAx`, 0 warnings)
- `make sync`: passed (58 jobs built, executable demo succeeded)

---

## PR #58: feat(qrh): higher-truncation 2D zero-free rectangles via CRT-NTT precision engine
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/ultradeep-crt-ntt-rectangles` -> `main`
- **Created**: 2026-11-14T22:11:10Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/58

### Description

Closes #57

## Summary
- **`src/LeanAsm/QuasiRiemann.lean`**: Added `HighTruncZeroFreeRectSpec`, `HasCertifiedNonVanishing`, constructive `nonvanishing_of_certified`, `InBox2D`, `LipTile2D`, `IsValidLipTile2D`, `intervalMinSq_le_sq_of_scaled_mem`, constructive `isValidLipTile2D_sound`, `IsPartition2x2Tiles`, and constructive `partition2x2_covers_all_points`.
- **`src/LeanAsm/QuasiRiemann/UltraDeep72.lean`**:
  - Added 90-digit CRT-NTT interval engine (`ln_table_1_to_512_valid`, `crtNtt_phase_reduction_512_sound`) certifying phase reduction `t ln n mod 2π` across `n ≤ 512` at heights `t ~ 10^12` and `t ~ 10^18` to `< 10^-60` radians via `PiChudnovsky.intMulBigViaCrtNtt` / `PiChudnovsky.pi_100_digits_certified`.
  - Refactored `eulerMaclaurinB2TailCore` and proved `eulerMaclaurinB2TailRect2DForN_128_eq`, universal `eulerMaclaurinB2TailRect2DForN_monotone`, and `euler_maclaurin_tail_shrinks_with_N` down to `σ = 0.5005` (`1001/2000`) and `σ = 0.50025` (`2001/4000`).
  - Certified compositional `2 × 2` 2D Lipschitz box tilings (`crtNtt_highTrunc_2d_zero_free_rect`) at `(σ = 0.5005, N = 256, t ~ 10^12)` and `(σ = 0.50025, N = 512, t ~ 10^18)`.
- **`src/LeanAsm/ProvenanceSummary.lean`, `tests/TestAxioms.lean`, `Main.lean`, `README.md`**: Wired `HighTruncRectProvenanceProp` into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified`, added Part 36 `#print axioms` checks, added CLI summary output, and updated documentation (`≤ 80` cols in `README.md`, `≤ 120` chars in `.lean`).

## Verification
- `make build-incremental`: passed (`28/28` modules cached/built, `0` warnings).
- `lake env lean tests/TestAxioms.lean`: passed (`0` `Classical.choice`, `0` `sorryAx`, `0` warnings; all Part 36 theorems depend only on `[propext]` / `[propext, Quot.sound]`).
- `make sync`: passed (`58 jobs`, Lean executable test & provenance checks succeeded).

---

## PR #62: feat(langlands): GSp(4) to SO(5) functorial lift and Selberg / Kim-Sarnak ladder (#61)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/gsp4-functoriality-bridge` -> `main`
- **Created**: 2026-11-14T22:30:43Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/62

### Description

Closes #61

## Summary
- Added `src/LeanAsm/GSp4FunctorialityBridge.lean` (exported from `src/LeanAsm.lean`) formalizing:
  1. **Cleared-Denominator `GSp(4) -> SO(5)` Standard Euler-Factor Lift**: `gsp4StandardEulerPoly`, `gsp4StdQuarticCofactor`, `gsp4StandardEulerHomog`, `gsp4StdRecipEval`, and `gsp4_std_functional_equation` proving `(1 - T)` factorization, anti-palindromic symmetry `T^5 (q * L_std(1/T)) = -(q * L_std(T))`, and `q * L_std(1) = 0`.
  2. **Genus-2 Curve `C / F_5` Cyclotomic Lift & Ramanujan Temperedness**: `genus2_f5_so5_cyclotomic_lift` and `genus2_f5_so5_ramanujan_tempered`, specializing to `(q, a₁, a₂) = (5, -5, 15)` from `FiniteFieldRH` and `Genus2Jacobian` (`#J(C)(F_5) = 71`), proving `5 * L_std(T) = 5 (1 - T) Φ_10(T)`, exact `1 - T^10` divisibility, and unit-circle `T^10 = 1` eigenvalue temperedness.
  3. **Langlands Symmetric-Power (`Sym^k`) & Selberg / Kim–Sarnak Ladder**: `kim_sarnak_ramanujan_ladder_strict` (`0 < 7/64 < 1/9 < 1/5 < 1/4 < 1/2`) and `selberg_laplacian_eigenvalue_ladder` (`3/16 < 21/100 < 77/324 < 975/4096 < 1/4` with exact `Sym^3 -> Sym^4` spectral gap `127/331776`) in constructive `QRat`.
- Wired the new theorems into `src/LeanAsm/ProvenanceSummary.lean` (`LeanAsm.finiteFieldWeil_provenance_certified` & `LeanAsm.leanasm_full_provenance_certified`).
- Added Part 37 `#print axioms` checks in `tests/TestAxioms.lean` (`0 Classical.choice`, `0 sorryAx`).
- Updated `Main.lean` Part 7 CLI output and `README.md` (`≤ 80` cols).

## Verification
- `make build-incremental`: 0 errors, 0 warnings (29/29 modules up to date)
- `lake env lean tests/TestAxioms.lean`: all Part 37 theorems depend only on `[]`, `[propext]`, or `[propext, Quot.sound]` (`0 Classical.choice`, `0 sorryAx`)
- `make sync`: clean build, executable run, and workspace sync passed

---

## PR #63: feat(qrh): add openai-20261028 scanner and Cauchy-Lipschitz box bounds
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `chore/scan-openai-20261028` -> `main`
- **Created**: 2026-11-14T23:23:08Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/63

### Description

Zero-dependency scanner for subrepos/YM/submissions/openai-20261028 (MANIFEST, LEAN_TOC, QRH_7_8_CANDIDATES) plus cleared-denominator Cauchy-Lipschitz interior box lower-bound and telescoping contraction certificates in UltraDeep72 and ProvenanceSummary.

---

## PR #64: feat(artin): add GL(1) Artin-Fermat Euler & MiniVM NTT bridge
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/artin-fermat-bridge` -> `main`
- **Created**: 2026-11-14T23:48:41Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/64

### Description

Closes #59

## Summary
- Added `src/LeanAsm/ArtinFermatBridge.lean` (`ArtinFermatCharacterSpec`, `artinFermatTowerSpecs` for `(F_k, \omega_4) \in \{(5,2), (17,4), (257,16), (65537,256)\}` with `\phi(F_k) = 2^{2^k} \in \{4, 16, 256, 65536\}`), proving:
  - `artin_split_euler_factor_collapse`: links `EulerFactorNonVanishing.FermatTowerStripCert` and `fermat_tower_dedekind_euler_strip_certs` to cleared-denominator `(d - r)^\phi(F_k)` split Euler products and positive strip evaluations.
  - `artin_order4_cyclotomic_factorization`: certifies `\prod_{j=0}^{3} (1 - \omega_4^j T) \equiv 1 - T^4 \pmod{F_k}` across `{5, 17, 257, 65537}`.
  - `artin_char_transform_eq_ntt4`: proves the 4-element GL(1) Artin Fourier transform equals `NttArithmetic.ntt4` for all `(F_k, \omega_4)` and every valid `ArtinFermatCharacterSpec` / `FermatNtt4Spec`.
  - `artin_char_orthogonality_minivm`: composes `MiniVMNttBridge.ntt4AsmFermat_sound` and `intt4_ntt4_asm_fermat_roundtrip` to certify GL(1) Artin character orthogonality (`\delta_{i,m}`) inside `MiniVM` assembly execution.
- Exported `LeanAsm.ArtinFermatBridge` in `src/LeanAsm.lean` and bundled the four headline theorems into `EulerRnsProvenance` / `eulerRns_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
- Added Part 39 `#print axioms` checks in `tests/TestAxioms.lean`, updated Part 6 CLI output in `Main.lean`, and updated `README.md` (`30` modules, `28` submodules, `Parts 1-39`).

## Verification
- `make build-incremental` (`30/30` modules, `0` warnings, `0` errors)
- `lake env lean tests/TestAxioms.lean` (`Parts 1-39` passed, `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`)
- `make sync` (full `lake build` + CLI execution across Parts 1-11 + unified provenance, exit `0`)

---

## PR #66: feat(port): audit 21 pure constructive openai-20261028 files and port bridge
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/port-openai-constructive` -> `main`
- **Created**: 2026-11-15T00:08:35Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/66

### Description

Closes #65

## Summary
- Audits all 21 `leanasm_pure_constructive` `.lean` files under `subrepos/YM/submissions/openai-20261028` in [`docs/openai-20261028/CONSTRUCTIVE_AUDIT.md`](docs/openai-20261028/CONSTRUCTIVE_AUDIT.md) (4 substantive lattice/gauge modules = 57 declarations, 1 metaprogramming module = 4 declarations, 6 vintage macro scripts = 0 declarations, 10 audit/stub/control files = 6 declarations).
- Adds pure-constructive [`src/LeanAsm/ConstructiveOpenaiBridge.lean`](src/LeanAsm/ConstructiveOpenaiBridge.lean) porting 4D lattice routes, closed square walks, `boxSites`/`slabSites` foliation (`slab_sum_foliation`), gauge connection holonomy covariance (`holonomy_gauge_covariant`), `SignedSym4` face-holonomy trace invariance (`classFn_send_price`), and concrete non-abelian `Q_8 subset SU(2)` instantiations (`q8_plaquette_holonomy_gauge_invariant`, `q8_send_price_trace_invariant`) with **zero** `Classical.choice` and **zero** `sorryAx`.
- Exports `LeanAsm.ConstructiveOpenaiBridge` in `src/LeanAsm.lean`, extends `YangMillsProvenance` / `yangMills_provenance_certified` (bundled into `LeanAsm.leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`, adds Part 41 axiom checks in `tests/TestAxioms.lean`, updates Part 4 CLI output in `Main.lean`, and updates `README.md`.

## Verification
- `make build-incremental` (`31` modules, `0` errors, `0` warnings)
- `lake env lean tests/TestAxioms.lean` (`459` axiom check lines, `0 Classical.choice`, `0 sorryAx`, `0 warnings`)
- `make sync` (`64` build jobs + `leanasm` executable verified)
- `git -C subrepos/YM status -s` clean


---

## PR #67: feat(weil): add E_11a1 / f_11 elliptic modularity bridge
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/elliptic-modularity-bridge` -> `main`
- **Created**: 2026-11-15T00:31:37Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/67

### Description

Closes #60

### Summary
- Add `LeanAsm.EllipticModularityBridge` (`src/LeanAsm/EllipticModularityBridge.lean`) certifying:
  - Exact integer truncated `q`-expansion coefficients `heckeCoeff11 n` up to degree `100` for the weight-2 cusp form $f_{11}(\tau) = \eta(\tau)^2 \eta(11\tau)^2 \in S_2(\Gamma_0(11))$ via chunked convolution (`etaStage1`–`etaStage10`, `f11Coeffs_eq_table`, `heckeCoeff11_bad_11`).
  - Point counts `#E_{11a1}(F_p)` (`ec11a1_point_counts_97`), balanced binary sum-tree equivalence (`sumTree_eq_range_foldl`), and `5`-torsion divisibility (`ec11a1_five_torsion_97`) for $E_{11a1} : y^2 + y = x^3 - x^2 - 10x - 20$ across all `24` good primes $p \le 97$.
  - Constructive Eichler–Shimura Hecke–Frobenius trace equality `eichler_shimura_trace_eq_11a1` ($c_p(f_{11}) = a_p(E_{11a1})$ for all $24$ good primes $p \le 97$, plus $c_{11} = 1$).
  - Strict Hasse–Weil / Ramanujan temperedness (`a_p^2 < 4p`) and cleared-denominator `GL(2)` Euler-factor positivity (`0 < v^2 - a_p u v + p u^2` for $v > 0$) via `hasse_weil_ramanujan_11a1_certs`.
  - Hecke multiplicativity (`c_1 = 1`, `c_{mn} = c_m c_n` for coprime `m, n >= 1` with `mn <= 100`, and `c_{p^2} = c_p^2 - p` for $p \in \{2, 3, 5, 7\}$) via `hecke_multiplicativity_11a1_certs`.
- Export `LeanAsm.EllipticModularityBridge` in `src/LeanAsm.lean` and integrate into `FiniteFieldWeilProvenance` / `LeanAsm.leanasm_full_provenance_certified` (`src/LeanAsm/ProvenanceSummary.lean`).
- Add Part 42 axiom audit to `tests/TestAxioms.lean`, Part 7 modularity telemetry to `Main.lean`, and update `README.md` (`32` modules / `30` submodules / `21` domain modules, Parts 1–42).

### Verification
- `make build-incremental`: `66` jobs built cleanly (`0` errors, `0` warnings).
- `lake env lean tests/TestAxioms.lean`: all axiom audits (Parts 1–42) verified with `0 Classical.choice`, `0 sorryAx`, `0` warnings; `LeanAsm.leanasm_full_provenance_certified` uses only `[propext, Quot.sound]`.
- `make sync`: `lake build`, `leanasm` executable, and environment checks passed with `0` warnings.
- `git -C subrepos/YM status -s`: clean.


---

## PR #72: docs(qrh): add v1.2.0 architecture roadmap (#68-#71)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `docs/roadmap-v1-2-0` -> `main`
- **Created**: 2026-11-15T00:47:30Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/72

### Description

## Summary
- Add `docs/ROADMAP_V1_2_0.md` (strictly `<= 80` cols) capturing the architectural scan on `main` (`d96e3d9`), cross-pillar disconnections across the 32 verified modules, candidate lemmas from `docs/openai-20261028/LEAN_TOC.json` (`Extension/UV`, `UVExtension`, `Contacts`, `EveryPhase`, `RemainderComparison`, `RG08`), and the four `v1.2.0` issue specs (`#68`–`#71`).

## Verification
- Line-length check on `docs/ROADMAP_V1_2_0.md`: `124` lines, max `80/80` cols (`0` violations).
- `git -C subrepos/YM status -s`: clean.


---

## PR #73: feat(qrh): parametric beyond-7/8 QRH ladder and Kim-Sarnak coupling
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/parametric-qrh-ladder` -> `main`
- **Created**: 2026-11-15T00:57:17Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/73

### Description

Closes #68

## Summary
- Added `src/LeanAsm/QuasiRiemann/ParametricQrhLadder.lean` and exported it from `src/LeanAsm.lean`:
  - `qrhShortExponent (k : Nat) = (2^k + 1) / 2^(k + 1)` and dual `qrhDualFraction (k : Nat) = (2^(k + 1) - 1) / 2^(k + 1)`.
  - `qrhShortExponent_strict_anti`: inductive descent `1/2 < qrhShortExponent (k + 1) < qrhShortExponent k` and `k ≥ 2 → qrhShortExponent k < 7/8` (`5/8 > 9/16 > 17/32 > 33/64 > 1/2`).
  - `qrhShortExponent_density_benchmarks`: comparison against Huxley (`7/12`), Guth–Maynard (`17/30`), and `zdGuthMaynard` saving (`11/26`).
  - `qrhDualFraction_strict_mono`: inductive ascent `7/8 < 15/16 < 31/32 < ... < 1` and exact dualities (`qrhShortExponent k + qrhDualFraction k = 3/2`, `qrhDualFraction k - 1/2 = 1 - qrhShortExponent k`, `qrhThresholdFromMollifier (qrhDualFraction k) = qrhShortExponent (k + 1)`).
  - `ParametricQrhBridgeSpec`, `mollifierFromAutomorphic`, `qrhFromAutomorphic_eqv_half_add`, `shortIntervalQrh1732Spec_has_prime` (`θ = 17/32` at `[10^96, +10^57]`), `kim_sarnak_amplified_qrh_step`, and `parametric_qrh_kim_sarnak_certs` coupling `GSp4FunctorialityBridge.thetaKimSarnakSym4 = 7/64` and `selbergLambda1 = 975/4096`.
- Wired `ParametricQrhLadderProp` into `QuasiRiemannProvenance` and `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
- Added Part 43 `#print axioms` checks in `tests/TestAxioms.lean`, updated Part 5 CLI summary in `Main.lean`, and updated `README.md` (`33 modules`, `31 submodules`, Parts 1–43).

## Verification
- `make build-incremental`: passed (`33` modules, `0` errors, `0` warnings).
- `lake env lean tests/TestAxioms.lean`: passed (all Part 43 theorems and `quasiRiemann_provenance_certified` / `leanasm_full_provenance_certified` depend only on `[propext, Quot.sound]`, `0 Classical.choice`, `0 sorryAx`).
- `make sync`: passed (`0` errors, `0` warnings); `git -C subrepos/YM status -s` clean.


---

## PR #74: feat(qrh): N=256,512 rational contraction and ZeroDensityBridge strip export
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/ultradeep72-rational-contraction` -> `main`
- **Created**: 2026-11-15T01:43:06Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/74

### Description

Implements #69 cleanly with zero `Classical.choice`, zero `sorryAx`, and zero compiler warnings.

### Summary
- **`src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (Part 19):**
  - Added `RationalBoxContractionSpec`, `RationalBoxContractionSpec.lip_mul_radius_lt`, constructive `rational_box_contraction_step`, and `rational_telescoping_chain_cert` generalizing `1/2` halving to arbitrary cleared-denominator rational contraction ratios `0 < qNum < qDen` with shrunk-ball `M / (r - δ)` derivative margins.
  - Certified `ultraDeep72_N256_rational_rect_cert` (`N = 256`, `σ = 0.5005`, `t ~ 10^12`, `q = 1/3`, `dirichletGradBoundScaled6_512 500500 256 = 117284435`) and `ultraDeep72_N512_rational_rect_cert` (`N = 512`, `σ = 0.50025 = 1/2 + 1/4000`, `t ~ 10^18`, `q = 2/5`, `dirichletGradBoundScaled6_512 500250 512 = 195620879`).
- **`src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` (Part 7):**
  - Imported `LeanAsm.QuasiRiemann.UltraDeep72`, added `CertifiedStripWidthSpec` (`certifiedStrip05005_N256`, `certifiedStrip050025_N512`), `exponent_strict_mono_sigma`, `ultradeep72_strip_to_zero_density_bridge`, and `ultradeep72_N512_strip_zd_certs`, proving exact critical-strip exponent tightenings (`3/5200` on `zdGuthMaynard` and `3/5000` on `zdHuxley`) from `σ = 1/2 + 1/4000`.
- **Provenance, Audit, CLI & Docs:**
  - Wired `HighTruncRationalContractionProp` into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified` (and transitively `LeanAsm.leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
  - Added **Part 44** `#print axioms` checks in `tests/TestAxioms.lean`.
  - Updated `Main.lean` Part 5 CLI output and `README.md` (`Parts 1-44`).

### Verification
- `make build-incremental` (`33` modules, `0` errors, `0` warnings)
- `lake env lean tests/TestAxioms.lean` (`0` `Classical.choice`, `0` `sorryAx`, `0` warnings across Parts 1-44)
- `make sync` (`lake build` + `lake exe leanasm` passed; `subrepos/YM` clean)

Closes #69


---

## PR #75: feat(artin): add GL(1) Artin character-twisted short-interval bridge (Closes #70)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/artin-short-interval-bridge` -> `main`
- **Created**: 2026-11-15T02:04:26Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/75

### Description

Closes #70

## Summary
- Added `src/LeanAsm/ArtinShortIntervalBridge.lean` and exported it from `src/LeanAsm.lean`, lifting `ShortIntervalPrimes.ApShortIntervalSpec` and `ParametricQrhLadder.qrhShortExponent` bounds to order-4 `GL(1)` Artin character-twisted short-interval prime sums across the Fermat-prime tower `{5, 17, 257, 65537}` and beyond-`7/8` parametric exponents (`17/32 < 39/64 < 5/8 < 2/3 < 3/4 < 7/8`).
- Proved `artin_gaussian_char_orthogonality`, `artin_ntt4_residue_class_recovery`, `artin_twisted_ap_short_interval_pos`, `artin_twisted_coset_short_interval_pos`, and `fermat_tower_artin_short_interval_certs` connecting `MiniVM` 4-point NTT/INTT execution to residue-class recovery and prime positivity.
- Wired `ArtinShortIntervalProvenanceProp` into `EulerRnsProvenance` / `eulerRns_provenance_certified` (and transitively `leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
- Added **Part 45** `#print axioms` checks in `tests/TestAxioms.lean`, updated Part 6 output in `Main.lean`, and documented the 34-module inventory and Part 45 in `README.md` (`<= 80` cols).

## Verification
- `make build-incremental`: passed (34/34 modules, 70 jobs, `0` warnings).
- `lake env lean tests/TestAxioms.lean`: passed across Parts 1–45 with `0` `Classical.choice`, `0` `sorryAx`, and `0` warnings.
- `make sync` & `.lake/build/bin/leanasm`: passed cleanly with `subrepos/YM` clean.

---

## PR #76: feat(qrh): add constructive dyadic-shell and discrete Abel summation bridge (Closes #71)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/dyadic-abel-bridge` -> `main`
- **Created**: 2026-11-15T02:18:16Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/76

### Description

Closes #71

## Summary
- Added `src/LeanAsm/QuasiRiemann/DyadicAbelBridge.lean` and exported it from `src/LeanAsm.lean`, extending `ConstructiveOpenaiBridge.slab_sum_foliation` and `QuasiRiemann.ShortIntervalPrimes` / `ParametricQrhLadder` with constructive `[M, M * 2^k)` dyadic-shell partitioning, discrete Abel summation-by-parts, and cleared-denominator quadratic `1 / √N` tail gates.
- Proved `dyadic_shell_sum_partition`, `dyadic_shell_sum_foliation`, `discrete_abel_summation_by_parts`, `abel_summation_by_parts_list`, `abel_monotone_weight_envelope`, `abel_monotone_weight_envelope_qrat`, `sqrt_tail_gate_of_sq_le`, `inv_sqrt_tail_gate_dyadic_step`, `sqrt_tail_gate_dyadic_step`, `short_interval_dyadic_abel_envelope`, and `dyadic_abel_short_interval_certs` across the beyond-`7/8` ladder (`17/32 < 9/16 < 5/8 < 2/3 < 3/4 < 7/8`).
- Wired `DyadicAbelProvenanceProp` into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified` (and transitively `leanasm_full_provenance_certified`) in `src/LeanAsm/ProvenanceSummary.lean`.
- Added **Part 46** `#print axioms` checks in `tests/TestAxioms.lean`, updated Part 5 CLI output in `Main.lean`, and updated `README.md` (`<= 80` cols) to document the 35-module inventory and Parts 1–46.

## Verification
- `make build-incremental`: passed (35/35 modules, 72 jobs, `0` warnings).
- `lake env lean tests/TestAxioms.lean`: passed across Parts 1–46 with `0` `Classical.choice`, `0` `sorryAx`, and `0` warnings.
- `make sync`: passed cleanly with `subrepos/YM` clean.

---

## PR #77: docs: ingest, verify, and refactor v1.2.0 architecture review
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `docs/ingest-arch-review-1.2.0` -> `main`
- **Created**: 2026-11-15T02:35:56Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/77

### Description

Ingests and refactors the v1.2.0 architecture review into `docs/ARCH_REVIEW_V1_2_0.md` and brings `README.md` module/audit counts up to date with `v1.2.0` (`6db78d7`).

### Summary
- Add [`docs/ARCH_REVIEW_V1_2_0.md`](docs/ARCH_REVIEW_V1_2_0.md) formatted to Directive 04 (`<= 80` cols, path header/footer) with factual corrections verified against `main` (`6db78d7`):
  - Correct 4-prime Fermat modulus `M_4 = (2^32 - 1)/3 = 1,431,655,765` (`3 * M_4 = 2^32 - 1`).
  - Distinguish 100-digit Chudnovsky `pi` bounds from 192-digit Karatsuba CRT-NTT multiplication and 90-digit `UltraDeep72` phase reductions.
  - Document pure Lean 4 core constructive primitives (zero Mathlib, `List.nodup_range`, `Nat.decLt`/`Int.decLt`) and `ProvenanceSummary`'s eight `def ... : Prop` conjunctions + explicit 8-way `LeanAsm.leanasm_full_provenance_certified`.
- Update `README.md` (`35` modules, `33` submodules / `22` domain modules, `Parts 1-46`, `Abel` under `QuasiRiemann/`, and links to `docs/ROADMAP_V1_2_0.md` & `docs/ARCH_REVIEW_V1_2_0.md`).

### Verification
- `make sync`: 72/72 Lake jobs, 0 warnings, 0 errors.

---

## PR #82: docs: add v1.3.0 architecture roadmap (#78-#81) and v1.2.0 code digest
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `docs/roadmap-v1-3-0` -> `main`
- **Created**: 2026-11-15T02:48:53Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/82

### Description

Adds the `v1.3.0` architecture roadmap (`#78`–`#81`) and merges `docs/V1_2_0_CODE_DIGEST.md` into `main`, updating `README.md` links.

### Summary
- Add [`docs/ROADMAP_V1_3_0.md`](docs/ROADMAP_V1_3_0.md) (`<= 80` cols, Directive 04 header/footer) covering Issues `#78`–`#81` (Parts 47–50):
  - `#78`: `MollifierVariationalBridge.lean` (closed-loop rungs `k = 5, 6` and quadratic variational mollifier optimization)
  - `#79`: `UltraDeep72.lean` build-performance split + 108-digit `twoPiInterval108` + `N = 1024, 2048` down to `σ = 0.5000625` + `MiniVM` 8-pt NTT `ntt8AsmFermat_sound`
  - `#80`: `LanglandsRankinSelbergBridge.lean` (unified `GL(1) x GL(2) -> GSp(4)` Rankin-Selberg & Hecke short-interval bridge)
  - `#81`: `ProthNttTowerBridge.lean` (5-prime Proth NTT tower `P_5 = 15*2^27 + 1` & Dedekind strip bounds)
- Include [`docs/V1_2_0_CODE_DIGEST.md`](docs/V1_2_0_CODE_DIGEST.md) summarizing `v1.2.0` additions in oversized modules.
- Link `docs/ROADMAP_V1_3_0.md` and `docs/V1_2_0_CODE_DIGEST.md` in `README.md`.

(Issues `#78`–`#81` remain open until their implementation PRs land.)

---

## PR #83: feat(qrh): closed-loop dyadic-Abel rungs k=5,6 and variational mollifier bridge
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/mollifier-variational-bridge` -> `main`
- **Created**: 2026-11-15T03:02:36Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/83

### Description

Implements GitHub Issue #78 (`v1.3.0` roadmap workstream).

## Summary
- **New module [`MollifierVariationalBridge.lean`](src/LeanAsm/QuasiRiemann/MollifierVariationalBridge.lean)** (exported in `src/LeanAsm.lean`, zero Mathlib, zero `Classical.choice`, zero `sorryAx`, zero warnings):
  - **Closed-loop dyadic-Abel rungs `k = 5, 6`**: `dyadic_abel_unlocks_next_rung` couples `abel_monotone_weight_envelope_qrat`, `inv_sqrt_tail_gate_dyadic_step`, ladder advance, and `short_interval_spec_guarantees_theta_pos`. Certifies concrete `HasGuaranteedPrime` for `k = 5` (`33/64` on `[10^192, 10^192 + 10^108]`) and `k = 6` (`65/128 = 1/2 + 1/128` on `[10^384, 10^384 + 10^206]`), extending `65/128 < 33/64 < 17/32 < 7/8`.
  - **Two-piece `QRat` variational mollifier (`TwoPieceMollifierSpec`, `variational_mollifier_beats_linear`)**:
    - Explicitly separates `mollifierDirichletEnergy c1 c2 = c1^2 + 2*c1*c2 + (4/3)*c2^2` (= `(c1+c2)^2 + (1/3)*c2^2 >= 1`, equal to `49/48` at `(3/4, 1/4)`; `linear_minimizes_dirichlet_energy`) from the cleared-denominator variational off-diagonal energy `mollifierVariationalEnergy c1 c2 = c1^2 + c1*c2 + c2^2 = (c1+c2)^2 - c1*c2` (and `mollifierRatioL2Energy = 37/48 < 1`), proving `variational_energy_lt_one_of_pos` (`13/16 < 1` at `(3/4, 1/4)`) and strictly tightening the `thetaKimSarnakSym4 = 7/64` (`selbergLambda1 = 975/4096`) QRH threshold to `603/1024 < 39/64`.
- **Provenance & CLI**: Wired `MollifierVariationalProp` into `QuasiRiemannProvenance` / `quasiRiemann_provenance_certified` in `ProvenanceSummary.lean`, updated `Main.lean` Part 5 output and `README.md` (`36` modules / `Parts 1-47`, `<= 80` cols).
- **Verification**:
  - `make build-incremental`: 74 Lake jobs, 0 errors, 0 warnings across 36 modules.
  - `lake env lean tests/TestAxioms.lean`: Parts 1-47 (525 axiom checks) strictly `[propext]` or `[propext, Quot.sound]` (0 `Classical.choice`, 0 `sorryAx`).
  - `make sync`: clean pass, `subrepos/YM` clean.

Closes #78

---

## PR #84: feat(qrh,minivm): UltraDeep108 N=1024/2048 tiling and MiniVM 8-pt Fermat NTT
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/ultradeep-n2048-minivm-ntt8` -> `main`
- **Created**: 2026-11-15T17:39:55Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/84

### Description

Implements GitHub Issue #79 (`v1.3.0` roadmap workstream).

## Summary
- **Modularized `UltraDeep72` & 108-digit Chudnovsky phase reduction**:
  - Split `UltraDeep72.lean` into `UltraDeep72Core.lean`, `UltraDeep90.lean`, and the `UltraDeep108` stack (`UltraDeep108Tables.lean`, `UltraDeep108Eval.lean`, `UltraDeep108N1024.lean`, `UltraDeep108N2048.lean`, `UltraDeep108.lean`), registered in `UltraDeep72.lean` and `LeanAsm.lean`.
  - Certified `phase_reduction_width_1e30_under_1e75` (`< 10^-75` rad up to `t ~ 10^30`, `N <= 2048`, zero `Classical.choice`, zero `sorryAx`).
  - Certified 128-step chunked 2D zero-free tilings & rational contractions `crtNtt_highTrunc108_N1024_rect` / `ultraDeep72_N1024_rational_rect_cert` (`N = 1024`, `σ = 0.500125`, `t ~ 10^24`, gradient `319421067`) and `crtNtt_highTrunc108_N2048_rect` / `ultraDeep72_N2048_rational_rect_cert` (`N = 2048`, `σ = 0.5000625`, `t ~ 10^30`, gradient `512891320`).
- **Zero-density bridge & `MiniVM` 8-pt Fermat NTT**:
  - Added `ZeroDensityBridge.lean` Part 8 (`certifiedStrip0500125_N1024`, `certifiedStrip05000625_N2048`, `ultradeep72_N2048_strip_zd_certs`).
  - Wired `MiniVMNttBridge.fermatTowerNtt8_asm_roundtrip_certs` (`fermatTowerNtt8Specs_valid`) into `MiniVmProvenance` and `UltraDeep108` certificates into `HighTruncRationalContractionProp` / `QuasiRiemannProvenance` in `ProvenanceSummary.lean`.
- **Tests, CLI, & Docs**:
  - Added Part 48 to `tests/TestAxioms.lean`, updated `Main.lean` Parts 1 & 5, and updated `README.md` (`43` modules, `Parts 1-48`).
- **Verification**:
  - `make build-incremental`: `Build completed successfully (88 jobs).`
  - `lake env lean tests/TestAxioms.lean`: Parts 1-48 strictly `[propext]` or `[propext, Quot.sound]` (`0 Classical.choice`, `0 sorryAx`, `0 warnings`).
  - `./.lake/build/bin/leanasm` & `make sync`: clean pass; `subrepos/YM` clean.

Closes #79

---

## PR #85: feat(local): add Ollama Qwen + DeepSeek codebase auditor and config_env toggles
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/ollama-local-config` -> `main`
- **Created**: 2026-11-16T00:58:02Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/85

### Description

Adds local Windows/WSL2 Ollama configuration, Antigravity SDK runners, and the profiled Qwen + DeepSeek codebase auditor:

- `config_env`: CLI tags/flags (`deepseek`, `qwen`, `gemini`, `argon`, `argon-low`, `sonnet`, `opus`), `LEANASM_USE_OLLAMA` toggle, and non-mutating `agy_session()` helper ( / ).
- `local/`: `agent.py`, `prover_orchestrator.py`, `auditor.py` (`--direct`, `--two-phase`, `--qwen-only`, `--prover-only`, smart source slicing, `--cooldown-secs`, `--budget-secs`, `--resume`, full JSONL/memory/VRAM/CPU-spill profiling), and `local/audit/usingQwenPlusDeepseek.sh`.
- `docs/`: `ollama_local.md`, `local_llm_brainstorming.md`, and `local_audit_todo.md` consolidating deterministic 43/43 + initial 17/43 local AI review findings.

---

## PR #87: feat(valuation): constructive p-adic ultrametric, telescoping contraction, and Prime Tower Hensel lifting over QRat
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feat/ultrametric-valuation` -> `main`
- **Created**: 2026-11-16T05:10:08Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/87

### Description

## Summary

Adds the three-module `QuasiRiemann.Valuation` stack (`Ultrametric`, `Contraction`, `Hensel`) to provide constructive $p$-adic ultrametric denominator-height control and Prime Tower CRT modular lifting over cleared-denominator `QRat`, strictly within Lean 4.35.0's `[propext, Quot.sound]` axiom cone (**zero Mathlib**, **zero `Classical.choice`**, **zero `sorryAx`**).

### Modules & Integration

1. **`src/LeanAsm/QuasiRiemann/Valuation/Ultrametric.lean`**
   - Constructive, decidable trial-division primality (`IsPrime`) and Euclid's lemma (`IsPrime.dvd_mul`).
   - Fuel-bounded structural $p$-adic valuation (`padicValNat`, `padicValInt`, `pAdicVal : Nat → QRat → ExtVal`).
   - Negation invariance (`pAdicVal_neg`), multiplicativity (`pAdicVal_mul`), and strong ultrametric triangle inequality (`ultrametric_ineq`).
   - Cleared-denominator prime-power height bounds across sums, products, `List QRat` folds, and Horner polynomial evaluation (`denVal_hornerEval_deg_le`, `denVal_hornerEvalTight_deg_le`).

2. **`src/LeanAsm/QuasiRiemann/Valuation/Contraction.lean`**
   - Cleared-denominator cross-multiplication valuation invariance (`pAdicVal_eq_of_cross_mul`) and telescoping identity (`pAdicVal_sub_add_sub`).
   - `IsPAdicStepContraction` framework with linear $n$-step valuation growth (`iterate_val_growth`) and zero-slack multi-step Cauchy bounds (`iterate_val_range`, `iterate_val_range_of_init`).

3. **`src/LeanAsm/QuasiRiemann/Valuation/Hensel.lean` (Parts 1–10)**
   - **Parts 1–3:** Stationary Newton-Schulz contraction (`stationary_isStepContraction`) and quadratic Newton-Schulz inverse lifting (`nsStep_residual_val_double`, `hensel_newton_schulz_quadratic_residual`, `hensel_newton_schulz_cauchy_range`) with `by decide` Mersenne certificates (`p = 7, 31, 127`).
   - **Parts 4–7:** Two-prime and arbitrary `List Nat` Prime Tower CRT divisibility and lifting (`prime_tower_pow_dvd_of_all`, `hensel_prime_tower_crt`), `CrossEq` equivalence of `hornerEval` and `hornerEvalTight`, and constructive CRT idempotent/seed synthesis (`crtCofactor`, `crtIdempotent`, `buildCrtSeed`, `hensel_build_prime_tower_crt`).
   - **Parts 8–10:** Ultrametric Horner perturbation bounds (`hornerEval_sub_val_ge_of_integral`, `hornerEval_zero_const_sub_val_ge`), divided-difference slope factorization (`hornerEval_sub_cross_eq_slope`, `polySlope_diag_cross_eq_deriv`), arbitrary-degree simple-root lifting (`hensel_poly_simple_root_pow_dvd`), and Prime Tower CRT root lifting (`hensel_poly_prime_tower_crt`, `hensel_poly_build_prime_tower_crt`, `hensel_mersenne_tower_sqrt2_built` for $\sqrt{2} \bmod 27559^{n+1}$).

4. **Top-Level Wiring & Axiom Audit (`LeanAsm.lean`, `ProvenanceSummary.lean`, `Main.lean`, `Makefile`, `tests/TestAxioms.lean`)**
   - Exports `QuasiRiemann.Valuation` in the library and provenance summary, archives processed inbox artifacts under `inbox/archive/`, and adds Part 48 `#print axioms` checks confirming `[propext, Quot.sound]` across the entire stack.

### Verification

- `lake build` — 94 jobs succeed with zero errors and zero warnings (`Hensel.lean` builds in ~6.2s).
- `lake env lean tests/TestAxioms.lean` — zero `Classical.choice`, zero `Lean.ofReduceBool`, zero `sorryAx`.


---

## PR #88: feat(langlands): add Rankin-Selberg, Sym^2(f_11), and GSp(4) spinor bridge (#80)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/langlands-rankin-selberg-80` -> `main`
- **Created**: 2026-11-16T20:21:21Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/88

### Description

## Summary
Zero-Mathlib, constructive Langlands bridge for `E_{11a1}` / `f_{11}`.

- `LanglandsRankinSelbergBridge.lean`
  - `rs_pos_goodPrimes`: f_11 x chi_4 cleared Euler factor > 0, p <= 97.
  - `sym2_pos_goodPrimes`: Sym^2 cleared factor > 0 (incl. a_p = 0).
  - `gl2ProdToGSp4Spinor_reciprocal`, `spin_eq_product`: GL2 x GL2 ->
    GSp4 spinor polynomial, tied to `gsp4SpinEulerPoly`.
  - `hecke_chi4_short_interval_bound`: Abel summation,
    |sum c_n phi(n)| <= 2 B phi(M).
- `ProvenanceSummary.lean`: `LanglandsRankinSelbergProvenance` plus
  the Hensel/Mersenne sqrt2 provenance wiring.
- `tests/TestAxioms.lean`: Part 50 audit; duplicate Part 48 block removed.
- `LeanAsm.lean`, `Main.lean` wired.

## Verification
`lake build`, `make sync`, and the axiom audit: 0 warnings, 0 `sorryAx`,
0 `Classical.choice`.

Closes #80


---

## PR #89: feat(ntt): add 5-prime Proth NTT tower and Garner CRT reconstruction (#81)
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/proth-ntt-tower-81` -> `main`
- **Created**: 2026-11-16T20:44:47Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/89

### Description

Adds the 5-prime Proth NTT tower bridge and Garner CRT reconstruction, with provenance summary, axiom test, and roadmap updates.

Closes #81

---

## PR #90: feat(rns): implement constructive RNS/CRT valuation and high-order contraction loops
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/rns-crt-valuation` -> `main`
- **Created**: 2026-11-17T05:38:43Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/90

### Description

## Summary

This pull request implements Residue Number System (RNS) arithmetic and Chinese Remainder Theorem (CRT) constructive reconstruction for high-precision valuation and rational box contraction loops in Lean 4.

### Key Changes
- **RNS & CRT Foundations (`src/LeanAsm/QuasiRiemann/Valuation/RNS.lean`)**:
  - Implemented `RnsInt` and `RnsQRat` with length-invariance proofs.
  - Implemented constructive `RnsInt.add` and `RnsInt.reconstruct` folding over coprime moduli products.
  - Implemented `RnsQRat.toQRat` converting reconstructed numerator and denominator pairs to `QRat`.
  - Added high-order contraction loops ($N = 1024, 2048$) with certified soundness guarantees.
- **Verification & Axiom Provenance**:
  - Added `tests/TestRNS.lean` validating RNS and CRT reconstruction logic.
  - Updated `tests/TestAxioms.lean`.
  - Verified 0 `sorryAx`, 0 `Classical.choice`, adhering strictly to standard Lean foundational axioms (`[propext, Quot.sound]`).

### Commits
- `d60dea5`: feat(rns): implement RnsInt, RnsQRat, and constructive CRT reconstruction
- `5537e87`: feat(rns): integrate high-order rational box contraction loops (N=1024, 2048) and certified soundness

---

## PR #91: feat(build): consolidate sequential build with telemetry and heap capping
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/consolidate-sequential-build` -> `main`
- **Created**: 2026-11-17T07:32:04Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/91

### Description

## Summary
- Consolidates sequential build runner into `tools/incremental_build.py`.
- Enforces default 4096MB heap capping (`-M 4096` / `LEAN_OPTS="-M4096"`) on elaboration tasks to prevent RAM thrashing on large modules like `Genus2Jacobian` and `PiChudnovsky`.
- Integrates rolling telemetry and +10% regression warning detection against `.lake/build-history.json`.
- Adds standard `make build-seq` target to the `Makefile`.
- Removes obsolete scratch scripts (`build_sequential*.py`).
- Documents preferred sequential build directives in `AI.md` ([Directive 01]).

## Verification
- Clean run of `make build-seq` caching and elaborating all 52 modules.
- `make sync` zero-axiom test suite passes.

---

## PR #92: feat(valuation): unicritical polynomial preperiodic dynamics & valuation partitions
- **Status**: MERGED
- **Author**: @fekerr
- **Branch**: `feature/preperiodic-dynamics` -> `main`
- **Created**: 2026-11-17T07:37:41Z
- **Labels**: None
- **URL**: https://github.com/aomaker-org/leanasm/pull/92

### Description

### Summary

Formalizes unicritical polynomial preperiodic dynamics {d,\alpha}(x) = x^d + \alpha$ and preperiodic partition sets (S, f) = f^n(S) \setminus f^{n+1}(S)$ following Andersen & Garton (arXiv:2405.00605v1), verified over constructive zero-Mathlib `QRat`.

### Key Formalizations
- **Constructive Polynomial Dynamics**: Horner evaluator, addition, unicritical families {d,\alpha}(x) = x^d + \alpha$, and iterated evaluation over `QRat`.
- **Preperiodic & Generalized Partitions**: Constructive representations and upper/lower bounds for (S, f)$ and generalized partition sets {m,n}(S, f)$.
- **Proposition 2.2**: Concrete verification of valuation stabilization and dynamical properties.
- **Theorem 5.1**: Asymptotic density bounds for preperiodic partitions as  \to \infty$.
- **Theorem 1.3 / Corollary 5.1**: Average proportion bounds over quadratic polynomial families.
- **Proposition 5.3**: Average generalized partition bounds.
- **Key Lemma 4.2 & Lemma 4.3**: Wreath product multiplicity bounds and uniform divisibility bounds.
- **Axiom Audit**: Added `tests/TestPreperiodic.lean` and updated `tests/TestAxioms.lean` to audit strict axiom compliance (`[propext, Quot.sound]`, zero `sorryAx`, zero `Classical.choice`).

---

