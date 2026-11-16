<!-- Path: leanasm/docs/local_audit_todo.md -->
<!-- Max Column: 80 Columns -->

# Local Qwen + DeepSeek Audit Findings & Actionable TODO List

Consolidated TODO list from the deterministic 43-module baseline
(`audit_20261115_225111`) and local Qwen + DeepSeek module reviews across
Phases C and D. See [`local_llm_brainstorming.md`](local_llm_brainstorming.md).

## 1. Verified Soundness Baseline (43/43 Modules)

- [x] **Zero `sorry` / zero custom `axiom` across all 43 modules**
- [x] **`44/44` `lake` build + `TestAxioms.lean` checks passed (`exit=0`)**

---

## 2. Deterministic Hygiene Issues Found (Phase A Sweep)

### Missing File Footer (`AI.md` Directive 04)
- [ ] **`src/LeanAsm/MiniVMNttBridge.lean`**: Missing `-- end of file:` footer
  (`Header/Footer = Y/N` in `audit_20261115_225111`, 2,355 lines).

### Line-Length Violations (`>100` Columns in `.lean` Files)
- [ ] `src/LeanAsm/QuasiRiemann/UltraDeep108Tables.lean` — `633` lines `>100`
- [ ] `src/LeanAsm/QuasiRiemann/UltraDeep90.lean` — `106` lines `>100` cols
- [ ] `Main.lean` — `58` lines `>100` cols
- [ ] `src/LeanAsm/QuasiRiemann.lean` — `39` lines `>100` cols
- [ ] `src/LeanAsm/CrtNttUniversal.lean` — `37` lines `>100` cols
- [ ] `src/LeanAsm/NttArithmetic.lean` — `33` lines `>100` cols
- [ ] `src/LeanAsm/CrtNtt.lean` — `32` lines `>100` cols
- [ ] `src/LeanAsm/QuasiRiemann/UltraDeep72Core.lean` — `26` lines `>100` cols
- [ ] Minor (`1–8` lines `>100` cols): `EulerFactorNonVanishing` (`8`),
  `EllipticModularityBridge` (`6`), `PiChudnovsky` (`6`),
  `ParametricQrhLadder` (`6`), `CollatzQrhBridge` (`5`),
  `DyadicAbelBridge` (`4`), `GSp4FunctorialityBridge` (`3`),
  `Genus2Jacobian` (`3`), `WeilZetaBridge` (`3`),
  `MollifierVariationalBridge` (`2`), `ArtinShortIntervalBridge` (`1`),
  `MiniVMNttBridge` (`1`), `PiChudnovsky/CrtMulBridge` (`1`),
  `ProvenanceSummary` (`1`), `ZeroDensityBridge` (`1`), `YangMillsToy` (`1`),
  `LeanAsm` (`1`).

---

## 3. Code & Docstring Review Findings (Qwen + DeepSeek Audits)

All audited modules so far received **Verdict: PASS** on correctness and build
verification. Actionable cleanup/documentation suggestions flagged by Qwen:

- [ ] **`src/LeanAsm/QuasiRiemann/Rat.lean`** (`audit_20261115_223726` &
  `224523`):
  - Expand `QRat.ofInt` docstring.
  - Document the `b.num ≠ 0` divisor requirement on `QRat.div`, and clarify the
    `b.num = 0` fallback behavior in `QRat.div?` and `QRat.divOrZero`.
  - Optional: add dedicated algebraic helper lemmas for `QRat.div` / `QRat.eqv`.
- [ ] **`src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean`**
  (`audit_20261115_230538`):
  - Expand docstring on `octaveLnUpper36_bounds_lnInterval36` to state the
    explicit relationship between `t`, `ln2Upper36Scaled`, and
    `(lnInterval36 2).hi`.
- [ ] **`src/LeanAsm/YangMillsQ8.lean`** (`audit_20261115_230538`):
  - Tighten `Q8.mul` docstring with a concise summary of the quaternion
    multiplication table structure.
- [ ] **`src/LeanAsm/MiniVM.lean`** (`audit_20261115_232106`):
  - Review whether helper lemmas `get_set_same`, `get_set_other`, `get_set_pc`,
    `add_comm_equiv`, and `mul_mod_reg_correct` should be marked `@[simp]` or
    trimmed/consolidated around `exec_garner_crt_sound`.
- [ ] **`src/LeanAsm/YangMillsToy.lean`** (`audit_20261115_232106`):
  - Unify docstring terminology between "vacuum configuration" and
    "trivially +1".
- [ ] **`src/LeanAsm.lean`** (`audit_20261115_232106`):
  - Add brief section comments grouping the top-level module imports.
- [ ] **`src/LeanAsm/QuasiRiemann/UltraDeep108Eval.lean`**
  (`audit_20261115_235957`):
  - Remove redundant type annotation on `sigmaIv18` in
    `dirichletGradBoundScaled6_2048Core`.
  - Improve parameter naming/doc clarity on `zetaAnchorStep108Core` and
    `evalZetaAnchorHigh108Core`.
- [ ] **`src/LeanAsm/FiniteFieldRH.lean`**,
  **`src/LeanAsm/GSp4FunctorialityBridge.lean`**, and
  **`src/LeanAsm/QuasiRiemann/UltraDeep108N1024.lean`**
  (`audit_20261116_003840`):
  - Add brief docstrings to internal helper definitions and intermediate
    certificate lemmas (`t24_0_c1`..`t24_0_c8`).

---

## 4. Remaining Local Audit Sweep Queue

- [x] **Phase A (Deterministic 43/43 + `TestAxioms.lean`)**: Done (`10.25 s`)
- [x] **Phase B (`--two-phase`, `--qwen-only`, smart slicing)**: Complete
- [x] **Phase C (Small modules `<= 8 KB`, `11/11`)**: Complete (`UltraDeep72`,
  `AsymptoticZfrBridge`, `Conjectures`, `LeanAsm`, `Sqrt10005`, `UltraDeep108`,
  `YangMillsQ8`, `Rat`, `RnsArithmetic`, `YangMillsToy`, `MiniVM`)
- [ ] **Phase D (Medium modules `8–35 KB`, `6/12` complete)**:
  - [x] Batch 1 (`3/12`): `UltraDeep108Eval`, `PiChudnovsky`, `CrtMulBridge`
  - [x] Batch 2 (`3/12`, `audit_20261116_003840` `790.65 s`):
    `GSp4FunctorialityBridge`, `UltraDeep108N1024`, `FiniteFieldRH`
  - [ ] Batch 3 (`6/12` remaining): `MollifierVariationalBridge`,
    `ChudnovskySeries`, `EllipticModularityBridge`, `Main`,
    `UltraDeep108N2048`, `ParametricQrhLadder`
- [ ] **Phase E (Large modules `> 35 KB`, `20` modules)**: Run in resumable
  slices (`--qwen-only --num-ctx 4096 --max-source-chars 8000`)

---

## 5. Future Zero-Quota Tooling & `openai-20261028` TODOs

- [ ] **Live runtime heartbeat viewer (`local/audit_status.py`)**: Display
  active module, elapsed time, `events.jsonl` tok/s, `/api/ps` memory, and
  recent lines of `/mnt/c/Users/feker/AppData/Local/Ollama/server.log`.
- [ ] **Offline QRH 7/8 candidate filter over `docs/openai-20261028/`**:
  Batch-score the `782` matched declarations in `QRH_7_8_CANDIDATES.md` +
  `LEAN_TOC.json` using local Qwen/DeepSeek to filter out Yang-Mills/Mathlib
  collisions and surface portable cleared-denominator lemmas.
- [ ] **Optional `core11` (`10.0.0.213`) remote prover node**: Install Windows
  Ollama on `core11` if dual-laptop `--prover-base-url` runs are desired.

<!-- end of file: leanasm/docs/local_audit_todo.md -->
