<!-- Path: leanasm/docs/yang_mills_formalization_overview.md -->
<!-- Max Column: 80 Columns -->

# 4D Pure Yang–Mills Formalization & Verification Guide

## Executive Overview

In late 2026, OpenAI submitted a formal proof package for 4D pure Yang–Mills
theory (`yang-mills-group/OpenAI-YM-20261028`), evaluated independently by the
Yang–Mills review group (`yang-mills-group/YM`, Assessment 1, Nov 10, 2026).

This document analyzes the formal structure, the mathematical scope, the
Osterwalder–Schrader (OS) / Wightman reconstruction chain, and reproduction
instructions.

---

## 1. Scope of the Proved Claim vs. Millennium Problem

| Aspect | What Was Proved | What Was NOT Proved |
| :--- | :--- | :--- |
| **Continuum Limit** | Relativistic QFT satisfying Wightman / OS axioms constructed as a scaling limit of 4D Wilson lattice gauge theory for any simple compact Lie group $G$. | Does **NOT** establish uniqueness of the thermodynamic / infinite-volume limit. |
| **Mass Gap** | Proves fixed-volume UV convergence and a positive lattice probe. | Does **NOT** prove a non-zero strictly positive continuum mass gap ($\Delta > 0$). |
| **Perturbative Matching** | Leading short-distance trace logarithmic power law. | Not an all-orders perturbative matching with QCD. |

---

## 2. Core Lean 4 Formalization Architecture

The proof package spans three primary layers:

### A. The Challenge Specification (`ChallengeSpec.lean` / `Challenge.lean`)
```lean
theorem YangMills.jointExistence : YangMills.JointExistence := by
  sorry
```
- Defines the `JointExistence` predicate:
  1. Existence of a Wilson family of gauge observables.
  2. Regularity of correlation functions.
  3. Operator Product Expansion (OPE) hierarchy and trace law bounds.

### B. The Construction Chain (`Construction.lean` / `Solution.lean`)
```lean
theorem YangMills.jointExistence : YangMills.JointExistence := by
  intro g hg
  obtain ⟨C, _, _, reg, orders⟩ := YangMills.constructed.{0,0} g hg 1 zero_lt_one
  refine ⟨YangMills.wilsonFamily C, reg, fun p hp => ?_⟩
  ...
```
- Constructs the continuum measure from the lattice limit:
  - $\mathbb{Z}^4$ Wilson lattice action with compact gauge group $G$.
  - Phase averaging and UV cutoff removal.
  - Multi-scale extraction order hierarchy.

### C. The Review Group's Independent Checks (A1–A8)
The review group (`yang-mills-group/YM`) verified the package against 8 formal
criteria in `checks/CombinedAcceptance.lean`:
- **A1**: Centered stress-trace scalar family satisfies Douglas–Mei–Yin
  Osterwalder–Schrader axioms (E0–E4) and linear growth.
- **A2**: Registered invariant polynomial operator content and faithful dense domain.
- **A3 & A7**: Agreement with Wilson lattice action after coupling conversion.
- **A4**: Trace two-point kernel UV power-law bounds.
- **A5**: Common scale and lattice probe.
- **A6**: Translation Ward identity with fixed sign and cutoff independence.
- **A8**: Separate Operator Product Expansion (OPE) remainder bounds.

---

## 3. How to Hydrate & Reproduce Locally

The Yang–Mills suite can be hydrated into `subrepos/YM` using the lazy hydration
workflow:

```bash
# 1. Register or clone into subrepos (or an external work tree)
mkdir -p subrepos
git clone https://github.com/yang-mills-group/YM.git subrepos/YM
cd subrepos/YM/submissions/openai-20261028

# 2. Check byte-level SHA-256 integrity of inputs & upstream specs
python3 scripts/verify.py integrity

# 3. Memory & Threading recommendations (avoid OOM thrashing on <=16GB RAM)
# Pinned to leanprover/lean4:v4.32.0 (elan auto-downloads this version)
export LEAN_NUM_THREADS=2

# 4. Run the review build and axiom check
python3 scripts/verify.py all
```

---

## 4. Axiom Audit Standard

Following Lean FRO standards, the review runner enforces:
- **Zero warnings** across all 43 review modules.
- **Dependencies strictly limited** to standard axioms:
  `[propext, Classical.choice, Quot.sound]`.
- Rejection of `sorryAx` or `Lean.ofReduceBool` (`native_decide`).

<!-- end of file: leanasm/docs/yang_mills_formalization_overview.md -->
