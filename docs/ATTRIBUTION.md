# Path: leanasm/docs/ATTRIBUTION.md
# docs/ATTRIBUTION.md - Mathematical Citations & External Paper Inclusions
# Max Column: 80 Columns

## Overview

This repository includes constructive, zero-Mathlib formalizations derived from
and inspired by mathematical literature. This document provides explicit
attribution, arXiv identifiers, publication references, and source module
mappings for external papers preserved in [`docs/`](../docs/).

---

## 1. Andersen & Garton (2024)

### Citation & Paper Metadata
- **Authors**: Aaron Andersen and Derek Garton
- **Title**: *Preperiodic points of polynomial dynamical systems over finite
  fields*
- **arXiv**: [arXiv:2405.00605](https://arxiv.org/abs/2405.00605) (`[math.DS]`,
  `[math.NT]`)
- **PDF Artifact**: [`docs/2405.00605v1.pdf`](2405.00605v1.pdf)
- **Raw URL**:
  `https://raw.githubusercontent.com/aomaker-org/leanasm/main/docs/2405.00605v1.pdf`

### Formalization & Inclusion in `leanasm`
- **Module**:
  [`src/LeanAsm/QuasiRiemann/Valuation/PreperiodicDynamics.lean`](../src/LeanAsm/QuasiRiemann/Valuation/PreperiodicDynamics.lean)
- **Test / Axiom Suite**:
  [`tests/TestPreperiodic.lean`](../tests/TestPreperiodic.lean) and
  [`tests/TestAxioms.lean`](../tests/TestAxioms.lean) (Part 52)
- **Core Results Formalized**:
  1. **Unicritical Polynomial Dynamics**: Constructive Horner evaluator and
     iteration for the family $f_{d,\alpha}(x) = x^d + \alpha$ over `QRat`.
  2. **Preperiodic Partition Sets**:
     $W_n(S, f) = f^n(S) \setminus f^{n+1}(S)$ and generalized partitions
     $W_{m,n}(S, f)$.
  3. **Proposition 2.2**: Concrete verification of valuation stabilization and
     dynamical partition behavior.
  4. **Theorem 3.2**: Constructive upper bound helper for partition sizes.
  5. **Theorem 5.1**: Asymptotic density bounds for preperiodic partitions as
     degree/iteration parameters scale.
  6. **Theorem 1.3 / Corollary 5.1**: Average proportion bounds over quadratic
     polynomial families.
  7. **Proposition 5.3**: Generalized partition average bounds.
  8. **Key Lemma 4.2 & Lemma 4.3**: Wreath product multiplicity bounds and
     uniform divisibility bounds.

---

## 2. Chiriac & Jorza (2026)

### Citation & Paper Metadata
- **Authors**: Liubomir Chiriac and Andrei Jorza
- **Title**: *Lacunary recurrences and 2-adic properties of Eisenstein series*
- **arXiv**: [arXiv:2605.09738](https://arxiv.org/abs/2605.09738) (`[math.NT]`)
- **PDF Artifact**: [`docs/2605.09738v2.pdf`](2605.09738v2.pdf)
- **Raw URL**:
  `https://raw.githubusercontent.com/aomaker-org/leanasm/main/docs/2605.09738v2.pdf`

### Formalization & Inclusion in `leanasm`
- **Modules**:
  - [`src/LeanAsm/QuasiRiemann/Valuation/Eisenstein2Adic.lean`](../src/LeanAsm/QuasiRiemann/Valuation/Eisenstein2Adic.lean)
  - [`src/LeanAsm/QuasiRiemann/Valuation/EisensteinWeights.lean`](../src/LeanAsm/QuasiRiemann/Valuation/EisensteinWeights.lean)
- **Test / Axiom Suite**:
  [`tests/TestAxioms.lean`](../tests/TestAxioms.lean) (Part 52)
- **Core Results Formalized**:
  1. **Binary Hamming Weight & 2-Adic Valuation**:
     Constructive `hammingWeight` $s(n)$ and 2-adic valuation $v_2(n)$ on
     `Nat` and `QRat`.
  2. **Valuation Step Identity (§3.1)**:
     $s(m) + v_2(m) = s(m - 1) + 1$ for $m \ge 1$.
  3. **Legendre Formula (§3.1)**:
     $v_2(m!) + s(m) = m$.
  4. **Romik Recurrence 2-Adic Balance (§3.1)**:
     2-adic valuation balance for recurrence coefficients of modular forms with
     weights $k = 6n + 2$, $1 \le j \le n$.
  5. **Proposition 4 (§2)**:
     For weight $k = 2^{m+2}$, the unique coefficient of
     $G_k = \sum_{4a + 6b = k} w(a, k) G_4^a G_6^b$ with $v_2(w(a, k)) = 0$ is
     $a = 2^m$, while $v_2(w(a, k)) > 0$ for all $a \ne 2^m$.
  6. **Explicit Weight Calculations (§2–§3)**:
     Concrete certified weights for $k \in \{16, 32, 64\}$ verified over
     constructive `QRat` (`weight_16_4`, `weight_32_8`, `weight_64_16`,
     `prop4_computed_m0` through `prop4_computed_m4`).

---

## 3. General Citation & Reproduction Policy

All formalizations in `leanasm` adhering to these papers maintain:
- **Zero Mathlib Dependency**: Completely self-contained definitions of
  valuations, rational numbers (`QRat`), and polynomial algebra.
- **Strict Axiom Governance**: All imported definitions and theorems audit
  strictly to `[propext, Quot.sound]` (zero `Classical.choice` and zero
  `sorryAx`).
- **Reproducibility**: Run `lake env lean tests/TestAxioms.lean` to verify the
  entire dependency cone of both papers.

<!-- end of file: leanasm/docs/ATTRIBUTION.md -->
