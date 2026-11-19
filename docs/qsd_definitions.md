# Path: leanasm/docs/qsd_definitions.md
# QSD[1-4] Algebraic Variants and Formal Definitions Reference
# Max Column: 80 Columns

This reference specifies the four Quasi-Spectral Decomposition algebraic
variants (`QSD[1]`, `QSD[2]`, `QSD[3]`, `QSD[4]`) formalized in `leanasm`.
All structures, theorems, and certificates are implemented constructively in
Lean 4 without Mathlib, requiring zero `Classical.choice` and zero `sorryAx`
(reducing strictly to foundational axioms `[propext, Quot.sound]`).

The QSD family bridges non-commutative, dual-jet, and residue-ring dynamics
with the Quasi-Riemann Hypothesis (QRH) analytic box-contraction pipelines
and master provenance certificates.

---

## 1. Overview of the QSD Algebraic Family

The four QSD variants capture distinct algebraic and arithmetic structures:

- **`QSD[1]`**: Dual jets and split idempotents (`SliceDualQRat`,
  `SplitIdempotentQRat`). Captures $m^2 = 0$, $L^2 = 1$, and log-derivative box
  contractions ($N = 1024, 2048$).
- **`QSD[2]`**: Truncated 6-basis ring (`QsdTrunc6`). Models associativity
  defects along the nilpotent $f$-axis under quadratic truncation.
- **`QSD[3]`**: $\mathbb{Z}_2$-graded superalgebra (`Z2Grading`,
  `GradedFactor`). Formalizes Koszul anti-commutation obstructions blocking
  naive Euler product swapping.
- **`QSD[4]`**: Residue rings and Hensel towers (`QsdModRing`,
  `QsdDualModRing`). Formalizes CRT channel decomposition, nilpotent
  zero-divisor lifting, and prime-tower tangent lifts.

---

## 2. QSD[1]: Central Tensor, Dual Jets, and Split Idempotents

`QSD[1]` formalizes first-order dual-jet arithmetic and orthogonal split
idempotents over rational numbers `QRat` (`LeanAsm.QuasiRiemann.Rat`).

### 2.1 Dual Jet Ring (`SliceDualQRat`)

The structure `SliceDualQRat` represents jet elements $u + \tau m$ with
nilpotent parameter $m^2 = 0$:

```lean
structure SliceDualQRat where
  val : QRat
  tan : QRat
  deriving Repr, DecidableEq
```

- **Leibniz Product Rule**: `slice_dual_leibniz` proves exact tangent
  propagation for Dirichlet-polynomial factors:
  $$(D(s) + D'(s) m)(W(s) + W'(s) m) = D(s)W(s) + (D(s)W'(s) + D'(s)W(s)) m$$
- **Dual Inverses**: `sliceDualInv` computes $(u + \tau m)^{-1} = u^{-1} -
  (\tau / u^2) m$ whenever $u.num \neq 0$. `qsd1_slice_dual_inv_laws`
  formally verifies $(x \cdot x^{-1}).val = 1$ and $(x \cdot x^{-1}).tan = 0$.
- **Logarithmic Derivative**: `logDeriv(x) = x.tan / x.val`.
  `qsd1_log_deriv_mul_additive` proves constructive additivity:
  $$\text{logDeriv}(A \cdot B) = \text{logDeriv}(A) + \text{logDeriv}(B)$$

### 2.2 Split Idempotent Generators (`SplitIdempotentQRat`)

The structure `SplitIdempotentQRat` encapsulates split generators $L$ with
$L^2 = 1$. The canonical projectors are:
- $e_+ = (1 + L) / 2$ (`e_plus`)
- $e_- = (1 - L) / 2$ (`e_minus`)

Theorem `split_idempotent_properties` verifies orthogonal decomposition on
canonical instances `canL` ($L = 1$) and `canL_neg` ($L = -1$):
- $e_+ + e_- = 1$
- $e_+^2 = e_+$ and $e_-^2 = e_-$
- $e_+ \cdot e_- = 0$

### 2.3 Rational Box Contraction Bridges ($N=1024$, $N=2048$)

`DualJetBoxBoundSpec` couples dual-jet envelopes $(D_{lo} \le |D(s_0)|,
|D'(s)| \le M_{lip})$ and logarithmic-derivative margins to the concrete
analytic specifications in `UltraDeep108N1024` and `UltraDeep108N2048Part3`:

- **Theorem `qsd1_log_deriv_to_rational_box_contraction`**:
  Proves that a cleared dual-jet bound $2 M_{lip} r \le D_{lo}(r - \delta)$
  guarantees the non-vanishing interior ball condition:
  $$2 \cdot M_{lip} \cdot r \le D_{lo} \cdot (r - \delta)$$
- **Certificate `qsd1_log_deriv_N1024_cert`**:
  $N = 1024$ ($\sigma = 0.500125$, $t \sim 10^{24}$),
  $D_{lo} = 2.5 \times 10^{12}$, $M_{lip} = 3.2 \times 10^8$.
- **Certificate `qsd1_log_deriv_N2048_cert`**:
  $N = 2048$ ($\sigma = 0.5000625$, $t \sim 10^{30}$),
  $D_{lo} = 2.7 \times 10^{12}$, $M_{lip} = 5.13 \times 10^8$.

---

## 3. QSD[2]: Truncated 6-Basis Ring & Associativity Defect

`QSD[2]` captures quadratic and higher-order truncation errors occurring in
finite-dimensional polynomial approximations of Dirichlet flows.

### 3.1 6-Basis Coordinate Structure (`QsdTrunc6`)

The structure `QsdTrunc6` represents elements in the 6-dimensional basis
$\{1, i, j, k, L, m\}$:

```lean
structure QsdTrunc6 where
  a : QRat  -- 1 (scalar)
  b : QRat  -- i
  c : QRat  -- j
  d : QRat  -- k
  e : QRat  -- L (split generator)
  f : QRat  -- m (nilpotent tangent)
  deriving Repr, DecidableEq
```

### 3.2 Truncated Multiplication and Associativity Defect

Multiplication `mulTrunc6` truncates high-degree interactions into lower
channels:
$$(x \cdot y)_e = x_a y_e + x_e y_a + x_b y_b$$
$$(x \cdot y)_f = x_a y_f + x_f y_a + x_e y_b$$

Theorem `qsd2_truncation_associativity_defect` constructs an explicit witness
using basis element $b = (0, 1, 0, 0, 0, 0)$ (`b_basis`):
- $(b \cdot b) \cdot b \neq b \cdot (b \cdot b)$
- Defect vector $\Delta = (b \cdot b) \cdot b - b \cdot (b \cdot b)$
  has non-zero projection on coordinate $f$:
  $$(\text{qsd2\_assoc\_defect}(b, b, b)).f = 1$$

This demonstrates constructively that truncation operations introduce
associativity curvature along the nilpotent tangent direction.

---

## 4. QSD[3]: Z2-Graded Sign Laws & Anti-Commuting Obstruction

`QSD[3]` formalizes $\mathbb{Z}_2$-graded commutation rules, demonstrating
how sign parity prevents naive commutative Euler-product rearrangement.

### 4.1 Grading and Koszul Signs

- **Inductive Type**: `Z2Grading` with constructors `even` and `odd`.
- **Koszul Sign Factor**: `Z2Grading.mulSign g1 g2` evaluates to $-1$ if and
  only if both factors are `odd`; otherwise $+1$.
- **Graded Factor**: `GradedFactor` pairs a grading `deg : Z2Grading` with an
  amplitude `val : QRat`.

### 4.2 Anti-Commutation Theorem

The graded commutation operation is defined by:
$$\text{gradedCommute}(A, B) = (-1)^{|A||B|} (A.val \cdot B.val)$$

Theorem `qsd3_anticommute_order_obstruction` proves that for any two factors
with `deg = odd` and non-zero amplitude $(A.val \cdot B.val).num \neq 0$:
$$\text{gradedCommute}(A, B) \neq A.val \cdot B.val$$

This obstruction governs fermion-like operator ordering in spectral zeta
formulations.

---

## 5. QSD[4]: Residue Rings, CRT, Nilpotent Lifts & Hensel Towers

`QSD[4]` bridges finite-ring modular arithmetic with $p$-adic Hensel towers
and nilpotent tangent lifts.

### 5.1 Residue Ring Arithmetic (`QsdModRing`)

`QsdModRing m` models $\mathbb{Z} / m\mathbb{Z}$ over `Nat`:
- Embedding: `QsdModRing.ofNat m hm x = \langle x \% m, \dots \rangle`
- Additive and Multiplicative operations: `QsdModRing.add`, `QsdModRing.mul`

### 5.2 RNS Chinese Remainder Theorem Decomposition

Theorem `qsd4_rns_channel_crt_decomposition` verifies exact channel
reconstruction across the Mersenne prime tower $(7, 31, 127)$ from
`LeanAsm.QuasiRiemann.RNS`:
- Residues: $x \equiv 3 \pmod 7$, $x \equiv 25 \pmod{31}$,
  $x \equiv 51 \pmod{127}$
- Reconstructed integer $x.reconstruct$ matches channel values precisely.

### 5.3 Nilpotent Zero-Divisor Lifting

Theorem `qsd4_nilpotent_zero_divisor_lift` proves that in
$\mathbb{Z} / m^2\mathbb{Z}$ for $m > 1$, the element $x = m$ satisfies:
- $x \not\equiv 0 \pmod{m^2}$ ($elem.val \neq 0$)
- $x^2 \equiv 0 \pmod{m^2}$ ($(elem \cdot elem).val = 0$)

This provides a discrete residue model of the dual tangent carrier $m^2 = 0$.

### 5.4 Dual Residue Rings (`QsdDualModRing`)

In `Valuation/QsdHenselTower.lean`, `QsdDualModRing m` pairs residue elements
with nilpotent tangent shifts modulo $m$:
$$(v_1 + t_1 \varepsilon)(v_2 + t_2 \varepsilon) =
v_1 v_2 + (v_1 t_2 + t_1 v_2) \varepsilon \pmod m$$

### 5.5 Hensel Tangent Lifts and Prime Towers

- **Theorem `qsd4_hensel_tangent_lift_step`**:
  For prime power step $p^k \to p^{k+1}$, a tangent lift $x_{k+1} = x + t p^k$
  satisfies $x_{k+1} \equiv x \pmod{p^k}$ while the squared tangent remainder
  vanishes modulo $p^{2k}$:
  $$(t p^k)^2 \equiv 0 \pmod{p^{2k}}$$
- **Theorem `qsd4_prime_tower_nilpotent_remainder_bound`**:
  In $\mathbb{Z} / p^{2k}\mathbb{Z}$, the carrier $m = p^k$ satisfies
  $m^2 \equiv 0 \pmod{p^{2k}}$ and $p^{2k} \mid m^2$.
- **Certificate `qsd4_hensel_tower_cert_p7`**:
  Hensel lift certificate for $x^2 \equiv 2 \pmod{7^k}$ across rungs
  $k = 1, 2, 3$:
  - Rung 1: $x_1 = 3$, $3^2 \equiv 2 \pmod 7$, $\nu_7(3^2 - 2) = 1$
  - Rung 2: $x_2 = 10 = 3 + 1 \cdot 7$, $10^2 \equiv 2 \pmod{49}$,
    $\nu_7(10^2 - 2) = 2$
  - Rung 3: $x_3 = 108 = 10 + 2 \cdot 49$, $108^2 \equiv 2 \pmod{343}$,
    $\nu_7(108^2 - 2) = 3$
- **Certificate `qsd4_hensel_tower_cert_p2`**:
  Unital idempotent lift for $p = 2$ ($x^2 \equiv x \pmod{2^k}$) with
  infinite $2$-adic valuation on the residual $1^2 - 1 = 0$.

---

## 6. Provenance Wiring and Axiomatic Hygiene

The QSD theorems are bound directly into the master provenance pipeline:

1. **`QsdAlgebraProvenanceProp`**:
   Defined in `QsdAlgebraBridge.lean`, conjoining formal claims for `QSD[1]`,
   `QSD[2]`, `QSD[3]`, and `QSD[4]`. Certified by
   `qsd_algebra_provenance_certified`.
2. **`ValuationDynamicsProvenance`**:
   Defined in `ProvenanceSummary.lean`, conjoining `QsdAlgebraProvenanceProp`
   with 2-adic Eisenstein dynamics and Romik weights. Certified by
   `valuation_dynamics_provenance_certified`.
3. **Master Synthesis**:
   Incorporated into `LeanAsm.leanasm_full_provenance_certified`.

### Axiomatic Verification

All proofs obey the strict foundational constraints of `leanasm`:
- **Mathlib Dependencies**: `0` (standalone standard library and core).
- **Axioms**: Strictly restricted to `[propext, Quot.sound]`.
- **Non-Constructive Principles**: `0` uses of `Classical.choice`.
- **Incomplete Proofs**: `0` instances of `sorryAx` / `sorry`.

Audited continuously via Parts 58 and 59 in `tests/TestAxioms.lean`.

<!-- end of file: leanasm/docs/qsd_definitions.md -->
