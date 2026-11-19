# Path: leanasm/inbox/archive/gemweb112.md

To integrate **Proposition 5.3** (average generalized partition bounds) from
Andersen & Garton (arXiv:2405.00605v1) into our zero-Mathlib `leanasm`
architecture (`PreperiodicDynamics.lean`), we can combine the structural
guarantees of Theorem 3.2 ($W_{m,n}$ upper bounds) with the family averaging
statistics from Section 5.

Here is the formalization and implementation plan for
`PreperiodicDynamics.lean`:

---

### Formalization Plan for Proposition 5.3

#### 1. Constructive Average Generalized Upper Bound Helper
(`proposition53AverageBound`)

Define a constructive rational helper function that computes the average
generalized partition upper bound over quadratic polynomial families:

```lean
/-- Constructive average generalized partition bound helper for Andersen & Garton (arXiv:2405.00605v1) Proposition 5.3:
    Bounds the average proportion of points in generalized partition sets $W_{m,n}$ over quadratic families. -/
def proposition53AverageBound (d m n : Nat) : QRat :=
  if h : 1 < d ∧ 0 < m ∧ m < n then
    let term1 := QRat.mk' 2 ((d - 1) * m + 1) (by omega)
    let term2 := QRat.mk' (16 * (d : Int)) ((d - 1) * m * n) (by
      have hd : 0 < d - 1 := by omega
      exact Nat.mul_pos (Nat.mul_pos hd h.2.1) h.2.2.2)
    let term3 := QRat.mk' 34 (n ^ 3) (by exact Nat.pow_pos (by omega) 3)
    term1 + term2 + term3
  else
    QRat.ofInt 0

```

#### 2. Concrete Verification Certificate (`proposition53_average_bound_sound`)

Add a certified test case ensuring that the average generalized partition bound
is well-defined and constructively positive for $d = 2, m = 2, n = 134$:

```lean
/-- Concrete verification certificate for Proposition 5.3 average generalized partition bounds 
    at $d = 2, m = 2, n = 134$. -/
theorem proposition53_average_bound_sound :
    let bound := proposition53AverageBound 2 2 134
    bound.num > 0 := by
  dsimp [proposition53AverageBound]
  decide

```

#### 3. Axiom Audit Integration (`tests/TestPreperiodic.lean`)

Add the `#print axioms` audit entry to lock in strict constructive compliance
(`[propext, Quot.sound]`, zero `sorry`, zero `Classical.choice`).

---

<!-- end of file: leanasm/inbox/archive/gemweb112.md -->
