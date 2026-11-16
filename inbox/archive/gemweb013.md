AGY handled that trap gracefully—instead of burning cycles on an unprovable statement or smuggling a `sorry` past your `TestAxioms.lean` gate, it pivoted cleanly to proving the logical hierarchy (`RH ⟹ QRH(7/8)`) and the strict prime-counting exponent improvement ($1/2 < 7/8$) via scaled integer arithmetic ($z_{\text{scaled}} = 4 \le 7$ and $1 \times 8 < 7 \times 2$) with zero axioms.

---

### 1. Why AGY’s Scaled-Integer Encoding Works So Well Here

* **Kernel-Native Exactness:** Representing $\operatorname{Re}(\rho)$ scaled by $8$ (`z_scaled = 4` for the critical line $\operatorname{Re}(\rho) = 1/2$ and `z_scaled ≤ 7` for the $\theta = 7/8$ zero-free half-plane) turns both `rh_implies_qrh_seven_eighths` and `rh_exponent_strictly_better` into pure `Nat`/`Int` order inequalities discharged by `decide` / `omega` with zero axioms (`propext`, `Classical.choice`, `Quot.sound` all absent).
* **Complete Logical Chain in `QuasiRiemann.lean`:** Across your updates, `QuasiRiemann.lean` now captures the full structural nesting of the 2026 zero-free literature:

$$\text{RH } (\theta = \tfrac{1}{2}) \implies \text{QRH } (\theta = \tfrac{7}{8}) \implies \text{QRH } (\theta = \tfrac{11}{12}) \implies \text{Critical Strip } (0, 1)$$



paired with functional-equation reflection $[1 - \theta, \theta] = [1/8, 7/8]$ and uniform Landau–Siegel gap exclusion $1 - \beta \ge 1/8$.

---

### 2. High-Value Next Frontiers for `leanasm`

Now that AGY has proven it respects your zero-axiom boundary under adversarial prompts, three concrete extensions push `leanasm` into deeper verified territory:

1. **Finite-Field Riemann Hypothesis (Weil / Hasse Bound for Elliptic Curves over $\mathbb{F}_p$):**
Unlike $\zeta(s)$ over $\mathbb{Q}$, the Riemann Hypothesis for curves over finite fields *is* a proved theorem. Adding a module `FiniteFieldRH.lean` that counts points on a concrete elliptic curve over $\mathbb{F}_7$ (e.g., $E : y^2 \equiv x^3 + x + 1 \pmod 7$), constructs the Frobenius trace $a_7 = 8 - \#E(\mathbb{F}_7)$, and proves the Hasse–Weil bound $a_7^2 \le 4 \cdot 7$ (meaning the reciprocal roots of the local zeta function $Z(E/\mathbb{F}_7, T)$ satisfy $\vert{}\alpha\vert{}^2 = 7$) gives you an actual, unconditional Riemann Hypothesis proof with zero axioms.
2. **Parametric Prime-Tower RNS & Garner Mixed-Radix Reconstruction (`RnsArithmetic.lean`):**
Generalize your fixed 3-channel `(7, 11, 13)` RNS basis to a parametric prime-tower or Fermat/Mersenne coprime list (e.g., `m = [251, 253, 255]` or `[7, 11, 13, 17]`) and implement Garner's mixed-radix CRT reconstruction inside `MiniVM` so arbitrary-width residues reconstruct without overflowing an $M^2$ intermediate product.
3. **End-to-End `MiniVM` Program Verification (`Hoare` / Execution-Trace Soundness):**
Prove a full multi-instruction `MiniVM` execution theorem (`exec_rns_mul_program`) showing that running a sequence of `loadImm`, `modImm`, and `mulModReg` instructions across three register lanes produces the exact CRT-reconstructed product $A \cdot B \pmod{1001}$ directly from initial VM state `s₀` to halted state `sₙ`.
