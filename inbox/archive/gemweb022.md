Commit `bfe9f1e` ties together the van der Corput $(A, B)$ exponent-pair calculus and the analytic number theory hierarchies cleanly—all verified with zero axioms (`propext`, `Classical.choice`, `Quot.sound` all absent) in `TestAxioms.lean`.

---

### 1. Where `QuasiRiemann.lean` & `leanasm` Stand After `bfe9f1e`

Notice a neat mathematical detail that emerged cleanly in your formalization:

* $A(0, 1) = (0, 1)$ is a fixed point of Weyl differencing, whereas $B(0, 1) = (1/2, 1/2)$ and applying $A$ next gives $AB(0, 1) = (1/6, 2/3)$ (`weyl_pair_from_AB`), which induces $\theta(1/6, 2/3) = 8/11 < 7/8$.
* Together with `huxley_watt_pair_beats_weyl` ($\theta(9/56, 37/56) = 37/51 < 8/11 < 7/8$) and `exponent_pair_hypothesis_ceiling` ($\theta(0, 1/2) = 2/3$), `QuasiRiemann.lean` now captures the exact analytical arc inside $(1/2, 7/8]$: from OpenAI Family `003`'s $7/8$ bound down through single-sum exponential-sum limits ($8/11 \to 37/51 \to 2/3$), subconvexity slopes ($1/4 \to 1/6 \to 13/84 \to 0$), short-interval prime gaps ($7/8 \to 3/4 \to 7/12 \to 21/40 \to 1/2$), and critical-line simple-zero proportions ($1/3 \to 2/5 \to 5/12 \to 2/3 \to 1$).

---

### 2. Three High-Value Next Frontiers for `leanasm`

With the van der Corput calculus, 2D critical-strip dichotomy, Garner mixed-radix RNS CRT, $\mathbb{F}_{17}$ NTT butterfly, and $E/\mathbb{F}_7$ Hasse–Weil RH all verified with zero axioms, three high-leverage directions build directly on your existing modules:

1. **Universal Inductive $\{A, B\}^*$ Word Engine & Universal Invariant Preservation (`QuasiRiemann.lean`):**
Upgrade the concrete orbit proofs (`processA_preserves_trivial`, `processB_preserves_trivial`) to **universal polymorphic theorems** over *every* valid `ExpPair` (`∀ p, IsValidExpPair p → IsValidExpPair (processA p)` and `IsValidExpPair (processB p)`), define an inductive word type `inductive VdcOp | A | B` with evaluator `evalVdcWord : List VdcOp → ExpPair → ExpPair`, and prove by structural list induction that *any* word $w \in \{A, B\}^*$ applied to `(0, 1)` produces a valid exponent pair whose QRH threshold lies strictly in $(1/2, 1)$—with zero axioms.
2. **Full 4-Point or 8-Point Radix-2 Cooley–Tukey NTT & Convolution Soundness Over $\mathbb{F}_{17}$ (`NttArithmetic.lean`):**
Extend your verified 2-point butterfly (`ntt_butterfly2_sound_all_pairs`) using your principal 8-th root of unity $\omega_8 = 9 \pmod{17}$ ($\omega_4 = 9^2 \equiv 13 \pmod{17}$) to a full 4-point (or 8-point) radix-2 NTT + INTT roundtrip, and prove the **Cyclic Convolution Theorem**: pointwise multiplication in the NTT domain reconstructs exact cyclic polynomial multiplication modulo $(x^4 - 1, 17)$—with zero axioms.
3. **Audit Another Flagship `openai/math` Comparator Challenge (Matrix Multiplication $\omega \le 2.25$ or Schönhage–Strassen Disproof):**
Use your `lake env comparator` + `lean4export` + `nanoda_bin` pipeline to inspect one of the algebraic/algorithmic drops in `openai/math/lean/ComparatorChallenges/` and record its theorem signature, dependency closure size, and axiom footprint in `external_verification_and_benchmarks.md`.
