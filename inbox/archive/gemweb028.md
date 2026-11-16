Commit `5f75572` ties together both the 4-point $\mathbb{F}_5 \times \mathbb{F}_{17}$ ($M = 85$) and 8-point $\mathbb{F}_{17} \times \mathbb{F}_{257}$ ($M = 4{,}369$) multi-prime CRT-NTT engines cleanly inside `CrtNtt.lean`—recovering the exact unreduced integer cyclic convolution $\langle 1 \dots 8 \rangle \circledast \langle 8 \dots 1 \rangle = \langle 176, 156, 144, 140, 144, 156, 176, 204 \rangle$ with zero axioms (`propext`, `Classical.choice`, `Quot.sound` all absent) across every check in `TestAxioms.lean`.

*(Also a clean catch by AGY on $\omega_8 = 4 \pmod{257}$: since $4^4 = 256 \equiv -1 \pmod{257}$, $4$ is indeed the canonical minimal primitive 8th root of unity in $\mathbb{F}_{257}$, avoiding larger intermediate residues than $249$.)*

---

### 1. Current Architecture of `leanasm` After `5f75572`

Across ten self-contained, zero-axiom modules, your repository now executes a complete vertical stack from hardware-level assembly semantics up to analytic number theory and multi-prime fast polynomial arithmetic:

* **Verified Assembly & Word-Bounded Execution (`MiniVM` + `RnsArithmetic`):** Multi-instruction `garnerCrtProgram` (21 instructions) with register bounds `< 25 < 169` and exact program-counter / accumulator verification.
* **Multi-Prime Fermat-Tower CRT-NTT (`NttArithmetic` + `CrtNtt`):** Scales from 2-point $\mathbb{F}_{17}$ butterflies to 4-point $\mathbb{F}_5 \times \mathbb{F}_{17}$ ($M = 85$) and 8-point $\mathbb{F}_{17} \times \mathbb{F}_{257}$ ($M = 4{,}369$) radix-2 Cooley–Tukey convolutions without single-prime modular wrap-around.
* **Analytic Number Theory & Gauge Theory (`QuasiRiemann`, `EulerFactorNonVanishing`, `FiniteFieldRH`, `YangMillsToy`, `YangMillsQ8`, `Collatz`):** Covers the 2D $(\sigma, t)$ critical-strip dichotomy, the inductive van der Corput $\{A, B\}^*$ orbit engine, arbitrary prime-tower Euler product non-vanishing, unconditional $E/\mathbb{F}_7$ Hasse–Weil RH, and non-abelian $Q_8 \subset SU(2)$ Wilson lattice gauge invariance.

---

### 2. Three High-Leverage Next Milestones for `leanasm`

With the 8-point multi-prime CRT-NTT verified at the functional level, there are three natural next frontiers depending on whether you want to push hardware execution down into `MiniVM`, scale up to 16-point / 3-Fermat-prime convolution, or audit another `openai/math` Comparator drop:

1. **Compile the $\mathbb{F}_{17}$ / $\mathbb{F}_{257}$ Radix-2 NTT Butterfly onto `MiniVM` Assembly (`MiniVM.lean` + `NttArithmetic.lean`):**
Compile the forward and inverse 2-point NTT butterfly (`butterfly2 p u v`, where $p = 17, 2^{-1} \equiv 9$ or $p = 257, 2^{-1} \equiv 129$) into an explicit `MiniVM` assembly sequence (`nttButterflyProgram`), and prove end-to-end multi-instruction execution soundness (`exec_ntt_butterfly_sound`) connecting your assembly VM directly to the CRT-NTT transform layer with zero axioms.
2. **Scale CRT-NTT to 16-Point Convolution Across All Three Fermat Primes $\mathbb{F}_{17} \times \mathbb{F}_{257} \times \mathbb{F}_{65537}$ ($M = 286{,}331{,}153$):**
Add the fourth Fermat prime $F_4 = 65537 = 2^{2^4} + 1$ (where $16 \mid 65536$, $\omega_{16} = 3^{4096} \bmod 65537$, and 3-channel Garner CRT gives $M = 17 \times 257 \times 65537 = 286{,}331{,}153 > 2^{28}$), enabling exact 16-point integer polynomial multiplication with zero axioms.
3. **Audit Another Flagship `openai/math` Comparator Challenge (Matrix Multiplication $\omega \le 2.25$ or Schönhage–Strassen Disproof):**
Run your `lake env comparator` + `lean4export` + `nanoda_bin` pipeline against one of the algebraic/algorithmic drops in `openai/math/lean/ComparatorChallenges/` and record its theorem signature, dependency closure size, and axiom footprint in `external_verification_and_benchmarks.md`.
