Commit `e4ce5ea` brings both the inductive `{A, B}*` van der Corput word engine (`QuasiRiemann.lean`) and the 4-point radix-2 Cooley–Tukey NTT + cyclic convolution theorem (`NttArithmetic.lean`) cleanly into the zero-axiom suite (`TestAxioms.lean`), with full binary integration in `Main.lean`.

---

### 1. Where `leanasm` Stands After `e4ce5ea`

Your repository now spans nine self-contained, zero-axiom verified modules (`MiniVM`, `Collatz`, `YangMillsToy`, `YangMillsQ8`, `QuasiRiemann`, `RnsArithmetic`, `FiniteFieldRH`, `EulerFactorNonVanishing`, and `NttArithmetic`), establishing three verified computational bridges:

1. **Analytic Number Theory (`QuasiRiemann` + `EulerFactorNonVanishing`):** Connects OpenAI Family `003`'s uniform $\theta = 7/8$ QRH half-plane to the 2D $(\sigma, t)$ critical-strip dichotomy, the inductive van der Corput $\{A, B\}^*$ orbit generator ($AAB(0, 1) = (1/14, 11/14) \implies \theta = 19/26 < 7/8$), and arbitrary prime-tower Euler product non-vanishing.
2. **Hardware-Bounded Residue & Transform Arithmetic (`RnsArithmetic` + `NttArithmetic`):** Combines word-bounded Garner mixed-radix CRT reconstruction (`< 25 < 169` intermediate bounds) over `(7, 11, 13)` with radix-2 Cooley–Tukey NTT cyclic convolution over the Fermat prime $\mathbb{F}_{17}$ (`⟨1, 2, 3, 4⟩ ⊛ ⟨5, 6, 7, 8⟩ = ⟨15, 0, 15, 9⟩`).
3. **Verified VM Execution (`MiniVM`):** Compiles multi-instruction assembly sequences (`garnerCrtProgram`) with machine-checked register and program-counter invariants.

---

### 2. Three High-Leverage Next Milestones for `leanasm`

With both the 4-point NTT and the RNS/Garner CRT pipelines proven independently with zero axioms, the cleanest next step is unifying them—either by compiling the NTT butterfly onto `MiniVM` or combining RNS + NTT into a multi-prime **CRT-NTT** polynomial multiplier:

1. **Compile the $\mathbb{F}_{17}$ Radix-2 NTT Butterfly onto `MiniVM` Assembly (`MiniVM.lean` + `NttArithmetic.lean`):**
Write an explicit `MiniVM` assembly sequence (`nttButterfly2Program`) using your existing `addReg`, `addImm`, `subReg`, `modImm`, and `mulModReg` instructions to execute both the forward 2-point NTT butterfly and inverse butterfly (`2⁻¹ ≡ 9 (mod 17)`) directly in `MiniVM` registers, and prove end-to-end execution soundness (`exec_ntt_butterfly2_sound`) with zero axioms.
2. **Multi-Prime CRT-NTT Polynomial Convolution (`CrtNtt.lean`):**
Combine your RNS/Garner CRT engine with NTT arithmetic across two small NTT-friendly primes that both admit 4th roots of unity—specifically $p_1 = 5$ ($4 \mid 5 - 1$, principal 4th root $\omega_4 = 2 \pmod 5$) and $p_2 = 17$ ($4 \mid 17 - 1$, principal 4th root $\omega_4 = 13 \pmod{17}$), giving dynamic range $M = 5 \times 17 = 85$—to perform exact integer cyclic convolution of `⟨1, 2, 3, 4⟩ ⊛ ⟨5, 6, 7, 8⟩ = ⟨66, 68, 66, 60⟩` without single-prime wrap-around!
3. **Universal Algebraic Upgrade for `ntt4` (`ntt4_roundtrip_all` & `ntt4_cyclic_convolution_all`):**
Upgrade the concrete `(1, 2, 3, 4)` checks in `NttArithmetic.lean` to universal proofs over all `v : Vec4` (`intt4 (ntt4 v) = normVec4 v`) and all pairs `a b : Vec4` (`intt4 (pointwiseMul4 (ntt4 a) (ntt4 b)) = cyclicConv4 a b`) using `Fin 17` / modular ring algebra with zero axioms.
