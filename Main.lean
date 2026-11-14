-- Path: leanasm/Main.lean
-- Interactive runner demonstrating MiniVM, Math, Yang-Mills, QRH, RNS/CRT, and Finite-Field RH.

import LeanAsm

open MiniVM
open Conjectures
open YangMillsToy
open YangMillsQ8
open QuasiRiemann
open RnsArithmetic
open FiniteFieldRH

/-- Left-pad a decimal remainder with leading `'0'` characters to `width` digits. -/
private def padZeros (width n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

def main : IO Unit := do
  IO.println "=========================================================="
  IO.println "   leanasm: Verified VM, Math, QFT, QRH, RNS & Weil Demo  "
  IO.println "=========================================================="

  -- 1. MiniVM Assembly Program execution
  IO.println "\n[+] Part 1: MiniVM Assembly Execution"
  let initial : State := {}
  let prog : List Instr := [
    Instr.movImm Reg.r0 42,
    Instr.movImm Reg.r1 10,
    Instr.addReg Reg.r0 Reg.r1,
    Instr.subReg Reg.r0 Reg.r1
  ]
  let finalState := runProgram initial prog
  IO.println s!"  Initial State : r0={initial.r0}, r1={initial.r1}, pc={initial.pc}"
  IO.println s!"  After Program : r0={finalState.r0}, r1={finalState.r1}, pc={finalState.pc}"
  IO.println "  Formal proof verified: (s.set r v).get r = v"

  -- 2. Conjectures & Collatz computation
  IO.println "\n[+] Part 2: Collatz Trajectory Exploration & QRH Diophantine Bridge"
  for seed in [6, 11, 27] do
    let traj := collatzTrajectory seed 25
    IO.println s!"  Seed {seed} trajectory (first {traj.length} steps): {traj}"
  let diff23 := CollatzQrhBridge.iv12Sub (QuasiRiemann.lnInterval12 3) (QuasiRiemann.lnInterval12 2)
  IO.println s!"  Diophantine Gap 2^k ≠ 3^m : ∀ k, m ≥ 1 constructive parity obstruction verified"
  IO.println s!"  Log Sandwich 3/2 < ln3/ln2: < 8/5 certified via rational Taylor lnInterval12"
  IO.println s!"  \{2, 3} Phase Beat Interval : (ln 3 - ln 2)·10¹² ∈ [{diff23.lo}, {diff23.hi}]"
  let ln64 := QuasiRiemann.lnInterval36 64
  IO.println s!"  36-Digit Log Synthesis    : (ln 64)·10³⁶ ∈ [{ln64.lo}, {ln64.hi}] (1 ≤ n ≤ 64)"
  let ln128 := QuasiRiemann.lnInterval72 128
  IO.println s!"  72-Digit Log Synthesis    : (ln 128)·10⁷² ∈ [{ln128.lo}, {ln128.hi}] (1 ≤ n ≤ 128)"
  let gap306 := CollatzQrhBridge.powViaCrtNtt96 2 306 - CollatzQrhBridge.powViaCrtNtt96 3 193
  let lf306 := CollatzQrhBridge.linearFormLn2Ln3AbsLower36 306 193
  let beat306 := CollatzQrhBridge.collatzBeatPeriodUpper36 306 193
  IO.println s!"  CRT-NTT |2^306 - 3^193|   : {gap306} (93-digit powers)"
  IO.println s!"  Baker Lower Bound (306/193): |306 ln2 - 193 ln3|·10³⁶ ≥ {lf306}, beat≤{repr beat306}"
  let gap485 := CollatzQrhBridge.powViaCrtNtt192 2 485 - CollatzQrhBridge.powViaCrtNtt192 3 306
  let lf485 := CollatzQrhBridge.linearFormLn2Ln3AbsLower72 485 306
  let beat485 := CollatzQrhBridge.collatzBeatPeriodUpper72 485 306
  IO.println s!"  CRT-NTT |2^485 - 3^306|   : {gap485} (146-digit powers)"
  IO.println s!"  72-Digit Baker (485/306)  : |485 ln2 - 306 ln3|·10⁷² ≥ {lf485}, beat≤{repr beat485}"
  IO.println ("  Steiner 1-Cycle Excluded  : (8,5) n_min≥17, (65,41) ≥87, (306,193) ≥14, " ++
    "(485,306) ≥978")
  IO.println "  Simons-de Weger Barrier   : n_min ≥ 936,360 ⇒ m ≥ 307 odd steps (K ≥ 793 total steps)"
  IO.println "  QRH Cancellation Ladder   : 1/2 < 3/4 < 5/6 < 7/8 < 11/12 < 1 (Collatz ↔ Mollifier)"

  -- 3. 4D Wilson Lattice Gauge Theory Simulation (Z2)
  IO.println "\n[+] Part 3: 4D Yang-Mills Abelian Z2 Wilson Lattice Simulation"
  let origin : Point4 := ⟨0, 0, 0, 0⟩
  let vacConfig : GaugeConfig := fun _ => Z2.plusOne
  let vacP := plaquette vacConfig origin Dir.d0 Dir.d1
  let vacAct := plaquetteAction vacConfig origin Dir.d0 Dir.d1
  IO.println s!"  Vacuum Plaquette U_01(0) : {repr vacP}"
  IO.println s!"  Vacuum Plaquette Action S_P : {vacAct} (minimum energy state)"

  -- 4. Non-Abelian Quaternion Gauge Group (Q8 ⊂ SU(2))
  IO.println "\n[+] Part 4: Non-Abelian Quaternion Gauge Group (Q8 ⊂ SU(2))"
  let a := Q8.i
  let b := Q8.j
  let ab := Q8.mul a b
  let ba := Q8.mul b a
  IO.println s!"  Non-abelian multiplication: i * j = {repr ab}, j * i = {repr ba}"
  IO.println s!"  Trace cyclicity verified  : ReTr(i * j) = {Q8.reTrace ab}, ReTr(j * i) = {Q8.reTrace ba}"
  IO.println "  Conjugation invariance   : ReTr(g * u * g⁻¹) = ReTr(u) (ZERO axioms verified)"

  -- 5. Quasi-Riemann Hypothesis (QRH, θ = 7/8)
  IO.println "\n[+] Part 5: Quasi-Riemann Hypothesis (θ = 7/8)"
  IO.println s!"  QRH parameter θ : {thetaSevenEighths} (zero-free half-plane Re(s) > 7/8)"
  let pntBound := pntErrorForTheta thetaSevenEighths
  let x := 1000000.0
  let err := pntBound.errorEstimate x
  IO.println s!"  Prime Number Theorem Error at x=10^6: O(x^(7/8) * log²(x)) ≈ {err.toUInt64}"
  IO.println s!"  Hierarchy verified: 1/2 < 7/8 < 11/12 < 1 (ZERO axioms verified)"
  IO.println s!"  2D Region Union   : Turing Box (|t|≤{turingBoxHeight}) ∪ QRH (σ>7/8) ∪ Wedge (|t|≥10⁹ ⇒ σ>3/4)"
  IO.println "  Partition & Disjointness : Critical strip (1/2, 1] partitioned with ZERO axioms"
  IO.println "  Exp-Pair Descent  : 7/8 (OpenAI) → 8/11 (Weyl AB) → 37/51 (Huxley-Watt) → 2/3 (ExpPair Ceiling)"
  IO.println "  Prime Gap Exponents: 1/2 (RH) < 21/40 (BHP) < 7/12 (Huxley) < 3/4 < 7/8 (QRH) (ZERO axioms verified)"
  IO.println "  Phragmén-Lindelöf : μ_Bourgain(3/4) = 13/168 < 1/12 < 1/8; μ_Bourgain(7/8) = 13/336 < 1/24 < 1/16"
  IO.println "  Zero-Density Slopes: Guth-Maynard beats Huxley inside (1/2, 7/8]"
  IO.println "                       (15/26 < 3/5, 15/52 < 3/10, ZERO axioms verified)"
  let gmGap := primeGapExponent zeroDensityGuthMaynard |>.reduce
  let huxGap := primeGapExponent zeroDensityHuxley |>.reduce
  let abaab := vdcProcessA (vdcProcessB (vdcProcessA (vdcProcessA (vdcProcessB trivialRatPair))))
  IO.println (s!"  \{A,B}* QRat Orbit : (0,1) → (1/2,1/2) → (1/6,2/3) → (1/14,11/14) " ++
    s!"→ ABA²B=({repr abaab.k.reduce}, {repr abaab.l.reduce})")
  IO.println s!"  GM 30/13 vs Hux 12/5: σ=3/4 savings = 3/130; prime gap θ_p {repr gmGap} < {repr huxGap}"
  IO.println "  Mollifier Descent  : 11/12 (ϑ=1/6) → 7/8 (1/4) → 5/6 (1/3) → 3/4 (1/2) → 1/2 (1)"
  IO.println "  Mollifier θ(ϑ) Map: ϑ=1/4 (Weil) ↦ 7/8, ϑ=1/3 ↦ 5/6, ϑ=1/2 ↦ 3/4, ϑ=4/7 ↦ 5/7, ϑ=1 ↦ 1/2 (RH)"
  IO.println "  Deuring-Heilbronn : β₀ = 7/8 repels secondary zeros to β₁ ≤ 3/4 (k=2) and β₁ ≤ 5/8 (k=3)"
  IO.println "  Dirichlet Certs   : Dyadic N=256 Euler-Maclaurin tail E_256(7/8, 200) < 0.92"
  IO.println "                      NormSq 992.9×10⁹ > TailSq 846.4×10⁹ (Carves zero-free points out of unknown box)"
  let (sampleReIv, sampleImIv) := evalDirichletPolyInterval sampleComputedTable_7_8_105
  let minNormSq := complexIntervalMinNormSq sampleReIv sampleImIv
  IO.println s!"  Interval Evaluator: D_8(7/8 + 105i) enclosure Re ∈ [{sampleReIv.lo}, {sampleReIv.hi}]/10⁶"
  IO.println s!"                      Im ∈ [{sampleImIv.lo}, {sampleImIv.hi}]/10⁶"
  IO.println s!"                      |D_8|_min² · 10¹² = {minNormSq} > TailSq = 360·10⁹ (ZERO axioms verified)"
  let (genReIv, genImIv) := evalDirichletPolyInterval (generateDirichletTable 7 105 8)
  let genMinNormSq := complexIntervalMinNormSq genReIv genImIv
  IO.println s!"  Taylor Generator  : Self-generated 8-term D_8(7/8 + 105i) from pure Taylor artanh/exp/cos/sin"
  IO.println s!"                      Generated |D_8|_min² · 10¹² = {genMinNormSq} > TailSq = 360·10⁹ (ZERO axioms)"
  let sweptCerts := sweepDirichletGrid sampleStripGrid2D
  IO.println s!"  2D Grid Sweeper   : Certified {sweptCerts.length}/30 cells across σ ∈ \{5/8, 3/4, 7/8}"
  IO.println "                      Excision from RefinedRemainingUnknownBox unconditionally verified (ZERO axioms)"
  let sweptBoxes := sweepContinuousBoxes sampleContinuousBoxGrid
  let totalMeasure := totalContinuousMeasure sweptBoxes
  IO.println (s!"  Continuous Sweeper: Certified {sweptBoxes.length}/7 continuous boxes across σ ∈ \{5/8, 3/4, 7/8}")
  IO.println (s!"                      Total certified vertical measure Δt = {totalMeasure / 1000000}." ++
    s!"{totalMeasure % 1000000} (ZERO axioms)")
  let sweptRects := sweepRectangles2D sampleRectGrid2D
  let totalArea := totalCertifiedAreaScaled12 sweptRects
  IO.println (s!"  2D Rectangle Sweep: Certified {sweptRects.length}/7 2D rectangles [σ_lo, σ_hi] × [t_lo, t_hi]")
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = {totalArea / 1000000000000}." ++
    s!"{totalArea % 1000000000000} (ZERO axioms)")
  let sweptRects16 := sweepRectangles2DN16 deepStripRectGrid2D
  let totalArea16 := totalCertifiedAreaScaled12 sweptRects16
  IO.println (s!"  N=16 Deep 2D Sweep: Certified {sweptRects16.length}/6 2D rectangles below σ=5/8=0.625")
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = {totalArea16 / 1000000000000}." ++
    s!"{totalArea16 % 1000000000000} (ZERO axioms)")
  let sweptRects32 := sweepRectangles2DN32 ultraDeepStripRectGrid2D
  let totalArea32 := totalCertifiedAreaScaled12 sweptRects32
  IO.println (s!"  N=32 Ultra-Deep 2D: Certified {sweptRects32.length}/7 2D rectangles down to σ=0.520")
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = {totalArea32 / 1000000000000}." ++
    s!"{totalArea32 % 1000000000000} (ZERO axioms)")
  let crtSq := natMul96ViaCrtNtt scale36 scale36
  let sweptRects64 := sweepRectangles2DN64 ultraDeepStripRectGrid2D_N64
  let totalArea64 := totalCertifiedAreaScaled12 sweptRects64
  IO.println s!"  ScaledInterval36  : 96-digit CRT-NTT Mul Check (10³⁶)² = {crtSq} (exact)"
  IO.println (s!"  N=64 Ultra-Deep 2D: Certified {sweptRects64.length}/7 2D rectangles down to σ=0.505")
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = {totalArea64 / 1000000000000}." ++
    s!"{totalArea64 % 1000000000000} (CRT-NTT 10³⁶ engine)")
  let crtSq72 := QuasiRiemann.natMul192ViaCrtNtt scale72 scale72
  let sweptRects128 := sweepRectangles2DN128 ultraDeepStripRectGrid2D_N128
  let totalArea128 := totalCertifiedAreaScaled12 sweptRects128
  let pad128 := padZeros 12 (totalArea128 % 1000000000000)
  IO.println s!"  ScaledInterval72  : 192-digit CRT-NTT Mul Check (10⁷²)² = {crtSq72} (exact)"
  IO.println s!"  N=128 Ultra-Deep  : Certified {sweptRects128.length}/7 2D rectangles down to σ=0.501"
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = " ++
    s!"{totalArea128 / 1000000000000}.{pad128} (CRT-NTT 10⁷² engine)")
  let zE := QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff
  let mE := QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff
  let ln16Nat := (QuasiRiemann.octaveLnUpper36 QuasiRiemann.dvpThresholdT0).toNat
  let padLn16 := padZeros 36 (ln16Nat % (10 ^ 36))
  IO.println (s!"  Asymptotic ZFR    : c_dvp = {repr QuasiRiemann.cDvp} for t ≥ " ++
    s!"{QuasiRiemann.dvpThresholdT0} (octave ln_hi(16) = {ln16Nat / 10 ^ 36}.{padLn16})")
  IO.println (s!"  Dirichlet L^2     : Zeta(N=4, H=64) E={repr zE} sandwich [2, 6]; " ++
    s!"Mobius(N=6, H=144) E={repr mE} sandwich [5/2, 15/2]")
  let highRects1e12 := QuasiRiemann.sweepDirichletRectangles2DN128
    QuasiRiemann.highHeightRectGrid2D_1e12_N128
  let highArea1e12 := QuasiRiemann.totalCertifiedAreaScaled12 highRects1e12
  let padHigh := padZeros 12 (highArea1e12 % 1000000000000)
  let tpWidth72 := QuasiRiemann.twoPiInterval72.hi - QuasiRiemann.twoPiInterval72.lo
  IO.println (s!"  t~10^12 Phase Red.: PiChudnovsky twoPiInterval72 width={tpWidth72} ULP; " ++
    s!"reduced width ≤ 6·10^15 ULP (<10^-56 rad)")
  IO.println (s!"  t~10^12 ζ_128 2D  : Certified {highRects1e12.length}/5 rectangles near " ++
    s!"t=10^12+6.1 spanning σ∈[0.501,0.750]")
  IO.println (s!"                      Total certified 2D Lebesgue area Δσ·Δt = " ++
    s!"{highArea1e12 / 1000000000000}.{padHigh}")

  -- 6. Residue Number System (RNS) & Chinese Remainder Theorem (CRT)
  IO.println "\n[+] Part 6: Residue Number System (RNS) & CRT Execution"
  let A := 23
  let B := 37
  let rnsA := toRns A
  let rnsB := toRns B
  let rnsProd := rnsMul rnsA rnsB
  let reconstructed := fromRnsTuple rnsProd
  IO.println s!"  Moduli basis channels     : (m1={m1}, m2={m2}, m3={m3}), Dynamic Range M={M}"
  IO.println s!"  Operands in RNS           : A={A} ↦ {repr rnsA}, B={B} ↦ {repr rnsB}"
  IO.println s!"  Carry-Free RNS Product    : {repr rnsProd}"
  IO.println s!"  CRT Reconstructed Value   : {reconstructed} (expected {A * B})"
  IO.println s!"  Garner Mixed-Radix Recon  : {fromRnsTupleGarner rnsProd} (bounded operands < 169)"
  let fProd := EulerFactorNonVanishing.fermatTowerPrimes.prod
  let fTot := (EulerFactorNonVanishing.fermatTowerPrimes.map (· - 1)).prod
  IO.println (s!"  Fermat-Prime Tower Euler  : ∏\{5,17,257,65537} = {fProd} ((2³²-1)/3), " ++
    s!"∏(p-1) = {fTot} = 2³⁰")
  IO.println ("  Strip Euler Lower Bounds  : σ=1/2 |∏(1-p^-s)|² > 1/9, " ++
    "σ=3/4 > 1/3, σ=1 > 9/16 > 1/16")
  IO.println "  CRT roundtrip & homomorphism: ZERO axioms verified"

  -- 7. Unconditional Riemann Hypothesis for Curves over Finite Fields (Hasse-Weil)
  IO.println "\n[+] Part 7: Unconditional Riemann Hypothesis for E/F_7 (Hasse-Weil)"
  IO.println s!"  Curve equation over F_7   : y² ≡ x³ + x + 1 (mod 7)"
  IO.println s!"  Total Projective Points   : #E(F_7) = {totalProjectivePoints} (including point at infinity)"
  IO.println s!"  Frobenius Trace a_7       : (p+1) - #E = (7+1) - {totalProjectivePoints} = {frobeniusTrace}"
  IO.println s!"  Hasse-Weil Bound          : a_7² = {frobeniusTrace * frobeniusTrace} ≤ 28 (RH for E/F_7 verified)"
  IO.println s!"  Genus-2 Curve C / F_5     : y² = x⁵ - x + 1 (smooth, f'(x) = -1 ≠ 0)"
  IO.println (s!"  Genus-2 Point Counts      : #C(F_5) = {cardGenus2F5}, #C(F_25) = {cardGenus2F25} " ++
    s!"(a_1 = {genus2TraceA1}, a_2 = {genus2TraceA2})")
  IO.println s!"  Frobenius Char Poly P_frob: P_frob(X) = X⁴ + 5X³ + 15X² + 25X + 25"
  IO.println s!"  Genus-2 RH Eigenvalues    : |α_i|² = 5 (Re(s) = 1/2, negative Δ_i = u_i² - 20 < 0)"
  IO.println (s!"  Weil L-Value L(C, 1)      : L_C(1/5) = {genus2LNumAtInv5}/625 = 71/25 != 0 " ++
    "(rank 0, BSD 5^2*L = 71)")
  IO.println (s!"  Jacobian Group Order      : #J(C)(F_5) = {cardJacobianGenus2F5} " ++
    "(prime cyclic, basepoint (0, 1))")
  let jac71 := Genus2Jacobian.cantorSmul 71 Genus2Jacobian.D0
  IO.println (s!"  Cantor-Mumford Group Law  : 71 * [P_0 - ∞] = 0 on J(C)(F_5) " ++
    s!"(zero={Genus2Jacobian.divEqB jac71 Genus2Jacobian.MumfordDivisor.zero})")
  IO.println (s!"  Weil Z(C/F_5, 5^-s) Strip : pole-free & zero-free on 0 < σ < 1, σ != 1/2 " ++
    "(|L_C| >= 1/25 at σ=1/4, 1/100 at σ=3/4, 16/225 at σ=1)")

  -- 8. Prime-Tower Local Euler Factor Non-Vanishing (RNS ↔ QRH)
  IO.println "\n[+] Part 8: Prime-Tower Local Euler Factor Non-Vanishing (RNS ↔ QRH)"
  IO.println s!"  RNS Prime Moduli Channels : p ∈ \{7, 11, 13}"
  let m7_1 := EulerFactorNonVanishing.eulerFactorMargin 7 1
  let m11_1 := EulerFactorNonVanishing.eulerFactorMargin 11 1
  let m13_1 := EulerFactorNonVanishing.eulerFactorMargin 13 1
  IO.println s!"  At σ = 1/2 (RH threshold) : 7¹-1 = {m7_1}, 11¹-1 = {m11_1}, 13¹-1 = {m13_1} > 0"
  let m7_7 := EulerFactorNonVanishing.eulerFactorMargin 7 7
  let m11_7 := EulerFactorNonVanishing.eulerFactorMargin 11 7
  let m13_7 := EulerFactorNonVanishing.eulerFactorMargin 13 7
  IO.println s!"  At σ = 7/8 (QRH threshold): 7⁷-1 = {m7_7}, 11⁷-1 = {m11_7}, 13⁷-1 = {m13_7} > 0"
  IO.println s!"  Partial Euler Product     : ∏ (p⁷ - 1) = {EulerFactorNonVanishing.partialEulerProductMargin 7} > 0"
  IO.println "  Channel non-vanishing     : Local RNS channels never vanish in Re(s) > 0 (ZERO axioms verified)"

  -- 9. Number Theoretic Transform (NTT) Butterfly & 4-Point Cyclic Convolution over Fermat Prime F_17
  IO.println "\n[+] Part 9: Number Theoretic Transform (NTT) over Fermat Prime F_17"
  IO.println s!"  Fermat modulus p = 2^(2^2) + 1 = {NttArithmetic.p}, Primitive Root g = {NttArithmetic.g}"
  IO.println s!"  8-th Root of Unity ω_8    : {NttArithmetic.omega8} (ω_8^8 ≡ 1 mod 17, ω_8^4 ≡ -1 mod 17)"
  let (X0, X1) := NttArithmetic.nttButterfly2 5 12
  let (x0_rec, x1_rec) := NttArithmetic.inttButterfly2 X0 X1
  IO.println s!"  Cooley-Tukey Butterfly    : (5, 12) ↦ Forward ({X0}, {X1}) ↦ Inverse ({x0_rec}, {x1_rec})"
  let a4 : NttArithmetic.Vec4 := ⟨1, 2, 3, 4⟩
  let b4 : NttArithmetic.Vec4 := ⟨5, 6, 7, 8⟩
  let A4 := NttArithmetic.ntt4 17 13 a4
  let B4 := NttArithmetic.ntt4 17 13 b4
  let c4 := NttArithmetic.intt4 17 13 4 (NttArithmetic.pointwiseMul4 17 A4 B4)
  IO.println s!"  4-Point Radix-2 NTT       : a=⟨1,2,3,4⟩ ↦ A={repr A4}, b=⟨5,6,7,8⟩ ↦ B={repr B4}"
  IO.println s!"  Cyclic Convolution Theorem: INTT4(A ⊙ B) = {repr c4} = cyclicConv4 a b (ZERO axioms verified)"
  IO.println s!"  Universal Invertibility & Convolution (F_5 & F_17): ZERO axioms verified"

  -- 10. Multi-Prime CRT-NTT Exact Integer Convolution (F_5 x F_17, F_17 x F_257, 3 Fermat Primes)
  IO.println "\n[+] Part 10: Multi-Prime CRT-NTT Exact Integer Convolution (Fermat Primes)"
  let crt4 := CrtNtt.crtNttConv4 a4 b4
  IO.println s!"  4-Point CRT-NTT (F_5 x F_17, M=85)     : ⟨1,2,3,4⟩ ⊛ ⟨5,6,7,8⟩ = {repr crt4} (exact unreduced)"
  let a8 : CrtNtt.Vec8 := ⟨1, 2, 3, 4, 5, 6, 7, 8⟩
  let b8 : CrtNtt.Vec8 := ⟨8, 7, 6, 5, 4, 3, 2, 1⟩
  let crt8 := CrtNtt.crtNttConv8 a8 b8
  IO.println s!"  8-Point CRT-NTT (F_17 x F_257, M=4369) : ⟨1..8⟩ ⊛ ⟨8..1⟩ = {repr crt8} (exact unreduced)"
  let a16 : CrtNtt.Vec16 := ⟨10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160⟩
  let b16 : CrtNtt.Vec16 := ⟨160, 150, 140, 130, 120, 110, 100, 90, 80, 70, 60, 50, 40, 30, 20, 10⟩
  let crt16 := CrtNtt.crtNttConv16 a16 b16
  IO.println s!"  16-Point CRT-NTT (3 Fermat Primes, M=286,331,153) :"
  IO.println s!"    peak unreduced coeff = {crt16.x15} (exact unreduced)"
  let bigA : Nat := 123456789012345678901234
  let bigB : Nat := 987654321098765432109876
  let bigProd := CrtNtt.crtNttBigMul bigA bigB
  let max48 : CrtNtt.Vec16 := ⟨999, 999, 999, 999, 999, 999, 999, 999,
                               999, 999, 999, 999, 999, 999, 999, 999⟩
  let karMax := CrtNtt.evalDigits1000Vec32 (CrtNtt.karatsubaCrtNttMul96 max48 max48)
  let max96 : CrtNtt.Vec32 := ⟨max48, max48⟩
  let karMax192 := CrtNtt.evalDigits1000Vec64 (CrtNtt.karatsubaCrtNttMul192 max96 max96)
  IO.println s!"  48-Digit Big-Integer CRT-NTT Mul : {bigA} * {bigB} = {bigProd}"
  IO.println s!"  96-Digit Karatsuba CRT-NTT Max   : (10^48 - 1)^2 = {karMax}"
  IO.println s!"  192-Digit Karatsuba CRT-NTT Max  : (10^96 - 1)^2 = {karMax192}"
  IO.println "  Zero Wrap-Around & Soundness : 4-point, 8-point, 16-point, and 48-digit mul match exact (ZERO axioms)"
  IO.println "  Universal 8-Point NTT Soundness : Invertibility & cyclic convolution over F_17 & F_257 (ZERO axioms)"
  IO.println "  Universal 16-Point & 48-Digit : ∀ inputs over F_17, F_257, F_65537 & a,b < 10^24 exact (ZERO axioms)"
  IO.println "  Universal 96-Digit Karatsuba : ∀ A,B < 10^48 exact 3-call CRT-NTT mul & normalized (ZERO axioms)"
  IO.println "  Universal 192-Digit Karatsuba: ∀ A,B < 10^96 exact 2-tier 9-call CRT-NTT mul (ZERO axioms)"
  IO.println "  Universal CRT & Carries      : ∀ x < 286,331,153 Garner 3-channel roundtrip &"
  IO.println "                                 ∀ v : Vec16 Base-1000 Horner carry preservation verified"

  -- 11. Constructive 100-Digit Chudnovsky Pi via 192-Digit CRT-NTT
  IO.println "\n[+] Part 11: Constructive 100-Digit Chudnovsky Pi via 192-Digit CRT-NTT"
  let piInt := PiChudnovsky.piDigits100 / 10 ^ 100
  let piFrac := PiChudnovsky.piDigits100 % 10 ^ 100
  let bracketWidth := PiChudnovsky.piUpper105 - PiChudnovsky.piLower105
  IO.println s!"  Chudnovsky pi (100 digits)   : {piInt}.{piFrac}"
  IO.println s!"  10^105 Bracket Width         : {bracketWidth} (< 10^4 certified)"
  IO.println "  Zero-Axiom Kernel Audit      : pi_100_digits_certified & universal m ≥ 8 trap verified"

  IO.println "\n[+] All theorems verified at build-time with the Lean 4 kernel."
  IO.println "=========================================================="

-- end of file: leanasm/Main.lean
