-- Path: leanasm/src/LeanAsm/ProvenanceSummary.lean
-- Top-level zero-axiom synthesis tying together headline theorems across all 11 CLI parts.
-- Max Column: 120 Columns

import LeanAsm.MiniVM
import LeanAsm.MiniVMNttBridge
import LeanAsm.Conjectures
import LeanAsm.YangMillsToy
import LeanAsm.YangMillsQ8
import LeanAsm.QuasiRiemann
import LeanAsm.QuasiRiemann.UltraDeep72
import LeanAsm.QuasiRiemann.AsymptoticZfr
import LeanAsm.QuasiRiemann.AsymptoticZfrBridge
import LeanAsm.QuasiRiemann.ZeroDensityBridge
import LeanAsm.QuasiRiemann.ShortIntervalPrimes
import LeanAsm.RnsArithmetic
import LeanAsm.FiniteFieldRH
import LeanAsm.Genus2Jacobian
import LeanAsm.EulerFactorNonVanishing
import LeanAsm.WeilZetaBridge
import LeanAsm.NttArithmetic
import LeanAsm.CrtNtt
import LeanAsm.CrtNttUniversal
import LeanAsm.CollatzQrhBridge
import LeanAsm.PiChudnovsky.CrtMulBridge
import LeanAsm.PiChudnovsky
import LeanAsm.GSp4FunctorialityBridge

namespace LeanAsm

-- =============================================================================
-- Part 1: MiniVM Assembly & Parametric Fermat-Tower NTT/Garner CRT Provenance
-- =============================================================================

/-- Part 1 provenance specification bundling `MiniVM` Garner CRT execution,
2-point (`289` states) and 4-point (`83,521` states) `F_17` NTT/INTT assembly
soundness, parametric 4-prime `{5, 17, 257, 65537}` NTT/INTT assembly
roundtrips, compiled 4-channel Garner CRT reconstruction (`M_4 = 1,431,655,765`),
and end-to-end 4-point CRT-NTT cyclic convolution assembly soundness. -/
def MiniVmProvenance : Prop :=
  (let sInit : MiniVM.State := { r0 := 0, r1 := 4, r2 := 4, r3 := 6, pc := 0 }
   let sFinal := MiniVM.runProgram sInit MiniVM.garnerCrtProgram
   sFinal.r0 = 851 ∧ sFinal.pc = 21) ∧
  (∀ (s : MiniVM.State) (a b : Nat),
    a < NttArithmetic.p → b < NttArithmetic.p →
    s.r0 = a → s.r1 = b →
    let s' := MiniVM.runProgram s MiniVMNttBridge.ntt2AsmF17
    (s'.r0, s'.r1) = NttArithmetic.nttButterfly2 a b NttArithmetic.p) ∧
  (∀ (s : MiniVM.State) (a b : Nat),
    a < NttArithmetic.p → b < NttArithmetic.p →
    s.r0 = a → s.r1 = b →
    let s1 := MiniVM.runProgram s MiniVMNttBridge.ntt2AsmF17
    let s2 := MiniVM.runProgram s1 MiniVMNttBridge.intt2AsmF17
    (s2.r0, s2.r1) = (a, b)) ∧
  (∀ (s : MiniVM.State) (a b c d : Nat),
    a < NttArithmetic.p → b < NttArithmetic.p →
    c < NttArithmetic.p → d < NttArithmetic.p →
    s.r0 = a → s.r1 = b → s.r2 = c → s.r3 = d →
    let s' := MiniVM.runProgram s MiniVMNttBridge.ntt4AsmF17
    (⟨s'.r0, s'.r1, s'.r2, s'.r3⟩ : NttArithmetic.Vec4) =
      NttArithmetic.ntt4 NttArithmetic.p NttArithmetic.omega4 ⟨a, b, c, d⟩) ∧
  (∀ (s : MiniVM.State) (a b c d : Nat),
    a < NttArithmetic.p → b < NttArithmetic.p →
    c < NttArithmetic.p → d < NttArithmetic.p →
    s.r0 = a → s.r1 = b → s.r2 = c → s.r3 = d →
    let s1 := MiniVM.runProgram s MiniVMNttBridge.ntt4AsmF17
    let s2 := MiniVM.runProgram s1 MiniVMNttBridge.intt4AsmF17
    (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : NttArithmetic.Vec4) = ⟨a, b, c, d⟩) ∧
  (∀ cfg ∈ MiniVMNttBridge.fermatTowerNtt4Specs, cfg.Valid) ∧
  (∀ cfg ∈ MiniVMNttBridge.fermatTowerNtt4Specs,
    ∀ (s : MiniVM.State) (a b c d : Nat),
      a < cfg.p → b < cfg.p → c < cfg.p → d < cfg.p →
      s.r0 = a → s.r1 = b → s.r2 = c → s.r3 = d →
      let s1 := MiniVM.runProgram s (MiniVMNttBridge.ntt4AsmFermat cfg.p cfg.omega4)
      let s2 := MiniVM.runProgram s1
        (MiniVMNttBridge.intt4AsmFermat cfg.p cfg.invFour cfg.invOmega4)
      (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : NttArithmetic.Vec4) = ⟨a, b, c, d⟩) ∧
  (∀ (s : MiniVM.State) (x : Nat),
    x < CrtNtt.fermatTowerMod4 →
    s.r0 = x % 5 → s.r1 = x % 17 → s.r2 = x % 257 → s.r3 = x % 65537 →
    (MiniVM.runProgram s MiniVMNttBridge.garnerReconstruct4Asm).r0 = x) ∧
  (∀ (a b : NttArithmetic.Vec4),
    a.x0 ≤ 18918 → a.x1 ≤ 18918 → a.x2 ≤ 18918 → a.x3 ≤ 18918 →
    b.x0 ≤ 18918 → b.x1 ≤ 18918 → b.x2 ≤ 18918 → b.x3 ≤ 18918 →
    let c := MiniVMNttBridge.crtNtt4ConvAsmReconstruct a b
    c = MiniVMNttBridge.exactCyclicConv4Vec a b ∧
    c.x0 < CrtNtt.fermatTowerMod4 ∧ c.x1 < CrtNtt.fermatTowerMod4 ∧
    c.x2 < CrtNtt.fermatTowerMod4 ∧ c.x3 < CrtNtt.fermatTowerMod4)

/-- Zero-axiom certificate for `MiniVM` Garner CRT & parametric Fermat-tower NTT assembly. -/
theorem miniVm_provenance_certified : MiniVmProvenance :=
  ⟨MiniVM.exec_garner_crt_sound,
   fun s a b ha hb hr0 hr1 => MiniVMNttBridge.ntt2AsmF17_sound s a b ha hb hr0 hr1,
   fun s a b ha hb hr0 hr1 =>
     MiniVMNttBridge.intt2_ntt2_asm_F17_roundtrip s a b ha hb hr0 hr1,
   fun s a b c d ha hb hc hd hr0 hr1 hr2 hr3 =>
     MiniVMNttBridge.ntt4AsmF17_sound s a b c d ha hb hc hd hr0 hr1 hr2 hr3,
   fun s a b c d ha hb hc hd hr0 hr1 hr2 hr3 =>
     MiniVMNttBridge.intt4_ntt4_asm_F17_roundtrip s a b c d ha hb hc hd hr0 hr1 hr2 hr3,
   MiniVMNttBridge.fermatTowerNtt4Specs_valid,
   MiniVMNttBridge.fermatTowerNtt4_asm_roundtrip_certs,
   MiniVMNttBridge.garnerReconstruct4Asm_sound,
   MiniVMNttBridge.crtNtt4ConvAsm_sound⟩

-- =============================================================================
-- Part 2: Collatz Diophantine Barriers & Simons-de Weger Cycle Bounds
-- =============================================================================

/-- Part 2 provenance specification bundling Collatz base convergence, parity resonance
obstruction `2^k ≠ 3^m`, 144-digit CRT-NTT gap `2^485 - 3^306 > 0`, 72-digit Baker measure,
Steiner 1-cycle exclusions, and the Simons-de Weger `m ≥ 307` cycle-length barrier. -/
def CollatzProvenance : Prop :=
  Conjectures.CollatzReachesOne 1 ∧
  (∀ k m : Nat, 1 ≤ m → 2 ^ k ≠ 3 ^ m) ∧
  (CollatzQrhBridge.powViaCrtNtt192 3 5 < CollatzQrhBridge.powViaCrtNtt192 2 8 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 8 - CollatzQrhBridge.powViaCrtNtt192 3 5 = 13 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 19 < CollatzQrhBridge.powViaCrtNtt192 3 12 ∧
   CollatzQrhBridge.powViaCrtNtt192 3 12 - CollatzQrhBridge.powViaCrtNtt192 2 19 = 7153 ∧
   CollatzQrhBridge.powViaCrtNtt192 3 41 < CollatzQrhBridge.powViaCrtNtt192 2 65 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 65 - CollatzQrhBridge.powViaCrtNtt192 3 41 =
     420491770248316829 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 84 < CollatzQrhBridge.powViaCrtNtt192 3 53 ∧
   CollatzQrhBridge.powViaCrtNtt192 3 53 - CollatzQrhBridge.powViaCrtNtt192 2 84 =
     40432553845953101497907 ∧
   CollatzQrhBridge.powViaCrtNtt192 3 193 < CollatzQrhBridge.powViaCrtNtt192 2 306 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 306 - CollatzQrhBridge.powViaCrtNtt192 3 193 =
     8919004416877265287627107489485238050671456548349002814112640455483105104697086921213106941 ∧
   CollatzQrhBridge.powViaCrtNtt192 3 306 < CollatzQrhBridge.powViaCrtNtt192 2 485 ∧
   CollatzQrhBridge.powViaCrtNtt192 2 485 - CollatzQrhBridge.powViaCrtNtt192 3 306 =
     CollatzQrhBridge.expectedGap485 ∧
   0 < CollatzQrhBridge.powViaCrtNtt192 2 485 - CollatzQrhBridge.powViaCrtNtt192 3 306) ∧
  (let scale71 : Int := 10 ^ 71
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 8 5 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 8 5 * (5 * 5 : Int)) ∧
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 19 12 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 19 12 * (12 * 12 : Int)) ∧
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 65 41 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 65 41 * (41 * 41 : Int)) ∧
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 84 53 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 84 53 * (53 * 53 : Int)) ∧
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 306 193 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 306 193 * (193 * 193 : Int)) ∧
   (0 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 485 306 ∧
     scale71 < CollatzQrhBridge.linearFormLn2Ln3AbsLower72 485 306 * (306 * 306 : Int))) ∧
  (¬ ((CollatzQrhBridge.powViaCrtNtt192 2 8 - CollatzQrhBridge.powViaCrtNtt192 3 5) ∣
    (CollatzQrhBridge.powViaCrtNtt192 3 5 - CollatzQrhBridge.powViaCrtNtt192 2 5)) ∧
   ¬ ((CollatzQrhBridge.powViaCrtNtt192 2 65 - CollatzQrhBridge.powViaCrtNtt192 3 41) ∣
    (CollatzQrhBridge.powViaCrtNtt192 3 41 - CollatzQrhBridge.powViaCrtNtt192 2 41)) ∧
   ¬ ((CollatzQrhBridge.powViaCrtNtt192 2 306 - CollatzQrhBridge.powViaCrtNtt192 3 193) ∣
    (CollatzQrhBridge.powViaCrtNtt192 3 193 - CollatzQrhBridge.powViaCrtNtt192 2 193)) ∧
   ¬ ((CollatzQrhBridge.powViaCrtNtt192 2 485 - CollatzQrhBridge.powViaCrtNtt192 3 306) ∣
    (CollatzQrhBridge.powViaCrtNtt192 3 306 - CollatzQrhBridge.powViaCrtNtt192 2 306)) ∧
   (∀ (k m : Nat), (k = 8 ∧ m = 5) ∨ (k = 65 ∧ m = 41) ∨
       (k = 306 ∧ m = 193) ∨ (k = 485 ∧ m = 306) →
     ∀ (nMin : Nat) (a : Nat → Nat),
       (∀ j, j + 1 < m → a j = 1) →
       nMin * (2 ^ k - 3 ^ m) ≠ CollatzQrhBridge.cycleRhs a m)) ∧
  (∀ {m : Nat} (c : CollatzQrhBridge.CollatzOddCycle m), 1 ≤ m →
    (m ≤ 306 → c.nMin < 10 * m * m ∧ c.nMin < 936360) ∧
    (936360 ≤ c.nMin →
      307 ≤ m ∧ 487 ≤ CollatzQrhBridge.cycleShift c.a m ∧
      793 ≤ CollatzQrhBridge.cycleShift c.a m + m)) ∧
  (2 ^ 1054 < 3 ^ 665 ∧ 0 < 3 ^ 665 - 2 ^ 1054) ∧
  (2 ^ 1054 < 3 ^ 665 ∧ 3 ^ 306 < 2 ^ 485 ∧ 1054 * 306 < 485 * 665) ∧
  ((∀ (c : CollatzQrhBridge.CollatzOddCycle 665),
      CollatzQrhBridge.cycleShift c.a 665 ≠ 1054) ∧
   ¬ ((2 ^ 1055 - 3 ^ 665) ∣ (3 ^ 665 - 2 ^ 665)) ∧
   (∀ (nMin : Nat) (a : Nat → Nat),
     (∀ j, j + 1 < 665 → a j = 1) →
     nMin * (2 ^ 1055 - 3 ^ 665) ≠ CollatzQrhBridge.cycleRhs a 665)) ∧
  (∀ {m : Nat} (c : CollatzQrhBridge.CollatzOddCycle m), 1 ≤ m →
    (m ≤ 665 → c.nMin < 936360) ∧
    (936360 ≤ c.nMin →
      666 ≤ m ∧ 1055 ≤ CollatzQrhBridge.cycleShift c.a m ∧
      1721 ≤ CollatzQrhBridge.cycleShift c.a m + m)) ∧
  (∀ d x : Nat, x ∈ CollatzQrhBridge.collatzPredTree d 1 →
    Conjectures.iterate Conjectures.collatzStep d x = 1) ∧
  (let s14_3_4 : CollatzQrhBridge.PredecessorDensitySpec := ⟨14, 18, 3, 4⟩
   let s14_kl  : CollatzQrhBridge.PredecessorDensitySpec := ⟨14, 18, 84, 100⟩
   let s15_kl  : CollatzQrhBridge.PredecessorDensitySpec := ⟨15, 24, 84, 100⟩
   let s20_maz : CollatzQrhBridge.PredecessorDensitySpec := ⟨20, 72, 9, 10⟩
   (s14_3_4.MatchesDepthTree ∧ s14_3_4.BeatsHalvingSpine ∧ s14_3_4.ExceedsSublinearPower) ∧
   (s14_kl.MatchesDepthTree ∧ s14_kl.BeatsHalvingSpine ∧ s14_kl.ExceedsSublinearPower) ∧
   (s15_kl.MatchesDepthTree ∧ s15_kl.BeatsHalvingSpine ∧ s15_kl.ExceedsSublinearPower) ∧
   (s20_maz.MatchesDepthTree ∧ s20_maz.BeatsHalvingSpine ∧ s20_maz.ExceedsSublinearPower) ∧
   (3 * 100 < 84 * 4 ∧ 84 * 10 < 9 * 100 ∧ 9 < 10))

/-- Zero-axiom certificate for Collatz parity, Baker, Steiner, Simons-de Weger,
`(1054, 665)` convergent, `m ≥ 666` cycle barrier, and predecessor-tree density bounds. -/
theorem collatz_provenance_certified : CollatzProvenance :=
  ⟨Conjectures.collatz_one_reaches_one,
   CollatzQrhBridge.collatz_no_exact_power_resonance,
   CollatzQrhBridge.collatz_convergent_485_306_separation_certified,
   CollatzQrhBridge.baker_effective_measure_485_306_verified,
   CollatzQrhBridge.steiner_1cycle_excluded_at_convergents,
   fun c hm => CollatzQrhBridge.collatz_cycle_length_lower_bound_306 c hm,
   CollatzQrhBridge.convergent_1054_665_gap_pos,
   CollatzQrhBridge.log2_3_convergent_bracket_665,
   CollatzQrhBridge.steiner_1cycle_excluded_1054_665,
   fun c hm => CollatzQrhBridge.simons_de_weger_barrier_665 c hm,
   CollatzQrhBridge.collatzPredTree_sound,
   CollatzQrhBridge.collatz_pred_tree_growth_certs⟩

-- =============================================================================
-- Parts 3-4: 4D Abelian Z_2 & Non-Abelian Q_8 Lattice Gauge Invariance
-- =============================================================================

/-- Parts 3-4 provenance specification for `Z_2` Wilson plaquette gauge invariance
and `Q_8 ⊂ SU(2)` trace conjugation invariance. -/
def YangMillsProvenance : Prop :=
  (∀ (g : YangMillsToy.GaugeTransform) (U : YangMillsToy.GaugeConfig)
      (x : YangMillsToy.Point4) (μ ν : YangMillsToy.Dir),
    YangMillsToy.plaquetteAction (YangMillsToy.gaugeTransform g U) x μ ν =
      YangMillsToy.plaquetteAction U x μ ν) ∧
  (∀ (g u : YangMillsQ8.Q8),
    YangMillsQ8.Q8.reTrace (YangMillsQ8.Q8.mul (YangMillsQ8.Q8.mul g u) (YangMillsQ8.Q8.inv g)) =
      YangMillsQ8.Q8.reTrace u)

/-- Zero-axiom certificate for 4D lattice gauge invariance across `Z_2` and `Q_8`. -/
theorem yangMills_provenance_certified : YangMillsProvenance :=
  ⟨YangMillsToy.plaquette_action_gauge_invariant,
   YangMillsQ8.q8_trace_conjugation_invariant⟩

-- =============================================================================
-- Part 5: Analytic QRH, Ultra-Deep 2D Rectangles, DVP ZFR, & Chebyshev Envelopes
-- =============================================================================

/-- Type alias bundling the Chebyshev remainder savings certificate statement. -/
def ChebyshevSavingsProp : Prop :=
  let θ₁ := QuasiRiemann.qrhThresholdThreeQuarters
  let θ₂ := QuasiRiemann.qrhThresholdSevenEighths
  let θ₃ := QuasiRiemann.qrhThresholdElevenTwelfths
  let θ₄ := QuasiRiemann.qrhThresholdFortySevenFortyEighths
  let s24_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s24_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s24_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s48_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s48_4 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₄, by decide, by decide⟩
  (QuasiRiemann.tenPowThetaExactExp 2 θ₁ = 18 ∧
   QuasiRiemann.tenPowThetaExactExp 2 θ₂ = 21 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_2 =
     QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 * 1000 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 ≤
     QuasiRiemann.qrhRemainderBoundAtTenPow s24_2) ∧
  (QuasiRiemann.tenPowThetaExactExp 2 θ₃ = 22 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_3 =
     QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 * 10000 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 ≤
     QuasiRiemann.qrhRemainderBoundAtTenPow s24_3) ∧
  (QuasiRiemann.tenPowThetaExactExp 4 θ₁ = 36 ∧
   QuasiRiemann.tenPowThetaExactExp 4 θ₄ = 47 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s48_4 =
     QuasiRiemann.qrhRemainderBoundAtTenPow s48_1 * 10 ^ 11 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s48_1 ≤
     QuasiRiemann.qrhRemainderBoundAtTenPow s48_4)

/-- Type alias bundling the benchmark Chebyshev remainder certificate across `10^12..10^336`. -/
def ChebyshevBenchmarkProp : Prop :=
  let θ₁ := QuasiRiemann.qrhThresholdThreeQuarters
  let θ₂ := QuasiRiemann.qrhThresholdSevenEighths
  let θ₃ := QuasiRiemann.qrhThresholdElevenTwelfths
  let θ₄ := QuasiRiemann.qrhThresholdFortySevenFortyEighths
  let s12_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨1, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s12_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨1, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s12_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨1, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s24_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s24_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s24_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨2, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s36_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨3, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s36_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨3, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s36_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨3, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s48_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s48_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s48_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s48_4 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨4, by decide, 1, by decide, θ₄, by decide, by decide⟩
  let s336_1 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨28, by decide, 1, by decide, θ₁, by decide, by decide⟩
  let s336_2 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨28, by decide, 1, by decide, θ₂, by decide, by decide⟩
  let s336_3 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨28, by decide, 1, by decide, θ₃, by decide, by decide⟩
  let s336_4 : QuasiRiemann.ChebyshevRemainderSpec :=
    ⟨28, by decide, 1, by decide, θ₄, by decide, by decide⟩
  (QuasiRiemann.qrhRemainderBoundAtTenPow s12_1 = 10 ^ 9 * 784 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s12_1 < 10 ^ 12 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s12_2 = 10 ^ 11 * 784 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s12_3 = 10 ^ 11 * 784) ∧
  (QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 = 10 ^ 18 * 3136 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s24_1 < 10 ^ 24 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_2 = 10 ^ 21 * 3136 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s24_3 = 10 ^ 22 * 3136) ∧
  (QuasiRiemann.qrhRemainderBoundAtTenPow s36_1 = 10 ^ 27 * 7056 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s36_1 < 10 ^ 36 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s36_2 = 10 ^ 32 * 7056 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s36_3 = 10 ^ 33 * 7056) ∧
  (QuasiRiemann.qrhRemainderBoundAtTenPow s48_1 = 10 ^ 36 * 12544 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s48_1 < 10 ^ 48 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s48_2 = 10 ^ 42 * 12544 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s48_2 < 10 ^ 48 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s48_3 = 10 ^ 44 * 12544 ∧
   QuasiRiemann.qrhRemainderBoundAtTenPow s48_4 = 10 ^ 47 * 12544) ∧
  (QuasiRiemann.tenPowThetaExactExp 28 θ₁ = 252 ∧
   QuasiRiemann.tenPowThetaExactExp 28 θ₂ = 294 ∧
   QuasiRiemann.tenPowThetaExactExp 28 θ₃ = 308 ∧
   QuasiRiemann.tenPowThetaExactExp 28 θ₄ = 329 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s336_1 < 10 ^ 336 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s336_2 < 10 ^ 336 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s336_3 < 10 ^ 336 ∧
   10 * QuasiRiemann.qrhRemainderBoundAtTenPow s336_4 < 10 ^ 336)

/-- Type alias bundling short-interval prime positivity, maximal prime-gap
contrapositive bounds, and the strict `1/2 < 17/30 < 7/12 < 2/3 < 3/4 < 7/8 < 1`
rational short-interval exponent ladder. -/
def ShortIntervalPrimesProp : Prop :=
  (QuasiRiemann.shortIntervalQrh78Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh34Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalRh12Spec.HasGuaranteedPrime ∧
   QuasiRiemann.tenPowThetaCeilExp 28 QuasiRiemann.qrhThresholdSevenEighths = 294 ∧
   QuasiRiemann.tenPowThetaCeilExp 14 QuasiRiemann.qrhThresholdThreeQuarters = 126 ∧
   QuasiRiemann.tenPowThetaCeilExp 14 (QuasiRiemann.QRat.mk' 1 2) = 84) ∧
  (let eDH := QuasiRiemann.shortIntervalDensityExponent 2 1
   let eGM := QuasiRiemann.shortIntervalDensityExponent 30 13
   let eHux := QuasiRiemann.shortIntervalDensityExponent 12 5
   let eIng := QuasiRiemann.shortIntervalDensityExponent 3 1
   let θ34 := QuasiRiemann.qrhThresholdThreeQuarters
   let θ78 := QuasiRiemann.qrhThresholdSevenEighths
   QuasiRiemann.QRat.eqv eDH (QuasiRiemann.QRat.mk' 1 2) ∧
   QuasiRiemann.QRat.eqv eGM (QuasiRiemann.QRat.mk' 17 30) ∧
   QuasiRiemann.QRat.eqv eHux (QuasiRiemann.QRat.mk' 7 12) ∧
   QuasiRiemann.QRat.eqv eIng (QuasiRiemann.QRat.mk' 2 3) ∧
   eDH < eGM ∧ eGM < eHux ∧ eHux < eIng ∧ eIng < θ34 ∧
   θ34 < θ78 ∧ θ78 < QuasiRiemann.QRat.ofInt 1 ∧
   QuasiRiemann.QRat.eqv (eHux - eGM) (QuasiRiemann.QRat.mk' 1 60) ∧
   QuasiRiemann.QRat.eqv (θ78 - eGM) (QuasiRiemann.QRat.mk' 37 120)) ∧
  (∀ (spec : QuasiRiemann.ChebyshevRemainderSpec)
      (s : QuasiRiemann.ShortIntervalChebyshevSpec),
    s.hScaleExp ≤ s.xScaleExp →
    QuasiRiemann.qrhRemainderBoundAtTwoTenPow spec ≤ s.errUpper →
    ∀ (psiX psiXH thetaX thetaXH : Int),
      Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ s.errUpper →
      Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤
        s.errUpper →
      (psiXH - psiX) - (thetaXH - thetaX) ≤ (s.primePowerCorr : Int) →
      (thetaXH - thetaX ≤ 0 → ¬ s.HasGuaranteedPrime) ∧
      (s.HasGuaranteedPrime →
        ∀ pCurr pNext : Nat,
          pCurr ≤ 10 ^ s.xScaleExp →
          (10 ^ s.xScaleExp + 10 ^ s.hScaleExp < pNext → thetaXH - thetaX ≤ 0) →
          pNext ≤ 10 ^ s.xScaleExp + 10 ^ s.hScaleExp ∧
          (pCurr = 10 ^ s.xScaleExp → pNext - pCurr ≤ 10 ^ s.hScaleExp))) ∧
  (EulerFactorNonVanishing.fermatTowerPrimes = [5, 17, 257, 65537] ∧
   (EulerFactorNonVanishing.fermatTowerPrimes.map (· - 1)).prod = 2 ^ 30 ∧
   EulerFactorNonVanishing.FermatTowerStripCert ∧
   ((QuasiRiemann.fermatAp78Spec 5 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp78Spec 17 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp78Spec 257 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp78Spec 65537 (by decide)).HasGuaranteedApPrime) ∧
   ((QuasiRiemann.fermatAp34Spec 5 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp34Spec 17 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp34Spec 257 (by decide)).HasGuaranteedApPrime ∧
    (QuasiRiemann.fermatAp34Spec 65537 (by decide)).HasGuaranteedApPrime)) ∧
  (∀ (s : QuasiRiemann.ApShortIntervalSpec)
      (psiApX psiApXH thetaApX thetaApXH : Int),
    Int.natAbs ((s.phiQ : Int) * psiApX - ((10 ^ s.base.xScaleExp : Nat) : Int)) ≤
      s.phiQ * s.base.errUpper →
    Int.natAbs ((s.phiQ : Int) * psiApXH -
        ((10 ^ s.base.xScaleExp + 10 ^ s.base.hScaleExp : Nat) : Int)) ≤
      s.phiQ * s.base.errUpper →
    (psiApXH - psiApX) - (thetaApXH - thetaApX) ≤ (s.base.primePowerCorr : Int) →
    s.HasGuaranteedApPrime →
    (0 : Int) < thetaApXH - thetaApX) ∧
  (let θ12 := QuasiRiemann.QRat.mk' 1 2
   let θ916 := QuasiRiemann.qrhThresholdNineSixteenths
   let θ58 := QuasiRiemann.qrhThresholdFiveEighths
   let θ23 := QuasiRiemann.qrhThresholdTwoThirds
   let θ34 := QuasiRiemann.qrhThresholdThreeQuarters
   let θ78 := QuasiRiemann.qrhThresholdSevenEighths
   (θ12 < θ916 ∧ θ916 < θ58 ∧ θ58 < θ23 ∧
    θ23 < θ34 ∧ θ34 < θ78 ∧ θ78 < QuasiRiemann.QRat.ofInt 1) ∧
   (QuasiRiemann.QRat.ofInt 0 < QuasiRiemann.chebyshevGap θ78 ∧
    QuasiRiemann.chebyshevGap θ78 < QuasiRiemann.chebyshevGap θ34 ∧
    QuasiRiemann.chebyshevGap θ34 < QuasiRiemann.chebyshevGap θ23 ∧
    QuasiRiemann.chebyshevGap θ23 < QuasiRiemann.chebyshevGap θ58 ∧
    QuasiRiemann.chebyshevGap θ58 < QuasiRiemann.chebyshevGap θ916 ∧
    QuasiRiemann.chebyshevGap θ916 < QuasiRiemann.chebyshevGap θ12) ∧
   (QuasiRiemann.tenPowThetaCeilExp 2 θ23 = 16 ∧
    QuasiRiemann.tenPowThetaCeilExp 2 θ58 = 15 ∧
    QuasiRiemann.tenPowThetaCeilExp 4 θ916 = 27) ∧
   (QuasiRiemann.shortIntervalQrh23Spec.HasGuaranteedPrime ∧
    10 ^ 20 < 2 * QuasiRiemann.shortIntervalQrh23Spec.errUpper +
      QuasiRiemann.shortIntervalQrh23Spec.primePowerCorr) ∧
   (QuasiRiemann.shortIntervalQrh58Spec.HasGuaranteedPrime ∧
    10 ^ 19 < 2 * QuasiRiemann.shortIntervalQrh58Spec.errUpper +
      QuasiRiemann.shortIntervalQrh58Spec.primePowerCorr) ∧
   (QuasiRiemann.shortIntervalQrh916Spec.HasGuaranteedPrime ∧
    10 ^ 31 < 2 * QuasiRiemann.shortIntervalQrh916Spec.errUpper +
      QuasiRiemann.shortIntervalQrh916Spec.primePowerCorr))

/-- Higher-truncation (`N ∈ {256, 512}`) 2D zero-free rectangle, 90-digit CRT-NTT phase
reduction (`< 10^-60` rad), and monotonic Euler–Maclaurin contraction specification. -/
def HighTruncRectProvenanceProp : Prop :=
  ((QuasiRiemann.twoPiInterval90.hi - QuasiRiemann.twoPiInterval90.lo = 1 ∧
    QuasiRiemann.twoPiInterval90.lo * 10 ^ 15 ≤ 2 * (PiChudnovsky.piLower105 : Int) ∧
    2 * (PiChudnovsky.piUpper105 : Int) ≤ QuasiRiemann.twoPiInterval90.hi * 10 ^ 15) ∧
   (∀ xIv : QuasiRiemann.ScaledInterval90,
     0 ≤ xIv.lo →
     xIv.hi ≤ 7 * (10 ^ 18 + 10) * QuasiRiemann.scale90Int →
     xIv.hi - xIv.lo ≤ 4 * 10 ^ 21 →
     (QuasiRiemann.reduceModTwoPiCentered90 xIv).hi -
       (QuasiRiemann.reduceModTwoPiCentered90 xIv).lo ≤ 5 * 10 ^ 21) ∧
   (∀ (t90Val lnVal twoPi : Int) (n : Nat),
     ((10 ^ 12 * QuasiRiemann.scale90Int ≤ t90Val ∧
       t90Val ≤ (10 ^ 12 + 10) * QuasiRiemann.scale90Int) ∨
      (10 ^ 18 * QuasiRiemann.scale90Int ≤ t90Val ∧
       t90Val ≤ (10 ^ 18 + 10) * QuasiRiemann.scale90Int)) →
     1 ≤ n → n ≤ 512 →
     (QuasiRiemann.lnInterval90_512 n).lo ≤ lnVal ∧
       lnVal ≤ (QuasiRiemann.lnInterval90_512 n).hi →
     QuasiRiemann.twoPiInterval90.lo ≤ twoPi ∧
       twoPi ≤ QuasiRiemann.twoPiInterval90.hi →
     let rIv90 := QuasiRiemann.reducePhaseModTwoPi90
       ⟨t90Val, t90Val, Int.le_refl t90Val⟩ (QuasiRiemann.lnInterval90_512 n)
     let rIv72 := QuasiRiemann.toIv72From90 rIv90
     rIv90.hi - rIv90.lo ≤ 4 * 10 ^ 21 ∧
     512 * (rIv90.hi - rIv90.lo) < 10 ^ 30 ∧
     rIv72.hi - rIv72.lo ≤ 4 * 10 ^ 3 + 2 ∧
     (QuasiRiemann.taylorCosInterval72 rIv72).lo ≤
       (QuasiRiemann.taylorCosInterval72 rIv72).hi ∧
     (QuasiRiemann.taylorSinInterval72 rIv72).lo ≤
       (QuasiRiemann.taylorSinInterval72 rIv72).hi ∧
     ∃ k p90 : Int,
       p90 * QuasiRiemann.scale90Int ≤ t90Val * lnVal ∧
       t90Val * lnVal ≤ (p90 + 1) * QuasiRiemann.scale90Int ∧
       rIv90.lo ≤ p90 - k * twoPi ∧
       p90 - k * twoPi ≤ rIv90.hi)) ∧
  ((∀ sLo6 tLo6 tHi6 : Nat, 500000 ≤ sLo6 →
     QuasiRiemann.eulerMaclaurinB2TailRect2DForN 512 sLo6 tLo6 tHi6 ≤
       QuasiRiemann.eulerMaclaurinB2TailRect2DForN 256 sLo6 tLo6 tHi6 ∧
     QuasiRiemann.eulerMaclaurinB2TailRect2DForN 256 sLo6 tLo6 tHi6 ≤
       QuasiRiemann.eulerMaclaurinB2TailRect2DForN 128 sLo6 tLo6 tHi6) ∧
   (QuasiRiemann.eulerMaclaurinB2TailRect2DForN 512 500250 108900000 108910000 <
      QuasiRiemann.eulerMaclaurinB2TailRect2DForN 256 500250 108900000 108910000 ∧
    QuasiRiemann.eulerMaclaurinB2TailRect2DForN 256 500250 108900000 108910000 <
      QuasiRiemann.eulerMaclaurinB2TailRect2DForN 128 500250 108900000 108910000) ∧
   (QuasiRiemann.eulerMaclaurinB2TailRect2DForN 512 500500 108900000 108910000 = 176912 ∧
    QuasiRiemann.eulerMaclaurinB2TailRect2DForN 256 500500 108900000 108910000 = 293217 ∧
    QuasiRiemann.eulerMaclaurinB2TailRect2DForN 128 500500 108900000 108910000 = 630769) ∧
   QuasiRiemann.spec05005_N256_mod.HasCertifiedNonVanishing ∧
   QuasiRiemann.spec050025_N512_mod.HasCertifiedNonVanishing) ∧
  (QuasiRiemann.highTruncTiles_1e12_N256.length = 4 ∧
   QuasiRiemann.highTruncTiles_1e18_N512.length = 4 ∧
   (∀ t ∈ QuasiRiemann.highTruncTiles_1e12_N256, QuasiRiemann.IsValidLipTile2D t) ∧
   (∀ t ∈ QuasiRiemann.highTruncTiles_1e18_N512, QuasiRiemann.IsValidLipTile2D t) ∧
   (∀ s6 t6 : Nat,
     QuasiRiemann.InBox2D 500500 504500 1000000000006090000 1000000000006130000 s6 t6 →
     ∃ tile ∈ QuasiRiemann.highTruncTiles_1e12_N256,
       QuasiRiemann.IsValidLipTile2D tile ∧
       QuasiRiemann.InBox2D tile.sLo6 tile.sHi6 tile.tLo6 tile.tHi6 s6 t6 ∧
       (∀ zRe0 zIm0 zRe zIm : Int,
         tile.anchorRe.lo * 1000000 ≤ zRe0 ∧ zRe0 ≤ tile.anchorRe.hi * 1000000 →
         tile.anchorIm.lo * 1000000 ≤ zIm0 ∧ zIm0 ≤ tile.anchorIm.hi * 1000000 →
         Int.natAbs (zRe - zRe0) ≤
           tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
             ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
         Int.natAbs (zIm - zIm0) ≤
           tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
             ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
         0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) ∧
   (∀ s6 t6 : Nat,
     QuasiRiemann.InBox2D 500250 504250
       1000000000000000000980000 1000000000000000001000000 s6 t6 →
     ∃ tile ∈ QuasiRiemann.highTruncTiles_1e18_N512,
       QuasiRiemann.IsValidLipTile2D tile ∧
       QuasiRiemann.InBox2D tile.sLo6 tile.sHi6 tile.tLo6 tile.tHi6 s6 t6 ∧
       (∀ zRe0 zIm0 zRe zIm : Int,
         tile.anchorRe.lo * 1000000 ≤ zRe0 ∧ zRe0 ≤ tile.anchorRe.hi * 1000000 →
         tile.anchorIm.lo * 1000000 ≤ zIm0 ∧ zIm0 ≤ tile.anchorIm.hi * 1000000 →
         Int.natAbs (zRe - zRe0) ≤
           tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
             ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
         Int.natAbs (zIm - zIm0) ≤
           tile.gradBound6 * (((s6 : Int) - tile.sMid6).natAbs +
             ((t6 : Int) - tile.tMid6).natAbs) + tile.epsCrt6 * 1000000 →
         0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))) ∧
   QuasiRiemann.highTruncSpec_1e12_N256.HasCertifiedNonVanishing ∧
   QuasiRiemann.highTruncSpec_1e18_N512.HasCertifiedNonVanishing)

/-- Part 5 provenance specification bundling mollifier descent, 2D rectangles down to
`σ = 0.501`, `t ~ 10^12` phase-reduced rectangles, DVP asymptotic strip, Dirichlet `L^2`
diagonal dominance, rational zero-density descent (`15/26 < 3/5 < 2/3`), QRH threshold
ladder `θ ∈ {3/4, 7/8, 11/12, 47/48}`, Chebyshev envelopes, short-interval primes, and
higher-truncation (`N ∈ {256, 512}`) CRT-NTT 2D zero-free rectangle certificates. -/
def QuasiRiemannProvenance : Prop :=
  (let th1 := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.ofInt 1)
   let thHalf := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.mk' 1 2)
   let thThird := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.mk' 1 3)
   let thQuarter := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.mk' 1 4)
   let thSixth := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.mk' 1 6)
   let thZero := QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.QRat.ofInt 0)
   QuasiRiemann.QRat.eqv th1 (QuasiRiemann.QRat.mk' 1 2) ∧
   QuasiRiemann.QRat.eqv thHalf (QuasiRiemann.QRat.mk' 3 4) ∧
   QuasiRiemann.QRat.eqv thThird (QuasiRiemann.QRat.mk' 5 6) ∧
   QuasiRiemann.QRat.eqv thQuarter (QuasiRiemann.QRat.mk' 7 8) ∧
   QuasiRiemann.QRat.eqv thSixth (QuasiRiemann.QRat.mk' 11 12) ∧
   QuasiRiemann.QRat.eqv thZero (QuasiRiemann.QRat.ofInt 1) ∧
   th1 < thHalf ∧ thHalf < thThird ∧ thThird < thQuarter ∧
   thQuarter < thSixth ∧ thSixth < thZero ∧
   QuasiRiemann.QRat.mk' 1 6 < QuasiRiemann.QRat.mk' 5 28 ∧
   QuasiRiemann.QRat.mk' 5 28 < QuasiRiemann.QRat.mk' 1 4 ∧
   QuasiRiemann.zeroDensityGuthMaynard < QuasiRiemann.zeroDensityHuxley ∧
   QuasiRiemann.primeGapExponent QuasiRiemann.zeroDensityGuthMaynard <
     QuasiRiemann.primeGapExponent QuasiRiemann.zeroDensityHuxley) ∧
  (let swept := QuasiRiemann.sweepRectangles2DN128 QuasiRiemann.ultraDeepStripRectGrid2D_N128
   0 < swept.length ∧ swept.length = 7 ∧
   0 < QuasiRiemann.totalCertifiedAreaScaled12 swept ∧
   QuasiRiemann.totalCertifiedAreaScaled12 swept = 140000000 ∧
   (∃ r ∈ swept, r.sLo6 = 501000)) ∧
  (let swept := QuasiRiemann.sweepDirichletRectangles2DN128
     QuasiRiemann.highHeightRectGrid2D_1e12_N128
   0 < swept.length ∧ swept.length = 5 ∧
   0 < QuasiRiemann.totalCertifiedAreaScaled12 swept ∧
   QuasiRiemann.totalCertifiedAreaScaled12 swept = 6970000000 ∧
   (∀ r ∈ swept, QuasiRiemann.IsValidDirichletRect2DN128 r) ∧
   (∃ r ∈ swept, r.sLo6 = 501000 ∧ 1000000000000000000 ≤ r.tLo6)) ∧
  (∀ (spec : QuasiRiemann.ZeroDensitySpec) (θ : QuasiRiemann.QRat)
      (_hdens : ∀ σ : QuasiRiemann.QRat,
        θ < σ → σ ≤ QuasiRiemann.QRat.ofInt 1 → spec.sublinearAt σ)
      (t : Nat) (_ht : QuasiRiemann.dvpThresholdT0 ≤ t)
      (β S0 S1 S2 : QuasiRiemann.QRat)
      (_hviol : QuasiRiemann.QRat.ofInt 1 ≤ spec.exponent β)
      (hgap : QuasiRiemann.QRat.ofInt 0 <
        QuasiRiemann.QRat.ofInt 1 + QuasiRiemann.dvpDelta t - β),
      QuasiRiemann.QRat.ofInt 0 ≤
        QuasiRiemann.QRat.ofInt 3 * S0 + QuasiRiemann.QRat.ofInt 4 * S1 + S2 →
      S0 ≤ QuasiRiemann.QRat.div (QuasiRiemann.QRat.ofInt 1) (QuasiRiemann.dvpDelta t)
          (by dsimp [QuasiRiemann.dvpDelta, QuasiRiemann.QRat.mk']; decide) +
        QuasiRiemann.QRat.ofInt 1 →
      S1 ≤ -(QuasiRiemann.QRat.div (QuasiRiemann.QRat.ofInt 1)
          (QuasiRiemann.QRat.ofInt 1 + QuasiRiemann.dvpDelta t - β)
          (Int.ne_of_gt ((QuasiRiemann.qrat_pos_iff _).mp hgap))) +
        QuasiRiemann.QRat.mk' 1 2 * QuasiRiemann.octaveLnUpper36QRat t →
      S2 ≤ QuasiRiemann.QRat.mk' 3 4 *
        (QuasiRiemann.octaveLnUpper36QRat t + QuasiRiemann.ln2Upper36QRat) →
      β ≤ θ ∧
      β ≤ QuasiRiemann.QRat.ofInt 1 -
        QuasiRiemann.QRat.div QuasiRiemann.cDvp (QuasiRiemann.octaveLnUpper36QRat t)
          (Int.ne_of_gt ((QuasiRiemann.qrat_pos_iff _).mp
            (QuasiRiemann.octaveLnUpper36_pos t).2.1)) ∧
      β < QuasiRiemann.QRat.ofInt 1 ∧
      QuasiRiemann.chebyshevGap θ ≤ QuasiRiemann.chebyshevGap β) ∧
  (QuasiRiemann.QRat.eqv
      (QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff)
      (QuasiRiemann.QRat.ofInt 4) ∧
   QuasiRiemann.QRat.eqv
      (QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff)
      (QuasiRiemann.QRat.ofInt 5) ∧
   (∀ offZ : QuasiRiemann.QRat,
     QuasiRiemann.QRat.abs offZ ≤
       QuasiRiemann.dirichletOffDiagEnvelope 4 64 QuasiRiemann.zetaDirichletCoeff →
     QuasiRiemann.QRat.mk' 1 2 (by decide) *
         QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff ≤
       QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff + offZ ∧
     QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff + offZ ≤
       QuasiRiemann.QRat.mk' 3 2 (by decide) *
         QuasiRiemann.dirichletDiagEnergy 4 QuasiRiemann.zetaDirichletCoeff) ∧
   (∀ offM : QuasiRiemann.QRat,
     QuasiRiemann.QRat.abs offM ≤
       QuasiRiemann.dirichletOffDiagEnvelope 6 144 QuasiRiemann.altMobiusCoeff →
     QuasiRiemann.QRat.mk' 1 2 (by decide) *
         QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff ≤
       QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff + offM ∧
     QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff + offM ≤
       QuasiRiemann.QRat.mk' 3 2 (by decide) *
         QuasiRiemann.dirichletDiagEnergy 6 QuasiRiemann.altMobiusCoeff)) ∧
  (let σ := QuasiRiemann.QRat.mk' 3 4
   QuasiRiemann.QRat.eqv (QuasiRiemann.zdIngham34.exponent σ) (QuasiRiemann.QRat.mk' 2 3) ∧
   QuasiRiemann.QRat.eqv (QuasiRiemann.zdHuxley.exponent σ) (QuasiRiemann.QRat.mk' 3 5) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.zdGuthMaynard.exponent σ) (QuasiRiemann.QRat.mk' 15 26) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.zdDensityHypothesis.exponent σ) (QuasiRiemann.QRat.mk' 1 2) ∧
   QuasiRiemann.zdDensityHypothesis.exponent σ < QuasiRiemann.zdGuthMaynard.exponent σ ∧
   QuasiRiemann.zdGuthMaynard.exponent σ < QuasiRiemann.zdHuxley.exponent σ ∧
   QuasiRiemann.zdHuxley.exponent σ < QuasiRiemann.zdIngham34.exponent σ ∧
   QuasiRiemann.zdIngham34.exponent σ < QuasiRiemann.zdInghamClassical.exponent σ ∧
   QuasiRiemann.zdGuthMaynard.sublinearAt σ ∧
   QuasiRiemann.zdHuxley.sublinearAt σ ∧
   QuasiRiemann.zdIngham34.sublinearAt σ ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.zdHuxley.exponent σ - QuasiRiemann.zdGuthMaynard.exponent σ)
     (QuasiRiemann.QRat.mk' 3 130) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.subconvLindelof.muAt (QuasiRiemann.QRat.mk' 1 2))
     (QuasiRiemann.QRat.ofInt 0) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.subconvBourgain.muAt (QuasiRiemann.QRat.mk' 1 2))
     (QuasiRiemann.QRat.mk' 13 84) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.subconvWeyl.muAt (QuasiRiemann.QRat.mk' 1 2))
     (QuasiRiemann.QRat.mk' 1 6) ∧
   QuasiRiemann.QRat.eqv
     (QuasiRiemann.subconvConvexity.muAt (QuasiRiemann.QRat.mk' 1 2))
     (QuasiRiemann.QRat.mk' 1 4) ∧
   QuasiRiemann.subconvLindelof.muHalf < QuasiRiemann.subconvBourgain.muHalf ∧
   QuasiRiemann.subconvBourgain.muHalf < QuasiRiemann.subconvWeyl.muHalf ∧
   QuasiRiemann.subconvWeyl.muHalf < QuasiRiemann.subconvConvexity.muHalf) ∧
  (∀ t : Nat, QuasiRiemann.dvpThresholdT0 ≤ t →
    let θ₁ := QuasiRiemann.qrhThresholdThreeQuarters
    let θ₂ := QuasiRiemann.qrhThresholdSevenEighths
    let θ₃ := QuasiRiemann.qrhThresholdElevenTwelfths
    let θ₄ := QuasiRiemann.qrhThresholdFortySevenFortyEighths
    let zfr := QuasiRiemann.QRat.ofInt 1 -
      QuasiRiemann.QRat.div QuasiRiemann.cDvp (QuasiRiemann.octaveLnUpper36QRat t)
        (Int.ne_of_gt ((QuasiRiemann.qrat_pos_iff _).mp
          (QuasiRiemann.octaveLnUpper36_pos t).2.1))
    (θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < QuasiRiemann.QRat.ofInt 1) ∧
    (QuasiRiemann.QRat.eqv (QuasiRiemann.chebyshevGap θ₁) (QuasiRiemann.QRat.mk' 1 4) ∧
     QuasiRiemann.QRat.eqv (QuasiRiemann.chebyshevGap θ₂) (QuasiRiemann.QRat.mk' 1 8) ∧
     QuasiRiemann.QRat.eqv (QuasiRiemann.chebyshevGap θ₃) (QuasiRiemann.QRat.mk' 1 12) ∧
     QuasiRiemann.QRat.eqv (QuasiRiemann.chebyshevGap θ₄) (QuasiRiemann.QRat.mk' 1 48) ∧
     QuasiRiemann.QRat.ofInt 0 < QuasiRiemann.chebyshevGap θ₄ ∧
     QuasiRiemann.chebyshevGap θ₄ < QuasiRiemann.chebyshevGap θ₃ ∧
     QuasiRiemann.chebyshevGap θ₃ < QuasiRiemann.chebyshevGap θ₂ ∧
     QuasiRiemann.chebyshevGap θ₂ < QuasiRiemann.chebyshevGap θ₁) ∧
    (θ₁ < zfr ∧ θ₂ < zfr ∧ θ₃ < zfr ∧ θ₄ < zfr)) ∧
  ChebyshevSavingsProp ∧
  ChebyshevBenchmarkProp ∧
  ShortIntervalPrimesProp ∧
  HighTruncRectProvenanceProp

set_option exponentiation.threshold 2000 in
/-- Zero-axiom certificate for Parts 3-5 analytic QRH, 2D rectangles, DVP, and Chebyshev. -/
theorem quasiRiemann_provenance_certified : QuasiRiemannProvenance :=
  ⟨QuasiRiemann.qrh_full_descent_chain_certified,
   QuasiRiemann.ultra_deep_rects_down_to_0501_certified,
   QuasiRiemann.high_height_dirichlet_rects_1e12_certified,
   fun spec θ hdens t ht β S0 S1 S2 hviol hgap hpos341 hS0 hS1 hS2 =>
     QuasiRiemann.zero_density_and_dvp_combined_region
       spec θ hdens t ht β S0 S1 S2 hviol hgap hpos341 hS0 hS1 hS2,
   QuasiRiemann.dirichlet_l2_zeta_and_mobius_certs,
   QuasiRiemann.qrh_zero_density_benchmark_certs,
   fun t ht => QuasiRiemann.qrh_theta_ladder_certs t ht,
   QuasiRiemann.qrh_chebyshev_savings_certs,
   QuasiRiemann.qrh_chebyshev_benchmark_certs,
   ⟨QuasiRiemann.qrh_short_interval_positivity_certs,
    QuasiRiemann.short_interval_density_ladder_strict,
    fun spec s hH hE pX pXH tX tXH hBX hBXH hC =>
      QuasiRiemann.qrh_maximal_prime_gap_bound
        spec s hH hE pX pXH tX tXH hBX hBXH hC,
    QuasiRiemann.fermat_tower_ap_short_interval_certs,
    fun s pX pXH tX tXH hBX hBXH hC hP =>
      QuasiRiemann.ap_short_interval_psi_diff_bound
        s pX pXH tX tXH hBX hBXH hC hP,
    QuasiRiemann.sub_three_quarters_qrh_ladder_certs⟩,
   ⟨QuasiRiemann.crtNtt_phase_reduction_512_sound,
    QuasiRiemann.euler_maclaurin_tail_shrinks_with_N,
    QuasiRiemann.crtNtt_highTrunc_2d_zero_free_rect⟩⟩

-- =============================================================================
-- Parts 6 & 8: RNS Garner & Fermat-Tower / Dedekind Euler Non-Vanishing
-- =============================================================================

/-- Parts 6 & 8 provenance specification bundling 3-channel Garner multiplication,
`EulerFactorNonVanishing.FermatTowerStripCert` (`half`, `threeQuarters`, `one`),
and cyclotomic Dedekind Euler product bounds across all `32,906` split prime ideals. -/
def EulerRnsProvenance : Prop :=
  (RnsArithmetic.fromRnsTupleGarner
    (RnsArithmetic.rnsMul (RnsArithmetic.toRns 23) (RnsArithmetic.toRns 37)) = 23 * 37) ∧
  EulerFactorNonVanishing.FermatTowerStripCert ∧
  (∀ zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int,
    (zx5 * zx5 + zy5 * zy5 ≤ 1 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fsHalf : List EulerFactorNonVanishing.CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 2, 1, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 4, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 16, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 256, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < EulerFactorNonVanishing.cyclotomicProdMarginPow fsHalf ∧
     EulerFactorNonVanishing.cyclotomicProdMarginPow fsHalf ≤
       EulerFactorNonVanishing.cyclotomicProdNormPow fsHalf ∧
     0 < EulerFactorNonVanishing.cyclotomicProdDenPow fsHalf) ∧
    (zx5 * zx5 + zy5 * zy5 ≤ 9 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fs34 : List EulerFactorNonVanishing.CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 10, 3, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 8, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 64, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 4096, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < EulerFactorNonVanishing.cyclotomicProdMarginPow fs34 ∧
     EulerFactorNonVanishing.cyclotomicProdMarginPow fs34 ≤
       EulerFactorNonVanishing.cyclotomicProdNormPow fs34 ∧
     0 < EulerFactorNonVanishing.cyclotomicProdDenPow fs34) ∧
    (zx5 * zx5 + zy5 * zy5 ≤ 1 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fsOne : List EulerFactorNonVanishing.CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 5, 1, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 17, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 257, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 65537, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < EulerFactorNonVanishing.cyclotomicProdMarginPow fsOne ∧
     EulerFactorNonVanishing.cyclotomicProdMarginPow fsOne ≤
       EulerFactorNonVanishing.cyclotomicProdNormPow fsOne ∧
     EulerFactorNonVanishing.cyclotomicProdDenPow fsOne <
       256 * EulerFactorNonVanishing.cyclotomicProdNormPow fsOne))

/-- Zero-axiom certificate for RNS Garner and Fermat-tower / Dedekind strip bounds. -/
theorem eulerRns_provenance_certified : EulerRnsProvenance :=
  ⟨RnsArithmetic.garner_mul_concrete_soundness,
   EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs,
   EulerFactorNonVanishing.fermat_tower_dedekind_euler_strip_certs⟩

-- =============================================================================
-- Part 7: Finite-Field RH, Genus-2 L(C,1)=71/25, Cantor Jacobian & Weil Zeta
-- =============================================================================

/-- Part 7 provenance specification bundling Hasse-Weil RH for `E / F_7`,
genus-2 `C / F_5` negative discriminants, `L(C, 1) = 71/25`, Cantor-Mumford group axioms
for `J(C)(F_5) ≅ Z/71Z`, punctured-strip zeta non-vanishing, `Ξ_C` reflection, and
`GSp(4) -> SO(5)` functorial Euler lift + Selberg / Kim-Sarnak exponent ladder. -/
def FiniteFieldWeilProvenance : Prop :=
  (FiniteFieldRH.frobeniusTrace * FiniteFieldRH.frobeniusTrace ≤
    4 * (FiniteFieldRH.p : Int)) ∧
  ((∀ s d : Int, 0 < d → s * s ≤ 5 * (d * d) →
    ((5 * d + s) * (5 * d + s) - 20 * ((2 * d) * (2 * d)) < 0 ∧
     (5 * d - s) * (5 * d - s) - 20 * ((2 * d) * (2 * d)) < 0)) ∧
   ((2236 : Int) * 2236 < 5 * 1000 * 1000 ∧
    5 * 1000 * 1000 < (2237 : Int) * 2237 ∧
    (30 * 1000 + 10 * 2237) < 80 * 1000 ∧
    (30 * 1000 - 10 * 2236) < 80 * 1000)) ∧
  QuasiRiemann.QRat.eqv
    (QuasiRiemann.QRat.mk' FiniteFieldRH.genus2LNumAtInv5 625 (by decide))
    (QuasiRiemann.QRat.mk' 71 25 (by decide)) ∧
  ((∀ A B C, Genus2Jacobian.inD0Orbit A → Genus2Jacobian.inD0Orbit B →
      Genus2Jacobian.inD0Orbit C →
      Genus2Jacobian.cantorAdd (Genus2Jacobian.cantorAdd A B) C =
        Genus2Jacobian.cantorAdd A (Genus2Jacobian.cantorAdd B C)) ∧
   (∀ A B, Genus2Jacobian.inD0Orbit A → Genus2Jacobian.inD0Orbit B →
      Genus2Jacobian.cantorAdd A B = Genus2Jacobian.cantorAdd B A) ∧
   (∀ A, Genus2Jacobian.inD0Orbit A →
      Genus2Jacobian.cantorAdd A Genus2Jacobian.MumfordDivisor.zero = A ∧
      Genus2Jacobian.cantorAdd Genus2Jacobian.MumfordDivisor.zero A = A) ∧
   (∀ A, Genus2Jacobian.inD0Orbit A →
      Genus2Jacobian.inD0Orbit (Genus2Jacobian.cantorNeg A) ∧
      Genus2Jacobian.cantorAdd A (Genus2Jacobian.cantorNeg A) =
        Genus2Jacobian.MumfordDivisor.zero ∧
      Genus2Jacobian.cantorAdd (Genus2Jacobian.cantorNeg A) A =
        Genus2Jacobian.MumfordDivisor.zero)) ∧
  (∀ (d tx ty rNum px1 py1 px2 py2 px3 py3 px4 py4 : Int) (num den : Nat),
    1 ≤ num → num < den → 0 < d → 0 < rNum → rNum < d → d < 5 * rNum →
    5 * (rNum * rNum) ≠ d * d →
    tx * tx + ty * ty = rNum * rNum →
    px1 * px1 + py1 * py1 = 5 * (rNum * rNum) →
    px2 * px2 + py2 * py2 = 5 * (rNum * rNum) →
    px3 * px3 + py3 * py3 = 5 * (rNum * rNum) →
    px4 * px4 + py4 * py4 = 5 * (rNum * rNum) →
    let m1 := (d - rNum) * (d - rNum)
    let m2 := (5 * rNum - d) * (5 * rNum - d)
    let d1sq := (d - tx) * (d - tx) + ty * ty
    let d2sq := (d - 5 * tx) * (d - 5 * tx) + (5 * ty) * (5 * ty)
    let B := 2 * (d * d + 5 * (rNum * rNum))
    let n1 := (d - px1) * (d - px1) + py1 * py1
    let n2 := (d - px2) * (d - px2) + py2 * py2
    let n3 := (d - px3) * (d - px3) + py3 * py3
    let n4 := (d - px4) * (d - px4) + py4 * py4
    (0 < EulerFactorNonVanishing.eulerFactorMargin 5 num ∧
     0 < EulerFactorNonVanishing.eulerFactorMargin 5 (den - num)) ∧
    (0 < m1 ∧ m1 ≤ d1sq) ∧
    (0 < m2 ∧ m2 ≤ d2sq) ∧
    (0 < m1 * m2 ∧ m1 * m2 ≤ d1sq * d2sq) ∧
    (0 < (d * d - 5 * (rNum * rNum)) ^ 8 ∧
     (d * d - 5 * (rNum * rNum)) ^ 8 ≤ B ^ 4 * (n1 * n2 * n3 * n4)) ∧
    (∀ X : Int,
      4 * FiniteFieldRH.genus2LPoly X = (2 + 5 * X + 10 * X ^ 2) ^ 2 - 5 * X ^ 2)) ∧
  ((∀ (u v : Int × Int) (du dv : Int),
      du ≠ 0 → dv ≠ 0 →
      WeilZetaBridge.gMul (WeilZetaBridge.gScalar 5) (WeilZetaBridge.gMul u v) =
        WeilZetaBridge.gScalar (du * dv) →
      WeilZetaBridge.gMul
        (WeilZetaBridge.genus2LPolyGHomog v dv)
        (WeilZetaBridge.completedZetaGDenomHomog u du) =
      WeilZetaBridge.gMul
        (WeilZetaBridge.genus2LPolyGHomog u du)
        (WeilZetaBridge.completedZetaGDenomHomog v dv)) ∧
   (∀ (u : Int × Int) (d : Int),
      d ≠ 0 → 5 * WeilZetaBridge.gNormSq u = d * d →
      WeilZetaBridge.completedZetaImagPart u d = 0) ∧
   (5 * WeilZetaBridge.gNormSq (1, 2) = 5 * 5 ∧
    WeilZetaBridge.completedZetaGDenomHomog (1, 2) 5 ≠ (0, 0) ∧
    WeilZetaBridge.completedZetaImagPart (1, 2) 5 = 0)) ∧
  (∀ q a1 a2 n d T : Int,
    GSp4FunctorialityBridge.gsp4StandardEulerPoly q a1 a2 T =
      (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor q a1 a2 T ∧
    GSp4FunctorialityBridge.gsp4StandardEulerHomog q a1 a2 T 1 =
      GSp4FunctorialityBridge.gsp4StandardEulerPoly q a1 a2 T ∧
    GSp4FunctorialityBridge.gsp4StandardEulerHomog q a1 a2 d n =
      -GSp4FunctorialityBridge.gsp4StandardEulerHomog q a1 a2 n d ∧
    GSp4FunctorialityBridge.gsp4StdRecipEval q a1 a2 T =
      -GSp4FunctorialityBridge.gsp4StandardEulerPoly q a1 a2 T ∧
    GSp4FunctorialityBridge.gsp4StandardEulerPoly q a1 a2 1 = 0) ∧
  (∀ T : Int,
    GSp4FunctorialityBridge.gsp4SpinEulerPoly 5
        (-FiniteFieldRH.genus2TraceA1) FiniteFieldRH.genus2TraceA2 T =
      FiniteFieldRH.genus2LPoly T ∧
    GSp4FunctorialityBridge.gsp4SpinEulerPoly 5
        (-FiniteFieldRH.genus2TraceA1) FiniteFieldRH.genus2TraceA2 1 =
      FiniteFieldRH.cardJacobianGenus2F5 ∧
    Genus2Jacobian.cantorSmul 71 Genus2Jacobian.D0 =
      Genus2Jacobian.MumfordDivisor.zero ∧
    GSp4FunctorialityBridge.gsp4StdQuarticCofactor 5
        (-FiniteFieldRH.genus2TraceA1) FiniteFieldRH.genus2TraceA2 T =
      5 * GSp4FunctorialityBridge.cyclotomic10Poly T ∧
    GSp4FunctorialityBridge.gsp4StandardEulerPoly 5
        (-FiniteFieldRH.genus2TraceA1) FiniteFieldRH.genus2TraceA2 T =
      5 * (1 - T) * GSp4FunctorialityBridge.cyclotomic10Poly T ∧
    GSp4FunctorialityBridge.gsp4StandardEulerPoly 5 (-5) 15 T =
      5 - 10 * T + 10 * T ^ 2 - 10 * T ^ 3 + 10 * T ^ 4 - 5 * T ^ 5) ∧
  ((∀ T : Int,
      (1 - T) * GSp4FunctorialityBridge.cyclotomic10Poly T *
        ((1 + T) * GSp4FunctorialityBridge.cyclotomic5Poly T) = 1 - T ^ 10) ∧
   (∀ T : Int,
      GSp4FunctorialityBridge.gsp4StandardEulerPoly 5 (-5) 15 T *
        ((1 + T) * GSp4FunctorialityBridge.cyclotomic5Poly T) = 5 * (1 - T ^ 10)) ∧
   (∀ T : Int, 0 < GSp4FunctorialityBridge.cyclotomic10Poly T) ∧
   (FiniteFieldRH.genus2TraceA1 * FiniteFieldRH.genus2TraceA1 ≤ 16 * 5) ∧
   (∀ s d : Int, 0 < d → s * s ≤ 5 * (d * d) →
     ((5 * d + s) * (5 * d + s) - 20 * ((2 * d) * (2 * d)) < 0 ∧
      (5 * d - s) * (5 * d - s) - 20 * ((2 * d) * (2 * d)) < 0))) ∧
  (GSp4FunctorialityBridge.thetaRamanujan <
      GSp4FunctorialityBridge.thetaKimSarnakSym4 ∧
   GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      GSp4FunctorialityBridge.thetaKimShahidiSym3 ∧
   GSp4FunctorialityBridge.thetaKimShahidiSym3 <
      GSp4FunctorialityBridge.thetaGelbartJacquetSym2 ∧
   GSp4FunctorialityBridge.thetaGelbartJacquetSym2 <
      GSp4FunctorialityBridge.thetaSelberg ∧
   GSp4FunctorialityBridge.thetaSelberg <
      GSp4FunctorialityBridge.thetaConvexity) ∧
  (QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaConvexity)
      (QuasiRiemann.QRat.ofInt 0) ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaSelberg)
      (QuasiRiemann.QRat.mk' 3 16) ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaGelbartJacquetSym2)
      (QuasiRiemann.QRat.mk' 21 100) ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimShahidiSym3)
      (QuasiRiemann.QRat.mk' 77 324) ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QuasiRiemann.QRat.mk' 975 4096) ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaRamanujan)
      (QuasiRiemann.QRat.mk' 1 4) ∧
   GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaSelberg <
      GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaGelbartJacquetSym2 ∧
   GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaGelbartJacquetSym2 <
      GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimShahidiSym3 ∧
   GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimShahidiSym3 <
      GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimSarnakSym4 ∧
   GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      GSp4FunctorialityBridge.selbergLambda1
        GSp4FunctorialityBridge.thetaRamanujan ∧
   QuasiRiemann.QRat.mk' 3 16 < QuasiRiemann.QRat.mk' 21 100 ∧
   QuasiRiemann.QRat.mk' 21 100 < QuasiRiemann.QRat.mk' 77 324 ∧
   QuasiRiemann.QRat.mk' 77 324 < QuasiRiemann.QRat.mk' 975 4096 ∧
   QuasiRiemann.QRat.mk' 975 4096 < QuasiRiemann.QRat.mk' 1 4 ∧
   QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1
          GSp4FunctorialityBridge.thetaKimSarnakSym4 -
        GSp4FunctorialityBridge.selbergLambda1
          GSp4FunctorialityBridge.thetaKimShahidiSym3)
      (QuasiRiemann.QRat.mk' 127 331776) ∧
   QuasiRiemann.QRat.ofInt 0 <
      GSp4FunctorialityBridge.selbergLambda1
          GSp4FunctorialityBridge.thetaKimSarnakSym4 -
        GSp4FunctorialityBridge.selbergLambda1
          GSp4FunctorialityBridge.thetaKimShahidiSym3)

/-- Zero-axiom certificate for Hasse-Weil RH, genus-2 Jacobian, completed zeta,
and `GSp(4) -> SO(5)` functoriality + Selberg / Kim-Sarnak ladder. -/
theorem finiteFieldWeil_provenance_certified : FiniteFieldWeilProvenance :=
  ⟨FiniteFieldRH.hasse_weil_riemann_hypothesis,
   FiniteFieldRH.genus2_frob_negative_discriminants,
   FiniteFieldRH.genus2_L_at_1_qrat,
   Genus2Jacobian.jacobian_group_axioms_on_orbit,
   fun d tx ty rNum px1 py1 px2 py2 px3 py3 px4 py4 num den
     hnum hden hd hr hrd h5r hoff hnormT h1 h2 h3 h4 =>
     WeilZetaBridge.weil_zeta_punctured_strip_regular_and_nonzero
       d tx ty rNum px1 py1 px2 py2 px3 py3 px4 py4 num den
       hnum hden hd hr hrd h5r hoff hnormT h1 h2 h3 h4,
   WeilZetaBridge.genus2_completed_zeta_reflection,
   GSp4FunctorialityBridge.gsp4_std_functional_equation,
   GSp4FunctorialityBridge.genus2_f5_so5_cyclotomic_lift,
   GSp4FunctorialityBridge.genus2_f5_so5_ramanujan_tempered,
   GSp4FunctorialityBridge.kim_sarnak_ramanujan_ladder_strict,
   GSp4FunctorialityBridge.selberg_laplacian_eigenvalue_ladder⟩

-- =============================================================================
-- Parts 9-10: Universal NTT, 192-Digit Karatsuba CRT-NTT, & 4-Prime Garner
-- =============================================================================

/-- Parts 9-10 provenance specification bundling 4-point cyclic NTT convolution over `F_17`,
universal 192-digit Karatsuba CRT-NTT multiplication, Fermat-tower modulus `M_4 = 1,431,655,765`,
4-channel Garner inverses `(7, 127, 32767)`, Garner roundtrip soundness, and sharp
convolution wrap-around thresholds (`B ≤ 18918 / 13377 / 9459`). -/
def CrtNttProvenance : Prop :=
  (∀ a b : NttArithmetic.Vec4,
    NttArithmetic.intt4 17 13 13
      (NttArithmetic.pointwiseMul4 17
        (NttArithmetic.ntt4 17 4 a) (NttArithmetic.ntt4 17 4 b)) =
      NttArithmetic.cyclicConv4 17 a b) ∧
  (∀ A B : CrtNtt.Vec32,
    CrtNtt.isNormalizedVec32 A → CrtNtt.isNormalizedVec32 B →
    CrtNtt.evalDigits1000Vec64 (CrtNtt.karatsubaCrtNttMul192 A B) =
      CrtNtt.evalDigits1000Vec32 A * CrtNtt.evalDigits1000Vec32 B) ∧
  (CrtNtt.fermatTowerMod4 = 1431655765 ∧
   CrtNtt.fermatTowerMod4 = EulerFactorNonVanishing.fermatTowerPrimes.prod ∧
   3 * CrtNtt.fermatTowerMod4 = 2 ^ 32 - 1 ∧
   2 ^ 30 < CrtNtt.fermatTowerMod4 ∧
   CrtNtt.fermatTowerMod4 < 2 ^ 31) ∧
  ((5 * 7) % 17 = 1 ∧ (85 * 127) % 257 = 1 ∧ (21845 * 32767) % 65537 = 1) ∧
  (∀ x : Nat, x < CrtNtt.fermatTowerMod4 →
    CrtNtt.garnerReconstruct4 (x % 5) (x % 17) (x % 257) (x % 65537) = x) ∧
  ((4 * (18918 * 18918) = 1431562896 ∧
    4 * (18918 * 18918) < CrtNtt.fermatTowerMod4 ∧
    CrtNtt.fermatTowerMod4 < 4 * (18919 * 18919)) ∧
   (8 * (13377 * 13377) = 1431553032 ∧
    8 * (13377 * 13377) < CrtNtt.fermatTowerMod4 ∧
    CrtNtt.fermatTowerMod4 < 8 * (13378 * 13378)) ∧
   (16 * (9459 * 9459) = 1431562896 ∧
    16 * (9459 * 9459) < CrtNtt.fermatTowerMod4 ∧
    CrtNtt.fermatTowerMod4 < 16 * (9460 * 9460)) ∧
   (∀ (a b : Nat → Nat) (idx : Nat → Nat),
     (∀ i, i < 4 → a i ≤ 18918) → (∀ j, j < 4 → b j ≤ 18918) →
     (∀ i, i < 4 → idx i < 4) →
     let c := CrtNtt.convPairSum a b idx 4
     c < CrtNtt.fermatTowerMod4 ∧
     CrtNtt.garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c) ∧
   (∀ (a b : Nat → Nat) (idx : Nat → Nat),
     (∀ i, i < 8 → a i ≤ 13377) → (∀ j, j < 8 → b j ≤ 13377) →
     (∀ i, i < 8 → idx i < 8) →
     let c := CrtNtt.convPairSum a b idx 8
     c < CrtNtt.fermatTowerMod4 ∧
     CrtNtt.garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c) ∧
   (∀ (a b : Nat → Nat) (idx : Nat → Nat),
     (∀ i, i < 16 → a i ≤ 9459) → (∀ j, j < 16 → b j ≤ 9459) →
     (∀ i, i < 16 → idx i < 16) →
     let c := CrtNtt.convPairSum a b idx 16
     c < CrtNtt.fermatTowerMod4 ∧
     CrtNtt.garnerReconstruct4 (c % 5) (c % 17) (c % 257) (c % 65537) = c))

/-- Zero-axiom certificate for universal NTT, 192-digit Karatsuba CRT-NTT, and Garner CRT. -/
theorem crtNtt_provenance_certified : CrtNttProvenance :=
  ⟨NttArithmetic.cyclic_conv4_ntt_universal_F17,
   CrtNtt.karatsubaCrtNttMul192_universal_sound,
   CrtNtt.fermat_tower_crt_modulus_bounds,
   CrtNtt.garner_4ch_inverses_sound,
   CrtNtt.garnerReconstruct4_sound,
   CrtNtt.fermat_tower_conv_bound_certs⟩

-- =============================================================================
-- Part 11: 100-Digit Chudnovsky Pi Provenance
-- =============================================================================

/-- Part 11 provenance specification bundling arbitrary-size signed CRT-NTT multiplication,
universal Chudnovsky truncation bracketing (`m ≥ 8`), and exact 100-digit `π`. -/
def ChudnovskyPiProvenance : Prop :=
  (∀ x y : Int, PiChudnovsky.intMulBigViaCrtNtt x y = x * y) ∧
  (∀ m : Nat, 8 ≤ m →
    (PiChudnovsky.piLower105 : Int) * 10 ^ 5 * (PiChudnovsky.chudPartialSum m).num ≤
      (426880 * (PiChudnovsky.sqrt10005Scaled110 : Int)) *
        ((PiChudnovsky.chudPartialSum m).den : Int) ∧
    (426880 * ((PiChudnovsky.sqrt10005Scaled110 : Int) + 1)) *
        ((PiChudnovsky.chudPartialSum m).den : Int) ≤
      (PiChudnovsky.piUpper105 : Int) * 10 ^ 5 * (PiChudnovsky.chudPartialSum m).num) ∧
  (PiChudnovsky.piLower105 / 10 ^ 5 = PiChudnovsky.piDigits100 ∧
   PiChudnovsky.piUpper105 / 10 ^ 5 = PiChudnovsky.piDigits100 ∧
   PiChudnovsky.piDigits100 =
     314159265358979323846264338327950288419716939937510 * 10 ^ 50 +
     58209749445923078164062862089986280348253421170679)

/-- Zero-axiom certificate for CRT-NTT big-integer multiplication and 100-digit Chudnovsky `π`. -/
theorem chudnovskyPi_provenance_certified : ChudnovskyPiProvenance :=
  ⟨PiChudnovsky.intMulBigViaCrtNtt_eq_mul,
   PiChudnovsky.pi_105_traps_all_chudnovsky_truncations,
   PiChudnovsky.pi_100_digits_certified⟩

-- =============================================================================
-- Master Zero-Axiom Provenance Theorem (All 11 CLI Parts)
-- =============================================================================

/-- Master conjunction theorem uniting every core domain certificate across all 11 CLI parts
of `leanasm` (`MiniVM`, `Collatz`, `Yang-Mills`, `QuasiRiemann`, `Euler-RNS`, `FiniteFieldRH` /
`Genus2Jacobian` / `WeilZeta`, `CrtNtt`, and `PiChudnovsky`), proved with ZERO `Classical.choice`
and ZERO `sorryAx`. -/
theorem leanasm_full_provenance_certified :
    MiniVmProvenance ∧
    CollatzProvenance ∧
    YangMillsProvenance ∧
    QuasiRiemannProvenance ∧
    EulerRnsProvenance ∧
    FiniteFieldWeilProvenance ∧
    CrtNttProvenance ∧
    ChudnovskyPiProvenance :=
  ⟨miniVm_provenance_certified,
   collatz_provenance_certified,
   yangMills_provenance_certified,
   quasiRiemann_provenance_certified,
   eulerRns_provenance_certified,
   finiteFieldWeil_provenance_certified,
   crtNtt_provenance_certified,
   chudnovskyPi_provenance_certified⟩

end LeanAsm

-- end of file: leanasm/src/LeanAsm/ProvenanceSummary.lean
