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
import LeanAsm.QuasiRiemann.ParametricQrhLadder
import LeanAsm.QuasiRiemann.ContractionReflectionBridge
import LeanAsm.QuasiRiemann.DyadicAbelBridge
import LeanAsm.QuasiRiemann.HighTruncDyadicAbelWeave
import LeanAsm.QuasiRiemann.MollifierVariationalBridge
import LeanAsm.QuasiRiemann.Valuation.Ultrametric
import LeanAsm.QuasiRiemann.Valuation.Contraction
import LeanAsm.QuasiRiemann.Valuation.Hensel
import LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic
import LeanAsm.QuasiRiemann.Valuation.EisensteinWeights
import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics
import LeanAsm.QuasiRiemann.Valuation.QsdHenselTower
import LeanAsm.QuasiRiemann.Valuation.RNS
import LeanAsm.QuasiRiemann.QsdAlgebraBridge
import LeanAsm.QuasiRiemann.GaussianQsdBridge
import LeanAsm.QuasiRiemann.RnsGaussianNormBridge
import LeanAsm.QuasiRiemann.Qsd1LogDerivStripBridge
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
import LeanAsm.ArtinFermatBridge
import LeanAsm.ArtinShortIntervalBridge
import LeanAsm.ConstructiveOpenaiBridge
import LeanAsm.EllipticModularityBridge
import LeanAsm.LanglandsRankinSelbergBridge
import LeanAsm.ProthNttTowerBridge
import LeanAsm.Genus2MultiPrimeWeil
import LeanAsm.Genus2WeilGSp4Weave
import LeanAsm.QuasiRiemann.Genus2HenselPreperiodicWeave
import LeanAsm.QuasiRiemann.PreperiodicQsd1StripWeave
import LeanAsm.QuasiRiemann.PreperiodicVariationalBridge
import LeanAsm.QuasiRiemann.Qsd1IdempotentDyadicAbelWeave
import LeanAsm.QuasiRiemann.RankinSelbergGSp4Sub78Bridge
import LeanAsm.QuasiRiemann.JacobianRankinSelbergWeave
import LeanAsm.QuasiRiemann.LuckyBeurlingStripWeave
import LeanAsm.QuasiRiemann.LuckyQrh78Strip
import LeanAsm.QuasiRiemann.SieveSequenceStripWeave
import LeanAsm.MiniVMRnsHenselWeave

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
  (∀ cfg ∈ MiniVMNttBridge.fermatTowerNtt8Specs, cfg.Valid) ∧
  (∀ cfg ∈ MiniVMNttBridge.fermatTowerNtt8Specs,
    ∀ (s : MiniVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 : Nat),
      x0 < cfg.p → x1 < cfg.p → x2 < cfg.p → x3 < cfg.p →
      x4 < cfg.p → x5 < cfg.p → x6 < cfg.p → x7 < cfg.p →
      s.r0 = x0 → s.r1 = x1 → s.r2 = x2 → s.r3 = x3 →
      s.r4 = x4 → s.r5 = x5 → s.r6 = x6 → s.r7 = x7 →
      let s1 := MiniVM.runProgram s (MiniVMNttBridge.ntt8AsmFermat cfg.p cfg.w1 cfg.w2 cfg.w3)
      let s2 := MiniVM.runProgram s1
        (MiniVMNttBridge.intt8AsmFermat cfg.p cfg.inv8 cfg.iw1 cfg.iw2 cfg.iw3)
      (⟨s2.r0, s2.r1, s2.r2, s2.r3, s2.r4, s2.r5, s2.r6, s2.r7⟩ : CrtNtt.Vec8) =
        ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩) ∧
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
   MiniVMNttBridge.fermatTowerNtt8Specs_valid,
   MiniVMNttBridge.fermatTowerNtt8_asm_roundtrip_certs,
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

/-- Parts 3-4 provenance specification for `Z_2` Wilson plaquette gauge invariance,
`Q_8 ⊂ SU(2)` trace conjugation invariance, and the pure-constructive `openai-20261028`
lattice/holonomy/foliation bridge. -/
def YangMillsProvenance : Prop :=
  (∀ (g : YangMillsToy.GaugeTransform) (U : YangMillsToy.GaugeConfig)
      (x : YangMillsToy.Point4) (μ ν : YangMillsToy.Dir),
    YangMillsToy.plaquetteAction (YangMillsToy.gaugeTransform g U) x μ ν =
      YangMillsToy.plaquetteAction U x μ ν) ∧
  (∀ (g u : YangMillsQ8.Q8),
    YangMillsQ8.Q8.reTrace (YangMillsQ8.Q8.mul (YangMillsQ8.Q8.mul g u) (YangMillsQ8.Q8.inv g)) =
      YangMillsQ8.Q8.reTrace u) ∧
  (∀ {G : Type} (L : ConstructiveOpenaiBridge.LatticeGroup G)
      (g : ConstructiveOpenaiBridge.GaugeTransform G)
      (U : ConstructiveOpenaiBridge.GaugeConnection G)
      (p : ConstructiveOpenaiBridge.LatticePlaquette4),
    ConstructiveOpenaiBridge.plaquetteHolonomy L
        (ConstructiveOpenaiBridge.gaugeTransformConnection L g U) p =
      L.mul (L.mul (g p.site) (ConstructiveOpenaiBridge.plaquetteHolonomy L U p))
        (L.inv (g p.site))) ∧
  (∀ (g : ConstructiveOpenaiBridge.GaugeTransform YangMillsQ8.Q8)
      (U : ConstructiveOpenaiBridge.GaugeConnection YangMillsQ8.Q8)
      (p : ConstructiveOpenaiBridge.LatticePlaquette4),
    YangMillsQ8.Q8.reTrace
        (ConstructiveOpenaiBridge.plaquetteHolonomy ConstructiveOpenaiBridge.q8LatticeGroup
          (ConstructiveOpenaiBridge.gaugeTransformConnection
            ConstructiveOpenaiBridge.q8LatticeGroup g U) p) =
      YangMillsQ8.Q8.reTrace
        (ConstructiveOpenaiBridge.plaquetteHolonomy ConstructiveOpenaiBridge.q8LatticeGroup U p)) ∧
  (∀ (U : ConstructiveOpenaiBridge.GaugeConnection YangMillsQ8.Q8)
      (p : ConstructiveOpenaiBridge.Face) (s : ConstructiveOpenaiBridge.SignedSym4)
      (t : ConstructiveOpenaiBridge.Cover4),
    YangMillsQ8.Q8.reTrace
        (ConstructiveOpenaiBridge.faceValue ConstructiveOpenaiBridge.q8LatticeGroup
          (ConstructiveOpenaiBridge.pullConnection
            ConstructiveOpenaiBridge.q8LatticeGroup s t U) p) =
      YangMillsQ8.Q8.reTrace
        (ConstructiveOpenaiBridge.faceValue ConstructiveOpenaiBridge.q8LatticeGroup U
          (ConstructiveOpenaiBridge.Face.send s t p))) ∧
  (∀ (r : Nat) (o : ConstructiveOpenaiBridge.Cover4) {i : ConstructiveOpenaiBridge.Axis}
      {l : List ConstructiveOpenaiBridge.Axis},
    i ∉ l → ∀ (f : ConstructiveOpenaiBridge.Cover4 → Int),
    ConstructiveOpenaiBridge.listSum (ConstructiveOpenaiBridge.slabSites r o (l ++ [i])) f =
      ConstructiveOpenaiBridge.listSum (ConstructiveOpenaiBridge.layerRange r)
        (fun z => ConstructiveOpenaiBridge.listSum
          (ConstructiveOpenaiBridge.slabSites r (o.update i z) l) f)) ∧
  (∀ (l : List ConstructiveOpenaiBridge.Axis) (x y : ConstructiveOpenaiBridge.Cover4),
    ConstructiveOpenaiBridge.axisRoute y x l.reverse =
      ConstructiveOpenaiBridge.walkReverse (ConstructiveOpenaiBridge.axisRoute x y l)) ∧
  (∀ (x : ConstructiveOpenaiBridge.Cover4) (a b : ConstructiveOpenaiBridge.Axis),
    ConstructiveOpenaiBridge.walkVisits x (ConstructiveOpenaiBridge.squareWalk a b) =
      [x,
       ConstructiveOpenaiBridge.Cover4.add x (ConstructiveOpenaiBridge.Cover4.step a),
       ConstructiveOpenaiBridge.Cover4.add
         (ConstructiveOpenaiBridge.Cover4.add x (ConstructiveOpenaiBridge.Cover4.step a))
         (ConstructiveOpenaiBridge.Cover4.step b),
       ConstructiveOpenaiBridge.Cover4.add x (ConstructiveOpenaiBridge.Cover4.step b),
       x]) ∧
  (∀ (s : ConstructiveOpenaiBridge.SignedSym4) (t : ConstructiveOpenaiBridge.Cover4)
      (p1 p2 : ConstructiveOpenaiBridge.Face),
    ConstructiveOpenaiBridge.Face.send s t p1 = ConstructiveOpenaiBridge.Face.send s t p2 →
      p1 = p2)

/-- Zero-axiom certificate for 4D lattice gauge invariance across `Z_2`, `Q_8`, and the
pure-constructive `openai-20261028` lattice/holonomy/foliation bridge. -/
theorem yangMills_provenance_certified : YangMillsProvenance :=
  ⟨YangMillsToy.plaquette_action_gauge_invariant,
   YangMillsQ8.q8_trace_conjugation_invariant,
   fun L g U p => ConstructiveOpenaiBridge.holonomy_gauge_covariant L g U p,
   ConstructiveOpenaiBridge.q8_plaquette_holonomy_gauge_invariant,
   ConstructiveOpenaiBridge.q8_send_price_trace_invariant,
   fun r o {_ _} hi f => ConstructiveOpenaiBridge.slab_sum_foliation r o hi f,
   ConstructiveOpenaiBridge.axisRoute_reverse,
   ConstructiveOpenaiBridge.squareWalk_corners,
   ConstructiveOpenaiBridge.Face.injective_send⟩

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
   QuasiRiemann.highTruncSpec_1e18_N512.HasCertifiedNonVanishing) ∧
  (∀ (spec : QuasiRiemann.CauchyBoxLowerBoundSpec) (centerMag pointMag dist : Nat),
     spec.centerLower ≤ centerMag →
     dist ≤ spec.radius →
     Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤ spec.lipschitzBound * dist →
     spec.centerLower / 2 ≤ pointMag ∧ (spec.centerLower + 1) / 2 ≤ pointMag ∧
       0 < pointMag ∧ spec.lipschitzBound * spec.radius < spec.centerLower) ∧
  (QuasiRiemann.nestedBox1e18_3.SubBox QuasiRiemann.nestedBox1e18_0 ∧
   QuasiRiemann.nestedBox1e18_3.sLo6 = 500250 ∧
   QuasiRiemann.QRat.eqv (QuasiRiemann.QRat.mk' 500250 1000000 (by decide))
     (QuasiRiemann.QRat.mk' 1 2 (by decide) + QuasiRiemann.QRat.mk' 1 4000 (by decide)) ∧
   QuasiRiemann.nestedBox1e18_0.radL1 = 96000 ∧
   QuasiRiemann.nestedBox1e18_1.radL1 = 48000 ∧
   QuasiRiemann.nestedBox1e18_2.radL1 = 24000 ∧
   QuasiRiemann.nestedBox1e18_3.radL1 = 12000 ∧
   2 ^ 3 * QuasiRiemann.driftSeq1e18 3 ≤ QuasiRiemann.driftSeq1e18 0 ∧
   (∀ centerMag pointMag s6 t6 : Nat,
     19200000 ≤ centerMag →
     QuasiRiemann.InBox2D QuasiRiemann.nestedBox1e18_3.sLo6
       QuasiRiemann.nestedBox1e18_3.sHi6 QuasiRiemann.nestedBox1e18_3.tLo6
       QuasiRiemann.nestedBox1e18_3.tHi6 s6 t6 →
     Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤
       100 * (((s6 : Int) - (QuasiRiemann.nestedBox1e18_3.sMid6 : Int)).natAbs +
         ((t6 : Int) - (QuasiRiemann.nestedBox1e18_3.tMid6 : Int)).natAbs) →
     9600000 ≤ pointMag ∧ 0 < pointMag ∧
       QuasiRiemann.InBox2D QuasiRiemann.nestedBox1e18_0.sLo6
         QuasiRiemann.nestedBox1e18_0.sHi6 QuasiRiemann.nestedBox1e18_0.tLo6
         QuasiRiemann.nestedBox1e18_0.tHi6 s6 t6) ∧
   (∀ s6 t6 : Nat,
     QuasiRiemann.InBox2D QuasiRiemann.nestedBox1e18_3.sLo6
       QuasiRiemann.nestedBox1e18_3.sHi6 QuasiRiemann.nestedBox1e18_3.tLo6
       QuasiRiemann.nestedBox1e18_3.tHi6 s6 t6 →
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
         0 < zRe * zRe + zIm * zIm ∧ (zRe ≠ 0 ∨ zIm ≠ 0))))

/-- Parametric beyond-`7/8` QRH binary ladder (`qrhShortExponent k = (2^k + 1) / 2^(k+1)`),
dual mollifier/strip ascent, density benchmarks, `kim_sarnak_amplified_qrh_step`, and concrete
`7/64` Kim-Sarnak short-interval certificates (`θ = 17/32` at `10^96 + 10^57`). -/
def ParametricQrhLadderProp : Prop :=
  (∀ k : Nat,
    QuasiRiemann.QRat.mk' 1 2 (by decide) < QuasiRiemann.qrhShortExponent (k + 1) ∧
    QuasiRiemann.qrhShortExponent (k + 1) < QuasiRiemann.qrhShortExponent k) ∧
  (∀ k : Nat, 2 ≤ k →
    QuasiRiemann.qrhShortExponent k < QuasiRiemann.qrhThresholdSevenEighths) ∧
  (QuasiRiemann.QRat.eqv
      (QuasiRiemann.QRat.ofInt 1 - QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 3 4))
      (QuasiRiemann.QRat.mk' 11 26) ∧
    QuasiRiemann.qrhShortExponent 3 < QuasiRiemann.shortIntervalDensityExponent 30 13) ∧
  (∀ k : Nat,
    QuasiRiemann.qrhDualFraction k < QuasiRiemann.qrhDualFraction (k + 1) ∧
    QuasiRiemann.qrhDualFraction (k + 1) < QuasiRiemann.QRat.ofInt 1) ∧
  (∀ k : Nat,
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.qrhThresholdFromMollifier (QuasiRiemann.qrhDualFraction k))
      (QuasiRiemann.qrhShortExponent (k + 1))) ∧
  (∀ (spec : QuasiRiemann.ParametricQrhBridgeSpec) (autoTheta' : QuasiRiemann.QRat),
    (0 : Int) ≤ autoTheta'.num →
    autoTheta' < spec.autoTheta →
    GSp4FunctorialityBridge.selbergLambda1 spec.autoTheta <
      GSp4FunctorialityBridge.selbergLambda1 autoTheta' ∧
    QuasiRiemann.qrhFromAutomorphic autoTheta' <
      QuasiRiemann.qrhFromAutomorphic spec.autoTheta ∧
    spec.nextShortSpec.thetaQRat < spec.shortSpec.thetaQRat ∧
    spec.nextShortSpec.thetaQRat < QuasiRiemann.qrhThresholdSevenEighths) ∧
  (QuasiRiemann.QRat.eqv
      (QuasiRiemann.qrhFromAutomorphic GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QuasiRiemann.QRat.mk' 39 64 (by decide)) ∧
    QuasiRiemann.QRat.eqv
      (GSp4FunctorialityBridge.selbergLambda1 GSp4FunctorialityBridge.thetaKimSarnakSym4)
      (QuasiRiemann.QRat.mk' 975 4096 (by decide)) ∧
    QuasiRiemann.kimSarnakBridgeSpec.nextShortSpec.HasGuaranteedPrime)

/-- Part 5 rational-contraction and higher-truncation N=256,512 strip export
into zero-density bounds (`UltraDeep72` Part 19 and `ZeroDensityBridge` Part 7). -/
def HighTruncRationalContractionProp : Prop :=
  (∀ (rSpec : QuasiRiemann.RationalBoxContractionSpec)
      (centerMag pointMag dist currDrift nextDrift : Nat),
      rSpec.centerLower ≤ centerMag →
      dist ≤ rSpec.radius →
      (rSpec.radius - rSpec.deltaShrink) * Int.natAbs ((centerMag : Int) - (pointMag : Int)) ≤
        rSpec.lipNumerator * dist →
      rSpec.qDen * nextDrift ≤ rSpec.qNum * currDrift →
      0 < pointMag ∧ (0 < currDrift → nextDrift < currDrift)) ∧
  (3 ^ 2 * QuasiRiemann.driftSeq1e12_N256 2 ≤ 1 ^ 2 * QuasiRiemann.driftSeq1e12_N256 0 ∧
    QuasiRiemann.dirichletGradBoundScaled6_512 500500 256 = 117284435 ∧
    QuasiRiemann.highTruncSpec_1e12_N256.HasCertifiedNonVanishing) ∧
  (5 ^ 2 * QuasiRiemann.driftSeq1e18_N512 2 ≤ 2 ^ 2 * QuasiRiemann.driftSeq1e18_N512 0 ∧
    QuasiRiemann.dirichletGradBoundScaled6_512 500250 512 = 195620879 ∧
    QuasiRiemann.highTruncSpec_1e18_N512.HasCertifiedNonVanishing) ∧
  (∀ (strip : QuasiRiemann.CertifiedStripWidthSpec)
      (zdSpec : QuasiRiemann.ZeroDensitySpec) (θ : QuasiRiemann.QRat),
      strip.sigmaLo < θ →
      θ < QuasiRiemann.QRat.ofInt 1 →
      QuasiRiemann.QRat.mk' 1 2 < strip.sigmaLo ∧
        zdSpec.exponent θ < zdSpec.exponent strip.sigmaLo ∧
        strip.rectSpec.HasCertifiedNonVanishing) ∧
  (QuasiRiemann.certifiedStrip050025_N512.halfWidth <
      QuasiRiemann.certifiedStrip05005_N256.halfWidth ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdGuthMaynard.exponent QuasiRiemann.certifiedStrip050025_N512.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 5200) ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdHuxley.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdHuxley.exponent QuasiRiemann.certifiedStrip050025_N512.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 5000)) ∧
  ((QuasiRiemann.twoPiInterval108.hi - QuasiRiemann.twoPiInterval108.lo = 2 ∧
    QuasiRiemann.twoPiInterval108.lo = (2 * PiChudnovsky.piLower108 : Int) ∧
    QuasiRiemann.twoPiInterval108.hi = (2 * PiChudnovsky.piUpper108 : Int)) ∧
    ∀ (xIv : QuasiRiemann.ScaledInterval108),
      0 ≤ xIv.lo →
      xIv.hi ≤ 8 * (10 ^ 30 + 10) * QuasiRiemann.scale108Int →
      xIv.hi - xIv.lo ≤ 6 * 10 ^ 31 →
      (QuasiRiemann.reduceModTwoPiCentered108 xIv).hi -
        (QuasiRiemann.reduceModTwoPiCentered108 xIv).lo ≤ 10 ^ 32 ∧
      (10 ^ 32 : Int) < 10 ^ 33) ∧
  (3 ^ 2 * QuasiRiemann.driftSeq1e24_N1024 2 ≤ 1 ^ 2 * QuasiRiemann.driftSeq1e24_N1024 0 ∧
    QuasiRiemann.dirichletGradBoundScaled6_2048 500125 1024 = 319421067 ∧
    QuasiRiemann.highTruncSpec_1e24_N1024.HasCertifiedNonVanishing) ∧
  (5 ^ 2 * QuasiRiemann.driftSeq1e30_N2048 2 ≤ 2 ^ 2 * QuasiRiemann.driftSeq1e30_N2048 0 ∧
    QuasiRiemann.dirichletGradBoundScaled6_2048 500062 2048 = 512891320 ∧
    QuasiRiemann.highTruncSpec_1e30_N2048.HasCertifiedNonVanishing) ∧
  (QuasiRiemann.certifiedStrip05000625_N2048.halfWidth <
      QuasiRiemann.certifiedStrip0500125_N1024.halfWidth ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdGuthMaynard.exponent QuasiRiemann.certifiedStrip05000625_N2048.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 20800) ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdHuxley.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdHuxley.exponent QuasiRiemann.certifiedStrip05000625_N2048.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 20000)) ∧
  (QuasiRiemann.certifiedStrip050003125_N2048.halfWidth <
      QuasiRiemann.certifiedStrip05000625_N2048.halfWidth ∧
    QuasiRiemann.certifiedStrip050003125_N2048.sigmaLo <
      QuasiRiemann.certifiedStrip05000625_N2048.sigmaLo ∧
    QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.certifiedStrip050003125_N2048.sigmaLo ∧
    QuasiRiemann.certifiedStrip050003125_N2048.sigmaLo < QuasiRiemann.qrhThresholdSevenEighths ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdGuthMaynard.exponent QuasiRiemann.certifiedStrip050003125_N2048.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 41600) ∧
    QuasiRiemann.QRat.eqv
      (QuasiRiemann.zdHuxley.exponent (QuasiRiemann.QRat.mk' 1 2) -
        QuasiRiemann.zdHuxley.exponent QuasiRiemann.certifiedStrip050003125_N2048.sigmaLo)
      (QuasiRiemann.QRat.mk' 3 40000) ∧
    QuasiRiemann.certifiedStrip050003125_N2048.rectSpec.HasCertifiedNonVanishing) ∧
  ((2 * QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
      QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius ≤
    QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
      (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
        QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink) ∧
   QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
      QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius <
    QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
      (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
        QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink)) ∧
  (QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ≤
      2 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
        QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
   QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
       QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 *
       QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 <
     QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
       QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 *
       QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
   8 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
       QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 ≤
     7 * QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1) ∧
  (QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.margin = 2682997 ∧
   (4 * QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.scaleN) *
       (QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.tailBound *
         QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.tailBound) ≤
     ((2 * QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.denomM) *
       (2 * QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.denomM)) *
       (QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.tailNum *
         QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.gate.tailNum) ∧
   QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
   QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
     QuasiRiemann.highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
   QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo < QuasiRiemann.QRat.mk' 3 4 ∧
   QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
     QuasiRiemann.qrhThresholdSevenEighths ∧
   QuasiRiemann.zdGuthMaynard.exponent
       QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
     QuasiRiemann.zdGuthMaynard.exponent (QuasiRiemann.QRat.mk' 1 2) ∧
   QuasiRiemann.zdHuxley.exponent
       QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
     QuasiRiemann.zdHuxley.exponent (QuasiRiemann.QRat.mk' 1 2) ∧
   QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing ∧
   (QuasiRiemann.highTruncTiles_1e30_N2048.length = 4 ∧
     (∀ t ∈ QuasiRiemann.highTruncTiles_1e30_N2048, QuasiRiemann.IsValidLipTile2D t))))

/-- Constructive `[M, M * 2^k)` dyadic-shell foliation, discrete Abel
summation-by-parts, monotone-weight error contraction, cleared-denominator `1/√N`
quadratic tail gates, and beyond-`7/8` short-interval tightening (Issue #71). -/
def DyadicAbelProvenanceProp : Prop :=
  (∀ (M k : Nat) (f : Nat → Int),
    QuasiRiemann.rangeSumInt f M (M * 2 ^ k) =
      ConstructiveOpenaiBridge.listSum (List.range k) (fun j =>
        ConstructiveOpenaiBridge.listSum (QuasiRiemann.dyadicShell M j) f)) ∧
  (∀ (r : Nat) (o : ConstructiveOpenaiBridge.Cover4) (i : ConstructiveOpenaiBridge.Axis)
     (l : List ConstructiveOpenaiBridge.Axis),
    i ∉ l → ∀ (M k : Nat) (f : ConstructiveOpenaiBridge.Cover4 → Int) (g : Nat → Int),
    ConstructiveOpenaiBridge.listSum (ConstructiveOpenaiBridge.slabSites r o (l ++ [i]))
        (fun x => f x * QuasiRiemann.rangeSumInt g M (M * 2 ^ k)) =
      ConstructiveOpenaiBridge.listSum (ConstructiveOpenaiBridge.layerRange r) (fun z0 =>
        ConstructiveOpenaiBridge.listSum
          (ConstructiveOpenaiBridge.slabSites r (o.update i z0) l) f) *
      ConstructiveOpenaiBridge.listSum (List.range k) (fun j =>
        ConstructiveOpenaiBridge.listSum (QuasiRiemann.dyadicShell M j) g)) ∧
  (∀ (f g : Nat → Int) (a b : Nat), a ≤ b →
    QuasiRiemann.rangeSumInt (fun n => f n * g n) a (b + 1) =
      QuasiRiemann.rangeSumInt f a (b + 1) * g b +
        QuasiRiemann.rangeSumInt
          (fun k => QuasiRiemann.rangeSumInt f a (k + 1) * (g k - g (k + 1))) a b) ∧
  (∀ (a w : Nat → Int) (M N E : Nat), M < N →
    0 ≤ w N →
    (∀ k, M + 1 ≤ k → k < N → w (k + 1) ≤ w k) →
    (∀ k, M ≤ k → k ≤ N → Int.natAbs (QuasiRiemann.partialSumInt a k - (k : Int)) ≤ E) →
    Int.natAbs (QuasiRiemann.rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) -
        QuasiRiemann.rangeSumInt w (M + 1) (N + 1)) ≤
      2 * E * Int.natAbs (w (M + 1))) ∧
  (∀ (spec : QuasiRiemann.ChebyshevRemainderSpec) (s : QuasiRiemann.ShortIntervalChebyshevSpec)
     (psiStep : Nat → Int) (M k : Nat) (gate : QuasiRiemann.SqrtTailGateSpec) (effErr : Nat),
    s.hScaleExp ≤ s.xScaleExp →
    QuasiRiemann.qrhRemainderBoundAtTwoTenPow spec ≤ s.errUpper →
    gate.tailBound = effErr →
    effErr ≤ s.errUpper →
    ∀ (psiX psiXH thetaX thetaXH : Int),
    Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ effErr →
    Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤ effErr →
    (psiXH - psiX) - (thetaXH - thetaX) ≤ (s.primePowerCorr : Int) →
    s.HasGuaranteedPrime →
    QuasiRiemann.rangeSumInt psiStep M (M * 2 ^ k) =
      ConstructiveOpenaiBridge.listSum (List.range k) (fun j =>
        ConstructiveOpenaiBridge.listSum (QuasiRiemann.dyadicShell M j) psiStep) ∧
    gate.denomM * gate.denomM * (effErr * effErr) ≤
      gate.scaleN * (gate.tailNum * gate.tailNum) ∧
    Int.natAbs (psiXH - psiX - ((10 ^ s.hScaleExp : Nat) : Int)) ≤ 2 * effErr ∧
    (0 : Int) < thetaXH - thetaX) ∧
  ((QuasiRiemann.dyadicShellPartition 1 4).flatten = QuasiRiemann.halfOpenRange 1 16 ∧
   QuasiRiemann.shortIntervalQrh1732Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh916Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh58Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh23Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh34Spec.HasGuaranteedPrime) ∧
  (QuasiRiemann.highTruncDyadicAbel1024Spec.margin = 2521997 ∧
   QuasiRiemann.highTruncDyadicAbel2048Spec.margin = 2682997 ∧
   QuasiRiemann.highTruncDyadicAbel1024Spec.strip.rectSpec.HasCertifiedNonVanishing ∧
   QuasiRiemann.highTruncDyadicAbel2048Spec.strip.rectSpec.HasCertifiedNonVanishing ∧
   QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.highTruncDyadicAbel1024Spec.strip.sigmaLo ∧
   QuasiRiemann.highTruncDyadicAbel1024Spec.strip.sigmaLo < QuasiRiemann.QRat.mk' 3 4 ∧
   QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
   QuasiRiemann.highTruncDyadicAbel2048Spec.strip.sigmaLo < QuasiRiemann.QRat.mk' 3 4) ∧
  (QuasiRiemann.highTruncDyadicAbel32000Spec.margin = 2682997 ∧
   QuasiRiemann.highTruncDyadicAbel32000Spec.strip.rectSpec.HasCertifiedNonVanishing ∧
   QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.highTruncDyadicAbel32000Spec.strip.sigmaLo ∧
   QuasiRiemann.highTruncDyadicAbel32000Spec.strip.sigmaLo <
     QuasiRiemann.highTruncDyadicAbel2048Spec.strip.sigmaLo ∧
   QuasiRiemann.highTruncDyadicAbel32000Spec.strip.sigmaLo <
     QuasiRiemann.qrhThresholdSevenEighths)

/-- Reusable Part 5 specification for closed-loop dyadic-Abel rungs (`k = 5, 6`)
and two-piece `QRat` variational mollifier optimization (`Issue #78`). -/
def MollifierVariationalProp : Prop :=
  (∀ (kCurr kNext : Nat) (specNext : QuasiRiemann.ChebyshevRemainderSpec)
      (sNext : QuasiRiemann.ShortIntervalChebyshevSpec)
      (_hLadderDrop : QuasiRiemann.qrhShortExponent kNext < QuasiRiemann.qrhShortExponent kCurr)
      (a wNum : Nat → Int) (M N E D : Nat) (_hMN : M < N) (hD : 0 < D)
      (_hw0 : 0 ≤ wNum N)
      (_hwAnti : ∀ k, M + 1 ≤ k → k < N → wNum (k + 1) ≤ wNum k)
      (_hRem : ∀ k, M ≤ k → k ≤ N → Int.natAbs (QuasiRiemann.partialSumInt a k - (k : Int)) ≤ E)
      (gate : QuasiRiemann.InvSqrtTailGateSpec)
      (_hHleX : sNext.hScaleExp ≤ sNext.xScaleExp)
      (_hEnv : QuasiRiemann.qrhRemainderBoundAtTwoTenPow specNext ≤ sNext.errUpper)
      (psiX psiXH thetaX thetaXH : Int)
      (_hBX : Int.natAbs (psiX - ((10 ^ sNext.xScaleExp : Nat) : Int)) ≤ sNext.errUpper)
      (_hBXH : Int.natAbs (psiXH - ((10 ^ sNext.xScaleExp + 10 ^ sNext.hScaleExp : Nat) : Int)) ≤
        sNext.errUpper)
      (_hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (sNext.primePowerCorr : Int))
      (_hPrime : sNext.HasGuaranteedPrime),
    QuasiRiemann.QRat.mk'
      (Int.natAbs (QuasiRiemann.rangeSumInt (fun n => a n * wNum n) (M + 1) (N + 1) -
        QuasiRiemann.rangeSumInt wNum (M + 1) (N + 1)) : Int) D hD ≤
      QuasiRiemann.QRat.mk' ((2 * E * Int.natAbs (wNum (M + 1)) : Nat) : Int) D hD ∧
    (4 * gate.scaleN) * (gate.tailBound * gate.tailBound) ≤
      ((2 * gate.denomM) * (2 * gate.denomM)) * (gate.tailNum * gate.tailNum) ∧
    (0 : Int) < thetaXH - thetaX) ∧
  (QuasiRiemann.QRat.eqv (QuasiRiemann.qrhShortExponent 5) (QuasiRiemann.QRat.mk' 33 64) ∧
   QuasiRiemann.QRat.eqv (QuasiRiemann.qrhShortExponent 6) (QuasiRiemann.QRat.mk' 65 128) ∧
   QuasiRiemann.shortIntervalQrh3364Spec.HasGuaranteedPrime ∧
   QuasiRiemann.shortIntervalQrh65128Spec.HasGuaranteedPrime) ∧
  (∀ m : QuasiRiemann.TwoPieceMollifierSpec,
    QuasiRiemann.QRat.ofInt 1 ≤ QuasiRiemann.mollifierDirichletEnergy m.c1 m.c2) ∧
  (∀ m : QuasiRiemann.TwoPieceMollifierSpec,
    (0 : Int) < m.c1.num → (0 : Int) < m.c2.num →
    QuasiRiemann.mollifierVariationalEnergy m.c1 m.c2 < QuasiRiemann.QRat.ofInt 1) ∧
  (QuasiRiemann.QRat.eqv
      (QuasiRiemann.mollifierVariationalEnergy QuasiRiemann.variationalMollifier3414Spec.c1
        QuasiRiemann.variationalMollifier3414Spec.c2) (QuasiRiemann.QRat.mk' 13 16) ∧
   QuasiRiemann.variationalQrhThreshold QuasiRiemann.variationalMollifier3414Spec
      GSp4FunctorialityBridge.thetaKimSarnakSym4 <
      QuasiRiemann.qrhFromAutomorphic
        GSp4FunctorialityBridge.thetaKimSarnakSym4 ∧
   (∀ (s8 tAbs : Nat), 4 < s8 → 0 < tAbs →
     QuasiRiemann.IsCertifiedZeroFree2D s8 tAbs ∨ QuasiRiemann.InRemainingUnknownBox s8 tAbs) ∧
   (∀ (s8 tAbs : Nat), QuasiRiemann.InQrhHalfPlane s8 tAbs →
     QuasiRiemann.IsCertifiedZeroFree2D s8 tAbs))

/-- Sub-specification for constructive p-adic ultrametric valuation & contraction on `QRat`. -/
def UltrametricValuationProp : Prop :=
  (∀ (p : Nat) (_hp : QuasiRiemann.Valuation.IsPrime p) (x y : QuasiRiemann.QRat),
    QuasiRiemann.Valuation.pAdicVal p (-x) = QuasiRiemann.Valuation.pAdicVal p x ∧
    QuasiRiemann.Valuation.pAdicVal p (x * y) =
      QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p x)
        (QuasiRiemann.Valuation.pAdicVal p y) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valMin
        (QuasiRiemann.Valuation.pAdicVal p x)
        (QuasiRiemann.Valuation.pAdicVal p y))
      (QuasiRiemann.Valuation.pAdicVal p (x + y))) ∧
  (∀ (p : Nat) (_hp : QuasiRiemann.Valuation.IsPrime p) (step : Int)
      (f : QuasiRiemann.QRat → QuasiRiemann.QRat)
      (_h_cont : QuasiRiemann.Valuation.IsPAdicStepContraction p step f)
      (x₀ : QuasiRiemann.QRat) (n k : Nat),
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.pAdicVal p (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀))
      (QuasiRiemann.Valuation.pAdicVal p (Nat.repeat f (n + 2) x₀ - Nat.repeat f (n + 1) x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p (Nat.repeat f (n + k) x₀ - Nat.repeat f n x₀))) ∧
  (∀ (p : Nat) (_hp : QuasiRiemann.Valuation.IsPrime p) (m : Int) (_hm : 1 ≤ m)
      (a x₀ : QuasiRiemann.QRat)
      (_ha : QuasiRiemann.Valuation.valLe (some 0) (QuasiRiemann.Valuation.pAdicVal p a))
      (_hx₀ : QuasiRiemann.Valuation.valLe (some 0) (QuasiRiemann.Valuation.pAdicVal p x₀))
      (_h_init : QuasiRiemann.Valuation.valLe (some m)
        (QuasiRiemann.Valuation.pAdicVal p (QuasiRiemann.Valuation.qOne - a * x₀)))
      (n k : Nat),
    QuasiRiemann.Valuation.valLe (some (Int.ofNat (2 ^ n) * m))
      (QuasiRiemann.Valuation.pAdicVal p
        (QuasiRiemann.Valuation.qOne - a *
          Nat.repeat (QuasiRiemann.Valuation.nsStep a) n x₀)) ∧
    QuasiRiemann.Valuation.valLe (some (Int.ofNat (2 ^ n) * m))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat (QuasiRiemann.Valuation.nsStep a) (n + k) x₀ -
         Nat.repeat (QuasiRiemann.Valuation.nsStep a) n x₀))) ∧
  QuasiRiemann.Valuation.JointCrtHenselCert 31 127 1 1
    (QuasiRiemann.Valuation.qOfInt 5) (QuasiRiemann.Valuation.qOfInt 1575) ∧
  QuasiRiemann.Valuation.PrimeTowerHenselCert [7, 31, 127] 1
    (QuasiRiemann.Valuation.qOfInt 5) (QuasiRiemann.Valuation.qOfInt 5512) ∧
  QuasiRiemann.Valuation.PrimeTowerHenselCert QuasiRiemann.Valuation.mersenneTower 1
    (QuasiRiemann.Valuation.qOfInt 5)
    (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
      (fun p => QuasiRiemann.Valuation.crtIdempotent
        QuasiRiemann.Valuation.mersenneTower p 1 0
        (QuasiRiemann.Valuation.mersenneCofactorInv p))
      QuasiRiemann.Valuation.mersenneFiveInv) ∧
  (let P := [QuasiRiemann.Valuation.qOfInt (-2),
             QuasiRiemann.Valuation.qZero,
             QuasiRiemann.Valuation.qOne]
   let f := QuasiRiemann.Valuation.polyNewtonStep P (QuasiRiemann.Valuation.qOfInt 6)
   (∀ n : Nat,
     7 ^ (1 + n * 1) ∣
       (QuasiRiemann.Valuation.hornerEval P
         (Nat.repeat f n (QuasiRiemann.Valuation.qOfInt 3))).num.natAbs) ∧
   (∀ n k : Nat,
     7 ^ (1 + n * 1) ∣
       (Nat.repeat f (n + k) (QuasiRiemann.Valuation.qOfInt 3) -
        Nat.repeat f n (QuasiRiemann.Valuation.qOfInt 3)).num.natAbs)) ∧
  (let e : Nat → QuasiRiemann.QRat := fun p =>
     QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower p 1 0
       (QuasiRiemann.Valuation.mersenneCofactorInv p)
   QuasiRiemann.Valuation.PrimeTowerPolyRootCert QuasiRiemann.Valuation.mersenneTower 1 1
     [QuasiRiemann.Valuation.qOfInt (-2), QuasiRiemann.Valuation.qZero,
      QuasiRiemann.Valuation.qOne]
     (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower e
       QuasiRiemann.Valuation.mersenneSqrt2RootSeed)
     (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower e
       QuasiRiemann.Valuation.mersenneSqrt2DerivInvSeed)) ∧
  (∀ (N : Nat) (theta : QuasiRiemann.QRat)
      (h_theta : QuasiRiemann.qrhThresholdSevenEighths < theta)
      (p : Nat) (_hp : QuasiRiemann.Valuation.IsPrime p)
      (step : Int) (f : QuasiRiemann.QRat → QuasiRiemann.QRat)
      (_h_cont : QuasiRiemann.Valuation.IsPAdicStepContraction p step f)
      (x₀ : QuasiRiemann.QRat) (n m : Nat),
    0 < (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).box1.toQRat.num ∧
    0 < (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).box2.toQRat.num ∧
    (¬ QuasiRiemann.QRat.eqv
      (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).box1.toQRat
      (QuasiRiemann.QRat.ofInt 0)) ∧
    (¬ QuasiRiemann.QRat.eqv
      (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).box2.toQRat
      (QuasiRiemann.QRat.ofInt 0)) ∧
    0 < (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract.num ∧
    (¬ QuasiRiemann.QRat.eqv
      (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract
      (QuasiRiemann.QRat.ofInt 0)) ∧
    (QuasiRiemann.nonDegenerateRnsPairBoxToBoxSupplyBound
      (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta)).xLo =
      (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract ∧
    QuasiRiemann.QRat.ofInt 0 <
      (QuasiRiemann.nonDegenerateRnsPairBoxToBoxSupplyBound
        (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta)).xLo ∧
    (¬ QuasiRiemann.QRat.eqv
      (QuasiRiemann.reflectHalf (QuasiRiemann.reflectHalf
        (QuasiRiemann.nonDegenerateHighOrderRnsPairBox N theta h_theta).stepContract))
      (QuasiRiemann.QRat.ofInt 0)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + 1) x₀ - Nat.repeat f n x₀)) ∧
    QuasiRiemann.Valuation.valLe
      (QuasiRiemann.Valuation.valAdd
        (QuasiRiemann.Valuation.pAdicVal p (f x₀ - x₀))
        (some (Int.ofNat n * step)))
      (QuasiRiemann.Valuation.pAdicVal p
        (Nat.repeat f (n + m) x₀ - Nat.repeat f n x₀))) ∧
  (∀ (p k : Nat) (hp : 0 < p) (c : Int) (_hc : c.natAbs < p ^ k)
      (s : QuasiRiemann.QRat)
      (x : LeanAsm.QuasiRiemann.RNS.RnsInt 3)
      (_h_mod : x.moduli = #[7, 31, 127])
      (r1 r2 r3 : Nat) (_h_res : x.residues = #[r1, r2, r3])
      (_hr1 : r1 < 7) (_hr2 : r2 < 31) (_hr3 : r3 < 127)
      (_hp_primes : QuasiRiemann.Valuation.AllPrimes x.moduli.toList)
      (_hd_primes : QuasiRiemann.Valuation.PairwiseDistinct x.moduli.toList)
      (_hnz : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0)
      (centerLower lipNumerator radius deltaShrink : Nat)
      (_h_shrink : deltaShrink < radius)
      (_h_contract : lipNumerator * radius < centerLower * (radius - deltaShrink))
      (z : Int) (_hz : z.natAbs ≤ lipNumerator * radius)
      (s8 tAbs : Nat) (_hs : 4 < s8) (_ht : 0 < tAbs) (_hHalf : QuasiRiemann.InQrhHalfPlane s8 tAbs),
    ¬ QuasiRiemann.QRat.eqv
        (QuasiRiemann.QRat.ofInt 1 -
          QuasiRiemann.QRat.mk' c (p ^ k) (Nat.pow_pos hp))
        (QuasiRiemann.QRat.ofInt 0) ∧
    QuasiRiemann.QRat.eqv (QuasiRiemann.reflectQRat (QuasiRiemann.reflectQRat s)) s ∧
    (QuasiRiemann.halfQRat < s ↔ QuasiRiemann.reflectQRat s < QuasiRiemann.halfQRat) ∧
    x.reconstruct ≠ 0 ∧
    ((centerLower * (radius - deltaShrink) : Nat) : Int) - z ≠ 0 ∧
    (QuasiRiemann.IsCertifiedZeroFree2D s8 tAbs ∨ QuasiRiemann.InRemainingUnknownBox s8 tAbs) ∧
    QuasiRiemann.IsCertifiedZeroFree2D s8 tAbs)

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
  HighTruncRectProvenanceProp ∧
  ParametricQrhLadderProp ∧
  HighTruncRationalContractionProp ∧
  DyadicAbelProvenanceProp ∧
  MollifierVariationalProp ∧
  UltrametricValuationProp ∧
  ((QuasiRiemann.QRat.ofInt 0 <
      LeanAsm.QuasiRiemann.LuckySieve.survivalProductRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) ∧
    QuasiRiemann.QRat.ofInt 0 <
      LeanAsm.QuasiRiemann.LuckySieve.luckyHarmonicRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) ∧
    (LeanAsm.QuasiRiemann.LuckySieve.luckyPrefixUpTo 50).length = 13 ∧
    QuasiRiemann.QRat.mk' 95 100 ≤
      LeanAsm.QuasiRiemann.LuckySieve.luckyHarmonicRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) ∧
    LeanAsm.QuasiRiemann.LuckySieve.luckyHarmonicRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) ≤
      QuasiRiemann.QRat.mk' 96 100 ∧
    LeanAsm.QuasiRiemann.LuckySieve.survivalProductRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) ≤
      QuasiRiemann.QRat.mk' 35 100) ∧
   ((2 * QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius ≤
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink) ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius <
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink)) ∧
     (QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ≤
         2 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
           QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 <
        QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      8 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 ≤
        7 * QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1) ∧
     (0 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.margin ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
        QuasiRiemann.qrhThresholdSevenEighths))) ∧
  ((QuasiRiemann.QRat.ofInt 0 <
      LeanAsm.QuasiRiemann.beurlingEulerPartialProductRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) 1 ∧
    QuasiRiemann.QRat.mk' 241 100 ≤
      LeanAsm.QuasiRiemann.beurlingEulerPartialProductRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) 1 ∧
    LeanAsm.QuasiRiemann.beurlingEulerPartialProductRat
        (LeanAsm.QuasiRiemann.LuckySieve.luckyGeneratorsUpTo 50) 1 ≤
      QuasiRiemann.QRat.mk' 242 100 ∧
    QuasiRiemann.qrhThresholdSevenEighths ≤ QuasiRiemann.qrhThresholdSevenEighths ∧
    QuasiRiemann.rationalBoxSpec_N256.lipNumerator * QuasiRiemann.rationalBoxSpec_N256.radius <
      QuasiRiemann.rationalBoxSpec_N256.centerLower *
        (QuasiRiemann.rationalBoxSpec_N256.radius - QuasiRiemann.rationalBoxSpec_N256.deltaShrink)) ∧
   ((2 * QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius ≤
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink) ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius <
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink)) ∧
     (QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ≤
         2 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
           QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 <
        QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      8 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 ≤
        7 * QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1) ∧
     (0 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.margin ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
        QuasiRiemann.qrhThresholdSevenEighths))) ∧
  (((QuasiRiemann.QRat.ofInt 0 <
       QuasiRiemann.SieveSequence.survivalProductRat
         (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50) ∧
     QuasiRiemann.QRat.ofInt 0 <
       QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50) ∧
     (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50).length = 14 ∧
     QuasiRiemann.QRat.mk' 16 10 ≤
       QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50) ∧
     QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50) ≤
       QuasiRiemann.QRat.mk' 17 10 ∧
     QuasiRiemann.SieveSequence.survivalProductRat
         (QuasiRiemann.SieveSequence.ludicGeneratorsUpTo 50) ≤
       QuasiRiemann.QRat.mk' 15 100) ∧
    (QuasiRiemann.QRat.ofInt 0 <
       QuasiRiemann.SieveSequence.survivalProductRat
         (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50) ∧
     QuasiRiemann.QRat.ofInt 0 <
       QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50) ∧
     (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50).length = 7 ∧
     QuasiRiemann.QRat.mk' 68 100 ≤
       QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50) ∧
     QuasiRiemann.SieveSequence.sequenceHarmonicRat
         (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50) ≤
       QuasiRiemann.QRat.mk' 70 100 ∧
     QuasiRiemann.SieveSequence.survivalProductRat
         (QuasiRiemann.SieveSequence.josephusGeneratorsUpTo 50) ≤
       QuasiRiemann.QRat.mk' 46 100)) ∧
   ((2 * QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius ≤
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink) ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.lipNumerator *
         QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius <
       QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.centerLower *
         (QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.radius -
           QuasiRiemann.qsd1LogDerivRung32000Spec.jetSpec.qSpec.deltaShrink)) ∧
     (QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ≤
         2 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
           QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum2
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 <
        QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 *
          QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen2 ∧
      8 * QuasiRiemann.mollifierThetaNum QuasiRiemann.qsd1LogDerivRung32000Spec.vNum1
          QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1 ≤
        7 * QuasiRiemann.mollifierThetaDen QuasiRiemann.qsd1LogDerivRung32000Spec.vDen1) ∧
     (0 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.margin ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QuasiRiemann.QRat.mk' 1 2 < QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo ∧
      QuasiRiemann.qsd1LogDerivRung32000Spec.weaveSpec.strip.sigmaLo <
        QuasiRiemann.qrhThresholdSevenEighths)))

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
    QuasiRiemann.crtNtt_highTrunc_2d_zero_free_rect,
    fun spec centerMag pointMag dist hC hD hL =>
      QuasiRiemann.cauchy_box_interior_nonvanishing spec centerMag pointMag dist hC hD hL,
    QuasiRiemann.telescoping_box_contraction_cert⟩,
   ⟨QuasiRiemann.qrhShortExponent_strict_anti.1,
    QuasiRiemann.qrhShortExponent_strict_anti.2.1,
    ⟨QuasiRiemann.qrhShortExponent_density_benchmarks.2.2.1,
     QuasiRiemann.qrhShortExponent_density_benchmarks.2.2.2.2.2.2.1⟩,
    QuasiRiemann.qrhDualFraction_strict_mono.1,
    QuasiRiemann.qrhDualFraction_strict_mono.2.2.2.1,
    fun spec autoTheta' hN hT =>
      let h := QuasiRiemann.kim_sarnak_amplified_qrh_step spec autoTheta' hN hT
      ⟨h.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.parametric_qrh_kim_sarnak_certs.2.1,
     QuasiRiemann.parametric_qrh_kim_sarnak_certs.2.2.2.2.1,
     QuasiRiemann.shortIntervalQrh1732Spec_has_prime⟩⟩,
   ⟨fun rSpec centerMag pointMag dist currDrift nextDrift hCenter hDist hLip hDrift =>
      let h := QuasiRiemann.rational_box_contraction_step rSpec centerMag pointMag dist currDrift
        nextDrift hCenter hDist hLip hDrift
      ⟨h.2.2.1, h.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.ultraDeep72_N256_rational_rect_cert.2.1,
     QuasiRiemann.ultraDeep72_N256_rational_rect_cert.2.2.2.2.1,
     QuasiRiemann.ultraDeep72_N256_rational_rect_cert.2.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.ultraDeep72_N512_rational_rect_cert.2.1,
     QuasiRiemann.ultraDeep72_N512_rational_rect_cert.2.2.2.2.2.1,
     QuasiRiemann.ultraDeep72_N512_rational_rect_cert.2.2.2.2.2.2.2.2.1⟩,
    fun strip zdSpec θ hLo hHi =>
      let h := QuasiRiemann.ultradeep72_strip_to_zero_density_bridge strip zdSpec θ hLo hHi
      ⟨h.1, h.2.2.1, h.2.2.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.ultradeep72_N512_strip_zd_certs.1,
     QuasiRiemann.ultradeep72_N512_strip_zd_certs.2.2.1,
     QuasiRiemann.ultradeep72_N512_strip_zd_certs.2.2.2.1⟩,
    ⟨QuasiRiemann.phase_reduction_width_1e30_under_1e75.1,
     QuasiRiemann.phase_reduction_width_1e30_under_1e75.2.1⟩,
    ⟨QuasiRiemann.ultraDeep72_N1024_rational_rect_cert.2.1,
     QuasiRiemann.ultraDeep72_N1024_rational_rect_cert.2.2.2.2.2.1,
     QuasiRiemann.ultraDeep72_N1024_rational_rect_cert.2.2.2.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.ultraDeep72_N2048_rational_rect_cert.2.1,
     QuasiRiemann.ultraDeep72_N2048_rational_rect_cert.2.2.2.2.2.1,
     QuasiRiemann.ultraDeep72_N2048_rational_rect_cert.2.2.2.2.2.2.2.2.1⟩,
    ⟨QuasiRiemann.ultradeep72_N2048_strip_zd_certs.1,
     QuasiRiemann.ultradeep72_N2048_strip_zd_certs.2.2.2.2.2.2.1,
     QuasiRiemann.ultradeep72_N2048_strip_zd_certs.2.2.2.2.2.2.2.1⟩,
    QuasiRiemann.ultradeep72_N2048_strip_rung_32000_cert,
    QuasiRiemann.qsd1_logderiv_rung32000_cert⟩,
   ⟨QuasiRiemann.dyadic_shell_sum_partition,
    fun r o _i _l hi M k f g => QuasiRiemann.dyadic_shell_sum_foliation r o hi M k f g,
    QuasiRiemann.discrete_abel_summation_by_parts,
    fun a w M N E hMN hw0 hwa hRem =>
      (QuasiRiemann.abel_monotone_weight_envelope a w M N E hMN hw0 hwa hRem).2.2,
    fun spec s psiStep M k gate effErr hH hE hG hL pX pXH tX tXH hX hXH hC hP =>
      let h := QuasiRiemann.short_interval_dyadic_abel_envelope spec s psiStep M k gate effErr
        hH hE hG hL pX pXH tX tXH hX hXH hC hP
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩,
    ⟨QuasiRiemann.dyadic_abel_short_interval_certs.1,
     QuasiRiemann.dyadic_abel_short_interval_certs.2.2.2.1,
     QuasiRiemann.dyadic_abel_short_interval_certs.2.2.2.2.1,
     QuasiRiemann.dyadic_abel_short_interval_certs.2.2.2.2.2.1,
     QuasiRiemann.dyadic_abel_short_interval_certs.2.2.2.2.2.2.1,
     QuasiRiemann.dyadic_abel_short_interval_certs.2.2.2.2.2.2.2.1⟩,
    ⟨⟨QuasiRiemann.hightrunc_dyadic_abel_weave_N1024_cert.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N2048_cert.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N1024_cert.2.2.2.2.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N2048_cert.2.2.2.2.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N1024_cert.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N1024_cert.2.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N2048_cert.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_N2048_cert.2.2.2.1⟩,
     ⟨QuasiRiemann.hightrunc_dyadic_abel_weave_rung32000_cert.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_rung32000_cert.2.2.2.2.2.2.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_rung32000_cert.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_rung32000_cert.2.2.2.1,
      QuasiRiemann.hightrunc_dyadic_abel_weave_rung32000_cert.2.2.2.2.2.1⟩⟩⟩,
   ⟨fun kC kN specN sN hD a w M N E D hMN hD0 hw0 hwA hR gate hHX hE pX pXH tX tXH hBX hBXH hC hP =>
      let h := QuasiRiemann.dyadic_abel_unlocks_next_rung kC kN specN sN hD a w M N E D hMN hD0
        hw0 hwA hR gate hHX hE pX pXH tX tXH hBX hBXH hC hP
      ⟨h.1, h.2.1, h.2.2.2.2⟩,
    ⟨QuasiRiemann.dyadic_abel_rungs_k5_k6_certs.1,
     QuasiRiemann.dyadic_abel_rungs_k5_k6_certs.2.1,
     QuasiRiemann.shortIntervalQrh3364Spec_has_prime,
     QuasiRiemann.shortIntervalQrh65128Spec_has_prime⟩,
    fun m => (QuasiRiemann.linear_minimizes_dirichlet_energy m).2,
    fun m hc1 hc2 => QuasiRiemann.variational_energy_lt_one_of_pos m hc1 hc2,
    ⟨QuasiRiemann.mollifier_variational_bridge_certs.2.2.2.2.1,
     QuasiRiemann.mollifier_variational_bridge_certs.2.2.2.2.2.2.1,
     QuasiRiemann.mollifier_variational_bridge_certs.2.2.2.2.2.2.2.1,
     QuasiRiemann.mollifier_variational_bridge_certs.2.2.2.2.2.2.2.2⟩⟩,
   ⟨fun p hp x y =>
      ⟨QuasiRiemann.Valuation.pAdicVal_neg p x,
       QuasiRiemann.Valuation.pAdicVal_mul p hp x y,
       QuasiRiemann.Valuation.ultrametric_ineq p hp x y⟩,
    fun p hp step f h_cont x₀ n k =>
      ⟨QuasiRiemann.Valuation.iterate_val_growth p step f h_cont x₀ n,
       QuasiRiemann.Valuation.iterate_val_mono p step f h_cont x₀ n,
       QuasiRiemann.Valuation.iterate_val_range p hp step f h_cont x₀ n k⟩,
    fun p hp m hm a x₀ ha hx₀ h_init n k =>
      ⟨QuasiRiemann.Valuation.hensel_newton_schulz_quadratic_residual p hp m hm a x₀ h_init n,
       QuasiRiemann.Valuation.hensel_newton_schulz_cauchy_range p hp m hm a x₀ ha hx₀ h_init n k⟩,
    QuasiRiemann.Valuation.hensel_crt_inv_5_mod_3937_pow,
    QuasiRiemann.Valuation.hensel_mersenne_tower_inv_5_mod_27559_pow,
    QuasiRiemann.Valuation.hensel_mersenne_tower_crt_built_inv_5,
    QuasiRiemann.Valuation.hensel_sqrt2_mod_pow_7,
    QuasiRiemann.Valuation.hensel_mersenne_tower_sqrt2_built,
    fun N theta h_theta p hp step f h_cont x₀ n m =>
      QuasiRiemann.non_degenerate_high_order_rns_pair_box_padic_weave
        N theta h_theta p hp step f h_cont x₀ n m,
    fun p k hp c hc s x h_mod r1 r2 r3 h_res hr1 hr2 hr3 hp_primes hd_primes hnz
        centerLower lipNumerator radius deltaShrink h_shrink h_contract z hz
        s8 tAbs hs ht hHalf =>
      QuasiRiemann.contraction_reflection_bridge_certs
        p k hp c hc s x h_mod r1 r2 r3 h_res hr1 hr2 hr3 hp_primes hd_primes hnz
        centerLower lipNumerator radius deltaShrink h_shrink h_contract z hz
        s8 tAbs hs ht hHalf⟩,
   QuasiRiemann.lucky_beurling_qsd1_strip_cert,
   QuasiRiemann.lucky_sub78_strip_cert_50_bridge,
   QuasiRiemann.SieveSequence.sieve_sequence_qsd1_strip_cert⟩

-- =============================================================================
-- Parts 6 & 8: RNS Garner & Fermat-Tower / Dedekind Euler Non-Vanishing
-- =============================================================================

/-- Part 6 GL(1) Artin character-twisted short-interval provenance specification bundling
exact `ℤ[i]` orthogonality, `MiniVM` `ntt4`/`intt4` residue-class recovery, AP/coset
short-interval positivity, and Fermat-tower beyond-`7/8` (`3/4, 2/3, 5/8, 39/64, 17/32`)
certificates across `{5, 17, 257, 65537}`. -/
def ArtinShortIntervalProvenanceProp : Prop :=
  (∀ (v : Fin 4 → Int) (m : Fin 4),
    ArtinShortIntervalBridge.artinInverseSumRe (ArtinShortIntervalBridge.artinTwistedSumRe v)
      (ArtinShortIntervalBridge.artinTwistedSumIm v) m = 4 * v m ∧
    ArtinShortIntervalBridge.artinInverseSumIm (ArtinShortIntervalBridge.artinTwistedSumRe v)
      (ArtinShortIntervalBridge.artinTwistedSumIm v) m = 0) ∧
  (∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs,
    ∀ (s : MiniVM.State) (v : NttArithmetic.Vec4),
      v.x0 < spec.primeMod → v.x1 < spec.primeMod →
      v.x2 < spec.primeMod → v.x3 < spec.primeMod →
      s.r0 = v.x0 → s.r1 = v.x1 → s.r2 = v.x2 → s.r3 = v.x3 →
      let s1 := MiniVM.runProgram s
        (MiniVMNttBridge.ntt4AsmFermat spec.primeMod spec.omega4)
      let s2 := MiniVM.runProgram s1
        (MiniVMNttBridge.intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
      (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : NttArithmetic.Vec4) =
        ArtinFermatBridge.artinCharTransform4 spec.primeMod spec.omega4 v ∧
      ArtinFermatBridge.artinCharTransform4 spec.primeMod spec.omega4 v =
        NttArithmetic.ntt4 spec.primeMod spec.omega4 v ∧
      (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : NttArithmetic.Vec4) = v ∧
      ((4 * s2.r0) % spec.primeMod = (4 * v.x0) % spec.primeMod ∧
       (4 * s2.r1) % spec.primeMod = (4 * v.x1) % spec.primeMod ∧
       (4 * s2.r2) % spec.primeMod = (4 * v.x2) % spec.primeMod ∧
       (4 * s2.r3) % spec.primeMod = (4 * v.x3) % spec.primeMod)) ∧
  (∀ (tw : ArtinShortIntervalBridge.ArtinTwistedShortIntervalSpec)
     (psiApX psiApXH thetaApX thetaApXH : Int)
     (re0X re1X re2X re3X re0XH re1XH re2XH re3XH : Int)
     (e0 e1 e2 e3 : Nat),
      4 * psiApX = re0X + re1X + re2X + re3X →
      4 * psiApXH = re0XH + re1XH + re2XH + re3XH →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re0X -
          4 * ((10 ^ tw.apSpec.base.xScaleExp : Nat) : Int)) ≤ tw.apSpec.phiQ * e0 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re1X) ≤ tw.apSpec.phiQ * e1 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re2X) ≤ tw.apSpec.phiQ * e2 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re3X) ≤ tw.apSpec.phiQ * e3 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re0XH -
          4 * ((10 ^ tw.apSpec.base.xScaleExp + 10 ^ tw.apSpec.base.hScaleExp : Nat) : Int)) ≤
          tw.apSpec.phiQ * e0 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re1XH) ≤ tw.apSpec.phiQ * e1 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re2XH) ≤ tw.apSpec.phiQ * e2 →
      Int.natAbs ((tw.apSpec.phiQ : Int) * re3XH) ≤ tw.apSpec.phiQ * e3 →
      e0 + e1 + e2 + e3 ≤ 4 * tw.apSpec.base.errUpper →
      (psiApXH - psiApX) - (thetaApXH - thetaApX) ≤
          (tw.apSpec.base.primePowerCorr : Int) →
      Int.natAbs ((tw.apSpec.phiQ : Int) * psiApX -
          ((10 ^ tw.apSpec.base.xScaleExp : Nat) : Int)) ≤
        tw.apSpec.phiQ * tw.apSpec.base.errUpper ∧
      Int.natAbs ((tw.apSpec.phiQ : Int) * psiApXH -
          ((10 ^ tw.apSpec.base.xScaleExp + 10 ^ tw.apSpec.base.hScaleExp : Nat) : Int)) ≤
        tw.apSpec.phiQ * tw.apSpec.base.errUpper ∧
      (0 : Int) < thetaApXH - thetaApX) ∧
  (∀ (cDiff : Fin 4 → Int) (mainTerm e0 e1 e2 e3 primeCorr : Nat),
      Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumRe cDiff 0 - (mainTerm : Int)) ≤ e0 →
      Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumRe cDiff 1) +
          Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumIm cDiff 1) ≤ e1 →
      Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumRe cDiff 2) ≤ e2 →
      Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumRe cDiff 3) +
          Int.natAbs (ArtinShortIntervalBridge.artinTwistedSumIm cDiff 3) ≤ e3 →
      e0 + e1 + e2 + e3 + primeCorr < mainTerm →
      ∀ m : Fin 4, (0 : Int) < 4 * cDiff m - (primeCorr : Int)) ∧
  (ArtinFermatBridge.artinFermatTowerSpecs.map (·.primeMod) = [5, 17, 257, 65537] ∧
   (QuasiRiemann.qrhShortExponent 4 = QuasiRiemann.QRat.mk' 17 32 (by decide) ∧
    QuasiRiemann.QRat.mk' 17 32 (by decide) < ArtinShortIntervalBridge.qrhThresholdKimSarnak ∧
    ArtinShortIntervalBridge.qrhThresholdKimSarnak < QuasiRiemann.qrhThresholdFiveEighths ∧
    QuasiRiemann.qrhThresholdFiveEighths < QuasiRiemann.qrhThresholdTwoThirds ∧
    QuasiRiemann.qrhThresholdTwoThirds < QuasiRiemann.qrhThresholdThreeQuarters ∧
    QuasiRiemann.qrhThresholdThreeQuarters < QuasiRiemann.qrhThresholdSevenEighths) ∧
   (∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs,
     ∃ tw : ArtinShortIntervalBridge.ArtinTwistedShortIntervalSpec,
       tw.artinSpec = spec ∧
       tw.apSpec.base.thetaQRat = ArtinShortIntervalBridge.qrhThresholdKimSarnak ∧
       tw.apSpec.base.thetaQRat < QuasiRiemann.qrhThresholdFiveEighths ∧
       tw.apSpec.HasGuaranteedApPrime) ∧
   (∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs,
     ∃ tw : ArtinShortIntervalBridge.ArtinTwistedShortIntervalSpec,
       tw.artinSpec = spec ∧
       tw.apSpec.base.thetaQRat = QuasiRiemann.qrhShortExponent 4 ∧
       tw.apSpec.HasGuaranteedApPrime))

/-- Parts 6 & 8 provenance specification bundling 3-channel Garner multiplication,
`EulerFactorNonVanishing.FermatTowerStripCert` (`half`, `threeQuarters`, `one`),
cyclotomic Dedekind Euler product bounds across all `32,906` split prime ideals,
and GL(1) Artin-Fermat Euler collapse, cyclotomic factorization, `ntt4` identity,
and `MiniVM` character orthogonality across `{5, 17, 257, 65537}`. -/
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
       256 * EulerFactorNonVanishing.cyclotomicProdNormPow fsOne)) ∧
  (∀ (spec : ArtinFermatBridge.ArtinFermatCharacterSpec), spec.Valid →
    ∀ (f : EulerFactorNonVanishing.EulerLocalFactorSpec),
      EulerFactorNonVanishing.ValidEulerLocalFactorSpec f →
      ArtinFermatBridge.artinCharProductEval (List.replicate spec.galoisOrder 1) f.d f.rNum =
        (f.d - f.rNum) ^ spec.galoisOrder ∧
      (f.d - f.rNum) ^ spec.galoisOrder =
        (f.d - f.rNum) ^ (2 * spec.splittingDeg) ∧
      0 < (f.d - f.rNum) ^ spec.galoisOrder ∧
      (f.d - f.rNum) ^ spec.galoisOrder ≤
        ((f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy) ^ spec.splittingDeg ∧
      0 < (f.d * f.d) ^ spec.splittingDeg ∧
      EulerFactorNonVanishing.FermatTowerStripCert ∧
      (ArtinFermatBridge.artinFermatTowerSpecs.map (·.primeMod) =
        EulerFactorNonVanishing.fermatTowerPrimes ∧
       ArtinFermatBridge.artinFermatTowerSpecs.map (·.splittingDeg) =
        EulerFactorNonVanishing.fermatTowerSplittingDegs ∧
       ArtinFermatBridge.artinFermatTowerSpecs.map (·.galoisOrder) = [4, 16, 256, 65536] ∧
       (ArtinFermatBridge.artinFermatTowerSpecs.map (·.galoisOrder)).prod = 2 ^ 30) ∧
      (∀ zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int,
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
           256 * EulerFactorNonVanishing.cyclotomicProdNormPow fsOne))) ∧
  ((∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs, ∀ T : Int,
      ArtinFermatBridge.artinOrder4EulerPoly spec.omega4 T % (spec.primeMod : Int) =
        (1 - T ^ 4) % (spec.primeMod : Int)) ∧
   (∀ spec : ArtinFermatBridge.ArtinFermatCharacterSpec, spec.Valid → ∀ T : Int,
      ArtinFermatBridge.artinOrder4EulerPoly spec.omega4 T % (spec.primeMod : Int) =
        (1 - T ^ 4) % (spec.primeMod : Int))) ∧
  ((∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs, ∀ v : NttArithmetic.Vec4,
      ArtinFermatBridge.artinCharTransform4 spec.primeMod spec.omega4 v =
        NttArithmetic.ntt4 spec.primeMod spec.omega4 v) ∧
   (∀ spec : ArtinFermatBridge.ArtinFermatCharacterSpec, spec.Valid →
      ∀ v : NttArithmetic.Vec4,
      ArtinFermatBridge.artinCharTransform4 spec.primeMod spec.omega4 v =
        NttArithmetic.ntt4 spec.primeMod spec.omega4 v) ∧
   (∀ cfg : MiniVMNttBridge.FermatNtt4Spec, cfg.Valid → ∀ v : NttArithmetic.Vec4,
      ArtinFermatBridge.artinCharTransform4 cfg.p cfg.omega4 v =
        NttArithmetic.ntt4 cfg.p cfg.omega4 v)) ∧
  ((∀ spec ∈ ArtinFermatBridge.artinFermatTowerSpecs,
      ∀ (s : MiniVM.State) (v : NttArithmetic.Vec4),
        v.x0 < spec.primeMod → v.x1 < spec.primeMod →
        v.x2 < spec.primeMod → v.x3 < spec.primeMod →
        s.r0 = v.x0 → s.r1 = v.x1 → s.r2 = v.x2 → s.r3 = v.x3 →
        let s1 := MiniVM.runProgram s
          (MiniVMNttBridge.ntt4AsmFermat spec.primeMod spec.omega4)
        let s2 := MiniVM.runProgram s1
          (MiniVMNttBridge.intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
        (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : NttArithmetic.Vec4) =
          ArtinFermatBridge.artinCharTransform4 spec.primeMod spec.omega4 v ∧
        (⟨s2.r0, s2.r1, s2.r2, s2.r3⟩ : NttArithmetic.Vec4) = v) ∧
   (∀ spec : ArtinFermatBridge.ArtinFermatCharacterSpec, spec.Valid →
      ∀ (s : MiniVM.State) (i m : Fin 4),
        s.r0 = (ArtinFermatBridge.basisVec4 i.val).x0 →
        s.r1 = (ArtinFermatBridge.basisVec4 i.val).x1 →
        s.r2 = (ArtinFermatBridge.basisVec4 i.val).x2 →
        s.r3 = (ArtinFermatBridge.basisVec4 i.val).x3 →
        let s1 := MiniVM.runProgram s
          (MiniVMNttBridge.ntt4AsmFermat spec.primeMod spec.omega4)
        let s2 := MiniVM.runProgram s1
          (MiniVMNttBridge.intt4AsmFermat spec.primeMod spec.invFour spec.invOmega4)
        (⟨s1.r0, s1.r1, s1.r2, s1.r3⟩ : NttArithmetic.Vec4) =
          ⟨ArtinFermatBridge.artinCharPow spec.primeMod spec.omega4 i.val 0,
           ArtinFermatBridge.artinCharPow spec.primeMod spec.omega4 i.val 1,
           ArtinFermatBridge.artinCharPow spec.primeMod spec.omega4 i.val 2,
           ArtinFermatBridge.artinCharPow spec.primeMod spec.omega4 i.val 3⟩ ∧
        ArtinFermatBridge.artinCharOrthoSum spec.primeMod spec.omega4
          spec.invOmega4 spec.invFour i.val m.val =
          (if i.val = m.val then 1 else 0) ∧
        (match m.val with
         | 0 => s2.r0
         | 1 => s2.r1
         | 2 => s2.r2
         | _ => s2.r3) = (if i.val = m.val then 1 else 0))) ∧
  ArtinShortIntervalProvenanceProp

/-- Zero-axiom certificate for RNS Garner, Fermat-tower / Dedekind strip bounds,
GL(1) Artin-Fermat Euler + MiniVM NTT orthogonality, and character-twisted
short-interval prime bridges. -/
theorem eulerRns_provenance_certified : EulerRnsProvenance :=
  ⟨RnsArithmetic.garner_mul_concrete_soundness,
   EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs,
   EulerFactorNonVanishing.fermat_tower_dedekind_euler_strip_certs,
   ArtinFermatBridge.artin_split_euler_factor_collapse,
   ArtinFermatBridge.artin_order4_cyclotomic_factorization,
   ArtinFermatBridge.artin_char_transform_eq_ntt4,
   ArtinFermatBridge.artin_char_orthogonality_minivm,
   ⟨ArtinShortIntervalBridge.artin_gaussian_char_orthogonality,
    fun spec hmem s v h0 h1 h2 h3 hr0 hr1 hr2 hr3 =>
      let h := ArtinShortIntervalBridge.artin_ntt4_residue_class_recovery
        spec hmem s v h0 h1 h2 h3 hr0 hr1 hr2 hr3
      ⟨h.1, h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩,
    ArtinShortIntervalBridge.artin_twisted_ap_short_interval_pos,
    ArtinShortIntervalBridge.artin_twisted_coset_short_interval_pos,
    ⟨ArtinShortIntervalBridge.fermat_tower_artin_short_interval_certs.2.1,
     ArtinShortIntervalBridge.fermat_tower_artin_short_interval_certs.2.2.1,
     ArtinShortIntervalBridge.fermat_tower_artin_short_interval_certs.2.2.2.2.1,
     ArtinShortIntervalBridge.fermat_tower_artin_short_interval_certs.2.2.2.2.2⟩⟩⟩

-- =============================================================================
-- Part 7: Finite-Field RH, Genus-2 L(C,1)=71/25, Cantor Jacobian & Weil Zeta
-- =============================================================================

/-- Issue #80 Langlands bridge: Rankin-Selberg / `Sym^2` positivity on `p <= 97`, the
`GL(2) x GL(2) -> GSp(4)` spinor product identity, and Hecke-weighted Abel bounds. -/
def LanglandsRankinSelbergProvenance : Prop :=
  (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
      0 < LanglandsRankinSelbergBridge.rsClearedEuler p
        (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
  (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u →
      0 < v - (p : Int) * u →
      0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p
        (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
  (∀ al1 al2 lam T : Int,
    GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
      (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2)) ∧
  (∀ (phi : Nat → Int) (B : Int),
    (∀ m, -B ≤ LanglandsRankinSelbergBridge.heckeChi4PartialSum m ∧
      LanglandsRankinSelbergBridge.heckeChi4PartialSum m ≤ B) →
    (∀ k, phi (k + 1) ≤ phi k) → (∀ k, 0 ≤ phi k) → ∀ M N : Nat,
      -(2 * B * phi M) ≤ LanglandsRankinSelbergBridge.blockSum
        (fun k => LanglandsRankinSelbergBridge.heckeChi4Coeff k * phi k) M N ∧
      LanglandsRankinSelbergBridge.blockSum
        (fun k => LanglandsRankinSelbergBridge.heckeChi4Coeff k * phi k) M N ≤ 2 * B * phi M)

theorem langlandsRankinSelberg_provenance_certified : LanglandsRankinSelbergProvenance :=
  ⟨LanglandsRankinSelbergBridge.rs_pos_goodPrimes,
   LanglandsRankinSelbergBridge.sym2_pos_goodPrimes,
   LanglandsRankinSelbergBridge.spin_eq_product,
   fun phi B hS hm hn M N =>
     LanglandsRankinSelbergBridge.hecke_chi4_short_interval_bound phi B hS hm hn M N⟩

/-- Part 51 provenance: 5-prime Proth NTT tower `{5, 17, 257, 65537, 2013265921}` with `M_5 > 2^61`,
`2^27`-th twiddle root, exact 5-channel Garner CRT, and Dedekind Euler strip bounds. -/
def ProthNttTowerProvenance : Prop :=
  Nat.gcd ProthNttTowerBridge.prothPrime5 CrtNtt.fermatTowerMod4 = 1 ∧
  2 ^ 61 < ProthNttTowerBridge.prothTowerMod5 ∧
  ProthNttTowerBridge.sqrIter ProthNttTowerBridge.prothOmega27 ProthNttTowerBridge.prothPrime5 27 = 1 ∧
  (∀ x : Nat, x < ProthNttTowerBridge.prothTowerMod5 →
    ProthNttTowerBridge.garnerReconstruct5Asm (x % 5) (x % 17) (x % 257) (x % 65537)
      (x % ProthNttTowerBridge.prothPrime5) = x) ∧
  ProthNttTowerBridge.ProthTowerStripCert

theorem prothNttTower_provenance_certified : ProthNttTowerProvenance :=
  ⟨ProthNttTowerBridge.prothPrime5_coprime_M4.1,
   ProthNttTowerBridge.prothTowerMod5_gt_2pow61.2.2.1,
   ProthNttTowerBridge.prothOmega27_order.2.1,
   ProthNttTowerBridge.garnerReconstruct5Asm_sound,
   ProthNttTowerBridge.proth_tower_euler_strip_certs⟩

/-- Part 52 provenance specification bundling 2-adic Eisenstein valuation,
Romik symmetry, RNS rational contraction, unicritical preperiodic polynomial dynamics bounds,
and constructive QSD[1-4] algebra bridges (including QSD[1] dual-jet logarithmic-derivative box contractions). -/
def ValuationDynamicsProvenance : Prop :=
  QuasiRiemann.QsdAlgebraProvenanceProp ∧
  (∀ m : Nat, QuasiRiemann.Valuation.Eisenstein2Adic.v2 (QuasiRiemann.Valuation.Eisenstein2Adic.fact m) +
    QuasiRiemann.Valuation.Eisenstein2Adic.hammingWeight m = m) ∧
  (∀ m : Nat, QuasiRiemann.Valuation.Eisenstein2Adic.isUnitMod2 m (2 ^ m) = true ∧
    ∀ a : Nat, a ≠ 2 ^ m → QuasiRiemann.Valuation.Eisenstein2Adic.isUnitMod2 m a = false) ∧
  (∀ (n j : Nat) (hj1 : 1 ≤ j) (hjn : j ≤ n),
    QuasiRiemann.Valuation.EisensteinWeights.romikCoeff n j =
      QuasiRiemann.Valuation.EisensteinWeights.romikCoeff n (n - j + 1)) ∧
  (QuasiRiemann.Valuation.EisensteinWeights.qratV2
    (QuasiRiemann.Valuation.EisensteinWeights.eisensteinWeight 16 64) = 0) ∧
  (∀ (k : Nat) (moduli : Array Nat) (h_mod : moduli.size = k),
    have initial := QuasiRiemann.RNS.RnsQRat.zero k moduli h_mod
    have result := QuasiRiemann.RNS.rnsContractionLoop 1024 initial #[initial]
    have final_qrat := result.toQRat
    final_qrat.num ≥ 0) ∧
  ((LeanAsm.QuasiRiemann.RNS.mersenneA.add LeanAsm.QuasiRiemann.RNS.mersenneB).reconstruct =
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct +
      LeanAsm.QuasiRiemann.RNS.mersenneB.reconstruct) % 27559) ∧
  ((LeanAsm.QuasiRiemann.RNS.mersenneA.mul LeanAsm.QuasiRiemann.RNS.mersenneB).reconstruct =
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct *
      LeanAsm.QuasiRiemann.RNS.mersenneB.reconstruct) % 27559) ∧
  (∀ (n : Nat) (val : LeanAsm.QuasiRiemann.RNS.RnsQRat 3)
    (coeffs : Array (LeanAsm.QuasiRiemann.RNS.RnsQRat 3)),
    (LeanAsm.QuasiRiemann.RNS.rnsContractionLoop n val coeffs).toQRat.num ≥ 0) ∧
  (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct = 5512 ∧
    (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
      (fun p => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower p 1 0
        (QuasiRiemann.Valuation.mersenneCofactorInv p))
      QuasiRiemann.Valuation.mersenneFiveInv).num % 27559 = 5512 ∧
    QuasiRiemann.Valuation.PrimeTowerHenselCert QuasiRiemann.Valuation.mersenneTower 1
      (QuasiRiemann.Valuation.qOfInt 5)
      (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
        (fun p => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower p 1 0
          (QuasiRiemann.Valuation.mersenneCofactorInv p))
        QuasiRiemann.Valuation.mersenneFiveInv)) ∧
  ((QuasiRiemann.Valuation.PreperiodicDynamics.w0_formula 5 2 (by decide) (by decide)).reduce =
    QuasiRiemann.QRat.mk' 2 5 (by decide)) ∧
  (QuasiRiemann.Valuation.PreperiodicDynamics.qratV2
    (QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
      (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly (QuasiRiemann.QRat.ofInt 2) 2) 2
      (QuasiRiemann.QRat.ofInt 0)) = 1) ∧
  (have base := QuasiRiemann.QRat.mk' 2 5 (by decide)
   have bound := QuasiRiemann.Valuation.PreperiodicDynamics.theorem51AsymptoticBound 2 2 base
   bound ≥ base) ∧
  (have bound := QuasiRiemann.Valuation.PreperiodicDynamics.theorem13AverageBound 134
   bound.num > 0) ∧
  (have bound := QuasiRiemann.Valuation.PreperiodicDynamics.proposition53AverageBound 2 2 134
   bound.num > 0) ∧
  (have bound := QuasiRiemann.Valuation.PreperiodicDynamics.wreathProductMultiplicityBound 2 2
    (QuasiRiemann.QRat.mk' 1 100 (by decide))
   bound.num > 0) ∧
  (have bound := QuasiRiemann.Valuation.PreperiodicDynamics.lemma43DivisibilityBound 2 3 1
    (QuasiRiemann.QRat.mk' 1 10 (by decide))
   bound.num > 0) ∧
  (∀ (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p) (alpha x0 : QuasiRiemann.QRat) (d : Nat),
    QuasiRiemann.Valuation.valLe (some 0) (QuasiRiemann.Valuation.pAdicVal p alpha) →
    QuasiRiemann.Valuation.valLe (some 0) (QuasiRiemann.Valuation.pAdicVal p x0) →
    ∀ n : Nat, QuasiRiemann.Valuation.valLe (some 0)
      (QuasiRiemann.Valuation.pAdicVal p
        (QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
          (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) n x0))) ∧
  (∀ (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p) {d : Nat} (hd : 2 ≤ d)
    (alpha x0 : QuasiRiemann.QRat) {v0 : Int} (hv0 : v0 < 0),
    QuasiRiemann.Valuation.pAdicVal p x0 = some v0 →
    QuasiRiemann.Valuation.valLe (some (Int.ofNat d * v0 + 1))
      (QuasiRiemann.Valuation.pAdicVal p alpha) →
    ∀ n : Nat, QuasiRiemann.Valuation.pAdicVal p
      (QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) n x0) =
      some (Int.ofNat (d ^ n) * v0)) ∧
  (∀ (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p) {d : Nat} (hd : 2 ≤ d)
    (alpha x0 : QuasiRiemann.QRat) {v0 : Int} (hv0 : v0 < 0),
    QuasiRiemann.Valuation.pAdicVal p x0 = some v0 →
    QuasiRiemann.Valuation.valLe (some (Int.ofNat d * v0 + 1))
      (QuasiRiemann.Valuation.pAdicVal p alpha) →
    ∀ m n : Nat, m ≠ n →
      QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) m x0 ≠
      QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) n x0) ∧
  (∀ (p : Nat) (hp : QuasiRiemann.Valuation.IsPrime p) {d : Nat} (hd : 2 ≤ d)
    (alpha x0 : QuasiRiemann.QRat) {v0 : Int} (hv0 : v0 < 0)
    (hx0 : QuasiRiemann.Valuation.pAdicVal p x0 = some v0)
    (ha : QuasiRiemann.Valuation.valLe (some (Int.ofNat d * v0 + 1))
      (QuasiRiemann.Valuation.pAdicVal p alpha))
    {k : Nat} (val : LeanAsm.QuasiRiemann.RNS.RnsQRat k)
    (coeffs : Array (LeanAsm.QuasiRiemann.RNS.RnsQRat k)),
    ((LeanAsm.QuasiRiemann.RNS.rnsContractionStep val coeffs).toQRat.num ≥ 0) ∧
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct = 5512 ∧
      (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
        (fun q => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower q 1 0
          (QuasiRiemann.Valuation.mersenneCofactorInv q))
        QuasiRiemann.Valuation.mersenneFiveInv).num % 27559 = 5512 ∧
      QuasiRiemann.Valuation.PrimeTowerHenselCert QuasiRiemann.Valuation.mersenneTower 1
        (QuasiRiemann.Valuation.qOfInt 5)
        (QuasiRiemann.Valuation.buildCrtSeed QuasiRiemann.Valuation.mersenneTower
          (fun q => QuasiRiemann.Valuation.crtIdempotent QuasiRiemann.Valuation.mersenneTower q 1 0
            (QuasiRiemann.Valuation.mersenneCofactorInv q))
          QuasiRiemann.Valuation.mersenneFiveInv)) ∧
    (∀ n : Nat, QuasiRiemann.Valuation.pAdicVal p
      (QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) n x0) =
      some (Int.ofNat (d ^ n) * v0)) ∧
    (∀ m n : Nat, m ≠ n →
      QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) m x0 ≠
      QuasiRiemann.Valuation.PreperiodicDynamics.iterateEval
        (QuasiRiemann.Valuation.PreperiodicDynamics.unicriticalPoly alpha d) n x0)) ∧
  (∀ (p k x t : Nat) (hp : 2 ≤ p) (_hk : 1 ≤ k),
    let m := p ^ (k + 1)
    let pk := p ^ k
    let x_lift := x + t * pk
    have hm_pos : 0 < m := QuasiRiemann.Valuation.pow_pos_of_ge_two hp (k + 1)
    let dual_lift : QuasiRiemann.Valuation.QsdDualModRing m :=
      ⟨QuasiRiemann.QsdModRing.ofNat m hm_pos x,
       QuasiRiemann.QsdModRing.ofNat m hm_pos (t * pk)⟩
    (x_lift % pk = x % pk) ∧
    ((t * pk) * (t * pk)) % (pk * pk) = 0 ∧
    dual_lift.val.val = x % m ∧
    dual_lift.tan.val = (t * pk) % m) ∧
  (∀ (p : Nat) (hp : 2 ≤ p) (k : Nat) (_hk : 1 ≤ k),
    let m := p ^ k
    let m2 := m * m
    have hm_pos : 0 < m := QuasiRiemann.Valuation.pow_pos_of_ge_two hp k
    have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
    let tan_elem := QuasiRiemann.QsdModRing.ofNat m2 hm2_pos m
    (QuasiRiemann.QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
    (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val)) ∧
  ((QuasiRiemann.Valuation.qsd4_hensel_tower_cert_p7.x1 = 3 ∧
    QuasiRiemann.Valuation.qsd4_hensel_tower_cert_p7.x2 = 10 ∧
    QuasiRiemann.Valuation.qsd4_hensel_tower_cert_p7.x3 = 108) ∧
   ((1 * 1) % 2 = 1 % 2 ∧
    (1 * 1) % (2 ^ 2) = 1 % (2 ^ 2) ∧
    (1 * 1) % (2 ^ 3) = 1 % (2 ^ 3) ∧
    QuasiRiemann.Valuation.pAdicVal 2 (QuasiRiemann.QRat.ofInt (1 * 1 - 1)) = none)) ∧
  (LeanAsm.MiniVMRnsHenselWeave.MiniVMRnsHenselWeaveCert ∧
   LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.num.reconstruct = 14332 ∧
   LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.den.reconstruct = 1 ∧
   LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.toQRat.num = 14332 ∧
   LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.toQRat.den = 1 ∧
   LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.toQRat.num * 1 =
     14332 * (LeanAsm.MiniVMRnsHenselWeave.rnsTowerMersenneQRat.toQRat.den : Int)) ∧
  ((∀ (x y : QuasiRiemann.GaussianQsdInt),
      QuasiRiemann.GaussianQsdInt.norm (QuasiRiemann.GaussianQsdInt.mulGaussian x y) =
        QuasiRiemann.GaussianQsdInt.norm x * QuasiRiemann.GaussianQsdInt.norm y) ∧
   (let z1 := QuasiRiemann.GaussianQsdInt.ofGaussian 2 1
    let z2 := QuasiRiemann.GaussianQsdInt.ofGaussian 1 3
    QuasiRiemann.GaussianQsdInt.norm z1 = 5 ∧
    QuasiRiemann.GaussianQsdInt.norm z2 = 10 ∧
    QuasiRiemann.GaussianQsdInt.norm (QuasiRiemann.GaussianQsdInt.mulGaussian z1 z2) = 50) ∧
   ((QuasiRiemann.gaussian_b_basis.mulTrunc QuasiRiemann.gaussian_b_basis).mulTrunc
        QuasiRiemann.gaussian_b_basis ≠
      QuasiRiemann.gaussian_b_basis.mulTrunc
        (QuasiRiemann.gaussian_b_basis.mulTrunc QuasiRiemann.gaussian_b_basis) ∧
    ((QuasiRiemann.gaussian_b_basis.mulTrunc QuasiRiemann.gaussian_b_basis).mulTrunc
        QuasiRiemann.gaussian_b_basis).f = 1) ∧
   (∀ (p k x t : Nat) (_hp : 2 ≤ p) (_hk : 1 ≤ k),
     let pk := p ^ k
     let x_lift := x + t * pk
     (x_lift % pk = x % pk) ∧
     ((t * pk) * (t * pk)) % (pk * pk) = 0) ∧
   (∀ (p : Nat) (hp : 2 ≤ p) (k : Nat) (_hk : 1 ≤ k),
     let m := p ^ k
     let m2 := m * m
     have hm_pos : 0 < m := QuasiRiemann.Valuation.pow_pos_of_ge_two hp k
     have hm2_pos : 0 < m2 := Nat.mul_pos hm_pos hm_pos
     let tan_elem := QuasiRiemann.QsdModRing.ofNat m2 hm2_pos m
     (QuasiRiemann.QsdModRing.mul hm2_pos tan_elem tan_elem).val = 0 ∧
     (p ^ (2 * k)) ∣ (tan_elem.val * tan_elem.val)) ∧
   ((LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct % 7 = 3) ∧
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct % 31 = 25) ∧
    (LeanAsm.QuasiRiemann.RNS.mersenneA.reconstruct % 127 = 51))) ∧
  ((LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z1_test.norm = 5 ∧
    LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z2_test.norm = 10 ∧
    LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test.norm = 50 ∧
    QuasiRiemann.GaussianQsdInt.norm
      (QuasiRiemann.GaussianQsdInt.mulGaussian
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z1_test
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z2_test) =
      LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z1_test.norm *
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z2_test.norm ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z1_test).residues = #[5, 5, 5] ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z1_test).reconstruct = 5 ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z2_test).residues = #[3, 10, 10] ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z2_test).reconstruct = 10 ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test).residues = #[1, 19, 50] ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test).reconstruct = 50 ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test).reconstruct % 7 = 1 ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test).reconstruct % 31 = 19 ∧
    (LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne
        LeanAsm.QuasiRiemann.RnsGaussianNormBridge.z12_test).reconstruct % 127 = 50) ∧
   (∀ x y : QuasiRiemann.GaussianQsdInt,
     0 ≤ x.norm ∧
     0 ≤ y.norm ∧
     QuasiRiemann.GaussianQsdInt.norm (QuasiRiemann.GaussianQsdInt.mulGaussian x y) =
       QuasiRiemann.GaussianQsdInt.norm x * QuasiRiemann.GaussianQsdInt.norm y ∧
     (let rnsX := LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne x
      (rnsX.reconstruct % 7 = ((x.norm.toNat % 7 : Nat) : Int)) ∧
      (rnsX.reconstruct % 31 = ((x.norm.toNat % 31 : Nat) : Int)) ∧
      (rnsX.reconstruct % 127 = ((x.norm.toNat % 127 : Nat) : Int))) ∧
     (let rnsY := LeanAsm.QuasiRiemann.RnsGaussianNormBridge.gaussianToRnsMersenne y
      (rnsY.reconstruct % 7 = ((y.norm.toNat % 7 : Nat) : Int)) ∧
      (rnsY.reconstruct % 31 = ((y.norm.toNat % 31 : Nat) : Int)) ∧
      (rnsY.reconstruct % 127 = ((y.norm.toNat % 127 : Nat) : Int)))))

/-- Zero-axiom certificate for Part 52 2-adic valuation and preperiodic dynamics bounds. -/
theorem valuation_dynamics_provenance_certified : ValuationDynamicsProvenance :=
  ⟨QuasiRiemann.qsd_algebra_provenance_certified,
   QuasiRiemann.Valuation.Eisenstein2Adic.legendre_v2_factorial,
   QuasiRiemann.Valuation.Eisenstein2Adic.proposition_4_unique,
   QuasiRiemann.Valuation.EisensteinWeights.romikCoeff_symm,
   QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m4.1,
   QuasiRiemann.RNS.rns_contraction_sound,
   LeanAsm.QuasiRiemann.RNS.rnsInt_reconstruct_add_sound,
   LeanAsm.QuasiRiemann.RNS.rnsInt_reconstruct_mul_sound,
   fun n val coeffs => LeanAsm.QuasiRiemann.RNS.rnsQRat_contraction_preserves_pos n val coeffs,
   LeanAsm.QuasiRiemann.RNS.rnsInt_reconstruct_mersenne_crt_seed_cert,
   QuasiRiemann.Valuation.PreperiodicDynamics.andersen_garton_prop22_q5_d2_reduced,
   QuasiRiemann.Valuation.PreperiodicDynamics.unicritical_iterate_valuation_growth.2.2,
   QuasiRiemann.Valuation.PreperiodicDynamics.theorem51_asymptotic_bound_sound,
   QuasiRiemann.Valuation.PreperiodicDynamics.theorem13_average_bound_sound,
   QuasiRiemann.Valuation.PreperiodicDynamics.proposition53_average_bound_sound,
   QuasiRiemann.Valuation.PreperiodicDynamics.wreath_product_bound_sound,
   QuasiRiemann.Valuation.PreperiodicDynamics.lemma43_divisibility_bound_sound,
   QuasiRiemann.Valuation.PreperiodicDynamics.unicritical_integral_orbit_invariant,
   QuasiRiemann.Valuation.PreperiodicDynamics.unicritical_escape_val_exact,
   QuasiRiemann.Valuation.PreperiodicDynamics.unicritical_escape_no_preperiodic,
   LeanAsm.QuasiRiemann.RNS.rns_valuation_orbit_step_sound,
   fun p k x t hp hk =>
     QuasiRiemann.Valuation.qsd4_hensel_tangent_lift_step p k x t hp hk,
   fun p hp k hk =>
     QuasiRiemann.Valuation.qsd4_prime_tower_nilpotent_remainder_bound p hp k hk,
   ⟨⟨rfl, rfl, rfl⟩, QuasiRiemann.Valuation.qsd4_hensel_tower_cert_p2⟩,
   LeanAsm.MiniVMRnsHenselWeave.minivm_ntt_rns_hensel_weave_bridge,
   QuasiRiemann.gaussian_qsd_hensel_tower_bridge,
   ⟨LeanAsm.QuasiRiemann.RnsGaussianNormBridge.rns_crt_gaussian_norm_cert,
    LeanAsm.QuasiRiemann.RnsGaussianNormBridge.rns_crt_gaussian_norm_bound⟩⟩

/-- Part 7 provenance specification bundling Hasse-Weil RH for `E / F_7`,
genus-2 `C / F_5` negative discriminants, `L(C, 1) = 71/25`, Cantor-Mumford group axioms
for `J(C)(F_5) ≅ Z/71Z`, punctured-strip zeta non-vanishing, `Ξ_C` reflection,
`GSp(4) -> SO(5)` functorial Euler lift + Selberg / Kim-Sarnak ladder, and
`E_{11a1}` / `f_{11}` GL(2) Eichler-Shimura modularity. -/
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
          GSp4FunctorialityBridge.thetaKimShahidiSym3) ∧
  ((∀ p ∈ EllipticModularityBridge.goodPrimes97,
      EllipticModularityBridge.heckeCoeff11 p =
        EllipticModularityBridge.ec11a1FrobTrace p) ∧
    EllipticModularityBridge.heckeCoeff11 11 = 1) ∧
  ((∀ p ∈ EllipticModularityBridge.goodPrimes97,
      EllipticModularityBridge.ec11a1FrobTrace p ^ 2 ≤ 4 * (p : Int)) ∧
   (∀ p ∈ EllipticModularityBridge.goodPrimes97,
      EllipticModularityBridge.ec11a1FrobTrace p ^ 2 < 4 * (p : Int)) ∧
   (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
      0 < EllipticModularityBridge.gl2EulerHomog
        (p : Int) (EllipticModularityBridge.ec11a1FrobTrace p) u v)) ∧
  (EllipticModularityBridge.heckeCoeff11 1 = 1 ∧
   (∀ m n : Nat, 1 ≤ m → 1 ≤ n → m * n ≤ 100 → Nat.gcd m n = 1 →
      EllipticModularityBridge.heckeCoeff11 (m * n) =
        EllipticModularityBridge.heckeCoeff11 m *
          EllipticModularityBridge.heckeCoeff11 n) ∧
   (∀ p ∈ EllipticModularityBridge.goodSqPrimes100,
      EllipticModularityBridge.heckeCoeff11 (p * p) =
        EllipticModularityBridge.heckeCoeff11 p ^ 2 - (p : Int))) ∧
  (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, Genus2MultiPrimeWeil.Genus2WeilCert p) ∧
  ((∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList,
      Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
   (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ n d : Int,
      Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
        (p : Int) ^ 2 * Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
   (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ T : Int,
      Genus2MultiPrimeWeil.standardEulerPoly p T =
        (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor
          (p : Int) (Genus2MultiPrimeWeil.frobeniusTrace p)
          (Genus2MultiPrimeWeil.degree2Trace p) T) ∧
   (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ n d : Int,
      Genus2WeilGSp4Weave.standardEulerHomogP p d n =
        -Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
   (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList,
      Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
  QuasiRiemann.Genus2HenselPreperiodicWeave.Genus2HenselPreperiodicWeaveBridge ∧
  (let spec := QuasiRiemann.PreperiodicQsd1StripWeave.preperiodicQsd1Rung32000Spec
   (((QuasiRiemann.Valuation.PreperiodicDynamics.w0_formula 5 2 (by decide) (by decide)).reduce =
       QuasiRiemann.QRat.mk' 2 5) ∧
    (let base := QuasiRiemann.QRat.mk' 2 5 (by decide)
     QuasiRiemann.Valuation.PreperiodicDynamics.theorem51AsymptoticBound 2 2 base ≥ base) ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.theorem13AverageBound 134).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.proposition53AverageBound 2 2 134).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.wreathProductMultiplicityBound 2 2
       (QuasiRiemann.QRat.mk' 1 100 (by decide))).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.lemma43DivisibilityBound 2 3 1
       (QuasiRiemann.QRat.mk' 1 10 (by decide))).num > 0) ∧
   ((2 * spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
     spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.stripBridgeSpec.jetSpec.qSpec.radius <
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
    (QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ≤
       2 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 ∧
     QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1 <
       QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ∧
     8 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 ≤
       7 * QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1) ∧
    (0 < spec.stripBridgeSpec.weaveSpec.margin ∧
     spec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
    (QuasiRiemann.QRat.mk' 1 2 < spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
     spec.stripBridgeSpec.weaveSpec.strip.sigmaLo < QuasiRiemann.qrhThresholdSevenEighths))) ∧
  (let spec := QuasiRiemann.preperiodicVariationalRung32000Spec
   (((QuasiRiemann.Valuation.PreperiodicDynamics.w0_formula 5 2 (by decide) (by decide)).reduce =
       QuasiRiemann.QRat.mk' 2 5) ∧
    (let base := QuasiRiemann.QRat.mk' 2 5 (by decide)
     QuasiRiemann.Valuation.PreperiodicDynamics.theorem51AsymptoticBound 2 2 base ≥ base) ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.theorem13AverageBound 134).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.proposition53AverageBound 2 2 134).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.wreathProductMultiplicityBound 2 2
       (QuasiRiemann.QRat.mk' 1 100 (by decide))).num > 0 ∧
    (QuasiRiemann.Valuation.PreperiodicDynamics.lemma43DivisibilityBound 2 3 1
       (QuasiRiemann.QRat.mk' 1 10 (by decide))).num > 0) ∧
   (QuasiRiemann.QRat.ofInt 0 < spec.windowBox.sLo ∧
    QuasiRiemann.QRat.ofInt 0 < spec.windowBox.tLo ∧
    ¬ QuasiRiemann.QRat.eqv spec.windowBox.sLo (QuasiRiemann.QRat.ofInt 0) ∧
    ¬ QuasiRiemann.QRat.eqv (QuasiRiemann.supplyNonDegenerateCharWitness 1 (by decide)
        spec.windowBox).boundLo (QuasiRiemann.QRat.ofInt 0)) ∧
   (QuasiRiemann.QRat.eqv (QuasiRiemann.reflectQRat (QuasiRiemann.reflectQRat spec.windowBox.sLo))
        spec.windowBox.sLo ∧
    (QuasiRiemann.halfQRat < spec.windowBox.sLo ↔
      QuasiRiemann.reflectQRat spec.windowBox.sLo < QuasiRiemann.halfQRat) ∧
    (∀ (p k : Nat) (hp : 0 < p) (c : Int) (_hc : c.natAbs < p ^ k),
      ¬ QuasiRiemann.QRat.eqv (QuasiRiemann.QRat.ofInt 1 -
          QuasiRiemann.QRat.mk' c (p ^ k) (Nat.pow_pos hp)) (QuasiRiemann.QRat.ofInt 0))) ∧
   (0 < (QuasiRiemann.mollifierVariationalEnergy spec.mollifierSpec.c1
        spec.mollifierSpec.c2).num ∧
    ¬ QuasiRiemann.QRat.eqv (QuasiRiemann.mollifierVariationalEnergy spec.mollifierSpec.c1
        spec.mollifierSpec.c2) (QuasiRiemann.QRat.ofInt 0) ∧
    QuasiRiemann.mollifierVariationalEnergy spec.mollifierSpec.c1
        spec.mollifierSpec.c2 < QuasiRiemann.QRat.ofInt 1) ∧
   ((2 * spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
     spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
     spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius <
     spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.weaveSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
    (QuasiRiemann.mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen2 ≤
       2 * QuasiRiemann.mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum2
         spec.weaveSpec.stripBridgeSpec.vDen2 ∧
     QuasiRiemann.mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum2
         spec.weaveSpec.stripBridgeSpec.vDen2 *
       QuasiRiemann.mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen1 <
     QuasiRiemann.mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum1
         spec.weaveSpec.stripBridgeSpec.vDen1 *
       QuasiRiemann.mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen2 ∧
     8 * QuasiRiemann.mollifierThetaNum spec.weaveSpec.stripBridgeSpec.vNum1
         spec.weaveSpec.stripBridgeSpec.vDen1 ≤
       7 * QuasiRiemann.mollifierThetaDen spec.weaveSpec.stripBridgeSpec.vDen1) ∧
    (0 < spec.weaveSpec.stripBridgeSpec.weaveSpec.margin ∧
     spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
    (QuasiRiemann.QRat.mk' 1 2 < spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
     spec.weaveSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
       QuasiRiemann.qrhThresholdSevenEighths))) ∧
  (let spec := QuasiRiemann.qsd1IdempotentDyadicAbelCertSpec
   (QuasiRiemann.QRat.eqv (QuasiRiemann.e_plus spec.splitGen +
       QuasiRiemann.e_minus spec.splitGen) (QuasiRiemann.QRat.ofInt 1) ∧
    QuasiRiemann.QRat.eqv (QuasiRiemann.e_plus spec.splitGen *
       QuasiRiemann.e_plus spec.splitGen) (QuasiRiemann.e_plus spec.splitGen) ∧
    QuasiRiemann.QRat.eqv (QuasiRiemann.e_minus spec.splitGen *
       QuasiRiemann.e_minus spec.splitGen) (QuasiRiemann.e_minus spec.splitGen) ∧
    QuasiRiemann.QRat.eqv (QuasiRiemann.e_plus spec.splitGen *
       QuasiRiemann.e_minus spec.splitGen) (QuasiRiemann.QRat.ofInt 0)) ∧
   ((2 * spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
     spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
       spec.stripBridgeSpec.jetSpec.qSpec.radius <
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius -
         spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
    (QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ≤
       2 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 ∧
     QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1 <
       QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ∧
     8 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 ≤
       7 * QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1) ∧
    (let weave := spec.stripBridgeSpec.weaveSpec
     0 < weave.margin ∧ weave.strip.rectSpec.HasCertifiedNonVanishing) ∧
    (QuasiRiemann.QRat.mk' 1 2 < spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
     spec.stripBridgeSpec.weaveSpec.strip.sigmaLo < QuasiRiemann.qrhThresholdSevenEighths))) ∧
  LanglandsRankinSelbergProvenance ∧
  (let spec := QuasiRiemann.RankinSelbergGSp4Sub78Bridge.rankinSelbergGSp4Rung32000Spec
   ((∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
    (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ n d : Int,
      Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
        (p : Int) ^ 2 * Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
    (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ T : Int,
      Genus2MultiPrimeWeil.standardEulerPoly p T =
        (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor (p : Int)
          (Genus2MultiPrimeWeil.frobeniusTrace p) (Genus2MultiPrimeWeil.degree2Trace p) T) ∧
    (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, ∀ n d : Int,
      Genus2WeilGSp4Weave.standardEulerHomogP p d n =
        -Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
    (∀ p ∈ Genus2MultiPrimeWeil.goodPrimesList, Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
   ((∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
      0 < LanglandsRankinSelbergBridge.rsClearedEuler p (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
    (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
      0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
    (∀ al1 al2 lam T : Int,
      GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
        (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2))) ∧
   ((2 * spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator * spec.stripBridgeSpec.jetSpec.qSpec.radius ≤
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius - spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
     spec.stripBridgeSpec.jetSpec.qSpec.lipNumerator * spec.stripBridgeSpec.jetSpec.qSpec.radius <
     spec.stripBridgeSpec.jetSpec.qSpec.centerLower *
       (spec.stripBridgeSpec.jetSpec.qSpec.radius - spec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
    (QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ≤
       2 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 ∧
     QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum2 spec.stripBridgeSpec.vDen2 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1 <
       QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 *
         QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen2 ∧
     8 * QuasiRiemann.mollifierThetaNum spec.stripBridgeSpec.vNum1 spec.stripBridgeSpec.vDen1 ≤
       7 * QuasiRiemann.mollifierThetaDen spec.stripBridgeSpec.vDen1) ∧
    (0 < spec.stripBridgeSpec.weaveSpec.margin ∧
     spec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
    (QuasiRiemann.QRat.mk' 1 2 < spec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
     spec.stripBridgeSpec.weaveSpec.strip.sigmaLo < QuasiRiemann.qrhThresholdSevenEighths))) ∧
  (let spec := QuasiRiemann.JacobianRankinSelbergWeave.jacobianRankinSelbergRung32000Spec
   (Genus2Jacobian.cantorSmul 71 Genus2Jacobian.D0 = Genus2Jacobian.MumfordDivisor.zero ∧
    (∀ k : Nat, 1 ≤ k → k ≤ 70 →
       Genus2Jacobian.cantorSmul k Genus2Jacobian.D0 ≠ Genus2Jacobian.MumfordDivisor.zero) ∧
    Genus2Jacobian.isReducedMumford Genus2Jacobian.D0.u Genus2Jacobian.D0.v = true ∧
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
          Genus2Jacobian.MumfordDivisor.zero))) ∧
   (((∀ p ∈ spec.rsSpec.goodPrimes, Genus2WeilGSp4Weave.Genus2WeilGSp4PrimeWeaveCert p) ∧
     (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
       Genus2WeilGSp4Weave.spinLPolyHomog p d ((p : Int) * n) =
         (p : Int) ^ 2 * Genus2WeilGSp4Weave.spinLPolyHomog p n d) ∧
     (∀ p ∈ spec.rsSpec.goodPrimes, ∀ T : Int,
       Genus2MultiPrimeWeil.standardEulerPoly p T =
         (1 - T) * GSp4FunctorialityBridge.gsp4StdQuarticCofactor (p : Int)
           (Genus2MultiPrimeWeil.frobeniusTrace p) (Genus2MultiPrimeWeil.degree2Trace p) T) ∧
     (∀ p ∈ spec.rsSpec.goodPrimes, ∀ n d : Int,
       Genus2WeilGSp4Weave.standardEulerHomogP p d n =
         -Genus2WeilGSp4Weave.standardEulerHomogP p n d) ∧
     (∀ p ∈ spec.rsSpec.goodPrimes, Genus2MultiPrimeWeil.standardEulerPoly p 1 = 0)) ∧
    ((∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 < v →
       0 < LanglandsRankinSelbergBridge.rsClearedEuler p
         (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
     (∀ p ∈ EllipticModularityBridge.goodPrimes97, ∀ u v : Int, 0 ≤ u → 0 < v - (p : Int) * u →
       0 < LanglandsRankinSelbergBridge.sym2ClearedEuler p
         (EllipticModularityBridge.heckeCoeff11 p) u v) ∧
     (∀ al1 al2 lam T : Int,
       GSp4FunctorialityBridge.gsp4SpinEulerPoly lam (al1 + al2) (al1 * al2 + 2 * lam) T =
         (1 - al1 * T + lam * T ^ 2) * (1 - al2 * T + lam * T ^ 2))) ∧
    ((2 * spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius ≤
      spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink) ∧
      spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.lipNumerator *
        spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius <
      spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.centerLower *
        (spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.radius -
          spec.rsSpec.stripBridgeSpec.jetSpec.qSpec.deltaShrink)) ∧
     (QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen2 ≤
        2 * QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum2
          spec.rsSpec.stripBridgeSpec.vDen2 ∧
      QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum2
          spec.rsSpec.stripBridgeSpec.vDen2 *
        QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen1 <
      QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum1
          spec.rsSpec.stripBridgeSpec.vDen1 *
        QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen2 ∧
      8 * QuasiRiemann.mollifierThetaNum spec.rsSpec.stripBridgeSpec.vNum1
          spec.rsSpec.stripBridgeSpec.vDen1 ≤
        7 * QuasiRiemann.mollifierThetaDen spec.rsSpec.stripBridgeSpec.vDen1) ∧
     (0 < spec.rsSpec.stripBridgeSpec.weaveSpec.margin ∧
      spec.rsSpec.stripBridgeSpec.weaveSpec.strip.rectSpec.HasCertifiedNonVanishing) ∧
     (QuasiRiemann.QRat.mk' 1 2 < spec.rsSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo ∧
      spec.rsSpec.stripBridgeSpec.weaveSpec.strip.sigmaLo <
        QuasiRiemann.qrhThresholdSevenEighths))))

/-- Zero-axiom certificate for Hasse-Weil RH, genus-2 Jacobian, completed zeta,
`GSp(4) -> SO(5)` functoriality + Selberg / Kim-Sarnak ladder,
`E_{11a1}` / `f_{11}` GL(2) Eichler-Shimura modularity, multi-prime genus-2 Weil RH,
and Genus2MultiPrimeWeil + WeilZetaBridge + GSp4FunctorialityBridge weave. -/
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
   GSp4FunctorialityBridge.selberg_laplacian_eigenvalue_ladder,
   EllipticModularityBridge.eichler_shimura_trace_eq_11a1,
   EllipticModularityBridge.hasse_weil_ramanujan_11a1_certs,
   EllipticModularityBridge.hecke_multiplicativity_11a1_certs,
   Genus2MultiPrimeWeil.genus2_multiprime_weil_certs,
   Genus2WeilGSp4Weave.genus2_multiprime_weil_gsp4_weave_bridge,
   QuasiRiemann.Genus2HenselPreperiodicWeave.genus2_hensel_preperiodic_weave_bridge,
   QuasiRiemann.PreperiodicQsd1StripWeave.preperiodic_qsd1_strip_cert,
   QuasiRiemann.preperiodic_variational_bridge_cert,
   QuasiRiemann.qsd1_idempotent_dyadic_abel_cert,
   langlandsRankinSelberg_provenance_certified,
   QuasiRiemann.RankinSelbergGSp4Sub78Bridge.rankin_selberg_gsp4_sub78_bridge
     QuasiRiemann.RankinSelbergGSp4Sub78Bridge.rankinSelbergGSp4Rung32000Spec,
   QuasiRiemann.JacobianRankinSelbergWeave.jacobian_split_rankin_selberg_weave
     QuasiRiemann.JacobianRankinSelbergWeave.jacobianRankinSelbergRung32000Spec⟩

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
def LeanAsmFullProvenance : Prop :=
  MiniVmProvenance ∧
  CollatzProvenance ∧
  YangMillsProvenance ∧
  QuasiRiemannProvenance ∧
  EulerRnsProvenance ∧
  FiniteFieldWeilProvenance ∧
  CrtNttProvenance ∧
  ChudnovskyPiProvenance ∧
  ProthNttTowerProvenance ∧
  ValuationDynamicsProvenance

theorem leanasm_full_provenance_certified : LeanAsmFullProvenance :=
  ⟨miniVm_provenance_certified,
   collatz_provenance_certified,
   yangMills_provenance_certified,
   quasiRiemann_provenance_certified,
   eulerRns_provenance_certified,
   finiteFieldWeil_provenance_certified,
   crtNtt_provenance_certified,
   chudnovskyPi_provenance_certified,
   prothNttTower_provenance_certified,
   valuation_dynamics_provenance_certified⟩

end LeanAsm

-- end of file: leanasm/src/LeanAsm/ProvenanceSummary.lean
