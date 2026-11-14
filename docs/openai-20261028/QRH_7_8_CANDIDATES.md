<!-- Path: leanasm/docs/openai-20261028/QRH_7_8_CANDIDATES.md -->
<!-- Max Column: 80 Columns -->

# QRH 7/8 Relevance Scan & Portability Candidates (v2)

## 1. Summary & Classification Breakdown

- **Total Matched Decls**: 782
- **YM Collision Penalized**: 152
- **Concepts Scanned**: 3/4, 7 / 8, 7/8, Chebyshev, Dirichlet, Euler,
  EulerMaclaurin, Lipschitz, Mellin, Perron, QRH, QuasiRiemann, criticalStrip,
  mollifier, primeGap, psi, shortInterval, theta, vonMangoldt, zeroDensity,
  zeroFree, zeta
- **Collision Penalties**: Axis(-22), Fermion(-18), Gauge(-14), Plaquette(-18),
  PriceCompiler(-20), SmallField(-20), WardBin(-22), Wick(-22), Wilson(-18)

### By Portability Classification

| Classification                 | Count |
| ------------------------------ | ----- |
| CLEARED_DENOMINATOR_ADAPTATION | 782   |

### By Target `leanasm` Module

| Target Module                         | Count |
| ------------------------------------- | ----- |
| EulerFactorNonVanishing.lean          | 105   |
| QuasiRiemann/ShortIntervalPrimes.lean | 551   |
| QuasiRiemann/UltraDeep72.lean         | 90    |
| QuasiRiemann/ZeroDensityBridge.lean   | 36    |

## 2. Top Overall QRH 7/8 Candidates (Top 60)

1. **[score=64]** `lemma YM.Extension.UV.Bare.zeroFree`
(`submission/YM/Extension/UV/Bare.lean:47`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: zeroFree
- **Signature**: `lemma zeroFree (t : ℝ) : ∃ r>0,∀ s∈Metric.ball (t:ℂ) r,
  numerator (n:=n) (G:=G) 1 s≠0`
2. **[score=64]** `lemma YM.UVExtension.Pier.zeroFree`
(`submission/YM/UVExtension/Pier/Power.lean:49`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: zeroFree
- **Signature**: `lemma zeroFree (hr:0<r)(hc:0<a)(hb:0<b): ∃ t:ℝ,0<t∧ t<r∧∀
  f:ℂ→ℂ,DifferentiableOn ℂ f (ball 0 r)→ (∀ z∈ball (0:ℂ) r, ‖f z‖ ≤a) → b ≤ ‖f
  0‖ → ∀ z∈ ball (0:ℂ) t, b/2≤‖f z‖`
3. **[score=40]** `lemma YM.Extension.UV.Startup.datum_lipschitz`
(`submission/YM/Extension/UV/Canon/State.lean:105`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma datum_lipschitz {x y:ℝ} (hx:x∈strictBand a N)
  (hy:y∈strictBand a N) : ‖datum e (x:ℂ)-datum e (y:ℂ)‖ ≤ |x-y|/(a.clock.hatBeta
  N/2)`
4. **[score=40]** `lemma YM.Extension.UV.diam_lipschitz`
(`submission/YM/Extension/UV/Holo.lean:57`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma diam_lipschitz (hs : Convex ℝ U) (hU : ∀
  x∈U,DifferentiableAt ℂ f x) (h : ∀ x∈U,DifferentiableOn ℂ f (Metric.ball x r))
  (hM : ∀ x∈U, ∀ y ∈ Metric.ball x r,‖f y‖ ≤ M) (hr : 0<r) : ∀ x∈U,∀ y∈U,‖f x-f
  y‖ ≤ M/r * ‖x-y‖`
5. **[score=40]** `lemma YM.Planned.JetPort.lipschitzLower`
(`submission/YM/Planned/STATIONARY_JET_PORT/Enclosures.lean:17`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma lipschitzLower (h : Convex ℝ s) (hf : ∀ x∈s, ContDiffAt
  ℝ ω f x) (he : ∀ x∈s, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ C) {x y : E} (hx : x∈s)
  (hy : y∈s) : ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖`
6. **[score=40]** `lemma YM.Push.Uniform.Before.Service.trail_lipschitz`
(`submission/YM/Push/STATIONARY_UNIFORM/Along.lean:106`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma trail_lipschitz (hp : R.Bounds p μ C Λ) (hK : Larger
  (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) : let P`
7. **[score=38]** `structure YM.Extension.UV.Tail.Lipschitz`
(`submission/YM/Extension/UV/Tail.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `structure Lipschitz (R : Rules E) : Prop`
8. **[score=34]** `theorem YM.Tensor.Euler`
(`submission/YM/Analysis/Homogeneous.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem Euler (h : Sym A) (x : E) : fderiv ℝ (diagonal A) x x
  = (j : ℝ) • diagonal A x`
9. **[score=30]** `lemma YM.EveryPhase.Stress.zeta_square`
(`submission/YM/EveryPhase/Tensor.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_square (a : Axis) : zeta a * zeta a = -(eta a : ℂ)`
10. **[score=28]** `def YM.EveryPhase.Stress.zeta`
(`submission/YM/EveryPhase/Tensor.lean:22`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a : Axis) : ℂ`
11. **[score=28]** `lemma YM.EveryPhase.Stress.TM`
(`submission/YM/EveryPhase/Tensor.lean:207`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma TM (Q : Wightman S) (T : S.Stress) (a b) (f : Test4) :
  fieldM Q T a b f = (-zeta a * zeta b) • Q.operators.field (S.pin 4 (T a b)) f`
12. **[score=28]** `lemma YM.PhysicalNext.Repeat.Daisy.Charity.convulse`
(`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/Daisy/
Wisteria.lean:82`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma convulse (N: Captain H j q d v Y A b r B C' n χ0)
  (hhh:Herd H N.conduit A B n)(k : Plating (b₁:=b₁) M H N a t g c₁ u κ'
  e)(hZeta:|θp| * jewelDebt M Q L x ≤ 1)(O: Forest S.ratio): let g`
13. **[score=28]** `def YM.TraceExtension.zeta`
(`submission/YM/TraceExtension/Sundial/Grand.lean:12`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a:Axis):ℂ`
14. **[score=22]** `lemma YM.ConnectedActivityE6.Blaze.Eider.elastic`
(`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Pommel.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private lemma elastic {g : E→E} (K : ℝ≥0) (h : LipschitzWith K
  g) (hp : K < 1) [CompleteSpace E] : Bijective (fun x=>x+g x)`
15. **[score=22]** `theorem YM.Extension.UV.Tail.improve`
(`submission/YM/Extension/UV/Tail.lean:80`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem improve (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
  (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk
  : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (hw : ℕ) (m : ℕ) : s m ≤
  (1/3)^hw+(3/2)*(K*...`
16. **[score=22]** `lemma YM.Extension.UV.Tail.inward`
(`submission/YM/Extension/UV/Tail.lean:100`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma inward (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀ i,
  s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk : 0≤ K) (hd
  : ∀ i, d i ≤ K* R.b i) (m : ℕ) : s m ≤ (3/2)*(K*R.b m/R.radius m)`
17. **[score=22]** `lemma YM.Extension.UV.Tail.telescope`
(`submission/YM/Extension/UV/Tail.lean:108`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma telescope (h:Lipschitz R) (h₀ : d 0 ≤ 0) (hd : ∀ i,d
  (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) {K : ℝ} (hk :
  0≤ K) (hs : ∀ i, s i ≤ (3/2)*(K*R.b i /R.radius i)) (hK : ∀ i,d i ≤ K*R.b i)
  (m...`
18. **[score=22]** `lemma YM.Extension.UV.Tail.squeezing`
(`submission/YM/Extension/UV/Tail.lean:134`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma squeezing (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀
  i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd :
  ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) (hK :
  ∀...`
19. **[score=22]** `lemma YM.Extension.UV.Tail.unique_infinite`
(`submission/YM/Extension/UV/Tail.lean:150`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma unique_infinite (h:Lipschitz R) (hL: Limits R) {z
  z':ℕ→ℝ} {v v':∀ i,E i} (hv : InfiniteCourse R z v) (hv' : InfiniteCourse R z'
  v') : z=z' ∧ v=v'`
20. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_cap`
(`submission/YM/Extension/UV/Tail.lean:183`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_cap (h:Lipschitz R) (z : ℕ → ℕ→ℝ) (hz : ∀ N i, i
  ≤ N → z N i∈R.band i) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖iterate R z N
  k i‖ ≤ 1/4`
21. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_close`
(`submission/YM/Extension/UV/Tail.lean:190`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_close (h:Lipschitz R) (hc : FiniteCourse R zN
  vN) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖vN N i-iterate R zN N k i‖ ≤
  (1/3)^k*(1/4)`
22. **[score=22]** `lemma YM.Extension.UV.Tail.extract_beta`
(`submission/YM/Extension/UV/Tail.lean:202`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma extract_beta (h:Lipschitz R) (hc : FiniteCourse R zN vN)
  (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ ℕ, StrictMono φ ∧ ∃ z : ℕ →
  ℝ, z∈pi univ R.band ∧ Tendsto (zN ∘g ∘ φ) atTop (𝓝 z)`
23. **[score=22]** `lemma YM.Extension.UV.Tail.ground_limit`
(`submission/YM/Extension/UV/Tail.lean:216`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma ground_limit (h:Lipschitz R) (hL : Limits R) (g : ℕ→ℕ)
  (hg : Tendsto g atTop atTop) (i : ℕ) (z : ℕ→ℝ) {z' : ℝ} (hb : Tendsto z atTop
  (𝓝 z')) (hb' : z'∈ R.band (i+1)) (hz : ∀ᶠ k in atTop,z k∈ R.band (i+1)) {x :
  ℕ...`
24. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_converges`
(`submission/YM/Extension/UV/Tail.lean:234`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_converges (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) (k i : ℕ) : ∃ x:E i,
  ‖x‖...`
25. **[score=22]** `lemma YM.Extension.UV.Tail.entries_converge`
(`submission/YM/Extension/UV/Tail.lean:247`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma entries_converge (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) : ∃ x:∀ i,E i, Tendsto
  (v...`
26. **[score=22]** `lemma YM.Extension.UV.Tail.walk`
(`submission/YM/Extension/UV/Tail.lean:268`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma walk (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse
  R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃
  (z : ℕ→ℝ) (x : ∀ i,E i), InfiniteCourse R z x ∧ Tendsto (zN ∘ g ∘ φ) atTop
  (𝓝...`
27. **[score=22]** `theorem YM.Extension.UV.Tail.strong_limit`
(`submission/YM/Extension/UV/Tail.lean:282`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem strong_limit (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) : ∃ (z: ℕ→ℝ) (x : ∀i, E i), InfiniteCourse R z x ∧
  Tendsto zN atTop (𝓝 z) ∧ Tendsto vN atTop (𝓝 x)`
28. **[score=22]** `theorem YM.Extension.UV.Tail.inward_finite`
(`submission/YM/Extension/UV/Tail.lean:300`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem inward_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d N /
  R.radius N) (step : ∀ i, i < N → s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius
  (i+1))) (K : ℝ) (hk : 0≤ K) (hd : ∀ i ≤ N, d i ≤ K* R.b i) {m : ℕ} (hm : m...`
29. **[score=22]** `theorem YM.Extension.UV.Tail.squeezing_finite`
(`submission/YM/Extension/UV/Tail.lean:320`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem squeezing_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d
  N / R.radius N) (d_pos : 0 ≤ d N) (step : ∀ i, i<N → s i ≤ (1/3)*s (i+1) +
  (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd : ∀ i,i<N → d (i+1) ≤ d
  i+R.e...`
30. **[score=22]** `theorem YM.Extension.UV.Tail.unique_one`
(`submission/YM/Extension/UV/Tail.lean:351`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem unique_one (h:Lipschitz R) {N : ℕ} {z z':ℕ→ℝ} {v v':∀
  i,E i} {start : ℝ→ E N} (hs : ∀ x∈R.band N,∀ y∈R.band N, ‖start x-start y‖ ≤
  |x-y|/R.radius N) {t : ℝ} (hv : OnePath R N start t z v) (hv' : OnePath R N
  st...`
31. **[score=22]** `lemma YM.Extra.Iteration.psi_curl`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:153`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_curl (hi : P.diagonal.acts f * P.dual_diag.acts f =
  1) (hd : installed g T.T * Q.diagonal.acts c * d 1 c = P.diagonal.acts f * d 1
  f * installed g T.A0) : installed g (psi P Q T none) * d 1 c = d 1 f *
  insta...`
32. **[score=22]** `lemma YM.Extra.Iteration.psi_cancels`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:161`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_cancels (hg : Odd L.val) (hT : Harmonic T) : Cancels
  (psi P Q T)`
33. **[score=22]** `lemma YM.Extra.Iteration.Inherited.psi_nonneg`
(`submission/YM/Extra/ITERATION_NO_LOSS/Inherited.lean:27`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `private lemma psi_nonneg : 0 ≤ psiPrice Ω Ω'`
34. **[score=22]** `theorem YM.Further.CorrectedLift.Scratch.sharp`
(`submission/YM/Further/CORRECTED_LIFT_COEFFICIENTS/LensBill.lean:63`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem sharp : ∃ c : NNReal, LipschitzOnWith c
  (compareAt H W w a) (Set.Icc 0 1)`
35. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.star_theta`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:89`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma star_theta : star theta = theta`
36. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_sq`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:96`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_sq : theta * theta=1`
37. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_mul_mul`
(`submission/YM/Next/BOUNDARY/Derived.lean:41`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_mul_mul (X : M4) : theta*(theta*X)=X`
38. **[score=22]** `lemma YM.Next.Free.Flight.psi_bridge`
(`submission/YM/Next/FREE_KERNELS/Current.lean:94`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_bridge : installed (P.visitRatio hc) (psi k P)=(blue
  k P.wing).acts f*installed (P.visitRatio hc) (duo k P).T*(pink k P.land).acts
  c`
39. **[score=22]** `lemma YM.Precision.psi_proj`
(`submission/YM/PREC/FrameResponse.lean:70`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_proj (v : form 0 f) (x : Body 0 c) : (fixRoot S *ᵥ
  (d 0 f *ᵥ v)) x=v ((S.ratio.embed x.1),vac)- ∑ a,S.patch.weight a*v (atPoint S
  x.1 a,vac)`
40. **[score=22]** `lemma
YM.PhysicalNext.PhysicalGuard7f546.Curved.psiCost_nonneg`
(`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/Psi.lean:35`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psiCost_nonneg {s E A B : ℝ} (he : 0≤E) (ha : 0≤A) (hb :
  0≤B) : 0≤psiCost s E A B`
41. **[score=22]** `lemma YM.PhysicalNext.PhysicalGuard7f546.Curved.psi_rows`
(`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/Psi.lean:40`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_rows (Pt : Teller G) {A B C : ℝ} (hs : 0 ≤ C) (hb :
  0 ≤ B) (he : 0 ≤ Pt.C) (hr : C ≤ Pt.η) (T : Tube G S) (H L : Bed) (hf :
  H.covered C A) (hh : L.covered C B) (ht : Pt.Funds S T) : let m : ℝ`
42. **[score=22]** `lemma YM.PhysicalNext.RankCovariance.psi_physical`
(`submission/YM/PhysicalNext/RANK_COVARIANCE_ATLAS/Atlas.lean:161`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_physical {l : ℕ → ℕ → ℝ} (H : Horizon A) (h :
  ShapePort A H l) (hi : i < N) : psiStep A N i p = (H.H N (i+1)).dual_diag.acts
  (A.S.side (i+1) p) * installed (A.clock.op i p).ratio (H.towers N i).T * (H.H
  N i)...`
- **Docstring**: Identify ψ without changing M/T choices across p.
43. **[score=22]** `lemma
YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut.psiBudget_nn`
(`submission/YM/PhysicalNext/WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C/Issue/Cut/
Cells.lean:97`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psiBudget_nn (a : ℝ) (ha : 0≤a) : 0≤psiBudget a`
44. **[score=22]** `lemma YM.Progress.StationaryScenes.Response.psi`
(`submission/YM/Progress/STATIONARY_SCENES/Response.lean:108`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi (v : form 1 f) (x : Site f) (y : Site c) (t : ℕ) (B
  : ℝ) (hB : 0 ≤ B) (h : ∀ z : Body 1 f, separation x z.1 ≤ t → |v z| ≤ B) (hh :
  separation x (S.ratio.embed y) + 12*r₀ ≤ t) : |(fixRoot S *ᵥ v) (y,vac)| ≤
  1...`
- **Docstring**: `ψ` bill (root of the actual Q).
45. **[score=22]** `lemma YM.Push.Loops.Psi_diff`
(`submission/YM/Push/LOOP_COEFFICIENT/Joint.lean:109`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma Psi_diff (h : S.patch.Branches S.kernel G) (t :
  S.Choices) {U : E → Loops.Inputs G c f} (hu : U x = 1) (hf : MatDiffAt U x) :
  MatDiffAt (Psi t ∘ U) x`
46. **[score=22]** `lemma YM.Push.Mark.theta_one`
(`submission/YM/Push/RELAY_MARK/HGroup.lean:19`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_one (p : Label G d) : theta 1 p=p`
47. **[score=22]** `lemma YM.Push.Mark.theta_mul`
(`submission/YM/Push/RELAY_MARK/HGroup.lean:20`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_mul (s t : Signed) (p : Label G d) : theta (s*t)
  p=theta s (theta t p)`
48. **[score=22]** `lemma YM.Push.Mark.theta_unit`
(`submission/YM/Push/RELAY_MARK/HGroup.lean:23`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_unit (s : Signed) : theta s (unit G d)=unit G d`
49. **[score=22]** `lemma YM.Push.Mark.theta_bar`
(`submission/YM/Push/RELAY_MARK/HGroup.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_bar (s : Signed) (p : Label G d) : theta s
  (realBar p)=realBar (theta s p)`
50. **[score=22]** `lemma YM.RG08.Drift.psi_nurture`
(`submission/YM/RG08/Fields/Banjo.lean:47`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_nurture (k : ℝ) (hk : 0<k) (S : Flight j n) (hn : 4
  ≤ n) : Flight.psi k S=composeRows (composeRows (nativeRow S.L (blue k S.wing))
  (S.duo k).T) (pink k S.land)`
51. **[score=22]** `lemma YM.Trace.theta_fixed`
(`submission/YM/Trace/Fields.lean:60`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_fixed (e : ℝ) (g : Ortho) : Y.sector.turns.act 4 g
  (theta Y e) = theta Y e`
52. **[score=22]** `lemma YM.Trace.theta_real`
(`submission/YM/Trace/Fields.lean:63`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_real (e : ℝ) : S.conj Y.room.kernel.spin 4 (theta
  Y e) = theta Y e`
53. **[score=22]** `lemma YM.Trace.theta_star`
(`submission/YM/Trace/Fields.lean:70`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_star (e : ℝ) : Y.action.J (S.pin 4 (theta Y e)) =
  (S.pin 4 (theta Y e))`
54. **[score=22]** `theorem YM.Trace.theta_measure`
(`submission/YM/Trace/Fields.lean:88`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `theorem theta_measure (e : ℝ) : let v`
- **Docstring**: Real subtraction kept as a parameter to include the vacuum
  centering.
55. **[score=22]** `lemma YM.Trace.Terrace.cheap_theta`
(`submission/YM/TraceExtension/Terrace/Traveller.lean:10`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma cheap_theta (A:Levels G)(k:ℕ): ((A.budget k).threshold^
  (2:ℕ))⁻¹ ≤ A.clock.hatBeta k`
56. **[score=22]** `lemma YM.UVExtension.Oriel.lineT`
(`submission/YM/UVExtension/Oriel/Dial.lean:18`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private lemma lineT (hY: Dense (S:Set X))(hF : LipschitzOnWith
  L F G) (hp:∀ x∈G,x∈S →∀ y∈ S, DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0)
  (x)(hx:x∈G)(y:X): DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0`
57. **[score=22]** `lemma YM.UVExtension.Oriel.across`
(`submission/YM/UVExtension/Oriel/Dial.lean:53`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma across (hY: Dense (S:Set X))(hF : LipschitzOnWith L F G)
  (hp:∀ x∈G,x∈S →∀ y∈ S, DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0) : Bumps G
  F`
58. **[score=22]** `lemma YM.UVExtension.Oriel.wells`
(`submission/YM/UVExtension/Oriel/Dial.lean:71`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma wells {f:X→Y} {T:Set X} (h:LipschitzOnWith L f T)
  {M:ℝ}(he : ∀ x∈T, ‖f x‖≤ M) : ∃ F:X→Y,EqOn F f T∧ (∀ x∈closure T, ‖F x‖ ≤ M)∧
  LipschitzOnWith L F (closure T)`
59. **[score=22]** `lemma YM.UVExtension.Swell.theta`
(`submission/YM/UVExtension/Swell/Too.lean:70`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta (Q:Levels G): PolyB Q.S (fun i=> Q.clock.threshold
  i|>Inv.inv)`
60. **[score=22]** `lemma YM.Work.B06.theta_generates`
(`submission/YM/Work/B06.lean:54`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `private lemma theta_generates (W : Ortho → Prop) (hi : W 1)
  (hm : ∀ j k, W j → W k → W (j*k)) (hc : ∀ j : Ortho, W (j * theta * j⁻¹)) (k :
  Ortho) : W k`

## 3. Direct Constructive Port Candidates (Top 30)

- None found.

## 4. Cleared-Denominator Adaptation Candidates (Top 40)

1. **[score=64]** `lemma YM.Extension.UV.Bare.zeroFree`
(`submission/YM/Extension/UV/Bare.lean:47`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: zeroFree
- **Signature**: `lemma zeroFree (t : ℝ) : ∃ r>0,∀ s∈Metric.ball (t:ℂ) r,
  numerator (n:=n) (G:=G) 1 s≠0`
2. **[score=64]** `lemma YM.UVExtension.Pier.zeroFree`
(`submission/YM/UVExtension/Pier/Power.lean:49`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: zeroFree
- **Signature**: `lemma zeroFree (hr:0<r)(hc:0<a)(hb:0<b): ∃ t:ℝ,0<t∧ t<r∧∀
  f:ℂ→ℂ,DifferentiableOn ℂ f (ball 0 r)→ (∀ z∈ball (0:ℂ) r, ‖f z‖ ≤a) → b ≤ ‖f
  0‖ → ∀ z∈ ball (0:ℂ) t, b/2≤‖f z‖`
3. **[score=40]** `lemma YM.Extension.UV.Startup.datum_lipschitz`
(`submission/YM/Extension/UV/Canon/State.lean:105`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma datum_lipschitz {x y:ℝ} (hx:x∈strictBand a N)
  (hy:y∈strictBand a N) : ‖datum e (x:ℂ)-datum e (y:ℂ)‖ ≤ |x-y|/(a.clock.hatBeta
  N/2)`
4. **[score=40]** `lemma YM.Extension.UV.diam_lipschitz`
(`submission/YM/Extension/UV/Holo.lean:57`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma diam_lipschitz (hs : Convex ℝ U) (hU : ∀
  x∈U,DifferentiableAt ℂ f x) (h : ∀ x∈U,DifferentiableOn ℂ f (Metric.ball x r))
  (hM : ∀ x∈U, ∀ y ∈ Metric.ball x r,‖f y‖ ≤ M) (hr : 0<r) : ∀ x∈U,∀ y∈U,‖f x-f
  y‖ ≤ M/r * ‖x-y‖`
5. **[score=40]** `lemma YM.Planned.JetPort.lipschitzLower`
(`submission/YM/Planned/STATIONARY_JET_PORT/Enclosures.lean:17`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma lipschitzLower (h : Convex ℝ s) (hf : ∀ x∈s, ContDiffAt
  ℝ ω f x) (he : ∀ x∈s, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ C) {x y : E} (hx : x∈s)
  (hy : y∈s) : ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖`
6. **[score=40]** `lemma YM.Push.Uniform.Before.Service.trail_lipschitz`
(`submission/YM/Push/STATIONARY_UNIFORM/Along.lean:106`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma trail_lipschitz (hp : R.Bounds p μ C Λ) (hK : Larger
  (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) : let P`
7. **[score=38]** `structure YM.Extension.UV.Tail.Lipschitz`
(`submission/YM/Extension/UV/Tail.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `structure Lipschitz (R : Rules E) : Prop`
8. **[score=34]** `theorem YM.Tensor.Euler`
(`submission/YM/Analysis/Homogeneous.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem Euler (h : Sym A) (x : E) : fderiv ℝ (diagonal A) x x
  = (j : ℝ) • diagonal A x`
9. **[score=30]** `lemma YM.EveryPhase.Stress.zeta_square`
(`submission/YM/EveryPhase/Tensor.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_square (a : Axis) : zeta a * zeta a = -(eta a : ℂ)`
10. **[score=28]** `def YM.EveryPhase.Stress.zeta`
(`submission/YM/EveryPhase/Tensor.lean:22`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a : Axis) : ℂ`
11. **[score=28]** `lemma YM.EveryPhase.Stress.TM`
(`submission/YM/EveryPhase/Tensor.lean:207`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma TM (Q : Wightman S) (T : S.Stress) (a b) (f : Test4) :
  fieldM Q T a b f = (-zeta a * zeta b) • Q.operators.field (S.pin 4 (T a b)) f`
12. **[score=28]** `lemma YM.PhysicalNext.Repeat.Daisy.Charity.convulse`
(`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/Daisy/
Wisteria.lean:82`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma convulse (N: Captain H j q d v Y A b r B C' n χ0)
  (hhh:Herd H N.conduit A B n)(k : Plating (b₁:=b₁) M H N a t g c₁ u κ'
  e)(hZeta:|θp| * jewelDebt M Q L x ≤ 1)(O: Forest S.ratio): let g`
13. **[score=28]** `def YM.TraceExtension.zeta`
(`submission/YM/TraceExtension/Sundial/Grand.lean:12`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a:Axis):ℂ`
14. **[score=22]** `lemma YM.ConnectedActivityE6.Blaze.Eider.elastic`
(`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Pommel.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private lemma elastic {g : E→E} (K : ℝ≥0) (h : LipschitzWith K
  g) (hp : K < 1) [CompleteSpace E] : Bijective (fun x=>x+g x)`
15. **[score=22]** `theorem YM.Extension.UV.Tail.improve`
(`submission/YM/Extension/UV/Tail.lean:80`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem improve (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
  (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk
  : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (hw : ℕ) (m : ℕ) : s m ≤
  (1/3)^hw+(3/2)*(K*...`
16. **[score=22]** `lemma YM.Extension.UV.Tail.inward`
(`submission/YM/Extension/UV/Tail.lean:100`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma inward (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀ i,
  s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk : 0≤ K) (hd
  : ∀ i, d i ≤ K* R.b i) (m : ℕ) : s m ≤ (3/2)*(K*R.b m/R.radius m)`
17. **[score=22]** `lemma YM.Extension.UV.Tail.telescope`
(`submission/YM/Extension/UV/Tail.lean:108`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma telescope (h:Lipschitz R) (h₀ : d 0 ≤ 0) (hd : ∀ i,d
  (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) {K : ℝ} (hk :
  0≤ K) (hs : ∀ i, s i ≤ (3/2)*(K*R.b i /R.radius i)) (hK : ∀ i,d i ≤ K*R.b i)
  (m...`
18. **[score=22]** `lemma YM.Extension.UV.Tail.squeezing`
(`submission/YM/Extension/UV/Tail.lean:134`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma squeezing (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀
  i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd :
  ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) (hK :
  ∀...`
19. **[score=22]** `lemma YM.Extension.UV.Tail.unique_infinite`
(`submission/YM/Extension/UV/Tail.lean:150`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma unique_infinite (h:Lipschitz R) (hL: Limits R) {z
  z':ℕ→ℝ} {v v':∀ i,E i} (hv : InfiniteCourse R z v) (hv' : InfiniteCourse R z'
  v') : z=z' ∧ v=v'`
20. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_cap`
(`submission/YM/Extension/UV/Tail.lean:183`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_cap (h:Lipschitz R) (z : ℕ → ℕ→ℝ) (hz : ∀ N i, i
  ≤ N → z N i∈R.band i) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖iterate R z N
  k i‖ ≤ 1/4`
21. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_close`
(`submission/YM/Extension/UV/Tail.lean:190`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_close (h:Lipschitz R) (hc : FiniteCourse R zN
  vN) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖vN N i-iterate R zN N k i‖ ≤
  (1/3)^k*(1/4)`
22. **[score=22]** `lemma YM.Extension.UV.Tail.extract_beta`
(`submission/YM/Extension/UV/Tail.lean:202`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma extract_beta (h:Lipschitz R) (hc : FiniteCourse R zN vN)
  (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ ℕ, StrictMono φ ∧ ∃ z : ℕ →
  ℝ, z∈pi univ R.band ∧ Tendsto (zN ∘g ∘ φ) atTop (𝓝 z)`
23. **[score=22]** `lemma YM.Extension.UV.Tail.ground_limit`
(`submission/YM/Extension/UV/Tail.lean:216`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma ground_limit (h:Lipschitz R) (hL : Limits R) (g : ℕ→ℕ)
  (hg : Tendsto g atTop atTop) (i : ℕ) (z : ℕ→ℝ) {z' : ℝ} (hb : Tendsto z atTop
  (𝓝 z')) (hb' : z'∈ R.band (i+1)) (hz : ∀ᶠ k in atTop,z k∈ R.band (i+1)) {x :
  ℕ...`
24. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_converges`
(`submission/YM/Extension/UV/Tail.lean:234`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_converges (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) (k i : ℕ) : ∃ x:E i,
  ‖x‖...`
25. **[score=22]** `lemma YM.Extension.UV.Tail.entries_converge`
(`submission/YM/Extension/UV/Tail.lean:247`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma entries_converge (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) : ∃ x:∀ i,E i, Tendsto
  (v...`
26. **[score=22]** `lemma YM.Extension.UV.Tail.walk`
(`submission/YM/Extension/UV/Tail.lean:268`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma walk (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse
  R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃
  (z : ℕ→ℝ) (x : ∀ i,E i), InfiniteCourse R z x ∧ Tendsto (zN ∘ g ∘ φ) atTop
  (𝓝...`
27. **[score=22]** `theorem YM.Extension.UV.Tail.strong_limit`
(`submission/YM/Extension/UV/Tail.lean:282`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem strong_limit (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) : ∃ (z: ℕ→ℝ) (x : ∀i, E i), InfiniteCourse R z x ∧
  Tendsto zN atTop (𝓝 z) ∧ Tendsto vN atTop (𝓝 x)`
28. **[score=22]** `theorem YM.Extension.UV.Tail.inward_finite`
(`submission/YM/Extension/UV/Tail.lean:300`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem inward_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d N /
  R.radius N) (step : ∀ i, i < N → s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius
  (i+1))) (K : ℝ) (hk : 0≤ K) (hd : ∀ i ≤ N, d i ≤ K* R.b i) {m : ℕ} (hm : m...`
29. **[score=22]** `theorem YM.Extension.UV.Tail.squeezing_finite`
(`submission/YM/Extension/UV/Tail.lean:320`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem squeezing_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d
  N / R.radius N) (d_pos : 0 ≤ d N) (step : ∀ i, i<N → s i ≤ (1/3)*s (i+1) +
  (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd : ∀ i,i<N → d (i+1) ≤ d
  i+R.e...`
30. **[score=22]** `theorem YM.Extension.UV.Tail.unique_one`
(`submission/YM/Extension/UV/Tail.lean:351`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem unique_one (h:Lipschitz R) {N : ℕ} {z z':ℕ→ℝ} {v v':∀
  i,E i} {start : ℝ→ E N} (hs : ∀ x∈R.band N,∀ y∈R.band N, ‖start x-start y‖ ≤
  |x-y|/R.radius N) {t : ℝ} (hv : OnePath R N start t z v) (hv' : OnePath R N
  st...`
31. **[score=22]** `lemma YM.Extra.Iteration.psi_curl`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:153`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_curl (hi : P.diagonal.acts f * P.dual_diag.acts f =
  1) (hd : installed g T.T * Q.diagonal.acts c * d 1 c = P.diagonal.acts f * d 1
  f * installed g T.A0) : installed g (psi P Q T none) * d 1 c = d 1 f *
  insta...`
32. **[score=22]** `lemma YM.Extra.Iteration.psi_cancels`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:161`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_cancels (hg : Odd L.val) (hT : Harmonic T) : Cancels
  (psi P Q T)`
33. **[score=22]** `lemma YM.Extra.Iteration.Inherited.psi_nonneg`
(`submission/YM/Extra/ITERATION_NO_LOSS/Inherited.lean:27`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `private lemma psi_nonneg : 0 ≤ psiPrice Ω Ω'`
34. **[score=22]** `theorem YM.Further.CorrectedLift.Scratch.sharp`
(`submission/YM/Further/CORRECTED_LIFT_COEFFICIENTS/LensBill.lean:63`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem sharp : ∃ c : NNReal, LipschitzOnWith c
  (compareAt H W w a) (Set.Icc 0 1)`
35. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.star_theta`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:89`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma star_theta : star theta = theta`
36. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_sq`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:96`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_sq : theta * theta=1`
37. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_mul_mul`
(`submission/YM/Next/BOUNDARY/Derived.lean:41`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_mul_mul (X : M4) : theta*(theta*X)=X`
38. **[score=22]** `lemma YM.Next.Free.Flight.psi_bridge`
(`submission/YM/Next/FREE_KERNELS/Current.lean:94`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_bridge : installed (P.visitRatio hc) (psi k P)=(blue
  k P.wing).acts f*installed (P.visitRatio hc) (duo k P).T*(pink k P.land).acts
  c`
39. **[score=22]** `lemma YM.Precision.psi_proj`
(`submission/YM/PREC/FrameResponse.lean:70`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_proj (v : form 0 f) (x : Body 0 c) : (fixRoot S *ᵥ
  (d 0 f *ᵥ v)) x=v ((S.ratio.embed x.1),vac)- ∑ a,S.patch.weight a*v (atPoint S
  x.1 a,vac)`
40. **[score=22]** `lemma
YM.PhysicalNext.PhysicalGuard7f546.Curved.psiCost_nonneg`
(`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/Psi.lean:35`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psiCost_nonneg {s E A B : ℝ} (he : 0≤E) (ha : 0≤A) (hb :
  0≤B) : 0≤psiCost s E A B`

## 5. Axiom- or Sorry-Blocked Candidates (Top 20)

- None found.

## 6. Target-Module & 7/8 Exponent Highlights

### `src/LeanAsm/QuasiRiemann/UltraDeep72.lean` (Top 10)

- **[score=64]** `lemma YM.Extension.UV.Bare.zeroFree`
  (`submission/YM/Extension/UV/Bare.lean:47`) [zeroFree]
- **[score=64]** `lemma YM.UVExtension.Pier.zeroFree`
  (`submission/YM/UVExtension/Pier/Power.lean:49`) [zeroFree]
- **[score=40]** `lemma YM.Extension.UV.Startup.datum_lipschitz`
  (`submission/YM/Extension/UV/Canon/State.lean:105`) [Lipschitz]
- **[score=40]** `lemma YM.Extension.UV.diam_lipschitz`
  (`submission/YM/Extension/UV/Holo.lean:57`) [Lipschitz]
- **[score=40]** `lemma YM.Planned.JetPort.lipschitzLower`
  (`submission/YM/Planned/STATIONARY_JET_PORT/Enclosures.lean:17`) [Lipschitz]
- **[score=40]** `lemma YM.Push.Uniform.Before.Service.trail_lipschitz`
  (`submission/YM/Push/STATIONARY_UNIFORM/Along.lean:106`) [Lipschitz]
- **[score=38]** `structure YM.Extension.UV.Tail.Lipschitz`
  (`submission/YM/Extension/UV/Tail.lean:43`) [Lipschitz]
- **[score=22]** `lemma YM.ConnectedActivityE6.Blaze.Eider.elastic`
  (`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Pommel.lean:45`)
  [Lipschitz]
- **[score=22]** `theorem YM.Extension.UV.Tail.improve`
  (`submission/YM/Extension/UV/Tail.lean:80`) [Lipschitz]
- **[score=22]** `lemma YM.Extension.UV.Tail.inward`
  (`submission/YM/Extension/UV/Tail.lean:100`) [Lipschitz]

### `src/LeanAsm/EulerFactorNonVanishing.lean` (Top 10)

- **[score=34]** `theorem YM.Tensor.Euler`
  (`submission/YM/Analysis/Homogeneous.lean:24`) [Euler]
- **[score=30]** `lemma YM.EveryPhase.Stress.zeta_square`
  (`submission/YM/EveryPhase/Tensor.lean:24`) [zeta]
- **[score=28]** `def YM.EveryPhase.Stress.zeta`
  (`submission/YM/EveryPhase/Tensor.lean:22`) [zeta]
- **[score=28]** `lemma YM.EveryPhase.Stress.TM`
  (`submission/YM/EveryPhase/Tensor.lean:207`) [zeta]
- **[score=28]** `lemma YM.PhysicalNext.Repeat.Daisy.Charity.convulse`
  (`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/Daisy/
  Wisteria.lean:82`)
  [zeta]
- **[score=28]** `def YM.TraceExtension.zeta`
  (`submission/YM/TraceExtension/Sundial/Grand.lean:12`) [zeta]
- **[score=21]** `lemma YM.EveryPhase.Stress.Killing.tilted_boost`
  (`submission/YM/EveryPhase/Killing.lean:41`) [theta, zeta]
- **[score=21]** `lemma YM.EveryPhase.Stress.we_split`
  (`submission/YM/EveryPhase/Shell.lean:108`) [theta, zeta]
- **[score=20]** `def YM.WardBin.euler`
  (`submission/YM/Next/WARD_BIN/Energy.lean:164`) [Euler]
- **[score=15]** `lemma YM.EveryPhase.Stress.boost_scale`
  (`submission/YM/EveryPhase/Tensor.lean:109`) [theta, zeta]

### `src/LeanAsm/QuasiRiemann/ZeroDensityBridge.lean` (Top 10)

- **[score=16]** `lemma YM.ConnectedActivityE6.SliceRows.sqrt_compare`
  (`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Remainder.lean:60`)
  [3/4]
- **[score=16]** `lemma YM.FullVolume.deep_margin`
  (`submission/YM/FullVolume/Arc.lean:40`) [3/4]
- **[score=16]** `lemma YM.PhysicalNext.Repeat.Muse.Contest.bound`
  (`submission/YM/FullVolume/Gain/Motion.lean:78`) [3/4]
- **[score=16]** `lemma YM.PhysicalNext.Repeat.Pass.good_mild`
  (`submission/YM/FullVolume/Table/Atlas.lean:49`) [3/4]
- **[score=16]** `lemma YM.ConnectedActivityE6.Lim.Umbra.raises`
  (`submission/YM/FullVolume/Umbra/Marys.lean:24`) [3/4]
- **[score=16]** `theorem YM.Next.Rank.Perch.holed`
  (`submission/YM/Next/RANK/Bird.lean:89`) [3/4]
- **[score=16]** `theorem YM.Next.Rank.Perch.sunny`
  (`submission/YM/Next/RANK/Bird.lean:100`) [3/4]
- **[score=16]** `lemma YM.PhysicalNext.InteractingRank.Milk.smashes`
  (`submission/YM/PhysicalNext/AFTERNOON_INTERACTING_RANK_COMPARISON/Opacity/
  Turbine.lean:48`)
  [3/4]
- **[score=16]** `lemma YM.PhysicalNext.PhysicalGuard7f546.Curved.linkRoom_sq`
  (`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/
  Scales.lean:27`)
  [3/4]
- **[score=16]** `lemma YM.PhysicalNext.Repeat.Yearling.comforts`
  (`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/
  Yearling/Elixir.lean:61`)
  [3/4]

### `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` (Top 10)

- **[score=22]** `lemma YM.Extra.Iteration.psi_curl`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:153`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.psi_cancels`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:161`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.Inherited.psi_nonneg`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Inherited.lean:27`) [psi]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.star_theta`
  (`submission/YM/Next/BOUNDARY/Coordinates.lean:89`) [theta]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_sq`
  (`submission/YM/Next/BOUNDARY/Coordinates.lean:96`) [theta]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_mul_mul`
  (`submission/YM/Next/BOUNDARY/Derived.lean:41`) [theta]
- **[score=22]** `lemma YM.Next.Free.Flight.psi_bridge`
  (`submission/YM/Next/FREE_KERNELS/Current.lean:94`) [psi]
- **[score=22]** `lemma YM.Precision.psi_proj`
  (`submission/YM/PREC/FrameResponse.lean:70`) [psi]
- **[score=22]** `lemma
  YM.PhysicalNext.PhysicalGuard7f546.Curved.psiCost_nonneg`
  (`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/Psi.lean:35`)
  [psi]
- **[score=22]** `lemma YM.PhysicalNext.PhysicalGuard7f546.Curved.psi_rows`
  (`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/Psi.lean:40`)
  [psi]

## 7. Pure Constructive Files & Declarations (All 21 Files)

1. `checks/AxiomAudit.lean` (12L, 0 decls)
   - (no top-level declarations)
2. `provenance/lgt/LGT/GaugeField/Connection.lean` (74L, 8 decls)
   - L31 `def GaugeConnection`
   - L34 `def AsymGaugeConnection`
   - L40 `def plaquetteHolonomy`
   - L45 `def asymPlaquetteHolonomy`
   - L53 `def GaugeTransform`
   - L56 `def AsymGaugeTransform`
   - L60 `def gaugeTransformConnection`
   - L65 `theorem holonomy_gauge_covariant`
3. `provenance/lgt/LGT/GaugeField/Holonomy.lean` (1L, 0 decls)
   - (no top-level declarations)
4. `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean` (1L, 0 decls)
   - (no top-level declarations)
5. `submission/Solution.lean` (10L, 1 decls)
   - L4 `theorem YangMills.jointExistence`
6. `submission/YM.lean` (1L, 0 decls)
   - (no top-level declarations)
7. `submission/YM/Lattice/Faces.lean` (145L, 20 decls)
   - L13 `abbrev YM.Lattice.PlaqAxes`
   - L14 `abbrev YM.Lattice.Face`
   - L18 `def YM.Lattice.PlaqAxes.ordered`
   - L24 `def YM.Lattice.PlaqAxes.rotate`
   - L27 `theorem YM.Lattice.PlaqAxes.rotate_inv`
   - L38 `def YM.Lattice.PlaqAxes.transform`
   - L47 `def YM.Lattice.faceValue`
   - L49 `theorem YM.Lattice.face_gauge`
   - L54 `theorem YM.Lattice.Step.rev_rev`
   - L57 `def YM.Lattice.oriented`
   - L59 `theorem YM.Lattice.stop_oriented`
   - L62 `theorem YM.Lattice.oriented_swap`
   - L69 `theorem YM.Lattice.oriented_next`
   - L81 `theorem YM.Lattice.price_flip`
   - L88 `def YM.Lattice.atFace`
   - L92 `theorem YM.Lattice.price_shift_pos`
   - L112 `def YM.Lattice.Face.lower`
   - L115 `def YM.Lattice.Face.send`
   - L119 `theorem YM.Lattice.Face.injective_send`
   - L128 `theorem YM.Lattice.Face.send_price`
8. `submission/YM/Lattice/Foliation.lean` (108L, 14 decls)
   - L15 `def YM.Lattice.layers`
   - L18 `def YM.Lattice.slab`
   - L21 `lemma YM.Lattice.box_iff_layers`
   - L23 `lemma YM.Lattice.card_layers`
   - L25 `lemma YM.Lattice.slab_iff`
   - L27 `lemma YM.Lattice.update_box`
   - L30 `lemma YM.Lattice.lower_pin`
   - L42 `lemma YM.Lattice.step_between`
   - L52 `lemma YM.Lattice.slab_update_image`
   - L62 `theorem YM.Lattice.slab_sum`
   - L73 `lemma YM.Lattice.axis_orthogonal`
   - L80 `theorem YM.Lattice.square_corners`
   - L86 `lemma YM.Lattice.axis_route_support`
   - L91 `theorem YM.Lattice.carry_succ`
9. `submission/YM/Lattice/Route.lean` (62L, 15 decls)
   - L10 `theorem YM.Lattice.reverse_append`
   - L12 `theorem YM.Lattice.reverse_straight`
   - L17 `theorem YM.Lattice.axisRoute_append`
   - L19 `theorem YM.Lattice.axisRoute_reverse`
   - L24 `lemma YM.Lattice.rev_range`
   - L26 `def YM.Lattice.backward`
   - L28 `theorem YM.Lattice.backward_back`
   - L30 `def YM.Lattice.backOrder`
   - L32 `theorem YM.Lattice.back_axes`
   - L36 `theorem YM.Lattice.back_route`
   - L39 `lemma YM.Lattice.indexRoute`
   - L45 `def YM.Lattice.sendOrder`
   - L47 `lemma YM.Lattice.sendOrder_inv`
   - L49 `def YM.Lattice.orderEquiv`
   - L55 `theorem YM.Lattice.send_route`
10. `submission/YM/UVExtension/Orchard/Apple.lean` (13L, 0 decls)
   - (no top-level declarations)
11. `submission/YM/UVExtension/Orchard/Barrel.lean` (71L, 4 decls)
   - L35 `def Aging.agingName`
   - L36 `def Aging.ferment`
   - L41 `def Aging.wine`
   - L43 `def Aging.store`
12. `submission/YM/UVExtension/Orchard/Muesli.lean` (10L, 0 decls)
   - (no top-level declarations)
13. `submission/YM/UVExtension/Orchard/Pours.lean` (11L, 0 decls)
   - (no top-level declarations)
14. `submission/YM/UVExtension/Orchard/Shears.lean` (12L, 0 decls)
   - (no top-level declarations)
15. `submission/YM/UVExtension/Orchard/Tarts.lean` (7L, 0 decls)
   - (no top-level declarations)
16. `submission/YM/UVExtension/Orchard/Vanilla.lean` (6L, 0 decls)
   - (no top-level declarations)
17. `submission/verification/Inventory.lean` (28L, 0 decls)
   - (no top-level declarations)
18. `submission/verification/Usage.lean` (66L, 1 decls)
   - L11 `def auditModule`
19. `verification/controls/accept/Solution.lean` (1L, 1 decls)
   - L1 `theorem comparatorSmoke`
20. `verification/controls/definition_mismatch/Solution.lean` (2L, 2 decls)
   - L1 `def reference`
   - L2 `theorem comparatorSmoke`
21. `verification/controls/statement_mismatch/Solution.lean` (1L, 1 decls)
   - L1 `theorem comparatorSmoke`

<!-- end of file: leanasm/docs/openai-20261028/QRH_7_8_CANDIDATES.md -->
