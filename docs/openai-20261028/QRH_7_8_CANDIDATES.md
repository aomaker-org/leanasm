<!-- Path: leanasm/docs/openai-20261028/QRH_7_8_CANDIDATES.md -->
<!-- Max Column: 80 Columns -->

# QRH 7/8 Relevance Scan & Portability Candidates

## 1. Summary & Classification Breakdown

- **Total Matched Decls**: 782
- **Concepts Scanned**: 3/4, 7 / 8, 7/8, Chebyshev, Dirichlet, Euler,
  EulerMaclaurin, Lipschitz, Mellin, Perron, QRH, QuasiRiemann, criticalStrip,
  mollifier, primeGap, psi, shortInterval, theta, vonMangoldt, zeroDensity,
  zeroFree, zeta

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
3. **[score=52]** `lemma YM.EveryPhase.Stress.zeta_wick`
(`submission/YM/EveryPhase/Tensor.lean:23`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_wick (a : Axis) : zeta a * wick a = 1`
4. **[score=52]** `lemma YM.EveryPhase.Stress.zeta_square`
(`submission/YM/EveryPhase/Tensor.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_square (a : Axis) : zeta a * zeta a = -(eta a : ℂ)`
5. **[score=50]** `def YM.EveryPhase.Stress.zeta`
(`submission/YM/EveryPhase/Tensor.lean:22`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a : Axis) : ℂ`
6. **[score=50]** `def YM.TraceExtension.zeta`
(`submission/YM/TraceExtension/Sundial/Grand.lean:12`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a:Axis):ℂ`
7. **[score=42]** `def YM.WardBin.euler`
(`submission/YM/Next/WARD_BIN/Energy.lean:164`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `def euler (U : Links R G.El) (e : Edge (Four R)) : G.Color`
- **Docstring**: The Euler gradient with respect to positive links.
8. **[score=40]** `lemma YM.Extension.UV.Startup.datum_lipschitz`
(`submission/YM/Extension/UV/Canon/State.lean:105`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma datum_lipschitz {x y:ℝ} (hx:x∈strictBand a N)
  (hy:y∈strictBand a N) : ‖datum e (x:ℂ)-datum e (y:ℂ)‖ ≤ |x-y|/(a.clock.hatBeta
  N/2)`
9. **[score=40]** `lemma YM.Extension.UV.diam_lipschitz`
(`submission/YM/Extension/UV/Holo.lean:57`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma diam_lipschitz (hs : Convex ℝ U) (hU : ∀
  x∈U,DifferentiableAt ℂ f x) (h : ∀ x∈U,DifferentiableOn ℂ f (Metric.ball x r))
  (hM : ∀ x∈U, ∀ y ∈ Metric.ball x r,‖f y‖ ≤ M) (hr : 0<r) : ∀ x∈U,∀ y∈U,‖f x-f
  y‖ ≤ M/r * ‖x-y‖`
10. **[score=40]** `lemma YM.Planned.JetPort.lipschitzLower`
(`submission/YM/Planned/STATIONARY_JET_PORT/Enclosures.lean:17`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma lipschitzLower (h : Convex ℝ s) (hf : ∀ x∈s, ContDiffAt
  ℝ ω f x) (he : ∀ x∈s, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ C) {x y : E} (hx : x∈s)
  (hy : y∈s) : ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖`
11. **[score=40]** `lemma YM.Push.Uniform.Before.Service.trail_lipschitz`
(`submission/YM/Push/STATIONARY_UNIFORM/Along.lean:106`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma trail_lipschitz (hp : R.Bounds p μ C Λ) (hK : Larger
  (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) : let P`
12. **[score=38]** `structure YM.Extension.UV.Tail.Lipschitz`
(`submission/YM/Extension/UV/Tail.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `structure Lipschitz (R : Rules E) : Prop`
13. **[score=37]** `lemma YM.EveryPhase.Stress.boost_scale`
(`submission/YM/EveryPhase/Tensor.lean:109`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: theta, zeta
- **Signature**: `lemma boost_scale (a i : Axis) {X : M4} (h : boostLike X) :
  zeta a * (-I) * ((X * theta) i a:ℂ) = zeta i * (X i a:ℂ)`
14. **[score=37]** `lemma YM.EveryPhase.Stress.space_scale`
(`submission/YM/EveryPhase/Tensor.lean:171`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: theta, zeta
- **Signature**: `lemma space_scale (a i : Axis) {X : M4} (h : theta*X=X*theta)
  : zeta a * (X i a:ℂ)=zeta i * (X i a:ℂ)`
15. **[score=34]** `theorem YM.Tensor.Euler`
(`submission/YM/Analysis/Homogeneous.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem Euler (h : Sym A) (x : E) : fderiv ℝ (diagonal A) x x
  = (j : ℝ) • diagonal A x`
16. **[score=34]** `lemma YM.Extra.FD.SphereTest.Pure.euler`
(`submission/YM/Extra/FREE_DETECTOR_ALGEBRA/Laplace.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma Pure.euler (hf : Pure j f) (x : E4) : ∑ i : Axis, x i •
  grad i f x = (j:ℝ) • f x`
17. **[score=34]** `theorem YM.Maxwell.grad_euler`
(`submission/YM/Maxwell/Exterior.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem grad_euler (A : T E4 F j) (h : Sym A) (x : E4) : ∑ k :
  Axis, x k • grad k (diagonal A) x = (j : ℝ) • diagonal A x`
18. **[score=34]** `lemma YM.WardBin.continuous_euler`
(`submission/YM/Next/WARD_BIN/Energy.lean:167`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `@[fun_prop] lemma continuous_euler {e : Edge (Four R)} :
  Continuous fun U : Links R G.El => euler U e`
19. **[score=34]** `lemma YM.WardBin.euler_gauge`
(`submission/YM/Next/WARD_BIN/Energy.lean:170`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_gauge (U : Links R G.El) (e : Edge (Four R)) (T :
  Four R → G.El) : euler (Lattice.gauge T U) e = G.adjoint (T e.1) (euler U e)`
20. **[score=34]** `lemma YM.WardBin.euler_at`
(`submission/YM/Next/WARD_BIN/Energy.lean:175`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_at {n : Side} (U : Config G n) (o : Site n) (x :
  Cover) (i : Axis) : euler (expandAt o U) (x,i) = euler U (wrap n x + o,i)`
21. **[score=34]** `lemma YM.Primitives.SmallFieldExterior.dirichlet_sq`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:52`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `lemma dirichlet_sq (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) :
  Dirichlet w r V u ^ 2 = ∑ i, w i ^2 * size r V (pc i u)^2`
22. **[score=34]** `lemma YM.Primitives.SmallFieldExterior.dirichlet_nn`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:54`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `lemma dirichlet_nn (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) :
  0 ≤ Dirichlet w r V u`
23. **[score=34]** `lemma YM.Push.FiniteDetection.Kelvin.euler_step`
(`submission/YM/Push/FINITE_DETECTION/Harmonic.lean:124`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_step (A : T E4 ℝ (j+1)) (x : E4) : ∑ i : Axis, x i
  * diagonal (A.curryLeft (basis i)) x = diagonal A x`
24. **[score=34]** `lemma YM.Trace.euler`
(`submission/YM/TraceExtension/Foundation/Dilate.lean:38`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler (w : Fin 3 → ℝ) (b : Axis) : (bareVector (G:=G)
  w).val b = (w 0 • ∑ i : Axis,(pairDeriv G b i b b i + pairDeriv G b i b b i))
  + (w 1 • ∑ a, ∑ i : Axis,(pairDeriv G a i b a i+ pairDeriv G a i b a i))+ (w
  2...`
25. **[score=34]** `lemma YM.TraceExtension.Wick.euler`
(`submission/YM/TraceExtension/Wick/Massive.lean:69`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler (m j s) (hs : 0<s) : s*moment m (j+2) 0 s=(j+3:ℝ)*
  moment m j 1 s`
26. **[score=32]** `def YM.Primitives.SmallFieldExterior.Dirichlet`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:28`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `def Dirichlet (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ)`
27. **[score=28]** `lemma YM.EveryPhase.Stress.cloth_split`
(`submission/YM/EveryPhase/Decree.lean:18`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma cloth_split (j : Fin (n+1)) (M : Joint n) (K : Killing)
  (b : Axis) (s : ℝ) (g) : cloth M j (stack K b s g) = zeta b • cloth M j (touch
  K b g) + affect K b s • cloth M j g`
28. **[score=28]** `lemma YM.EveryPhase.Stress.uplifting`
(`submission/YM/EveryPhase/Frost.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma uplifting (K : Killing) (b : Axis) (x : Space3) (t s :
  ℝ) : K.w b (lay x (arch t s))= zeta b*(K.realV (position x t) b:ℂ)+affect K b
  s`
29. **[score=28]** `lemma YM.EveryPhase.Stress.stack_zero`
(`submission/YM/EveryPhase/Frost.lean:53`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma stack_zero (K : Killing) (b : Axis) (f) : stack K b 0
  f=zeta b • touch K b f`
30. **[score=28]** `lemma YM.EveryPhase.Stress.Killing.w_real`
(`submission/YM/EveryPhase/Killing.lean:31`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma w_real (b : Axis) (r : Space3) (t : ℝ) : K.w b (lay r t)
  = zeta b * (K.realV (position r t) b:ℂ)`
31. **[score=28]** `lemma YM.EveryPhase.Stress.TM`
(`submission/YM/EveryPhase/Tensor.lean:207`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma TM (Q : Wightman S) (T : S.Stress) (a b) (f : Test4) :
  fieldM Q T a b f = (-zeta a * zeta b) • Q.operators.field (S.pin 4 (T a b)) f`
32. **[score=28]** `lemma YM.PhysicalNext.Repeat.Daisy.Charity.convulse`
(`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/Daisy/
Wisteria.lean:82`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma convulse (N: Captain H j q d v Y A b r B C' n χ0)
  (hhh:Herd H N.conduit A B n)(k : Plating (b₁:=b₁) M H N a t g c₁ u κ'
  e)(hZeta:|θp| * jewelDebt M Q L x ≤ 1)(O: Forest S.ratio): let g`
33. **[score=28]** `theorem YM.Push.PriceCompiler.Preparations.withTheta`
(`submission/YM/Push/PRICE_COMPILER/Post.lean:117`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `theorem withTheta (q : AfterBill) (u : PostCost D → ℕ → ℝ) (h
  : ∀ i, 0 < u (m.budget q) i) : ∃ T : Protection D, T.theta ≤ u (m.budget q)`
- **Docstring**: Example phase: theta can be chosen *after* these budgets, even
  when its bound uses them; arbitrary positive upper requests. Can shrink it
  further **before**...
34. **[score=22]** `lemma YM.ConnectedActivityE6.Blaze.Eider.elastic`
(`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Pommel.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private lemma elastic {g : E→E} (K : ℝ≥0) (h : LipschitzWith K
  g) (hp : K < 1) [CompleteSpace E] : Bijective (fun x=>x+g x)`
35. **[score=22]** `theorem YM.Extension.UV.Tail.improve`
(`submission/YM/Extension/UV/Tail.lean:80`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem improve (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
  (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk
  : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (hw : ℕ) (m : ℕ) : s m ≤
  (1/3)^hw+(3/2)*(K*...`
36. **[score=22]** `lemma YM.Extension.UV.Tail.inward`
(`submission/YM/Extension/UV/Tail.lean:100`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma inward (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀ i,
  s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk : 0≤ K) (hd
  : ∀ i, d i ≤ K* R.b i) (m : ℕ) : s m ≤ (3/2)*(K*R.b m/R.radius m)`
37. **[score=22]** `lemma YM.Extension.UV.Tail.telescope`
(`submission/YM/Extension/UV/Tail.lean:108`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma telescope (h:Lipschitz R) (h₀ : d 0 ≤ 0) (hd : ∀ i,d
  (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) {K : ℝ} (hk :
  0≤ K) (hs : ∀ i, s i ≤ (3/2)*(K*R.b i /R.radius i)) (hK : ∀ i,d i ≤ K*R.b i)
  (m...`
38. **[score=22]** `lemma YM.Extension.UV.Tail.squeezing`
(`submission/YM/Extension/UV/Tail.lean:134`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma squeezing (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀
  i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd :
  ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) (hK :
  ∀...`
39. **[score=22]** `lemma YM.Extension.UV.Tail.unique_infinite`
(`submission/YM/Extension/UV/Tail.lean:150`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma unique_infinite (h:Lipschitz R) (hL: Limits R) {z
  z':ℕ→ℝ} {v v':∀ i,E i} (hv : InfiniteCourse R z v) (hv' : InfiniteCourse R z'
  v') : z=z' ∧ v=v'`
40. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_cap`
(`submission/YM/Extension/UV/Tail.lean:183`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_cap (h:Lipschitz R) (z : ℕ → ℕ→ℝ) (hz : ∀ N i, i
  ≤ N → z N i∈R.band i) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖iterate R z N
  k i‖ ≤ 1/4`
41. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_close`
(`submission/YM/Extension/UV/Tail.lean:190`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_close (h:Lipschitz R) (hc : FiniteCourse R zN
  vN) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖vN N i-iterate R zN N k i‖ ≤
  (1/3)^k*(1/4)`
42. **[score=22]** `lemma YM.Extension.UV.Tail.extract_beta`
(`submission/YM/Extension/UV/Tail.lean:202`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma extract_beta (h:Lipschitz R) (hc : FiniteCourse R zN vN)
  (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ ℕ, StrictMono φ ∧ ∃ z : ℕ →
  ℝ, z∈pi univ R.band ∧ Tendsto (zN ∘g ∘ φ) atTop (𝓝 z)`
43. **[score=22]** `lemma YM.Extension.UV.Tail.ground_limit`
(`submission/YM/Extension/UV/Tail.lean:216`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma ground_limit (h:Lipschitz R) (hL : Limits R) (g : ℕ→ℕ)
  (hg : Tendsto g atTop atTop) (i : ℕ) (z : ℕ→ℝ) {z' : ℝ} (hb : Tendsto z atTop
  (𝓝 z')) (hb' : z'∈ R.band (i+1)) (hz : ∀ᶠ k in atTop,z k∈ R.band (i+1)) {x :
  ℕ...`
44. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_converges`
(`submission/YM/Extension/UV/Tail.lean:234`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_converges (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) (k i : ℕ) : ∃ x:E i,
  ‖x‖...`
45. **[score=22]** `lemma YM.Extension.UV.Tail.entries_converge`
(`submission/YM/Extension/UV/Tail.lean:247`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma entries_converge (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) {z : ℕ→ℝ} (hZ :
  z∈pi univ R.band) (hZ' : Tendsto (zN ∘g) atTop (𝓝 z)) : ∃ x:∀ i,E i, Tendsto
  (v...`
46. **[score=22]** `lemma YM.Extension.UV.Tail.walk`
(`submission/YM/Extension/UV/Tail.lean:268`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma walk (h:Lipschitz R) (hL : Limits R) (hc : FiniteCourse
  R zN vN) (g : ℕ→ℕ) (hg : Tendsto g atTop atTop) : ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃
  (z : ℕ→ℝ) (x : ∀ i,E i), InfiniteCourse R z x ∧ Tendsto (zN ∘ g ∘ φ) atTop
  (𝓝...`
47. **[score=22]** `theorem YM.Extension.UV.Tail.strong_limit`
(`submission/YM/Extension/UV/Tail.lean:282`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem strong_limit (h:Lipschitz R) (hL : Limits R) (hc :
  FiniteCourse R zN vN) : ∃ (z: ℕ→ℝ) (x : ∀i, E i), InfiniteCourse R z x ∧
  Tendsto zN atTop (𝓝 z) ∧ Tendsto vN atTop (𝓝 x)`
48. **[score=22]** `theorem YM.Extension.UV.Tail.inward_finite`
(`submission/YM/Extension/UV/Tail.lean:300`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem inward_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d N /
  R.radius N) (step : ∀ i, i < N → s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius
  (i+1))) (K : ℝ) (hk : 0≤ K) (hd : ∀ i ≤ N, d i ≤ K* R.b i) {m : ℕ} (hm : m...`
49. **[score=22]** `theorem YM.Extension.UV.Tail.squeezing_finite`
(`submission/YM/Extension/UV/Tail.lean:320`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem squeezing_finite (h:Lipschitz R) (N : ℕ) (hN: s N ≤ d
  N / R.radius N) (d_pos : 0 ≤ d N) (step : ∀ i, i<N → s i ≤ (1/3)*s (i+1) +
  (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd : ∀ i,i<N → d (i+1) ≤ d
  i+R.e...`
50. **[score=22]** `theorem YM.Extension.UV.Tail.unique_one`
(`submission/YM/Extension/UV/Tail.lean:351`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `theorem unique_one (h:Lipschitz R) {N : ℕ} {z z':ℕ→ℝ} {v v':∀
  i,E i} {start : ℝ→ E N} (hs : ∀ x∈R.band N,∀ y∈R.band N, ‖start x-start y‖ ≤
  |x-y|/R.radius N) {t : ℝ} (hv : OnePath R N start t z v) (hv' : OnePath R N
  st...`
51. **[score=22]** `lemma YM.Extra.Iteration.psi_strip`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:130`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_strip (a : Option Axis) : (psi P Q T a).strip η
  (psiPrice Ω Ω' / (L.val:ℝ)^(2+raised a))`
52. **[score=22]** `lemma YM.Extra.Iteration.psi_matrix`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:138`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_matrix (a : Option Axis) : installed g (psi P Q T a)
  = (P.dual_diag.acts f * installed g (moving T.T a)) * Q.diagonal.acts c`
53. **[score=22]** `lemma YM.Extra.Iteration.psi_read`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:143`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_read (hg : Odd L.val) (a : Option Axis) (v : Co c
  (TypeFace 2) → ℝ) (x b) : (installed g (psi P Q T a) *ᵥ v) (x,b) =
  Iteration.read a (fun z => (installed g (psi P Q T none) *ᵥ v) (z,b)) x`
54. **[score=22]** `lemma YM.Extra.Iteration.psi_curl`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:153`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_curl (hi : P.diagonal.acts f * P.dual_diag.acts f =
  1) (hd : installed g T.T * Q.diagonal.acts c * d 1 c = P.diagonal.acts f * d 1
  f * installed g T.A0) : installed g (psi P Q T none) * d 1 c = d 1 f *
  insta...`
55. **[score=22]** `lemma YM.Extra.Iteration.psi_cancels`
(`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:161`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `lemma psi_cancels (hg : Odd L.val) (hT : Harmonic T) : Cancels
  (psi P Q T)`
56. **[score=22]** `lemma YM.Extra.Iteration.Inherited.psi_nonneg`
(`submission/YM/Extra/ITERATION_NO_LOSS/Inherited.lean:27`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: psi
- **Signature**: `private lemma psi_nonneg : 0 ≤ psiPrice Ω Ω'`
57. **[score=22]** `theorem YM.Further.CorrectedLift.Scratch.sharp`
(`submission/YM/Further/CORRECTED_LIFT_COEFFICIENTS/LensBill.lean:63`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem sharp : ∃ c : NNReal, LipschitzOnWith c
  (compareAt H W w a) (Set.Icc 0 1)`
58. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_entry`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:86`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_entry (i j : Axis) : theta i j = if i=timeAxis
  then -basis j i else basis j i`
59. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.star_theta`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:89`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma star_theta : star theta = theta`
60. **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_sq`
(`submission/YM/Next/BOUNDARY/Coordinates.lean:96`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `lemma theta_sq : theta * theta=1`

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
3. **[score=52]** `lemma YM.EveryPhase.Stress.zeta_wick`
(`submission/YM/EveryPhase/Tensor.lean:23`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_wick (a : Axis) : zeta a * wick a = 1`
4. **[score=52]** `lemma YM.EveryPhase.Stress.zeta_square`
(`submission/YM/EveryPhase/Tensor.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma zeta_square (a : Axis) : zeta a * zeta a = -(eta a : ℂ)`
5. **[score=50]** `def YM.EveryPhase.Stress.zeta`
(`submission/YM/EveryPhase/Tensor.lean:22`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a : Axis) : ℂ`
6. **[score=50]** `def YM.TraceExtension.zeta`
(`submission/YM/TraceExtension/Sundial/Grand.lean:12`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `def zeta (a:Axis):ℂ`
7. **[score=42]** `def YM.WardBin.euler`
(`submission/YM/Next/WARD_BIN/Energy.lean:164`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `def euler (U : Links R G.El) (e : Edge (Four R)) : G.Color`
- **Docstring**: The Euler gradient with respect to positive links.
8. **[score=40]** `lemma YM.Extension.UV.Startup.datum_lipschitz`
(`submission/YM/Extension/UV/Canon/State.lean:105`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma datum_lipschitz {x y:ℝ} (hx:x∈strictBand a N)
  (hy:y∈strictBand a N) : ‖datum e (x:ℂ)-datum e (y:ℂ)‖ ≤ |x-y|/(a.clock.hatBeta
  N/2)`
9. **[score=40]** `lemma YM.Extension.UV.diam_lipschitz`
(`submission/YM/Extension/UV/Holo.lean:57`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma diam_lipschitz (hs : Convex ℝ U) (hU : ∀
  x∈U,DifferentiableAt ℂ f x) (h : ∀ x∈U,DifferentiableOn ℂ f (Metric.ball x r))
  (hM : ∀ x∈U, ∀ y ∈ Metric.ball x r,‖f y‖ ≤ M) (hr : 0<r) : ∀ x∈U,∀ y∈U,‖f x-f
  y‖ ≤ M/r * ‖x-y‖`
10. **[score=40]** `lemma YM.Planned.JetPort.lipschitzLower`
(`submission/YM/Planned/STATIONARY_JET_PORT/Enclosures.lean:17`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma lipschitzLower (h : Convex ℝ s) (hf : ∀ x∈s, ContDiffAt
  ℝ ω f x) (he : ∀ x∈s, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ C) {x y : E} (hx : x∈s)
  (hy : y∈s) : ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ C*‖x-y‖`
11. **[score=40]** `lemma YM.Push.Uniform.Before.Service.trail_lipschitz`
(`submission/YM/Push/STATIONARY_UNIFORM/Along.lean:106`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma trail_lipschitz (hp : R.Bounds p μ C Λ) (hK : Larger
  (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) : let P`
12. **[score=38]** `structure YM.Extension.UV.Tail.Lipschitz`
(`submission/YM/Extension/UV/Tail.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `structure Lipschitz (R : Rules E) : Prop`
13. **[score=37]** `lemma YM.EveryPhase.Stress.boost_scale`
(`submission/YM/EveryPhase/Tensor.lean:109`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: theta, zeta
- **Signature**: `lemma boost_scale (a i : Axis) {X : M4} (h : boostLike X) :
  zeta a * (-I) * ((X * theta) i a:ℂ) = zeta i * (X i a:ℂ)`
14. **[score=37]** `lemma YM.EveryPhase.Stress.space_scale`
(`submission/YM/EveryPhase/Tensor.lean:171`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: theta, zeta
- **Signature**: `lemma space_scale (a i : Axis) {X : M4} (h : theta*X=X*theta)
  : zeta a * (X i a:ℂ)=zeta i * (X i a:ℂ)`
15. **[score=34]** `theorem YM.Tensor.Euler`
(`submission/YM/Analysis/Homogeneous.lean:24`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem Euler (h : Sym A) (x : E) : fderiv ℝ (diagonal A) x x
  = (j : ℝ) • diagonal A x`
16. **[score=34]** `lemma YM.Extra.FD.SphereTest.Pure.euler`
(`submission/YM/Extra/FREE_DETECTOR_ALGEBRA/Laplace.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma Pure.euler (hf : Pure j f) (x : E4) : ∑ i : Axis, x i •
  grad i f x = (j:ℝ) • f x`
17. **[score=34]** `theorem YM.Maxwell.grad_euler`
(`submission/YM/Maxwell/Exterior.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `theorem grad_euler (A : T E4 F j) (h : Sym A) (x : E4) : ∑ k :
  Axis, x k • grad k (diagonal A) x = (j : ℝ) • diagonal A x`
18. **[score=34]** `lemma YM.WardBin.continuous_euler`
(`submission/YM/Next/WARD_BIN/Energy.lean:167`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `@[fun_prop] lemma continuous_euler {e : Edge (Four R)} :
  Continuous fun U : Links R G.El => euler U e`
19. **[score=34]** `lemma YM.WardBin.euler_gauge`
(`submission/YM/Next/WARD_BIN/Energy.lean:170`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_gauge (U : Links R G.El) (e : Edge (Four R)) (T :
  Four R → G.El) : euler (Lattice.gauge T U) e = G.adjoint (T e.1) (euler U e)`
20. **[score=34]** `lemma YM.WardBin.euler_at`
(`submission/YM/Next/WARD_BIN/Energy.lean:175`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_at {n : Side} (U : Config G n) (o : Site n) (x :
  Cover) (i : Axis) : euler (expandAt o U) (x,i) = euler U (wrap n x + o,i)`
21. **[score=34]** `lemma YM.Primitives.SmallFieldExterior.dirichlet_sq`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:52`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `lemma dirichlet_sq (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) :
  Dirichlet w r V u ^ 2 = ∑ i, w i ^2 * size r V (pc i u)^2`
22. **[score=34]** `lemma YM.Primitives.SmallFieldExterior.dirichlet_nn`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:54`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `lemma dirichlet_nn (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ) :
  0 ≤ Dirichlet w r V u`
23. **[score=34]** `lemma YM.Push.FiniteDetection.Kelvin.euler_step`
(`submission/YM/Push/FINITE_DETECTION/Harmonic.lean:124`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler_step (A : T E4 ℝ (j+1)) (x : E4) : ∑ i : Axis, x i
  * diagonal (A.curryLeft (basis i)) x = diagonal A x`
24. **[score=34]** `lemma YM.Trace.euler`
(`submission/YM/TraceExtension/Foundation/Dilate.lean:38`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler (w : Fin 3 → ℝ) (b : Axis) : (bareVector (G:=G)
  w).val b = (w 0 • ∑ i : Axis,(pairDeriv G b i b b i + pairDeriv G b i b b i))
  + (w 1 • ∑ a, ∑ i : Axis,(pairDeriv G a i b a i+ pairDeriv G a i b a i))+ (w
  2...`
25. **[score=34]** `lemma YM.TraceExtension.Wick.euler`
(`submission/YM/TraceExtension/Wick/Massive.lean:69`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Euler
- **Signature**: `lemma euler (m j s) (hs : 0<s) : s*moment m (j+2) 0 s=(j+3:ℝ)*
  moment m j 1 s`
26. **[score=32]** `def YM.Primitives.SmallFieldExterior.Dirichlet`
(`submission/YM/Primitives/SMALL_FIELD_EXTERIOR/Squares.lean:28`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: Dirichlet
- **Signature**: `def Dirichlet (w : ι → ℝ) (r : ℝ) (V u : Points ι → ℝ)`
27. **[score=28]** `lemma YM.EveryPhase.Stress.cloth_split`
(`submission/YM/EveryPhase/Decree.lean:18`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma cloth_split (j : Fin (n+1)) (M : Joint n) (K : Killing)
  (b : Axis) (s : ℝ) (g) : cloth M j (stack K b s g) = zeta b • cloth M j (touch
  K b g) + affect K b s • cloth M j g`
28. **[score=28]** `lemma YM.EveryPhase.Stress.uplifting`
(`submission/YM/EveryPhase/Frost.lean:43`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma uplifting (K : Killing) (b : Axis) (x : Space3) (t s :
  ℝ) : K.w b (lay x (arch t s))= zeta b*(K.realV (position x t) b:ℂ)+affect K b
  s`
29. **[score=28]** `lemma YM.EveryPhase.Stress.stack_zero`
(`submission/YM/EveryPhase/Frost.lean:53`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma stack_zero (K : Killing) (b : Axis) (f) : stack K b 0
  f=zeta b • touch K b f`
30. **[score=28]** `lemma YM.EveryPhase.Stress.Killing.w_real`
(`submission/YM/EveryPhase/Killing.lean:31`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma w_real (b : Axis) (r : Space3) (t : ℝ) : K.w b (lay r t)
  = zeta b * (K.realV (position r t) b:ℂ)`
31. **[score=28]** `lemma YM.EveryPhase.Stress.TM`
(`submission/YM/EveryPhase/Tensor.lean:207`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma TM (Q : Wightman S) (T : S.Stress) (a b) (f : Test4) :
  fieldM Q T a b f = (-zeta a * zeta b) • Q.operators.field (S.pin 4 (T a b)) f`
32. **[score=28]** `lemma YM.PhysicalNext.Repeat.Daisy.Charity.convulse`
(`submission/YM/PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP/Daisy/
Wisteria.lean:82`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/EulerFactorNonVanishing.lean`
- **Concepts**: zeta
- **Signature**: `lemma convulse (N: Captain H j q d v Y A b r B C' n χ0)
  (hhh:Herd H N.conduit A B n)(k : Plating (b₁:=b₁) M H N a t g c₁ u κ'
  e)(hZeta:|θp| * jewelDebt M Q L x ≤ 1)(O: Forest S.ratio): let g`
33. **[score=28]** `theorem YM.Push.PriceCompiler.Preparations.withTheta`
(`submission/YM/Push/PRICE_COMPILER/Post.lean:117`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean`
- **Concepts**: theta
- **Signature**: `theorem withTheta (q : AfterBill) (u : PostCost D → ℕ → ℝ) (h
  : ∀ i, 0 < u (m.budget q) i) : ∃ T : Protection D, T.theta ≤ u (m.budget q)`
- **Docstring**: Example phase: theta can be chosen *after* these budgets, even
  when its bound uses them; arbitrary positive upper requests. Can shrink it
  further **before**...
34. **[score=22]** `lemma YM.ConnectedActivityE6.Blaze.Eider.elastic`
(`submission/YM/AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Pommel.lean:45`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private lemma elastic {g : E→E} (K : ℝ≥0) (h : LipschitzWith K
  g) (hp : K < 1) [CompleteSpace E] : Bijective (fun x=>x+g x)`
35. **[score=22]** `theorem YM.Extension.UV.Tail.improve`
(`submission/YM/Extension/UV/Tail.lean:80`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `private theorem improve (h:Lipschitz R) (hs : ∀ i, s i ≤ 1)
  (step : ∀ i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk
  : 0≤ K) (hd : ∀ i, d i ≤ K* R.b i) (hw : ℕ) (m : ℕ) : s m ≤
  (1/3)^hw+(3/2)*(K*...`
36. **[score=22]** `lemma YM.Extension.UV.Tail.inward`
(`submission/YM/Extension/UV/Tail.lean:100`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma inward (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀ i,
  s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (K : ℝ) (hk : 0≤ K) (hd
  : ∀ i, d i ≤ K* R.b i) (m : ℕ) : s m ≤ (3/2)*(K*R.b m/R.radius m)`
37. **[score=22]** `lemma YM.Extension.UV.Tail.telescope`
(`submission/YM/Extension/UV/Tail.lean:108`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma telescope (h:Lipschitz R) (h₀ : d 0 ≤ 0) (hd : ∀ i,d
  (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) {K : ℝ} (hk :
  0≤ K) (hs : ∀ i, s i ≤ (3/2)*(K*R.b i /R.radius i)) (hK : ∀ i,d i ≤ K*R.b i)
  (m...`
38. **[score=22]** `lemma YM.Extension.UV.Tail.squeezing`
(`submission/YM/Extension/UV/Tail.lean:134`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma squeezing (h:Lipschitz R) (hs : ∀ i, s i ≤ 1) (step : ∀
  i, s i ≤ (1/3)*s (i+1) + (1/4)*(d (i+1)/R.radius (i+1))) (h₀ : d 0 ≤ 0) (hd :
  ∀ i,d (i+1) ≤ d i+R.eps (i+1)*((4/3)*s (i+1)+d (i+1)/R.radius (i+1))) (hK :
  ∀...`
39. **[score=22]** `lemma YM.Extension.UV.Tail.unique_infinite`
(`submission/YM/Extension/UV/Tail.lean:150`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma unique_infinite (h:Lipschitz R) (hL: Limits R) {z
  z':ℕ→ℝ} {v v':∀ i,E i} (hv : InfiniteCourse R z v) (hv' : InfiniteCourse R z'
  v') : z=z' ∧ v=v'`
40. **[score=22]** `lemma YM.Extension.UV.Tail.iterate_cap`
(`submission/YM/Extension/UV/Tail.lean:183`)
- **Class**: CLEARED_DENOMINATOR_ADAPTATION
- **Target**: `src/LeanAsm/QuasiRiemann/UltraDeep72.lean`
- **Concepts**: Lipschitz
- **Signature**: `lemma iterate_cap (h:Lipschitz R) (z : ℕ → ℕ→ℝ) (hz : ∀ N i, i
  ≤ N → z N i∈R.band i) (N : ℕ) (k : ℕ) {i : ℕ} (hi : i+k ≤ N) : ‖iterate R z N
  k i‖ ≤ 1/4`

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

- **[score=52]** `lemma YM.EveryPhase.Stress.zeta_wick`
  (`submission/YM/EveryPhase/Tensor.lean:23`) [zeta]
- **[score=52]** `lemma YM.EveryPhase.Stress.zeta_square`
  (`submission/YM/EveryPhase/Tensor.lean:24`) [zeta]
- **[score=50]** `def YM.EveryPhase.Stress.zeta`
  (`submission/YM/EveryPhase/Tensor.lean:22`) [zeta]
- **[score=50]** `def YM.TraceExtension.zeta`
  (`submission/YM/TraceExtension/Sundial/Grand.lean:12`) [zeta]
- **[score=42]** `def YM.WardBin.euler`
  (`submission/YM/Next/WARD_BIN/Energy.lean:164`) [Euler]
- **[score=37]** `lemma YM.EveryPhase.Stress.boost_scale`
  (`submission/YM/EveryPhase/Tensor.lean:109`) [theta, zeta]
- **[score=37]** `lemma YM.EveryPhase.Stress.space_scale`
  (`submission/YM/EveryPhase/Tensor.lean:171`) [theta, zeta]
- **[score=34]** `theorem YM.Tensor.Euler`
  (`submission/YM/Analysis/Homogeneous.lean:24`) [Euler]
- **[score=34]** `lemma YM.Extra.FD.SphereTest.Pure.euler`
  (`submission/YM/Extra/FREE_DETECTOR_ALGEBRA/Laplace.lean:43`) [Euler]
- **[score=34]** `theorem YM.Maxwell.grad_euler`
  (`submission/YM/Maxwell/Exterior.lean:45`) [Euler]

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
- **[score=16]** `lemma YM.PhysicalNext.InteractingRank.Milk.vanish`
  (`submission/YM/PhysicalNext/AFTERNOON_INTERACTING_RANK_COMPARISON/Opacity/
  Wiggle.lean:66`)
  [3/4]
- **[score=16]** `lemma YM.PhysicalNext.PhysicalGuard7f546.Curved.linkRoom_sq`
  (`submission/YM/PhysicalNext/PHYSICAL_GUARD_7F546/Continuation/
  Scales.lean:27`)
  [3/4]

### `src/LeanAsm/QuasiRiemann/ShortIntervalPrimes.lean` (Top 10)

- **[score=28]** `theorem YM.Push.PriceCompiler.Preparations.withTheta`
  (`submission/YM/Push/PRICE_COMPILER/Post.lean:117`) [theta]
- **[score=22]** `lemma YM.Extra.Iteration.psi_strip`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:130`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.psi_matrix`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:138`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.psi_read`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:143`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.psi_curl`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:153`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.psi_cancels`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Columns.lean:161`) [psi]
- **[score=22]** `lemma YM.Extra.Iteration.Inherited.psi_nonneg`
  (`submission/YM/Extra/ITERATION_NO_LOSS/Inherited.lean:27`) [psi]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_entry`
  (`submission/YM/Next/BOUNDARY/Coordinates.lean:86`) [theta]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.star_theta`
  (`submission/YM/Next/BOUNDARY/Coordinates.lean:89`) [theta]
- **[score=22]** `lemma YM.Next.BOUNDARY.Descent.theta_sq`
  (`submission/YM/Next/BOUNDARY/Coordinates.lean:96`) [theta]


<!-- end of file: leanasm/docs/openai-20261028/QRH_7_8_CANDIDATES.md -->
