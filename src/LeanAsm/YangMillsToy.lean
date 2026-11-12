-- Path: leanasm/src/LeanAsm/YangMillsToy.lean
-- A self-contained, executable toy model of 4D Wilson lattice gauge theory.
-- Demonstrates Wilson plaquette action, trace observables, and gauge invariance.
-- Max Column: 100 Columns

namespace YangMillsToy

/-- 4D Euclidean Spacetime Coordinate (x, y, z, t). -/
structure Point4 where
  x : Int
  y : Int
  z : Int
  t : Int
  deriving Repr, DecidableEq

/-- The 4 spacetime directions (μ ∈ {0, 1, 2, 3}). -/
inductive Dir : Type
  | d0
  | d1
  | d2
  | d3
  deriving Repr, DecidableEq

/-- Step one unit in direction μ on the $\mathbb{Z}^4$ lattice. -/
def Point4.shift (p : Point4) : Dir → Point4
  | Dir.d0 => { p with x := p.x + 1 }
  | Dir.d1 => { p with y := p.y + 1 }
  | Dir.d2 => { p with z := p.z + 1 }
  | Dir.d3 => { p with t := p.t + 1 }

/-- Directed lattice link (x, μ). -/
structure Link where
  origin : Point4
  dir : Dir
  deriving Repr, DecidableEq

/--
A toy discrete gauge group: $\mathbb{Z}_2 = \{+1, -1\}$.
In Wilson lattice gauge theory, link variables $U_\mu(x)$ take values in a gauge group $G$.
Here, we model the center $\mathbb{Z}_2 \subset SU(2)$ where group multiplication is sign product.
-/
inductive Z2 : Type
  | plusOne
  | minusOne
  deriving Repr, DecidableEq

/-- Group multiplication for $\mathbb{Z}_2$. -/
def Z2.mul : Z2 → Z2 → Z2
  | Z2.plusOne, b => b
  | Z2.minusOne, Z2.plusOne => Z2.minusOne
  | Z2.minusOne, Z2.minusOne => Z2.plusOne

/-- Group inverse for $\mathbb{Z}_2$ (every element is self-inverse). -/
def Z2.inv : Z2 → Z2
  | x => x

/-- Real character / trace of a $\mathbb{Z}_2$ group element. -/
def Z2.trace : Z2 → Int
  | Z2.plusOne => 1
  | Z2.minusOne => -1

/-- A lattice gauge configuration maps every link to a group element. -/
def GaugeConfig := Link → Z2

/--
Wilson Plaquette Observable:
The oriented product of 4 link variables around an elementary square in the (μ, ν) plane:
  $U_{\mu\nu}(x) = U_\mu(x) \cdot U_\nu(x + \hat{\mu}) \cdot U_\mu(x + \hat{\nu})^{-1} \cdot U_\nu(x)^{-1}$
-/
def plaquette (U : GaugeConfig) (x : Point4) (μ ν : Dir) : Z2 :=
  let u1 := U ⟨x, μ⟩
  let u2 := U ⟨x.shift μ, ν⟩
  let u3_inv := Z2.inv (U ⟨x.shift ν, μ⟩)
  let u4_inv := Z2.inv (U ⟨x, ν⟩)
  Z2.mul (Z2.mul u1 u2) (Z2.mul u3_inv u4_inv)

/-- Wilson Plaquette Action contribution $S_P = 1 - \frac{1}{N} \text{Re Tr}(U_P)$. -/
def plaquetteAction (U : GaugeConfig) (x : Point4) (μ ν : Dir) : Int :=
  1 - Z2.trace (plaquette U x μ ν)

/-- Local gauge transformation mapping each lattice site to a gauge group element. -/
def GaugeTransform := Point4 → Z2

/--
Action of a local gauge transformation $g$ on a link $U_\mu(x)$:
  $U'_\mu(x) = g(x) \cdot U_\mu(x) \cdot g(x + \hat{\mu})^{-1}$
-/
def gaugeTransform (g : GaugeTransform) (U : GaugeConfig) : GaugeConfig :=
  fun ⟨x, μ⟩ =>
    let gx := g x
    let ux := U ⟨x, μ⟩
    let gx_shift_inv := Z2.inv (g (x.shift μ))
    Z2.mul (Z2.mul gx ux) gx_shift_inv

-- =============================================================================
-- Formally Verified Theorems about Lattice Gauge Invariance
-- =============================================================================

/-- Theorem: For the vacuum configuration (all links +1), every plaquette is trivially +1. -/
theorem vacuum_plaquette_trivial (x : Point4) (μ ν : Dir) :
    plaquette (fun _ => Z2.plusOne) x μ ν = Z2.plusOne := by
  dsimp [plaquette, Z2.mul, Z2.inv]

/-- Theorem: The Wilson action of the vacuum configuration is zero everywhere. -/
theorem vacuum_action_zero (x : Point4) (μ ν : Dir) :
    plaquetteAction (fun _ => Z2.plusOne) x μ ν = 0 := by
  dsimp [plaquetteAction, Z2.trace]
  rw [vacuum_plaquette_trivial]
  decide

/-- Theorem: Plaquette trace is bounded between -1 and +1. -/
theorem plaquette_trace_bounded (g : Z2) :
    Z2.trace g = 1 ∨ Z2.trace g = -1 := by
  cases g <;> decide

/-- Lemma: Commutation of shifts in Euclidean space. -/
theorem shift_comm (p : Point4) (μ ν : Dir) :
    (p.shift μ).shift ν = (p.shift ν).shift μ := by
  cases μ <;> cases ν <;>
  dsimp [Point4.shift] <;>
  ext <;> omega

/--
Theorem (Local Gauge Invariance of Plaquette):
Under any local gauge transformation $g : \mathbb{Z}^4 \to \mathbb{Z}_2$,
the plaquette observable is strictly invariant:
  $U'_{\mu\nu}(x) = U_{\mu\nu}(x)$
Proved by case analysis and 2-dimensional shift commutativity.
-/
theorem plaquette_gauge_invariant
    (g : GaugeTransform) (U : GaugeConfig) (x : Point4) (μ ν : Dir) :
    plaquette (gaugeTransform g U) x μ ν = plaquette U x μ ν := by
  have h_shift := shift_comm x μ ν
  dsimp [plaquette, gaugeTransform, Z2.inv]
  rw [h_shift]
  cases U ⟨x, μ⟩ <;>
  cases U ⟨x.shift μ, ν⟩ <;>
  cases U ⟨x.shift ν, μ⟩ <;>
  cases U ⟨x, ν⟩ <;>
  cases g x <;>
  cases g (x.shift μ) <;>
  cases g (x.shift ν) <;>
  cases g ((x.shift ν).shift μ) <;>
  rfl

/--
Theorem (Local Gauge Invariance of Wilson Action):
The Wilson plaquette action $S_P[U]$ is invariant under any local gauge transformation.
-/
theorem plaquette_action_gauge_invariant
    (g : GaugeTransform) (U : GaugeConfig) (x : Point4) (μ ν : Dir) :
    plaquetteAction (gaugeTransform g U) x μ ν = plaquetteAction U x μ ν := by
  dsimp [plaquetteAction]
  rw [plaquette_gauge_invariant]

end YangMillsToy

-- end of file: leanasm/src/LeanAsm/YangMillsToy.lean
