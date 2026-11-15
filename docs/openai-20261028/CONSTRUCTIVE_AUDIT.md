<!-- Path: leanasm/docs/openai-20261028/CONSTRUCTIVE_AUDIT.md -->
<!-- Max Column: 80 Columns -->

# Audit of 21 Pure Constructive `openai-20261028` Lean Files

Source index: `docs/openai-20261028/LEAN_TOC.json`
(`hygiene.leanasm_pure_constructive = true`, 21 files of 9,564 `.lean` files;
`subrepos/YM` left strictly read-only).

## 1. Executive Summary & Classification

Every file below has zero `Classical` / `noncomputable`, zero `Real` /
`Complex` / `Filter` / `Asymptotics`, zero `sorry` / `admit`, zero direct
`Mathlib` imports, and zero custom `axiom` declarations in its own file text
(note that transitive imports in `subrepos/YM` pull in Mathlib helpers such as
`Finset.Icc`, `Equiv.Perm`, and `abel`/`group` tactics).

| Cat | Content | Files | Decls | Status |
| --- | --- | --- | --- | --- |
| A | Lattice geometry & gauge holonomy | 4 | 57 | Ported (bridge module) |
| B | Lean 4 `vintage` elaborator macro | 1 | 4 | Ref only (build-time meta) |
| C | Orchard `vintage` macro scripts | 6 | 0 | Not ported (macro scripts) |
| D | Audits, wrappers, stubs & controls | 10 | 6 | Not ported (trivial) |
| All | **21 pure constructive files** | **21** | **67** | **4 ported** |

## 2. Category A: Ported Discrete, Lattice & Gauge Algebra Files (4 Files)

### 2.1 `provenance/lgt/LGT/GaugeField/Connection.lean` (74 lines, 8 decls)
- **Category**: Lattice gauge connections & holonomy covariance.
- **Declarations**: `GaugeConnection`, `AsymGaugeConnection`,
  `plaquetteHolonomy`, `asymPlaquetteHolonomy`, `GaugeTransform`,
  `AsymGaugeTransform`, `gaugeTransformConnection`, `holonomy_gauge_covariant`.
- **Portability**: **Direct** -> ported via `LatticeGroup`,
  `GaugeConnection`, `plaquetteHolonomy`, `gaugeTransformConnection`, and
  `holonomy_gauge_covariant` (plus non-abelian `YangMillsQ8.Q8` corollary
  `q8_plaquette_holonomy_gauge_invariant`).

### 2.2 `submission/YM/Lattice/Faces.lean` (145 lines, 20 decls)
- **Category**: Discrete 4D plaquette orientation, face action & class fns.
- **Declarations**: `PlaqAxes`, `Face`, `PlaqAxes.ordered`, `PlaqAxes.rotate`,
  `PlaqAxes.rotate_inv`, `PlaqAxes.transform`, `faceValue`, `face_gauge`,
  `Step.rev_rev`, `oriented`, `stop_oriented`, `oriented_swap`,
  `oriented_next`, `price_flip`, `atFace`, `price_shift_pos`, `Face.lower`,
  `Face.send`, `Face.injective_send`, `Face.send_price`.
- **Portability**: **Direct** -> all core combinators and theorems ported
  constructively in `ConstructiveOpenaiBridge.lean` (`PlaqAxes`, `rotate_inv`,
  `face_gauge_covariant`, `stop_oriented`, `oriented_swap_transport`,
  `oriented_next_transport`, `classFn_price_flip`, `classFn_price_shift_pos`,
  `Face.injective_send`, `classFn_send_price`, plus `Q8.reTrace` instance).

### 2.3 `submission/YM/Lattice/Foliation.lean` (108 lines, 14 decls)
- **Category**: Finite box layers, pinned slabs, finite sums & transport steps.
- **Declarations**: `layers`, `slab`, `box_iff_layers`, `card_layers`,
  `slab_iff`, `update_box`, `lower_pin`, `step_between`, `slab_update_image`,
  `slab_sum`, `axis_orthogonal`, `square_corners`, `axis_route_support`,
  `carry_succ`.
- **Portability**: **Direct** -> ported constructively using duplicate-free
  lists (`layerRange`, `layerRange_length`, `boxSites`, `boxSites_length`,
  `slabSites`, `lower_pin_mem`, `step_between_mem`, `slab_sum_foliation`,
  `axis_orthogonal`, `squareWalk_corners`, `axisRoute_support`,
  `carry_succ_transport`).

### 2.4 `submission/YM/Lattice/Route.lean` (62 lines, 15 decls)
- **Category**: Signed 4D lattice routes, axis reversals & signed symmetries.
- **Declarations**: `reverse_append`, `reverse_straight`, `axisRoute_append`,
  `axisRoute_reverse`, `rev_range`, `backward`, `backward_back`, `backOrder`,
  `back_axes`, `back_route`, `indexRoute`, `sendOrder`, `sendOrder_inv`,
  `orderEquiv`, `send_route`.
- **Portability**: **Direct** -> ported constructively using `Perm4`,
  `SignedSym4`, `straightWalk`, `axisRoute`, `routeWalk`, `backOrder4`,
  `orderPerm4`, `walkReverse_append`, `reverse_straightWalk`,
  `axisRoute_append`, `axisRoute_reverse`, `back_axes`, `back_route`,
  `indexRoute`, and `send_route`.

## 3. Category B: Lean 4 Metaprogramming Helper (1 File)

1. `submission/YM/UVExtension/Orchard/Barrel.lean` (71 lines, 4 decls):
   - Private helpers `agingName`, `ferment`, `wine`, `store` plus command
     elaborator `vintage` that clones constant expressions in `CoreM` while
     rewriting `YM.*` prefixes to `Vintage.YM.*`. Build-time metaprogramming
     only; not mathematical theorem content for `LeanAsm`.

## 4. Category C: Orchard Macro Invocation Scripts (6 Files)

Each file imports upstream proofs and invokes the `vintage` macro plus
`#print axioms` / `#check` commands (0 new Lean declarations):

1. `submission/YM/UVExtension/Orchard/Apple.lean` (13 lines, 0 decls)
2. `submission/YM/UVExtension/Orchard/Muesli.lean` (10 lines, 0 decls)
3. `submission/YM/UVExtension/Orchard/Pours.lean` (11 lines, 0 decls)
4. `submission/YM/UVExtension/Orchard/Shears.lean` (12 lines, 0 decls)
5. `submission/YM/UVExtension/Orchard/Tarts.lean` (7 lines, 0 decls)
6. `submission/YM/UVExtension/Orchard/Vanilla.lean` (6 lines, 0 decls)

## 5. Category D: Audits, Wrappers, Stubs & Controls (10 Files)

1. `checks/AxiomAudit.lean` (12 lines, 0 decls): `#print axioms` & `#check`
   acceptance audit script.
2. `submission/verification/Inventory.lean` (28 lines, 0 decls): `Lean` meta
   `run_cmd` checker scanning imported `YM.*` constants for `sorryAx` and
   axioms.
3. `submission/verification/Usage.lean` (66 lines, 1 private def `auditModule`):
   `Lean` meta `run_cmd` reachability analyzer emitting TSV dependency tables.
4. `submission/Solution.lean` (10 lines, 1 theorem `YangMills.jointExistence`):
   Top-level wrapper delegating directly to `YangMills.constructed` (which
   depends on noncomputable real analysis in `Construction`).
5. `submission/YM.lean` (1 line, 0 decls): Root barrel re-exporting
   `YM.Nonperturbative.Headlines`.
6. `provenance/lgt/LGT/GaugeField/Holonomy.lean` (1 line, 0 decls): Comment stub
   (`-- Stub: Holonomy`).
7. `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean` (1 line, 0 decls):
   Comment stub (`-- Stub: WilsonLoop`).
8. `verification/controls/accept/Solution.lean` (1 line, 1 theorem
   `comparatorSmoke`): Trivial `(1 : Nat) + 1 = 2` comparator smoke test.
9. `verification/controls/definition_mismatch/Solution.lean` (2 lines, 2 decls
   `reference`, `comparatorSmoke`): Trivial `reference = reference` control.
10. `verification/controls/statement_mismatch/Solution.lean` (1 line, 1 theorem
    `comparatorSmoke`): Trivial `(2 : Nat) + 2 = 4` comparator smoke test.

<!-- end of file: leanasm/docs/openai-20261028/CONSTRUCTIVE_AUDIT.md -->
