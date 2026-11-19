-- Path: leanasm/src/LeanAsm/Genus2Jacobian/GroupLaw.lean
-- Cantor group law, addition, scalar multiplication, and certificate lemmas on J(C)(F_5).
-- Targets <= 100 cols, max 120 chars per line, zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 120 Columns

import LeanAsm.Genus2.Cantor
import LeanAsm.Genus2Jacobian.Core

namespace LeanAsm.Genus2Jacobian.GroupLaw

export LeanAsm.Genus2.Cantor (
  cantorCompose cantorReduceAux cantorAdd cantorNeg cantorSmulFuel cantorSmul
  orbitList orbitAt orbitList_length orbitAt_eq_smul orbitAt_smul orbitAt_all_reduced orbitAt_zero
  cantorNeg_orbitAt candidateDivisors memListB mem_of_memListB indexedMemOrbitAux
  indexedMemOrbitAux_sound finRange5_mem mem_candidates_of_reduced candidates_reduced_in_orbit
  exists_orbitAt_of_reduced checkPairZip checkRow checkRange cayley_rows_0_9 cayley_rows_9_18
  cayley_rows_18_27 cayley_rows_27_36 cayley_rows_36_45 cayley_rows_45_54 cayley_rows_54_63
  cayley_rows_63_71 checkRow_all checkPairZip_sound getD_rot_eq orbitAt_cayley
  cantorAdd_preserves_reduced cantorSmulFuel_preserves_reduced cantorSmul_preserves_reduced
  jacobian_D0_order_71 jacobian_D0_primitive inD0Orbit inD0Orbit_iff_smul
  jacobian_group_axioms_on_orbit
)

end LeanAsm.Genus2Jacobian.GroupLaw

-- end of file: leanasm/src/LeanAsm/Genus2Jacobian/GroupLaw.lean
