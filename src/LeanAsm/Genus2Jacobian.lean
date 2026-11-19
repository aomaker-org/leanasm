-- Path: leanasm/src/LeanAsm/Genus2Jacobian.lean
-- Cantor's Mumford divisor group law on J(C)(F_5) for C : y^2 = x^5 - x + 1.
-- Constructively proves 71 * [P_0 - ∞] = 0, primitivity, and the 71x71 group law (ZERO axioms).
-- Facade aggregating Core and GroupLaw submodules.
-- Targets <= 100 cols, max 120 chars per line, zero Mathlib, zero Classical.choice, zero sorryAx.
-- Max Column: 120 Columns

import LeanAsm.Genus2Jacobian.Core
import LeanAsm.Genus2Jacobian.GroupLaw

namespace Genus2Jacobian

export LeanAsm.Genus2Jacobian.Core (
  invF5 invF5_mul mul_invF5 f5_zero_mul f5_mul_zero f5_one_mul f5_mul_one f5_zero_add f5_add_zero
  f5_neg_zero f5_sub_self f5_sub_zero f5_add_neg_cancel f5_add_comm f5_add_assoc f5_mul_comm
  f5_mul_assoc f5_mul_add f5_add_mul f5_sub_eq_add_neg eqF5 eqF5_iff PolyF5 polyEqB polyEqB_iff trim
  isTrimmedB coeff leadCoeff isMonic isEmpty_true isEmpty_false isEmpty_of_ne_nil
  list_length_pos_of_ne_nil f5_eq_zero_iff_val f5_val_eq_zero_of_beq f5_ne_zero_of_beq_false
  isTrimmedB_tail isTrimmedB_trim trim_of_isTrimmedB trim_idempotent leadCoeff_eq_coeff
  leadCoeff_ne_zero_of_isTrimmedB lastCoeff_ne_zero_of_isTrimmedB coeff_ge_len_zero
  len_le_of_isTrimmedB_coeff_zero coeff_trim eq_of_isTrimmedB_coeff trim_eq_iff_coeff addRaw negRaw
  scaleRaw mulRaw polyZero polyOne polyX polyAdd polyNeg polySub polyScale polyMul polyMonic
  polyXpowMul coeff_addRaw coeff_negRaw coeff_scaleRaw coeff_polyAdd coeff_polyNeg coeff_polySub
  coeff_polyScale coeff_polyMul coeff_mulRaw_cons_zero coeff_mulRaw_cons_succ coeff_mulRaw_nil_right
  coeff_mulRaw_congr_right coeff_mulRaw_zero_coeff coeff_mulRaw_congr_left coeff_mulRaw_add_left
  coeff_mulRaw_scale_left coeff_mulRaw_shift_left coeff_mulRaw_comm coeff_mulRaw_assoc polyAdd_comm
  polyAdd_assoc polyAdd_zero polyZero_add polySub_add_cancel polyMul_trim_left polyMul_trim_right
  polyMul_comm polyMul_assoc polyMul_add_right polyMul_add_left polyMul_neg_right polyScale_add
  polyMul_scale_left polyMul_one_left polyMul_zero_left polyAdd_sub_cancel polySub_sub_distrib
  divModAux polyDivMod polyDiv polyMod coeff_mulRaw_shift_singleton coeff_polyMul_polyXpowMul
  divMod_step_len_lt divModAux_sound polyDivMod_sound polyDivMod_sound_trimmed xgcdAux polyXgcd
  polyGcd isMonic_polyScale_inv xgcdAux_bezout polyXgcd_bezout polyXgcd_bezout_trimmed
  curveF5 MumfordDivisor divEqB divEqB_iff isReducedMumford D0 D0_is_reduced zero_is_reduced
)

export LeanAsm.Genus2Jacobian.GroupLaw (
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

/-- Identity element `0_J = (1, 0)`. -/
def MumfordDivisor.zero : MumfordDivisor := LeanAsm.Genus2Jacobian.Core.MumfordDivisor.zero

end Genus2Jacobian

-- end of file: leanasm/src/LeanAsm/Genus2Jacobian.lean
