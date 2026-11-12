-- Path: leanasm/tests/TestAxioms.lean
-- Kernel verification test auditing that proofs only rely on standard axioms.

import LeanAsm

#print axioms MiniVM.get_set_same
#print axioms MiniVM.get_set_other
#print axioms MiniVM.add_comm_equiv
#print axioms Conjectures.collatz_one_reaches_one
#print axioms Conjectures.collatz_two_reaches_one
#print axioms Conjectures.collatz_four_reaches_one

-- end of file: leanasm/tests/TestAxioms.lean

#print axioms YangMillsToy.vacuum_plaquette_trivial
#print axioms YangMillsToy.vacuum_action_zero
#print axioms YangMillsToy.plaquette_trace_bounded

#print axioms YangMillsToy.plaquette_gauge_invariant
#print axioms YangMillsToy.plaquette_action_gauge_invariant

#print axioms YangMillsQ8.q8_trace_cyclic
#print axioms YangMillsQ8.q8_trace_conjugation_invariant

#print axioms QuasiRiemann.seven_eighths_lt_eleven_twelfths
#print axioms QuasiRiemann.seven_eighths_in_critical_strip

#print axioms QuasiRiemann.qrh_symmetric_strip
#print axioms QuasiRiemann.seven_eighths_symmetric_bounds

#print axioms QuasiRiemann.chebyshev_power_saving_k128
#print axioms QuasiRiemann.siegel_gap_from_seven_eighths

#print axioms MiniVM.mul_mod_reg_correct
#print axioms MiniVM.exec_garner_crt_sound
#print axioms RnsArithmetic.crt_weight_identities
#print axioms RnsArithmetic.crt_modulus_product
#print axioms RnsArithmetic.crt_roundtrip_851
#print axioms RnsArithmetic.rns_mul_concrete_soundness
#print axioms RnsArithmetic.garner_inverses_sound
#print axioms RnsArithmetic.garner_roundtrip_851
#print axioms RnsArithmetic.garner_mul_concrete_soundness

#print axioms QuasiRiemann.rh_exponent_strictly_better
#print axioms QuasiRiemann.rh_implies_qrh_seven_eighths
#print axioms QuasiRiemann.rh_exponent_strictly_better

#print axioms FiniteFieldRH.total_points_is_five
#print axioms FiniteFieldRH.frobenius_trace_is_three
#print axioms FiniteFieldRH.hasse_weil_riemann_hypothesis

#print axioms QuasiRiemann.guth_maynard_beats_huxley
#print axioms QuasiRiemann.theta_ladder_rungs_verified
#print axioms QuasiRiemann.theta_ladder_rungs_in_bounds

#print axioms QuasiRiemann.qrh_implies_certified_2d
#print axioms QuasiRiemann.turing_box_eliminates_low_zeros
#print axioms QuasiRiemann.asymptotic_wedge_penetrates_seven_eighths
#print axioms QuasiRiemann.critical_strip_dichotomy_2d
#print axioms QuasiRiemann.certified_and_unknown_disjoint

#print axioms QuasiRiemann.trivial_pair_valid
#print axioms QuasiRiemann.processA_preserves_trivial
#print axioms QuasiRiemann.processB_preserves_trivial
#print axioms QuasiRiemann.processB_involutive_concrete
#print axioms QuasiRiemann.weyl_pair_from_AB
#print axioms QuasiRiemann.trivial_pair_qrh_in_strip
#print axioms QuasiRiemann.weyl_pair_qrh_in_strip
#print axioms QuasiRiemann.weyl_pair_beats_seven_eighths
#print axioms QuasiRiemann.huxley_watt_pair_beats_weyl
#print axioms QuasiRiemann.exponent_pair_hypothesis_ceiling
#print axioms QuasiRiemann.subconvexity_hierarchy_verified
#print axioms QuasiRiemann.short_interval_prime_hierarchy
#print axioms QuasiRiemann.critical_line_proportion_bounds

#print axioms EulerFactorNonVanishing.prime_power_gt_one
#print axioms EulerFactorNonVanishing.local_euler_factor_nonvanishing
#print axioms EulerFactorNonVanishing.rns_prime_tower_euler_nonvanishing
#print axioms EulerFactorNonVanishing.partial_euler_product_nonvanishing
#print axioms EulerFactorNonVanishing.qrh_seven_eighths_euler_margins
#print axioms EulerFactorNonVanishing.list_euler_product_nonvanishing
#print axioms EulerFactorNonVanishing.fermat_tower_euler_nonvanishing_concrete

#print axioms NttArithmetic.ntt_roots_of_unity_sound
#print axioms NttArithmetic.ntt_butterfly2_roundtrip_5_12
#print axioms NttArithmetic.ntt_butterfly2_sound_all_pairs
