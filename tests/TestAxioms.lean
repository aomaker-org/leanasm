-- Path: leanasm/tests/TestAxioms.lean
-- Kernel verification test auditing that proofs only rely on standard axioms.

import LeanAsm

#print axioms MiniVM.get_set_same
#print axioms MiniVM.get_set_other
#print axioms MiniVM.add_comm_equiv
#print axioms Conjectures.collatz_one_reaches_one
#print axioms Conjectures.collatz_two_reaches_one
#print axioms Conjectures.collatz_four_reaches_one

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

#print axioms QuasiRiemann.vdc_word_AB_is_weyl
#print axioms QuasiRiemann.vdc_word_AAB_orbit_verified
#print axioms QuasiRiemann.vdc_word_BAB_orbit_verified
#print axioms QuasiRiemann.evalVdcWord_preserves_valid_on_trivial
#print axioms QuasiRiemann.vdc_words_in_strip

#print axioms QuasiRiemann.pl_interp_endpoints_samples
#print axioms QuasiRiemann.pl_interp_monotone_right
#print axioms QuasiRiemann.pl_interp_strict_order_inside_strip
#print axioms QuasiRiemann.pl_interp_concrete_rungs
#print axioms QuasiRiemann.zero_density_guth_maynard_strip_bounds

#print axioms QuasiRiemann.mollifier_theta_in_rh_range
#print axioms QuasiRiemann.mollifier_longer_improves_qrh
#print axioms QuasiRiemann.mollifier_regime_ladder_verified
#print axioms QuasiRiemann.deuring_heilbronn_repulsion_below_seven_eighths

#print axioms QuasiRiemann.euler_maclaurin_dyadic_tail_bound_256
#print axioms QuasiRiemann.dirichlet_cert_lower_bound_margin_samples
#print axioms QuasiRiemann.sample_certs_valid_in_unknown_box
#print axioms QuasiRiemann.refined_critical_strip_dichotomy_2d
#print axioms QuasiRiemann.refined_certified_and_unknown_disjoint

#print axioms QuasiRiemann.closestToZero_sq_eq_intervalMinSq
#print axioms QuasiRiemann.dirichletNormSq_toDirichletZeroFreeCert
#print axioms QuasiRiemann.computed_cert_implies_valid_cert
#print axioms QuasiRiemann.ivAdd_and_mul_samples_valid
#print axioms QuasiRiemann.complexIntervalMinNormSq_sound_samples
#print axioms QuasiRiemann.sample_computed_table_valid
#print axioms QuasiRiemann.evalDirichletPolyInterval_valid_sample
#print axioms QuasiRiemann.sample_computed_cert_7_8_105_verified
#print axioms QuasiRiemann.sample_computed_cert_lifts_to_valid_cert

#print axioms QuasiRiemann.toScaled6_preserves_valid_samples
#print axioms QuasiRiemann.ln_table_1_to_8_valid
#print axioms QuasiRiemann.generated_table_7_8_105_valid
#print axioms QuasiRiemann.generated_cert_7_8_105_verified
#print axioms QuasiRiemann.generated_cert_lifts_to_valid_cert

#print axioms QuasiRiemann.n8_pow_neg_upper_sound
#print axioms QuasiRiemann.buildGridCert_implies_valid
#print axioms QuasiRiemann.sweepDirichletGrid_all_valid
#print axioms QuasiRiemann.sample_grid_sweep_nonempty_and_refines
#print axioms QuasiRiemann.continuous_box_certifies_interior_heights
#print axioms QuasiRiemann.buildContinuousBoxCert_implies_valid
#print axioms QuasiRiemann.sweepContinuousBoxes_all_valid
#print axioms QuasiRiemann.sample_continuous_boxes_certified
#print axioms QuasiRiemann.n8_pow_neg_sigma6_sound
#print axioms QuasiRiemann.buildRect2DCert_implies_valid
#print axioms QuasiRiemann.sweepRectangles2D_all_valid
#print axioms QuasiRiemann.rect2d_certifies_interior_grid_points
#print axioms QuasiRiemann.sample_rects_2d_certified
#print axioms QuasiRiemann.ln_table_1_to_32_valid
#print axioms QuasiRiemann.n16_pow_neg_sigma6_sound
#print axioms QuasiRiemann.buildRect2DCertN16_implies_valid
#print axioms QuasiRiemann.sweepRectangles2DN16_all_valid
#print axioms QuasiRiemann.deep_strip_rects_below_five_eighths_certified
#print axioms QuasiRiemann.n32_pow_neg_sigma6_sound
#print axioms QuasiRiemann.buildRect2DCertN32_implies_valid
#print axioms QuasiRiemann.sweepRectangles2DN32_all_valid
#print axioms QuasiRiemann.ultra_deep_rects_down_to_052_certified

#print axioms CollatzQrhBridge.collatz_no_exact_power_resonance
#print axioms CollatzQrhBridge.diophantine_log3_log2_sandwich
#print axioms CollatzQrhBridge.collatz_2_3_phase_beat_interval
#print axioms CollatzQrhBridge.collatz_qrh_shared_cancellation_hierarchy

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

#print axioms NttArithmetic.ntt4_fourth_roots_sound
#print axioms NttArithmetic.ntt4_equals_direct_dft_concrete
#print axioms NttArithmetic.ntt4_roundtrip_concrete
#print axioms NttArithmetic.ntt4_cyclic_convolution_concrete

#print axioms CrtNtt.ntt4_mod5_roots_sound
#print axioms CrtNtt.garner_5_17_inverse_sound
#print axioms CrtNtt.garner_5_17_roundtrip_all
#print axioms CrtNtt.ntt4_mod5_roundtrip_concrete
#print axioms CrtNtt.crt_ntt_exact_integer_convolution

#print axioms CrtNtt.ntt8_mod17_roots_sound
#print axioms CrtNtt.ntt8_mod257_roots_sound
#print axioms CrtNtt.garner_17_257_inverse_sound
#print axioms CrtNtt.garner_17_257_roundtrip_samples
#print axioms CrtNtt.garner17_257_roundtrip_all
#print axioms CrtNtt.ntt8_mod17_and_mod257_roundtrip_concrete
#print axioms CrtNtt.crt_ntt8_exact_integer_convolution

#print axioms CrtNtt.ntt16_all_fermat_roots_sound
#print axioms CrtNtt.garner_17_257_65537_inverse_sound
#print axioms CrtNtt.garner_17_257_65537_roundtrip_samples
#print axioms CrtNtt.garner_17_257_65537_roundtrip_all
#print axioms CrtNtt.carryPassBase1000_limbs_lt_1000
#print axioms CrtNtt.carryPassBase1000_preserves_value_mod
#print axioms CrtNtt.carryPassBase1000_exact_when_bounded
#print axioms CrtNtt.ntt16_three_channels_roundtrip_concrete
#print axioms CrtNtt.crt_ntt16_exact_integer_convolution
#print axioms CrtNtt.base1000_limb_capacity_bound
#print axioms CrtNtt.base1000_roundtrip_concrete
#print axioms CrtNtt.crt_ntt_big_mul_12_digit
#print axioms CrtNtt.crt_ntt_big_mul_24_digit_max

-- Part 9: Universal NTT Algebraic Soundness Theorems (gemweb041)
#print axioms NttArithmetic.intt4_ntt4_universal_F5
#print axioms NttArithmetic.ntt4_intt4_universal_F5
#print axioms NttArithmetic.cyclic_conv4_ntt_universal_F5
#print axioms NttArithmetic.intt4_ntt4_universal_F17
#print axioms NttArithmetic.ntt4_intt4_universal_F17
#print axioms NttArithmetic.cyclic_conv4_ntt_universal_F17

-- Part 10: Universal 8-Point NTT Algebraic Soundness Theorems (gemweb042 Stage 1)
#print axioms CrtNtt.intt8_ntt8_universal_F17
#print axioms CrtNtt.ntt8_intt8_universal_F17
#print axioms CrtNtt.cyclic_conv8_ntt_universal_F17
#print axioms CrtNtt.intt8_ntt8_universal_F257
#print axioms CrtNtt.ntt8_intt8_universal_F257
#print axioms CrtNtt.cyclic_conv8_ntt_universal_F257

-- Part 10b: Universal 16-Point NTT & End-to-End 48-Digit Soundness (gemweb042 Stage 2)
#print axioms CrtNtt.intt16_ntt16_universal_F17
#print axioms CrtNtt.ntt16_intt16_universal_F17
#print axioms CrtNtt.cyclic_conv16_ntt_universal_F17
#print axioms CrtNtt.intt16_ntt16_universal_F257
#print axioms CrtNtt.ntt16_intt16_universal_F257
#print axioms CrtNtt.cyclic_conv16_ntt_universal_F257
#print axioms CrtNtt.intt16_ntt16_universal_F65537
#print axioms CrtNtt.ntt16_intt16_universal_F65537
#print axioms CrtNtt.cyclic_conv16_ntt_universal_F65537
#print axioms CrtNtt.crtNttBigMulVec8_universal_sound
#print axioms CrtNtt.crtNttBigMul_universal_sound

-- Part 10c: 2x2 Karatsuba-over-CRT-NTT 96-Digit Multiplier (gemweb042 Stage 3)
#print axioms CrtNtt.splitVec16_eval
#print axioms CrtNtt.addVec8WithCarry_sound
#print axioms CrtNtt.karatsuba_algebraic_identity
#print axioms CrtNtt.karatsubaCrtNttMul96_normalized
#print axioms CrtNtt.karatsubaCrtNttMul96_universal_sound
#print axioms CrtNtt.karatsuba_96_digit_max_verified

-- Part 10d: Second-Tier 2x2 Karatsuba-over-CRT-NTT 192-Digit Multiplier (gemweb043)
#print axioms CrtNtt.addVec32WithCarry_sound
#print axioms CrtNtt.subVec32WithBorrow_sound
#print axioms CrtNtt.karatsubaCrtNttMul192_normalized
#print axioms CrtNtt.karatsubaCrtNttMul192_universal_sound
#print axioms CrtNtt.karatsuba_192_digit_max_verified

-- end of file: leanasm/tests/TestAxioms.lean
