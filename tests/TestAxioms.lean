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

-- Part 5b: Constructive QRat {A,B}* Orbit, Guth-Maynard (30/13) & Mollifier Descent (gemweb044)
#print axioms QuasiRiemann.vdcProcessA_preserves_valid
#print axioms QuasiRiemann.vdcProcessB_preserves_valid
#print axioms QuasiRiemann.vdcProcessB_involutive
#print axioms QuasiRiemann.vdc_classic_orbit_chain
#print axioms QuasiRiemann.guth_maynard_strictly_improves_huxley
#print axioms QuasiRiemann.guth_maynard_prime_gap_threshold
#print axioms QuasiRiemann.mollifier_descent_monotone
#print axioms QuasiRiemann.mollifier_beyond_quarter_beats_seven_eighths
#print axioms QuasiRiemann.mollifier_one_third_yields_five_sixths
#print axioms QuasiRiemann.mollifier_one_half_yields_three_quarters
#print axioms QuasiRiemann.qrh_full_descent_chain_certified
#print axioms CollatzQrhBridge.collatz_qrh_mollifier_descent_synchronized

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

-- Part 11: ScaledInterval36 CRT-NTT & N = 64 Deep Zeta Certification (gemweb045)
#print axioms QuasiRiemann.natMul96ViaCrtNtt_eq_mul
#print axioms QuasiRiemann.mulInterval36_sound
#print axioms QuasiRiemann.ln_table_1_to_64_valid
#print axioms QuasiRiemann.n64_pow_neg_sigma36_sound
#print axioms QuasiRiemann.buildRect2DCertN64_implies_valid
#print axioms QuasiRiemann.sweepRectangles2DN64_all_valid
#print axioms QuasiRiemann.ultra_deep_rects_down_to_0505_certified

-- Safe QRat division & cancellation lawfulness (PR #2 review remediation)
#print axioms QuasiRiemann.qrat_div_mul_cancel
#print axioms QuasiRiemann.qrat_div?_zero
#print axioms QuasiRiemann.qrat_div?_eq_some
#print axioms QuasiRiemann.qrat_divOrZero_eq_div

-- Part 12: High-Convergent log2(3) Diophantine Gaps & CRT-NTT |2^k - 3^m| (gemweb046)
#print axioms CollatzQrhBridge.powViaCrtNtt96_eq_pow
#print axioms CollatzQrhBridge.collatz_convergent_powers_separation_certified
#print axioms CollatzQrhBridge.linearFormLn2Ln3Interval36_sound
#print axioms CollatzQrhBridge.linearFormLn2Ln3AbsLower36_sound
#print axioms CollatzQrhBridge.baker_effective_measure_verified
#print axioms CollatzQrhBridge.collatz_cycle_requires_positive_gap
#print axioms CollatzQrhBridge.collatzBeatPeriodUpper36_sound
#print axioms CollatzQrhBridge.collatz_qrh_phase_beat_lower_bound

-- Part 13: Constructive 100-Digit Chudnovsky Pi via 192-Digit CRT-NTT (gemweb047)
#print axioms PiChudnovsky.natMul192ViaCrtNtt_eq_mul
#print axioms PiChudnovsky.natMul192ViaCrtNtt_total_eq_mul
#print axioms PiChudnovsky.sqrt10005_scaled110_certified
#print axioms PiChudnovsky.sqrt10005_scaled110_crt_limbs_certified
#print axioms PiChudnovsky.chudnovsky_alternating_decreasing
#print axioms PiChudnovsky.chudnovsky_k8_tail_bound
#print axioms PiChudnovsky.chudPartialSum_trapped
#print axioms PiChudnovsky.chudBinarySplit_eq_exact
#print axioms PiChudnovsky.chud8_eq_partialSum8
#print axioms PiChudnovsky.chud9_eq_partialSum9
#print axioms PiChudnovsky.pi_105_bracket_valid
#print axioms PiChudnovsky.pi_105_traps_all_chudnovsky_truncations
#print axioms PiChudnovsky.pi_100_digits_certified

-- Part 14: 72-Digit CRT-NTT Fixed-Point Intervals, Chudnovsky 2π & N = 128 Down to σ = 0.501 (gemweb048)
#print axioms QuasiRiemann.natMul192ViaCrtNtt_eq_mul
#print axioms QuasiRiemann.mulInterval72_sound
#print axioms QuasiRiemann.twoPiInterval72_valid
#print axioms QuasiRiemann.twoPiInterval72_from_chudnovsky_sound
#print axioms QuasiRiemann.ln_table_1_to_128_valid
#print axioms QuasiRiemann.n128_pow_neg_sigma72_sound
#print axioms QuasiRiemann.buildRect2DCertN128_implies_valid
#print axioms QuasiRiemann.sweepRectangles2DN128_all_valid
#print axioms QuasiRiemann.ultra_deep_rects_down_to_0501_certified

-- Part 15: Smooth Genus-2 Curve C / F_5 Riemann Hypothesis (gemweb051)
#print axioms FiniteFieldRH.genus2_curve_smooth_F5
#print axioms FiniteFieldRH.genus2_N1_eq_11
#print axioms FiniteFieldRH.genus2_N2_eq_31
#print axioms FiniteFieldRH.genus2_weil_traces_verified
#print axioms FiniteFieldRH.genus2_frob_poly_functional_eq
#print axioms FiniteFieldRH.genus2_frob_poly_quad_factor_id
#print axioms FiniteFieldRH.genus2_real_trace_bounds
#print axioms FiniteFieldRH.genus2_frob_negative_discriminants

-- Part 16: 192-Digit CRT-NTT (485, 306) Gap & 72-Digit Linear Forms (gemweb052)
#print axioms CollatzQrhBridge.powViaCrtNtt192_eq_pow
#print axioms CollatzQrhBridge.collatz_convergent_485_306_separation_certified
#print axioms CollatzQrhBridge.linearFormLn2Ln3Interval72_sound
#print axioms CollatzQrhBridge.linearFormLn2Ln3AbsLower72_sound
#print axioms CollatzQrhBridge.baker_effective_measure_485_306_verified
#print axioms CollatzQrhBridge.collatz_485_306_cycle_denominator_certified
#print axioms CollatzQrhBridge.collatzBeatPeriodUpper72_sound
#print axioms CollatzQrhBridge.collatz_qrh_phase_beat_72_verified

-- Part 17: Genus-2 Weil L-Function & Jacobian Order #J(C)(F_5) = 71 (gemweb053)
#print axioms FiniteFieldRH.genus2_L_poly_eq_recip_frob
#print axioms FiniteFieldRH.genus2_zeta_rational_identity
#print axioms FiniteFieldRH.genus2_L_at_1_eq_71_div_25
#print axioms FiniteFieldRH.genus2_bsd_finite_field_identity
#print axioms FiniteFieldRH.genus2_jacobian_order_eq_71
#print axioms FiniteFieldRH.genus2_jacobian_order_71_prime
#print axioms FiniteFieldRH.genus2_basepoint_generates_jacobian

-- Part 18: Weil Zeta / Euler-Factor Punctured-Strip Non-Vanishing (gemweb054)
#print axioms WeilZetaBridge.genus2_L_poly_quad_factor_id
#print axioms WeilZetaBridge.weil_denom_factor1_nonvanishing
#print axioms WeilZetaBridge.weil_denom_factor2_nonvanishing
#print axioms WeilZetaBridge.weil_denom_product_lower_bound
#print axioms WeilZetaBridge.genus2_L_poly_lower_bound_off_half
#print axioms WeilZetaBridge.genus2_L_poly_explicit_strip_certs
#print axioms WeilZetaBridge.weil_zeta_punctured_strip_regular_and_nonzero

-- Part 19: Asymptotic Zero-Free Region & Dirichlet L^2 Diagonal Dominance (Issue #16)
#print axioms QuasiRiemann.octave_bracket_pow2
#print axioms QuasiRiemann.octaveLnUpper36_pos
#print axioms QuasiRiemann.octaveLnUpper36_mono
#print axioms QuasiRiemann.ln2Upper36_envelope_certs
#print axioms QuasiRiemann.trig_341_identity
#print axioms QuasiRiemann.trig_341_positivity
#print axioms QuasiRiemann.trig_341_positivity_qrat
#print axioms QuasiRiemann.trig_341_dirichlet_weighted_sum_nonneg
#print axioms QuasiRiemann.dvp_asymptotic_zero_free_region
#print axioms QuasiRiemann.dirichlet_log_ratio_lower
#print axioms QuasiRiemann.dirichlet_offdiag_sum_bound
#print axioms QuasiRiemann.dirichlet_offdiag_envelope_le_half_diag
#print axioms QuasiRiemann.dirichlet_l2_diagonal_dominance_sandwich
#print axioms QuasiRiemann.dirichlet_l2_zeta_and_mobius_certs
#print axioms QuasiRiemann.ln2Upper36Scaled_eq_lnInterval36_hi
#print axioms QuasiRiemann.octaveLnUpper36_bounds_lnInterval36

-- Part 20: Copilot Review Follow-Up Theorems (Issue #19)
#print axioms FiniteFieldRH.genus2DerivF5_eq_neg_one
#print axioms FiniteFieldRH.genus2_L_at_1_qrat

-- Part 21: Genus-2 Cantor-Mumford Jacobian Group Law (Issue #24)
#print axioms Genus2Jacobian.polyDivMod_sound
#print axioms Genus2Jacobian.polyXgcd_bezout
#print axioms Genus2Jacobian.D0_is_reduced
#print axioms Genus2Jacobian.orbitAt_cayley
#print axioms Genus2Jacobian.cantorAdd_preserves_reduced
#print axioms Genus2Jacobian.cantorSmul_preserves_reduced
#print axioms Genus2Jacobian.jacobian_D0_order_71
#print axioms Genus2Jacobian.jacobian_D0_primitive
#print axioms Genus2Jacobian.jacobian_group_axioms_on_orbit

-- Part 22: Steiner-Simons-de Weger Collatz Cycle Bounds (Issue #26)
#print axioms CollatzQrhBridge.collatz_cycle_min_element_lower_bound
#print axioms CollatzQrhBridge.collatz_odd_cycle_linear_eq
#print axioms CollatzQrhBridge.collatz_odd_cycle_gap_pos
#print axioms CollatzQrhBridge.collatz_odd_cycle_min_element_lower_bound
#print axioms CollatzQrhBridge.collatz_odd_cycle_product_bound
#print axioms CollatzQrhBridge.steiner_1cycle_divides
#print axioms CollatzQrhBridge.steiner_1cycle_excluded_at_convergents
#print axioms CollatzQrhBridge.collatz_convergent_nmin_lower_bounds
#print axioms CollatzQrhBridge.collatz_linear_form_uniform_306
#print axioms CollatzQrhBridge.collatz_cycle_length_lower_bound_306

-- Part 23: Fermat-Prime Tower {5, 17, 257, 65537} Euler Product Non-Vanishing (Issue #28)
#print axioms EulerFactorNonVanishing.fermat_prefix_prod_eq
#print axioms EulerFactorNonVanishing.fermat_tower_product_eq_2pow32_sub_1
#print axioms EulerFactorNonVanishing.local_euler_disk_nonvanishing
#print axioms EulerFactorNonVanishing.euler_product_finite_norm_lower_bound
#print axioms EulerFactorNonVanishing.fermat_tower_euler_product_nonvanishing
#print axioms EulerFactorNonVanishing.fermat_tower_euler_product_strip_certs
#print axioms EulerFactorNonVanishing.fermat_tower_sigma_half_lower_bound
#print axioms EulerFactorNonVanishing.fermat_tower_sigma_three_quarters_lower_bound
#print axioms EulerFactorNonVanishing.fermat_tower_sigma_one_lower_bound

-- Part 24: High-Height t ~ 10^12 2D Zero-Free Rectangles via PiChudnovsky Phase Reduction (Issue #29)
#print axioms QuasiRiemann.reduceModTwoPiCentered72_sound
#print axioms QuasiRiemann.high_height_phase_reduction_1e12
#print axioms QuasiRiemann.isValidHighDirichletTreeN128_sound
#print axioms QuasiRiemann.isValidDirichletRect2DN128_sound
#print axioms QuasiRiemann.buildDirichletRect2DCertN128_implies_valid
#print axioms QuasiRiemann.sweepDirichletRectangles2DN128_all_valid
#print axioms QuasiRiemann.high_height_dirichlet_rects_1e12_certified

-- Part 25: Genus-2 Hasse-Weil Functional Equation & Completed Zeta Reflection (Issue #34)
#print axioms WeilZetaBridge.genus2_L_poly_functional_eq
#print axioms WeilZetaBridge.genus2_weil_zeta_functional_eq
#print axioms WeilZetaBridge.genus2_completed_zeta_reflection

-- Part 26: Zero-Density-to-QRH Descent Bridge (Issue #36)
#print axioms QuasiRiemann.sublinearAt_iff_exponent_lt_one
#print axioms QuasiRiemann.exponent_mono_sigma
#print axioms QuasiRiemann.exponent_mono_slope
#print axioms QuasiRiemann.sublinearAt_mono_right
#print axioms QuasiRiemann.muAt_endpoints
#print axioms QuasiRiemann.muAt_antitone
#print axioms QuasiRiemann.chebyshevGap_pos_of_lt_one
#print axioms QuasiRiemann.chebyshevGap_antitone
#print axioms QuasiRiemann.qrh_zero_density_benchmark_certs
#print axioms QuasiRiemann.zero_density_implies_qrh_threshold
#print axioms QuasiRiemann.cDvp_div_octaveLnUpper36_le_inv168
#print axioms QuasiRiemann.qrh_theta_ladder_certs
#print axioms QuasiRiemann.zero_density_and_dvp_combined_region

-- Part 27: Cyclotomic Fermat-Tower Dedekind Zeta Euler Factor Non-Vanishing
#print axioms EulerFactorNonVanishing.fermat_prime_cyclotomic_splitting_deg
#print axioms EulerFactorNonVanishing.cyclotomic_split_euler_factor_nonvanishing
#print axioms EulerFactorNonVanishing.cyclotomic_euler_product_lower_bound
#print axioms EulerFactorNonVanishing.fermat_sigma_one_uniform_quarter_bound
#print axioms EulerFactorNonVanishing.fermat_tower_dedekind_euler_strip_certs

-- Part 28: Chebyshev Remainder Envelopes Across Benchmark Scales (Issue #40)
#print axioms QuasiRiemann.tenPowThetaCeilExp_eq_exact
#print axioms QuasiRiemann.tenPowThetaExactExp_lt_scale
#print axioms QuasiRiemann.chebyshev_remainder_mono_theta
#print axioms QuasiRiemann.tenPow_rel_err_lt_inv10
#print axioms QuasiRiemann.qrh_chebyshev_savings_certs
#print axioms QuasiRiemann.qrh_chebyshev_benchmark_certs

-- end of file: leanasm/tests/TestAxioms.lean
