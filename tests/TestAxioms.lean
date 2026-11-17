-- Path: leanasm/tests/TestAxioms.lean
-- Kernel verification test auditing that proofs only rely on standard axioms.

import LeanAsm
import LeanAsm.QuasiRiemann.Valuation.Ultrametric
import LeanAsm.QuasiRiemann.Valuation.Contraction
import LeanAsm.QuasiRiemann.Valuation.Hensel

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

-- Part 14: 72-Digit CRT-NTT Fixed-Point Intervals, Chudnovsky 2π & N = 128 (gemweb048)
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

-- Part 24: High-Height t ~ 10^12 2D Zero-Free Rectangles via PiChudnovsky (Issue #29)
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

-- Part 29: Garner Mixed-Radix CRT & Convolution Wrap-Around Bounds (Issue #42)
#print axioms CrtNtt.fermat_tower_crt_modulus_bounds
#print axioms CrtNtt.garner_4ch_inverses_sound
#print axioms CrtNtt.garnerReconstruct4_lt
#print axioms CrtNtt.garnerReconstruct4_sound
#print axioms CrtNtt.ntt_convolution_no_wraparound
#print axioms CrtNtt.fermat_tower_conv_bound_certs

-- Part 30: MiniVM F_17 2-Point & 4-Point NTT Assembly Soundness (Issue #11)
#print axioms MiniVMNttBridge.runProgram_butterfly2AsmF17
#print axioms MiniVMNttBridge.ntt2AsmF17_sound
#print axioms MiniVMNttBridge.intt2AsmF17_sound
#print axioms MiniVMNttBridge.intt2_ntt2_asm_F17_roundtrip
#print axioms MiniVMNttBridge.ntt4AsmF17_sound
#print axioms MiniVMNttBridge.intt4AsmF17_sound
#print axioms MiniVMNttBridge.intt4_ntt4_asm_F17_roundtrip

-- Part 31: Unified Top-Level Provenance Audit (Issue #45)
#print axioms LeanAsm.miniVm_provenance_certified
#print axioms LeanAsm.collatz_provenance_certified
#print axioms LeanAsm.yangMills_provenance_certified
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.eulerRns_provenance_certified
#print axioms LeanAsm.finiteFieldWeil_provenance_certified
#print axioms LeanAsm.crtNtt_provenance_certified
#print axioms LeanAsm.chudnovskyPi_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 32: Constructive Short-Interval Primes & Rational Exponent Ladder (Issue #49)
#print axioms QuasiRiemann.qrhRemainderBoundAtTenPow_le_twoTenPow
#print axioms QuasiRiemann.short_interval_psi_diff_bound
#print axioms QuasiRiemann.short_interval_spec_guarantees_theta_pos
#print axioms QuasiRiemann.qrh_maximal_prime_gap_bound
#print axioms QuasiRiemann.qrh_short_interval_positivity_certs
#print axioms QuasiRiemann.shortIntervalDensityExponent_eqv_primeGapExponent
#print axioms QuasiRiemann.short_interval_density_ladder_strict

-- Part 33: Fermat-Tower AP Short-Interval Primes & Sub-3/4 QRH Ladder (Issue #51)
#print axioms QuasiRiemann.ap_short_interval_psi_diff_bound
#print axioms QuasiRiemann.fermat_tower_ap_short_interval_certs
#print axioms QuasiRiemann.sub_three_quarters_qrh_ladder_certs

-- Part 34: Parametric 4-Prime Fermat-Tower MiniVM NTT/INTT & Garner CRT (Issue #53)
#print axioms MiniVMNttBridge.ntt4AsmFermat_sound
#print axioms MiniVMNttBridge.intt4AsmFermat_sound
#print axioms MiniVMNttBridge.fermatTowerNtt4Specs_valid
#print axioms MiniVMNttBridge.intt4_ntt4_asm_fermat_roundtrip
#print axioms MiniVMNttBridge.fermatTowerNtt4_asm_roundtrip_certs
#print axioms MiniVMNttBridge.garnerReconstruct4Asm_sound
#print axioms MiniVMNttBridge.crtNtt4ChannelConvAsm_sound
#print axioms MiniVMNttBridge.crtNtt4ConvAsm_sound
#print axioms LeanAsm.miniVm_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 35: Higher (1054, 665) Convergent Gaps & Predecessor-Tree Density (Issue #55)
#print axioms CollatzQrhBridge.convergent_1054_665_gap_pos
#print axioms CollatzQrhBridge.log2_3_convergent_bracket_665
#print axioms CollatzQrhBridge.steiner_1cycle_excluded_1054_665
#print axioms CollatzQrhBridge.simons_de_weger_barrier_665
#print axioms CollatzQrhBridge.collatzPredTree_sound
#print axioms CollatzQrhBridge.collatz_mod6_branching
#print axioms CollatzQrhBridge.predecessor_density_threshold_ladder
#print axioms CollatzQrhBridge.collatz_pred_tree_growth_certs
#print axioms LeanAsm.collatz_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 36: Higher-Truncation (N = 256, 512) 2D Rectangles & CRT-NTT Phase (Issue #57)
#print axioms QuasiRiemann.HighTruncZeroFreeRectSpec.nonvanishing_of_certified
#print axioms QuasiRiemann.isValidLipTile2D_sound
#print axioms QuasiRiemann.partition2x2_covers_all_points
#print axioms QuasiRiemann.ln_table_1_to_512_valid
#print axioms QuasiRiemann.crtNtt_phase_reduction_512_sound
#print axioms QuasiRiemann.eulerMaclaurinB2TailRect2DForN_128_eq
#print axioms QuasiRiemann.eulerMaclaurinB2TailRect2DForN_monotone
#print axioms QuasiRiemann.euler_maclaurin_tail_shrinks_with_N
#print axioms QuasiRiemann.crtNtt_highTrunc_2d_zero_free_rect
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 37: GSp(4) -> SO(5) Functorial Lift & Selberg / Kim-Sarnak Ladder (Issue #61)
#print axioms GSp4FunctorialityBridge.gsp4StandardEulerPoly_eq_one_sub_mul
#print axioms GSp4FunctorialityBridge.gsp4StandardEulerHomog_one
#print axioms GSp4FunctorialityBridge.gsp4StandardEulerHomog_anti_palindromic
#print axioms GSp4FunctorialityBridge.gsp4_std_functional_equation
#print axioms GSp4FunctorialityBridge.genus2_f5_so5_cyclotomic_lift
#print axioms GSp4FunctorialityBridge.genus2_f5_so5_ramanujan_tempered
#print axioms GSp4FunctorialityBridge.kim_sarnak_ramanujan_ladder_strict
#print axioms GSp4FunctorialityBridge.selberg_laplacian_eigenvalue_ladder
#print axioms LeanAsm.finiteFieldWeil_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 38: Cauchy-Lipschitz Interior Box Lower-Bound & Telescoping Contraction
#print axioms QuasiRiemann.CauchyBoxLowerBoundSpec.lip_lt_center
#print axioms QuasiRiemann.cauchy_box_interior_nonvanishing
#print axioms QuasiRiemann.cauchy_box_2d_subbox_nonvanishing
#print axioms QuasiRiemann.telescoping_squeezing_chain
#print axioms QuasiRiemann.telescoping_box_contraction_cert
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 39: GL(1) Artin-Fermat Euler Factor & MiniVM NTT Bridge (Issue #59)
#print axioms ArtinFermatBridge.ArtinFermatCharacterSpec.toNttSpec_valid
#print axioms ArtinFermatBridge.artinFermatTowerSpecs_valid
#print axioms ArtinFermatBridge.artinCharProductEval_replicate_one
#print axioms ArtinFermatBridge.artin_split_euler_factor_collapse
#print axioms ArtinFermatBridge.artinOrder4EulerPoly_mod_eq
#print axioms ArtinFermatBridge.artin_order4_cyclotomic_factorization
#print axioms ArtinFermatBridge.artinCharTransform4_eq_ntt4_generic
#print axioms ArtinFermatBridge.artin_char_transform_eq_ntt4
#print axioms ArtinFermatBridge.artin_char_orthogonality_minivm
#print axioms LeanAsm.eulerRns_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 41: Pure Constructive OpenAI-20261028 Bridge (Issue #65)
#print axioms ConstructiveOpenaiBridge.straightWalk_stop
#print axioms ConstructiveOpenaiBridge.axisRoute_support
#print axioms ConstructiveOpenaiBridge.axisRoute_reverse
#print axioms ConstructiveOpenaiBridge.squareWalk_corners
#print axioms ConstructiveOpenaiBridge.boxSites_nodup
#print axioms ConstructiveOpenaiBridge.slab_sum_foliation
#print axioms ConstructiveOpenaiBridge.PlaqAxes.rotate_inv
#print axioms ConstructiveOpenaiBridge.holonomy_gauge_covariant
#print axioms ConstructiveOpenaiBridge.oriented_swap_transport
#print axioms ConstructiveOpenaiBridge.oriented_next_transport
#print axioms ConstructiveOpenaiBridge.classFn_price_flip
#print axioms ConstructiveOpenaiBridge.classFn_price_shift_pos
#print axioms ConstructiveOpenaiBridge.Face.injective_send
#print axioms ConstructiveOpenaiBridge.classFn_send_price
#print axioms ConstructiveOpenaiBridge.q8_plaquette_holonomy_gauge_invariant
#print axioms ConstructiveOpenaiBridge.q8_send_price_trace_invariant
#print axioms LeanAsm.yangMills_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 42: GL(2) Elliptic Curve Modularity E_{11a1} & f_{11} (Issue #60)
#print axioms EllipticModularityBridge.f11Coeffs_eq_table
#print axioms EllipticModularityBridge.heckeCoeff11_bad_11
#print axioms EllipticModularityBridge.isPointOnE11a1_iff_int_diff
#print axioms EllipticModularityBridge.sumTree_eq_range_foldl
#print axioms EllipticModularityBridge.ec11a1_point_cond_eq
#print axioms EllipticModularityBridge.ec11a1_point_counts_97
#print axioms EllipticModularityBridge.ec11a1_five_torsion_97
#print axioms EllipticModularityBridge.eichler_shimura_trace_eq_11a1
#print axioms EllipticModularityBridge.gl2_euler_quad_identity
#print axioms EllipticModularityBridge.gl2_euler_homog_pos_of_ramanujan
#print axioms EllipticModularityBridge.hasse_weil_ramanujan_11a1_certs
#print axioms EllipticModularityBridge.hecke_multiplicativity_11a1_certs
#print axioms LeanAsm.finiteFieldWeil_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 43: Parametric Beyond-7/8 QRH Ladder & Kim-Sarnak Bridge (Issue #68)
#print axioms QuasiRiemann.qrhShortExponent_strict_anti
#print axioms QuasiRiemann.qrhShortExponent_density_benchmarks
#print axioms QuasiRiemann.qrhDualFraction_strict_mono
#print axioms QuasiRiemann.shortIntervalQrh1732Spec_has_prime
#print axioms QuasiRiemann.qrhFromAutomorphic_eqv_half_add
#print axioms QuasiRiemann.kim_sarnak_amplified_qrh_step
#print axioms QuasiRiemann.parametric_qrh_kim_sarnak_certs
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 44: Higher-Truncation N=256,512 Rational Contraction & Strip Bridge (Issue #69)
#print axioms QuasiRiemann.RationalBoxContractionSpec.lip_mul_radius_lt
#print axioms QuasiRiemann.rational_box_contraction_step
#print axioms QuasiRiemann.rational_telescoping_chain_cert
#print axioms QuasiRiemann.ultraDeep72_N256_rational_rect_cert
#print axioms QuasiRiemann.ultraDeep72_N512_rational_rect_cert
#print axioms QuasiRiemann.exponent_strict_mono_sigma
#print axioms QuasiRiemann.ultradeep72_strip_to_zero_density_bridge
#print axioms QuasiRiemann.ultradeep72_N512_strip_zd_certs
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 45: GL(1) Artin Character-Twisted Short-Interval Bounds (Issue #70)
#print axioms ArtinShortIntervalBridge.artin_gaussian_char_orthogonality
#print axioms ArtinShortIntervalBridge.artin_ntt4_residue_class_recovery
#print axioms ArtinShortIntervalBridge.artin_twisted_ap_short_interval_pos
#print axioms ArtinShortIntervalBridge.artin_twisted_coset_short_interval_pos
#print axioms ArtinShortIntervalBridge.fermat_tower_artin_short_interval_certs
#print axioms LeanAsm.eulerRns_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 46: Constructive Dyadic-Shell & Discrete Abel Summation Bridge (Issue #71)
#print axioms QuasiRiemann.dyadicShellPartition_flatten
#print axioms QuasiRiemann.dyadic_shell_sum_partition
#print axioms QuasiRiemann.dyadic_shell_sum_foliation
#print axioms QuasiRiemann.discrete_abel_summation_by_parts
#print axioms QuasiRiemann.abel_summation_by_parts_list
#print axioms QuasiRiemann.abel_monotone_weight_envelope
#print axioms QuasiRiemann.abel_monotone_weight_envelope_qrat
#print axioms QuasiRiemann.sqrt_tail_gate_of_sq_le
#print axioms QuasiRiemann.inv_sqrt_tail_gate_dyadic_step
#print axioms QuasiRiemann.sqrt_tail_gate_dyadic_step
#print axioms QuasiRiemann.short_interval_dyadic_abel_envelope
#print axioms QuasiRiemann.dyadic_abel_short_interval_certs
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 47: Closed-Loop Dyadic-Abel Rungs k=5,6 & Variational Mollifier (Issue #78)
#print axioms QuasiRiemann.dyadic_abel_unlocks_next_rung
#print axioms QuasiRiemann.chebyshevSpec192_3364_env_le
#print axioms QuasiRiemann.shortIntervalQrh3364Spec_has_prime
#print axioms QuasiRiemann.chebyshevSpec384_65128_env_le
#print axioms QuasiRiemann.shortIntervalQrh65128Spec_has_prime
#print axioms QuasiRiemann.dyadic_abel_rungs_k5_k6_certs
#print axioms QuasiRiemann.linear_minimizes_dirichlet_energy
#print axioms QuasiRiemann.variational_energy_lt_one_of_pos
#print axioms QuasiRiemann.variational_mollifier_beats_linear
#print axioms QuasiRiemann.mollifier_variational_bridge_certs
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 48: UltraDeep108 N=1024,2048 & MiniVM Parametric 8-Pt Fermat NTT (Issue #79)
#print axioms MiniVMNttBridge.fermatTowerNtt8Specs_valid
#print axioms MiniVMNttBridge.fermatTowerNtt8_asm_roundtrip_certs
#print axioms LeanAsm.miniVm_provenance_certified
#print axioms QuasiRiemann.twoPiInterval108_valid
#print axioms QuasiRiemann.ln_table_1_to_2048_valid
#print axioms QuasiRiemann.phase_reduction_width_1e30_under_1e75
#print axioms QuasiRiemann.crtNtt_highTrunc108_N1024_rect
#print axioms QuasiRiemann.crtNtt_highTrunc108_N2048_rect
#print axioms QuasiRiemann.crtNtt_highTrunc108_2d_zero_free_rect
#print axioms QuasiRiemann.ultraDeep72_N1024_rational_rect_cert
#print axioms QuasiRiemann.ultraDeep72_N2048_rational_rect_cert
#print axioms QuasiRiemann.ultradeep72_N2048_strip_zd_certs
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 49: Constructive p-Adic Ultrametric Valuation & Contraction (inbox/gemweb100-101)
#print axioms QuasiRiemann.Valuation.IsPrime.dvd_mul
#print axioms QuasiRiemann.Valuation.padicValNat_mul
#print axioms QuasiRiemann.Valuation.padicValInt_add_ge_min
#print axioms QuasiRiemann.Valuation.pAdicVal_eq_none_iff
#print axioms QuasiRiemann.Valuation.pAdicVal_neg
#print axioms QuasiRiemann.Valuation.pAdicVal_sub_comm
#print axioms QuasiRiemann.Valuation.pAdicVal_mul
#print axioms QuasiRiemann.Valuation.ultrametric_ineq
#print axioms QuasiRiemann.Valuation.pow_dvd_den_iff_le_denVal
#print axioms QuasiRiemann.Valuation.not_pow_succ_denVal_dvd_den
#print axioms QuasiRiemann.Valuation.denVal_add
#print axioms QuasiRiemann.Valuation.denVal_sub
#print axioms QuasiRiemann.Valuation.denVal_mul
#print axioms QuasiRiemann.Valuation.denVal_and_pAdicVal_add_bound
#print axioms QuasiRiemann.Valuation.denVal_and_pAdicVal_mul_bound
#print axioms QuasiRiemann.Valuation.denVal_foldl_add_le
#print axioms QuasiRiemann.Valuation.denVal_foldl_mul_le
#print axioms QuasiRiemann.Valuation.denVal_hornerEval_le
#print axioms QuasiRiemann.Valuation.denVal_hornerEval_deg_le
#print axioms QuasiRiemann.Valuation.hornerEval_and_pAdicVal_bound
#print axioms QuasiRiemann.Valuation.denVal_hornerEval_eq_zero
#print axioms QuasiRiemann.Valuation.denVal_hornerEvalTight_le
#print axioms QuasiRiemann.Valuation.denVal_hornerEvalTight_deg_le
#print axioms QuasiRiemann.Valuation.hornerEvalTight_and_pAdicVal_bound
#print axioms QuasiRiemann.Valuation.pAdicVal_eq_of_cross_mul
#print axioms QuasiRiemann.Valuation.pAdicVal_sub_add_sub
#print axioms QuasiRiemann.Valuation.iterate_val_growth
#print axioms QuasiRiemann.Valuation.iterate_val_ge_of_init
#print axioms QuasiRiemann.Valuation.iterate_val_mono
#print axioms QuasiRiemann.Valuation.iterate_val_range
#print axioms QuasiRiemann.Valuation.iterate_val_range_of_init
#print axioms QuasiRiemann.Valuation.stationary_isStepContraction
#print axioms QuasiRiemann.Valuation.stationary_residual_growth
#print axioms QuasiRiemann.Valuation.stationary_iterate_cauchy_range
#print axioms QuasiRiemann.Valuation.nsStep_residual_val_double
#print axioms QuasiRiemann.Valuation.hensel_newton_schulz_quadratic_residual
#print axioms QuasiRiemann.Valuation.hensel_newton_schulz_step_bound
#print axioms QuasiRiemann.Valuation.hensel_newton_schulz_cauchy_range
#print axioms QuasiRiemann.Valuation.prime_pow_dvd_mul_of_ne
#print axioms QuasiRiemann.Valuation.mkJointCrtCongruence
#print axioms QuasiRiemann.Valuation.hensel_joint_crt_combine
#print axioms QuasiRiemann.Valuation.crt_fuse_inverse_seeds
#print axioms QuasiRiemann.Valuation.hensel_crt_inv_5_mod_3937_pow
#print axioms QuasiRiemann.Valuation.prime_tower_pow_dvd_of_all
#print axioms QuasiRiemann.Valuation.prime_tower_graded_dvd_num
#print axioms QuasiRiemann.Valuation.prime_tower_list_pow_dvd_num
#print axioms QuasiRiemann.Valuation.hensel_prime_tower_crt
#print axioms QuasiRiemann.Valuation.hensel_mersenne_tower_inv_5_mod_27559_pow
#print axioms QuasiRiemann.Valuation.CrossEq.mul_left
#print axioms QuasiRiemann.Valuation.CrossEq.add_left
#print axioms QuasiRiemann.Valuation.hornerEval_cross_eq_tight
#print axioms QuasiRiemann.Valuation.pAdicVal_hornerEval_eq_tight
#print axioms QuasiRiemann.Valuation.pAdicVal_hornerEval_ge_tight_floor
#print axioms QuasiRiemann.Valuation.pow_dvd_crtCofactor
#print axioms QuasiRiemann.Valuation.crtIdempotent_self_residual
#print axioms QuasiRiemann.Valuation.crtIdempotent_other_val
#print axioms QuasiRiemann.Valuation.crtIdempotent_integrality_all
#print axioms QuasiRiemann.Valuation.buildCrtSeed_integrality
#print axioms QuasiRiemann.Valuation.buildCrtSeed_residual_at
#print axioms QuasiRiemann.Valuation.sumCrtIdempotents_tower_dvd
#print axioms QuasiRiemann.Valuation.hensel_build_prime_tower_crt
#print axioms QuasiRiemann.Valuation.hensel_mersenne_tower_crt_built_inv_5
#print axioms QuasiRiemann.Valuation.hornerEval_cons_sub_val_eq
#print axioms QuasiRiemann.Valuation.hornerEval_cons_sub_ultrametric
#print axioms QuasiRiemann.Valuation.hornerEval_integrality
#print axioms QuasiRiemann.Valuation.hornerEval_sub_val_ge_of_integral
#print axioms QuasiRiemann.Valuation.hornerEval_zero_const_sub_val_ge
#print axioms QuasiRiemann.Valuation.hornerEval_sub_val_ge_of_denVal
#print axioms QuasiRiemann.Valuation.hornerEval_sub_val_ge_of_deg_denVal
#print axioms QuasiRiemann.Valuation.pAdicVal_hornerEvalTight_sub_eq_hornerEval
#print axioms QuasiRiemann.Valuation.polyNewtonStep_linear_cross_eq
#print axioms QuasiRiemann.Valuation.hornerEval_sub_cross_eq_slope
#print axioms QuasiRiemann.Valuation.polySlope_diag_cross_eq_deriv
#print axioms QuasiRiemann.Valuation.polyDeriv_sub_slope_val_ge_min
#print axioms QuasiRiemann.Valuation.polyNewtonStep_ball_contraction
#print axioms QuasiRiemann.Valuation.hensel_poly_simple_root_lift
#print axioms QuasiRiemann.Valuation.hensel_poly_simple_root_pow_dvd
#print axioms QuasiRiemann.Valuation.hensel_sqrt2_mod_pow_7
#print axioms QuasiRiemann.Valuation.prime_mersenne_7
#print axioms QuasiRiemann.Valuation.prime_mersenne_31
#print axioms QuasiRiemann.Valuation.prime_mersenne_127
#print axioms QuasiRiemann.Valuation.prime_tower_list_pow_dvd_of_all
#print axioms QuasiRiemann.Valuation.hensel_poly_prime_tower_crt
#print axioms QuasiRiemann.Valuation.buildCrtSeed_approx_at
#print axioms QuasiRiemann.Valuation.hensel_poly_build_prime_tower_crt
#print axioms QuasiRiemann.Valuation.hensel_mersenne_tower_sqrt2_lift
#print axioms QuasiRiemann.Valuation.hensel_mersenne_tower_sqrt2_built
#print axioms LeanAsm.quasiRiemann_provenance_certified
#print axioms LeanAsm.leanasm_full_provenance_certified

-- Part 50: Langlands Rankin-Selberg, Sym^2 & Hecke-Abel Bridge (Issue #80)
#print axioms LanglandsRankinSelbergBridge.rs_at_11
#print axioms LanglandsRankinSelbergBridge.rs_good_eq_gl2
#print axioms LanglandsRankinSelbergBridge.chi4_sq_odd
#print axioms LanglandsRankinSelbergBridge.rs_pos_of_ramanujan
#print axioms LanglandsRankinSelbergBridge.spin_eq_product
#print axioms LanglandsRankinSelbergBridge.gl2ProdToGSp4Spinor_reciprocal
#print axioms LanglandsRankinSelbergBridge.sym2_quad_sos
#print axioms LanglandsRankinSelbergBridge.sym2_quad_alt
#print axioms LanglandsRankinSelbergBridge.sym2_quad_nonneg
#print axioms LanglandsRankinSelbergBridge.sym2_nonneg_of_ramanujan
#print axioms LanglandsRankinSelbergBridge.sym2_pos_of_ramanujan_pos_u
#print axioms LanglandsRankinSelbergBridge.sym2_at_11
#print axioms LanglandsRankinSelbergBridge.chi4_sq_goodPrimes_odd
#print axioms LanglandsRankinSelbergBridge.heckeCoeff11_hasse_goodPrimes
#print axioms LanglandsRankinSelbergBridge.rs_pos_goodPrimes
#print axioms LanglandsRankinSelbergBridge.sym2_pos_goodPrimes
#print axioms LanglandsRankinSelbergBridge.abel_summation
#print axioms LanglandsRankinSelbergBridge.hecke_chi4_abel
#print axioms LanglandsRankinSelbergBridge.abelTail_bound
#print axioms LanglandsRankinSelbergBridge.hecke_chi4_short_interval_bound
#print axioms LeanAsm.langlandsRankinSelberg_provenance_certified

-- Part 51: 5-Prime Proth NTT Tower & Dedekind Strip Bounds (Issue #81)
#print axioms ProthNttTowerBridge.prothPrime5_coprime_M4
#print axioms ProthNttTowerBridge.prothTowerMod5_gt_2pow61
#print axioms ProthNttTowerBridge.prothGen_primitive_root
#print axioms ProthNttTowerBridge.prothOmega27_order
#print axioms ProthNttTowerBridge.garnerReconstruct5Asm_lt
#print axioms ProthNttTowerBridge.garnerReconstruct5Asm_sound
#print axioms ProthNttTowerBridge.garnerReconstruct5Asm_residues
#print axioms ProthNttTowerBridge.garnerReconstruct5Asm_mod_P5
#print axioms ProthNttTowerBridge.proth_tower_euler_margin_pos
#print axioms ProthNttTowerBridge.proth_tower_euler_product_nonvanishing
#print axioms ProthNttTowerBridge.proth_tower_euler_strip_certs
#print axioms LeanAsm.prothNttTower_provenance_certified

-- Part 52: Chiriac-Jorza Eisenstein 2-Adic & Hamming Weight Bounds (arXiv:2605.09738v2)
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.hammingWeight_step
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.legendre_v2_factorial
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.romik_cj_valuation_balance
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.proposition_4
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.proposition_4_unique
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.v2_eq_padicValNat_two
#print axioms LeanAsm.QuasiRiemann.Valuation.Eisenstein2Adic.legendre_padicValNat_two_factorial

#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.romikCoeff_symm
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.v2_mul_pos
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.v2_fact
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.v2_romikCoeffRaw_num
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.v2_romikCoeffRaw_den
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.qratV2_romikCoeffRaw
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_16_4
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_16_1
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m0
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m1
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m2
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.romik_n1_j1_val
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.romik_lacunary_n1_matches_classical
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.romik_n2_symm_val

#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_32_8
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_32_5
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_32_2
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m3
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.romik_lacunary_n2_ratio

#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_16
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_13
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_10
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_7
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_4
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.weight_64_1
#print axioms LeanAsm.QuasiRiemann.Valuation.EisensteinWeights.prop4_computed_m4

#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.preperiodic_partition_sound
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.preperiodic_partition_n1_sound
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.generalized_partition_m1_n2_sound
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.proposition41_lower_bound_m2_n3_sound
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.preperiodic_partition_zero_sound
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.andersen_garton_prop22_q5_d2
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.andersen_garton_prop22_q5_d2_reduced
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iter0_val
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iter1_val
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.iter2_val
#print axioms LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics.unicritical_iterate_valuation_growth

#print axioms LeanAsm.QuasiRiemann.RNS.RnsInt.reconstruct
#print axioms LeanAsm.QuasiRiemann.RNS.RnsQRat.toQRat
#print axioms LeanAsm.QuasiRiemann.RNS.RnsInt.add
#print axioms LeanAsm.QuasiRiemann.RNS.RnsInt.zero

-- end of file: leanasm/tests/TestAxioms.lean
