-- Path: leanasm/tests/TestPreperiodic.lean
-- Kernel verification test auditing unicritical polynomial preperiodic dynamics axioms.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

open LeanAsm.QuasiRiemann.Valuation.PreperiodicDynamics

/-!
# Preperiodic Dynamics Axiom Provenance Audit

Verifies that unicritical polynomial preperiodic partition certificates,
Proposition 2.2 evaluations, and valuation stabilization theorems depend
strictly on authorized constructive axioms (`propext`, `Quot.sound`) with
ZERO `sorryAx` and ZERO `Classical.choice`.
-/

#print axioms preperiodic_partition_sound
#print axioms preperiodic_partition_n1_sound
#print axioms generalized_partition_m1_n2_sound
#print axioms proposition41_lower_bound_m2_n3_sound
#print axioms preperiodic_partition_zero_sound
#print axioms andersen_garton_prop22_q5_d2
#print axioms andersen_garton_prop22_q5_d2_reduced
#print axioms iter0_val
#print axioms iter1_val
#print axioms iter2_val
#print axioms unicritical_iterate_valuation_growth
#print axioms theorem51_asymptotic_bound_sound
#print axioms theorem13_average_bound_sound
#print axioms proposition53_average_bound_sound
#print axioms wreath_product_bound_sound
#print axioms lemma43_divisibility_bound_sound

-- end of file: leanasm/tests/TestPreperiodic.lean
