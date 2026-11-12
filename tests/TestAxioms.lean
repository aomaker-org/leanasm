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
