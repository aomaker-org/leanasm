-- Path: leanasm/src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean
-- Bridges QuasiRiemann 36-digit certified ln(2) bounds with AsymptoticZfr envelopes.
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann
import LeanAsm.QuasiRiemann.AsymptoticZfr

namespace QuasiRiemann

/-- Exact linkage between `AsymptoticZfr.ln2Upper36Scaled` and `(lnInterval36 2).hi`. -/
theorem ln2Upper36Scaled_eq_lnInterval36_hi :
    ln2Upper36Scaled = (lnInterval36 2).hi := by
  decide

/-- The constructive dyadic-octave upper envelope `octaveLnUpper36` agrees with multiples of
`(lnInterval36 2).hi` and upper-bounds the certified 36-digit intervals for powers of 2. -/
theorem octaveLnUpper36_bounds_lnInterval36 (t : Nat) :
    octaveLnUpper36 t = ((Nat.log2 t + 1 : Nat) : Int) * (lnInterval36 2).hi ∧
    (lnInterval36 2).hi ≤ octaveLnUpper36 t ∧
    (lnInterval36 4).hi ≤ octaveLnUpper36 4 ∧
    (lnInterval36 16).hi ≤ octaveLnUpper36 16 ∧
    (lnInterval36 64).hi ≤ octaveLnUpper36 64 := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · dsimp [octaveLnUpper36]
    rw [ln2Upper36Scaled_eq_lnInterval36_hi]
  · rw [← ln2Upper36Scaled_eq_lnInterval36_hi]
    exact (octaveLnUpper36_pos t).2.2

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/AsymptoticZfrBridge.lean
