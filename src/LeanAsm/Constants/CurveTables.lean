-- Path: leanasm/src/LeanAsm/Constants/CurveTables.lean
-- Hyperelliptic curve F_5 polynomial and precomputed Jacobian orbit table literals.
-- Max Column: 120 Columns

namespace LeanAsm.Constants.CurveTables

/-- Curve polynomial `f(x) = x^5 - x + 1 = x^5 + 4x + 1` over `F_5` in little-endian order. -/
def curveF5Coeffs : List (Fin 5) := [1, 4, 0, 0, 0, 1]

/-- Raw pairs `(u, v)` of polynomial coefficient lists representing the 71-element orbit of `J(C)(F_5)`. -/
def rawOrbitTable : List (List (Fin 5) × List (Fin 5)) := [
  ([1], []), ([0, 1], [1]), ([0, 0, 1], [1, 2]), ([3, 1, 1], [3, 1]), ([0, 3, 1], [4, 1]),
  ([3, 1], [1]), ([0, 3, 1], [1]), ([1, 1, 1], [3, 2]), ([4, 0, 1], [1]), ([1, 0, 1], [4]),
  ([4, 1, 1], [2, 2]), ([2, 3, 1], [1]), ([2, 2, 1], [4]), ([0, 2, 1], [4]), ([2, 1], [4]),
  ([0, 2, 1], [1, 1]), ([0, 4, 1], [4]), ([4, 1], [4]), ([0, 4, 1], [1, 3]), ([1, 0, 1], [0, 3]),
  ([3, 4, 1], [2, 1]), ([1, 2, 1], [2, 3]), ([2, 2, 1], [2, 2]), ([1, 4, 1], [1, 2]), ([0, 1, 1], [4, 3]),
  ([1, 1], [1]), ([0, 1, 1], [1]), ([2, 0, 1], [3, 3]), ([4, 4, 1], [0, 3]), ([4, 0, 1], [0, 1]),
  ([3, 4, 1], [1]), ([3, 1, 1], [4]), ([2, 3, 1], [2, 3]), ([3, 3, 1], [0, 2]), ([1, 3, 1], [1, 3]),
  ([3, 2, 1], [4, 2]), ([3, 2, 1], [1, 3]), ([1, 3, 1], [4, 2]), ([3, 3, 1], [0, 3]), ([2, 3, 1], [3, 2]),
  ([3, 1, 1], [1]), ([3, 4, 1], [4]), ([4, 0, 1], [0, 4]), ([4, 4, 1], [0, 2]), ([2, 0, 1], [2, 2]),
  ([0, 1, 1], [4]), ([1, 1], [4]), ([0, 1, 1], [1, 2]), ([1, 4, 1], [4, 3]), ([2, 2, 1], [3, 3]),
  ([1, 2, 1], [3, 2]), ([3, 4, 1], [3, 4]), ([1, 0, 1], [0, 2]), ([0, 4, 1], [4, 2]), ([4, 1], [1]),
  ([0, 4, 1], [1]), ([0, 2, 1], [4, 4]), ([2, 1], [1]), ([0, 2, 1], [1]), ([2, 2, 1], [1]),
  ([2, 3, 1], [4]), ([4, 1, 1], [3, 3]), ([1, 0, 1], [1]), ([4, 0, 1], [4]), ([1, 1, 1], [2, 3]),
  ([0, 3, 1], [4]), ([3, 1], [4]), ([0, 3, 1], [1, 4]), ([3, 1, 1], [2, 4]), ([0, 0, 1], [4, 3]),
  ([0, 1], [4])
]

/-- Length certificate: the raw orbit table contains exactly 71 divisor pairs. -/
theorem rawOrbitTable_length : rawOrbitTable.length = 71 := by decide

/-- Length certificate: the curve polynomial coefficients list has length 6. -/
theorem curveF5Coeffs_length : curveF5Coeffs.length = 6 := by decide

end LeanAsm.Constants.CurveTables

-- end of file: leanasm/src/LeanAsm/Constants/CurveTables.lean
