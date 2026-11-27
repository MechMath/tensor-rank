import OddCycleTarget.RectGrouping
import OddCycleTarget.C5Target.OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

namespace OddCycleTarget
open OAI.LinearAlgebra.MatrixExponent

/-- At positive inner dimension the rectangle contains a flattening of rank a*b. -/
theorem rectangleDecomposition_area {F : Type*} [Field F] {a b c r : ℕ} (hc : 0 < c)
    (h : RectangleDecomposition F a b c r) : a * b ≤ r :=
  (show Rectangle.RankLE F a b c r from h).area hc

end OddCycleTarget
