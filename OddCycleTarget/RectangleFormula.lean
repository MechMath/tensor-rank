import OddCycleTarget.C5Target.OAI.LinearAlgebra.MatrixExponent.FieldFormula

namespace OddCycleTarget
open OAI.LinearAlgebra.MatrixExponent

/-- The published all-field formula, OpenAI commit 3344da5, FieldFormula.lean. -/
theorem publicRectangularExponent (F : Type*) [Field F] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Rectangle.exponent F a b c = Rectangle.U a b c :=
  Rectangle.exponent_eq F ha hb hc

end OddCycleTarget
