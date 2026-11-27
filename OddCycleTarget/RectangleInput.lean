import OddCycleTarget.RectangleNumerics
import OddCycleTarget.RectangleFormula

namespace OddCycleTarget
open OAI.LinearAlgebra.MatrixExponent

theorem rectanglePowerLower {F : Type*} [Field F] {q n r : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n)
    (hr : RectangleDecomposition F (n ^ q) n n r) :
    n ^ ((2 * q + 1) ^ 2) ≤ r ^ (4 * q) :=
  rectanglePowerLower_of_exponent_eq hq hn hr
    (publicRectangularExponent F (Nat.cast_nonneg q) zero_le_one zero_le_one)

end OddCycleTarget
