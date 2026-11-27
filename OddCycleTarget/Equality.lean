import OddRoot
import OddCycleTarget.LowerConclusion

namespace OddCycleTarget

/-- The dyadic exact-rank exponent of every odd cycle in its original sites. -/
theorem odd_equality_all : UniversalEquality := by
  intro F _ m hm ho
  have upper := (integerUpper_iff_exponent_le F m hm).mp (odd_upper_all F m hm ho)
  exact le_antisymm upper (oddRankAndExponentLower F m hm ho).2

/-- Every positive-side dyadic rate sequence converges to the sharp exponent. -/
theorem odd_limit (F : Type*) [Field F] {m : ℕ} (hm : 3 ≤ m) (ho : Odd m) :
    Filter.Tendsto (fun t : ℕ => Real.logb 2 (exactRank F m (2 ^ t) : ℝ) / t)
      Filter.atTop (nhds ((A m : ℝ) / (D m : ℝ))) := by
  have h : exponent F m = (A m : ℝ) / (D m : ℝ) := odd_equality_all F m hm ho
  rw [← h]
  simpa only [Real.logb, div_div] using tendsto_dyadic_rate F m

/-- The normalized difference from the odd-cycle flattening bound is constant. -/
theorem odd_normalized_excess (F : Type*) [Field F] {m : ℕ} (hm : 3 ≤ m) (ho : Odd m) :
    ((m : ℝ) - 2) * (exponent F m - ((m : ℝ) - 1)) = 1 / 4 := by
  have h : exponent F m = (A m : ℝ) / (D m : ℝ) := odd_equality_all F m hm ho
  have hd : (D m : ℝ) = 4 * ((m : ℝ) - 2) := by
    simp [D, Nat.cast_sub (show 2 ≤ m by omega)]
  have ha := congrArg (Nat.cast (R := ℝ)) (numerator_identity hm)
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)] at ha
  have hp : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  rw [h, ha, hd]
  field_simp
  ring

end OddCycleTarget
