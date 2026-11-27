import OddCycleTarget.RectGrouping
import OddCycleTarget.C5Target.OAI.LinearAlgebra.MatrixExponent.Growth

/-! The arbitrary-side numerical lower from the public rectangular exponent formula. -/
namespace OddCycleTarget
open OAI.LinearAlgebra.MatrixExponent

theorem rectanglePowerLower_of_exponent_eq {F : Type*} [Field F] {q n r : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n)
    (hr : RectangleDecomposition F (n ^ q) n n r)
    (formula : Rectangle.exponent F (q : ℝ) 1 1 = Rectangle.U (q : ℝ) 1 1) :
    n ^ ((2 * q + 1) ^ 2) ≤ r ^ (4 * q) := by
  have hR : Rectangle.RankLE F (n ^ q) n n r := hr
  have hn0 : 0 < n := by omega
  have hr0 : 0 < r := (Nat.mul_pos (pow_pos hn0 q) hn0).trans_le (hR.area hn0)
  let rate := Real.logb (n : ℝ) r
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hv : (n : ℝ) ^ rate = (r : ℝ) :=
    Real.rpow_logb (by positivity) (ne_of_gt hn1) (by exact_mod_cast hr0)
  have sq : Rectangle.side n (q : ℝ) = n ^ q := by
    unfold Rectangle.side
    rw [Real.rpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast]
  have s1 : Rectangle.side n 1 = n := by simp [Rectangle.side]
  have ha : Rectangle.Admissible F q 1 1 rate :=
    Rectangle.admissible_of_rank hn (by positivity) zero_le_one zero_le_one
      sq.le s1.le s1.le hR hv.ge
  have he : Rectangle.exponent F q 1 1 ≤ rate :=
    csInf_le ⟨_, fun _ hs => Rectangle.areas_le_admissible hs⟩ ha
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hval : Rectangle.U (q : ℝ) 1 1 = (2 * (q : ℝ) + 1) ^ 2 / (4 * (q : ℝ)) := by
    rw [Rectangle.U, ite_eq_left (le_min hq1 le_rfl), Rectangle.benchmark,
      show ((q : ℝ) + 1) * 1 - q * 1 = 1 by ring, max_eq_left zero_le_one, one_pow]
    field_simp [hq0.ne']
    ring
  rw [formula, hval] at he
  have hcross := (div_le_iff₀ (show (0 : ℝ) < 4 * q by positivity)).mp he
  have hexp : (((2 * q + 1) ^ 2 : ℕ) : ℝ) ≤ rate * ((4 * q : ℕ) : ℝ) := by
    push_cast
    exact hcross
  have hpow : (n : ℝ) ^ ((2 * q + 1) ^ 2) ≤ (r : ℝ) ^ (4 * q) := calc
    _ = (n : ℝ) ^ (((2 * q + 1) ^ 2 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (n : ℝ) ^ (rate * ((4 * q : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1.le hexp
    _ = ((n : ℝ) ^ rate) ^ (4 * q) := Real.rpow_mul_natCast (by positivity) _ _
    _ = _ := by rw [hv]
  exact_mod_cast hpow

end OddCycleTarget
