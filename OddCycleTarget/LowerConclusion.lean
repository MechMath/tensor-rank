import OddCycleTarget.RectangleInput
import OddCycleTarget.LowerTransfer

namespace OddCycleTarget

/-- At every alphabet size n≥2, each individual exact decomposition of an odd
cycle on its original labelled slots obeys the sharp rectangular power lower. -/
theorem oddFiniteLower {F : Type*} [Field F] {m n r : ℕ} (hm : 3 ≤ m) (ho : Odd m)
    (hn : 2 ≤ n) (hd : HasDecomposition F m n r) : n ^ A m ≤ r ^ D m := by
  have hg : RectangleDecomposition F (n ^ (m - 2)) n n r := groupOddRectangle hm ho hd
  have h := rectanglePowerLower (by omega : 1 ≤ m - 2) hn hg
  have hA : 2 * m - 3 = 2 * (m - 2) + 1 := by omega
  simpa only [A, D, hA] using h

/-- The candidate is a lower bound on the dyadic exponent over every field. -/
theorem oddExponentLower (F : Type*) [Field F] (m : ℕ) (hm : 3 ≤ m) (ho : Odd m) :
    (A m : ℝ) / (D m : ℝ) ≤ exponent F m :=
  (allSidesLower_iff_exponent F m hm).mp (fun _ _ hn hd => oddFiniteLower hm ho hn hd)

/-- Sharp finite lower at the attained exact rank, together with the packet exponent lower. -/
theorem oddRankAndExponentLower (F : Type*) [Field F] (m : ℕ) (hm : 3 ≤ m) (ho : Odd m) :
    (∀ n : ℕ, 2 ≤ n → n ^ A m ≤ exactRank F m n ^ D m) ∧
      (A m : ℝ) / (D m : ℝ) ≤ exponent F m :=
  ⟨fun n hn => oddFiniteLower hm ho hn (exactRank_attained F m n), oddExponentLower F m hm ho⟩

end OddCycleTarget
