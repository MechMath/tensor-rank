import OddCycleTarget.PacketPrice

namespace OddCycleTarget
open scoped BigOperators

/-- Sharp perimeter in the packet indexing, for all ordered Ptolemy tests
and nonnegative real masses. The labels need not be separated. -/
theorem sharp_perimeter (m : ℕ) (hm : 3 ≤ m) (ho : Odd m) (d : Fin m → Fin m → ℝ)
    (h0 : ∀ i, d i i = 0) (hs : ∀ i j, d i j = d j i) (hn : ∀ i j, 0 ≤ d i j)
    (ht : ∀ i j k, d i k ≤ d i j + d j k)
    (hp : ∀ i j k l, d i k * d j l ≤ d i j * d k l + d i l * d j k)
    (hz : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2 * (∑ i, ∑ j, w i * w j * d i j) ≤ (∑ i, w i)^2) :
    (∑ i, d i (nextSite i)) ≤ (A m : ℝ) / (D m : ℝ) := by
  let _ : NeZero m := ⟨by omega⟩
  exact perimeter_le_packet hm ho d h0 hs hn ht
    (fun i j k l => (hp i k j l).trans_eq (by rw [hs k j])) hz

end OddCycleTarget
