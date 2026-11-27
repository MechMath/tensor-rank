import OddCycleTarget
import OddCycleTarget.UniversalPrice

namespace OddCycleTarget
open scoped BigOperators Fin.NatCast Fin.CommRing

/-- A modular step by one reads the same outgoing/incoming wire pair as the
coordinate tensor's own next-site function. -/
theorem nextSite_eq_add_one {m : ℕ} [NeZero m] (i : Fin m) : nextSite i = i+1 := by
  apply Fin.ext
  simp [nextSite, Fin.val_add, Nat.add_mod_mod]

/-- The geometric bound in exactly the exponent scaling and vertex indexing
used by the original coefficient model. -/
theorem perimeter_le_packet {m : ℕ} [NeZero m] (hm : 3 ≤ m) (odd : Odd m)
    (d : Fin m → Fin m → ℝ)
    (diag : ∀ i, d i i=0) (symm : ∀ i j, d i j=d j i)
    (hn : ∀ i j, 0 ≤ d i j) (tri : ∀ i j l, d i l ≤ d i j+d j l)
    (pt : ∀ a b c e, d a b*d c e ≤ d a c*d b e+d a e*d b c)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*d i j) ≤ (∑ i, w i)^2) :
    (∑ i, d i (nextSite i)) ≤ (A m : ℝ)/(D m : ℝ) := by
  have H := OddCycleOffset.universalPrice hm odd d diag symm hn tri pt zhou
  have h3 : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hA : (A m:ℝ) = (2*(m:ℝ)-3)^2 := by
    unfold A
    rw [Nat.cast_pow, Nat.cast_sub (by omega : 3 ≤ 2*m), Nat.cast_mul]
    norm_num
  have hD : (D m:ℝ) = 4*((m:ℝ)-2) := by
    unfold D
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
  simp_rw [nextSite_eq_add_one]
  rw [hA, hD]
  apply (le_div_iff₀ (show 0 < 4*((m:ℝ)-2) by linarith)).mpr
  nlinarith

end OddCycleTarget
