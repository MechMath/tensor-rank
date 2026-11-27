import Mathlib

/-! A sharp directed transition bound on a cube slice. -/
namespace OddCycleCube
open Finset
open scoped BigOperators Fin.NatCast

private theorem shift {m : ℕ} [NeZero m] (f : Fin m → ℝ) (c : Fin m) :
    ∑ i, f (i + c) = ∑ i, f i := Equiv.sum_comp (Equiv.addRight c) f

private theorem arc {m : ℕ} [NeZero m] (v w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, v i - v (i+1) ≤ w i) (i j : Fin m) :
    v i - v j ≤ ∑ t, w t := by
  let f (t : ℕ) := w (i + (t : Fin m))
  have head (n : ℕ) : v i - v (i + (n : Fin m)) ≤ ∑ t ∈ range n, f t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, Nat.cast_succ, ← add_assoc]
      exact (le_of_eq (by ring : v i - v (i + (n : Fin m) + 1) =
        (v i - v (i + (n : Fin m))) + (v (i + (n : Fin m)) - v (i + (n : Fin m) + 1)))).trans
        (add_le_add ih (h _))
  let n := (j-i).val
  have trunc : ∑ t ∈ range n, f t ≤ ∑ t ∈ range m, f t :=
    sum_le_sum_of_subset_of_nonneg (range_mono (j-i).isLt.le) (fun t _ _ => hw _)
  have total : ∑ t ∈ range m, f t = ∑ t, w t := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [f, add_comm] using Equiv.sum_comp (Equiv.addLeft i) w
  have at_end : i + (n : Fin m) = j := by simp [n, add_comm]
  simpa only [at_end] using ((head n).trans (trunc.trans_eq total))

private theorem lower {m : ℕ} [NeZero m] (hm : 4 ≤ m)
    (z : Fin m → ℝ) (i j : Fin m)
    (hlo : ∀ t, z j ≤ z t) (hhi : ∀ t, z t ≤ z i)
    (hz : 0 ≤ z j) (hh : 0 ≤ z i) (hs : 2 ≤ ∑ t, z t) (hab : z i + z j ≤ 1) :
    1 ≤ ∑ t, z t * (1-z (t+1)) := by
  let a := z j
  let b := z i
  let U (t : Fin m) := (z t-a)*(b-z (t+1))
  have hu := arc (fun t => (b-a)*z t) U
    (fun t => mul_nonneg (sub_nonneg.mpr (hlo t)) (sub_nonneg.mpr (hhi _))) (fun t => by
      dsimp only [U]
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hhi t)) (sub_nonneg.mpr (hlo (t+1)))]) i j
  have lu : (b-a)^2 ≤ ∑ t, U t := by
    change (b-a)*b - (b-a)*a ≤ _ at hu
    linarith [show (b-a)^2 = (b-a)*b - (b-a)*a by ring]
  have rearr : ∑ t, z t*(1-z (t+1)) = ∑ t, U t + (1-a-b)*(∑ t, z t) + (m:ℝ)*a*b := by
    calc
      _ = ∑ t, (U t + (1-b)*z t - a*z (t+1) + a*b) := by
        apply sum_congr rfl
        intro t _
        dsimp only [U]
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
          shift z 1]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  rw [rearr]
  have coef : 0 ≤ 1-a-b := by dsimp [a,b]; linarith
  have hc : (4:ℝ) ≤ m := by exact_mod_cast hm
  nlinarith only [lu, mul_le_mul_of_nonneg_left hs coef, sq_nonneg (1-a-b),
    mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg hz hh)]

/-- For any cyclic list in [0,1] of length at least four whose mass and
complementary mass are both at least two, there is at least one transition in total. -/
theorem transition {m : ℕ} [NeZero m] (hm : 4 ≤ m) (z : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ z i) (h1 : ∀ i, z i ≤ 1)
    (hs : 2 ≤ ∑ i, z i) (ht : ∑ i, z i ≤ (m:ℝ)-2) :
    1 ≤ ∑ i, z i*(1-z (i+1)) := by
  obtain ⟨j, _, hj⟩ := exists_min_image (univ : Finset (Fin m)) z univ_nonempty
  obtain ⟨i, _, hi⟩ := exists_max_image (univ : Finset (Fin m)) z univ_nonempty
  by_cases hab : z i + z j ≤ 1
  · exact lower hm z i j (fun t => hj t (mem_univ _)) (fun t => hi t (mem_univ _))
      (h0 _) (h0 _) hs hab
  let y (t : Fin m) := 1-z t
  have sy : 2 ≤ ∑ t, y t := by simpa [y, sum_sub_distrib] using (by linarith : 2 ≤ (m:ℝ)-∑ t, z t)
  have hy := lower hm y j i (fun t => sub_le_sub_left (hi t (mem_univ _)) _)
    (fun t => sub_le_sub_left (hj t (mem_univ _)) _) (sub_nonneg.mpr (h1 _))
    (sub_nonneg.mpr (h1 _)) sy (by dsimp [y]; linarith)
  have eqn : ∑ t, y t*(1-y (t+1)) = ∑ t, z t*(1-z (t+1)) := by
    calc
      _ = ∑ t, (z t*(1-z (t+1)) + (z (t+1) - z t)) := by
        apply sum_congr rfl
        intro t _
        dsimp only [y]
        ring
      _ = _ := by rw [sum_add_distrib, sum_sub_distrib, shift z 1]; ring
  rwa [eqn] at hy

#print axioms transition
end OddCycleCube
