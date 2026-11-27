import Mathlib

namespace OddCycleTarget

open Filter
open scoped BigOperators Topology

/-- The sum over ordered pairs counts each unordered pair twice. -/
theorem ordered_sum_eq_twice_upper {N : ℕ} (d : Fin N → Fin N → ℝ)
    (hz : ∀ i, d i i = 0) (hs : ∀ i j, d i j = d j i) :
    (∑ i, ∑ j, d i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, d i j := by
  classical
  let f (i j : Fin N) : ℝ := if i < j then d i j else 0
  have split (i j : Fin N) : d i j = f i j + f j i := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [f, h, h.asymm]
    · simp [f, hz]
    · simp [f, h, h.asymm, hs j i]
  have upper (i : Fin N) : (∑ j, f i j) = ∑ j ∈ Finset.Ioi i, d i j := by
    have hset : Finset.Ioi i = Finset.univ.filter (i < ·) := by ext j; simp
    rw [hset, Finset.sum_filter]
  calc
    _ = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, f j i) := by
      conv_lhs => enter [2, i, 2, j]; rw [split]
      simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, f i j := by rw [Finset.sum_comm (f := fun i j => f j i), two_mul]
    _ = _ := by simp_rw [upper]

/-- A bound for every equal-weight placement in a finite table implies the
weighted bound for every nonnegative integral multiplicity vector. -/
theorem nat_mass_of_placements {m : ℕ} (d : Fin m → Fin m → ℝ)
    (hz : ∀ i, d i i = 0) (a : Fin m → ℕ)
    (hplace : 2 ≤ ∑ i, a i → ∀ p : Fin (∑ i, a i) → Fin m,
      2 * (∑ u, ∑ v, d (p u) (p v)) ≤ ((∑ i, a i : ℕ) : ℝ) ^ 2) :
    2 * (∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * d i j) ≤ (∑ i, (a i : ℝ)) ^ 2 := by
  classical
  let N := ∑ i, a i
  let E := (i : Fin m) × Fin (a i)
  have hcard : Fintype.card E = N := by simp [E, N, Fintype.card_sigma]
  let e : Fin N ≃ E := (Fintype.equivFinOfCardEq hcard).symm
  let p (u : Fin N) : Fin m := (e u).1
  have count (g : Fin m → ℝ) : (∑ u : Fin N, g (p u)) = ∑ i, (a i : ℝ) * g i := by
    calc
      _ = ∑ x : E, g x.1 := e.sum_comp (fun x => g x.1)
      _ = _ := by simp [E, Fintype.sum_sigma]
  have pairs : (∑ u : Fin N, ∑ v : Fin N, d (p u) (p v)) =
      ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * d i j := by
    calc
      _ = ∑ u : Fin N, ∑ j, (a j : ℝ) * d (p u) j :=
        Finset.sum_congr rfl (fun u _ => count (d (p u)))
      _ = ∑ i, (a i : ℝ) * (∑ j, (a j : ℝ) * d i j) :=
        count (fun i => ∑ j, (a j : ℝ) * d i j)
      _ = _ := by simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← pairs, ← Nat.cast_sum]
  by_cases hN : 2 ≤ N
  · exact hplace hN p
  · have heq (u v : Fin N) : u = v := Fin.ext (by omega)
    have zero (u v : Fin N) : d (p u) (p v) = 0 := heq u v ▸ hz (p v)
    simp only [zero, Finset.sum_const_zero, mul_zero]
    positivity

/-- Homogeneity and approximating each weight by a scaled natural number
extend the ordered quadratic inequality to all nonnegative real weights. -/
theorem real_mass_of_nat_mass {m : ℕ} (d : Fin m → Fin m → ℝ)
    (hnat : ∀ a : Fin m → ℕ,
      2 * (∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * d i j) ≤ (∑ i, (a i : ℝ)) ^ 2)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    2 * (∑ i, ∑ j, w i * w j * d i j) ≤ (∑ i, w i) ^ 2 := by
  let a (x : ℝ) (i : Fin m) := ⌊w i * x⌋₊
  let v (i : Fin m) (x : ℝ) : ℝ := (a x i : ℝ) / x
  have lim (i : Fin m) : Tendsto (v i) atTop (𝓝 (w i)) :=
    tendsto_nat_floor_mul_div_atTop (hw i)
  apply le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ((lim i).mul (lim j)).mul_const (d i j)))
    ((tendsto_finsetSum Finset.univ fun i _ => lim i).pow 2)
  intro x
  change 2 * (∑ i, ∑ j, v i x * v j x * d i j) ≤ (∑ i, v i x) ^ 2
  have term (i j : Fin m) : v i x * v j x * d i j =
      (a x i : ℝ) * (a x j : ℝ) * d i j / x ^ 2 := by
    simp only [v, div_eq_mul_inv]
    ring
  simp_rw [term, ← Finset.sum_div]
  simp only [v, ← Finset.sum_div, div_pow]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hnat (a x)) (sq_nonneg x)

/-- Equal-weight tests on all finite multisets of marks imply the
nonnegative-real mass inequality, without a strict-positivity hypothesis. -/
theorem real_mass_of_placements {m : ℕ} (d : Fin m → Fin m → ℝ)
    (hz : ∀ i, d i i = 0)
    (hplace : ∀ (N : ℕ), 2 ≤ N → ∀ p : Fin N → Fin m,
      2 * (∑ u, ∑ v, d (p u) (p v)) ≤ (N : ℝ) ^ 2)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    2 * (∑ i, ∑ j, w i * w j * d i j) ≤ (Finset.univ.sum w) ^ 2 :=
  real_mass_of_nat_mass d (fun a => nat_mass_of_placements d hz a (hplace _)) w hw

end OddCycleTarget
