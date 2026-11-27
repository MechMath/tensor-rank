import Mathlib

/-! The endpoint-tilted mass test for a finite alternating path. All averages below are over
the actual uniform set of edges. Its two marginals retain their endpoint multiplicities. -/

namespace OddCycleTarget.TiltedPath

open scoped BigOperators

structure Table (V : Type*) where
  d : V → V → ℝ
  self : ∀ i, d i i = 0
  symm : ∀ i j, d i j = d j i
  nonneg : ∀ i j, 0 ≤ d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k
  ptolemy : ∀ i j k l, d i j * d k l ≤ d i k * d j l + d i l * d j k

namespace Table

variable {V : Type*} (g : Table V)

theorem variation (i k j : V) : |g.d i j - g.d k j| ≤ g.d i k := by
  have h := g.triangle k i j
  rw [g.symm k i] at h
  exact abs_le.mpr ⟨by linarith, by linarith [g.triangle i k j]⟩

/-- Ptolemy controls the determinant of the four crossed prices. Two one-variable
variations control the product left over when passing to an additive mixed difference. -/
theorem mixed (i k j l : V) (δ σ : ℝ) (hσ : 0 < σ)
    (hp : σ ≤ g.d k l) (hu : g.d i k ≤ δ) (hv : g.d j l ≤ δ) :
    |g.d i j + g.d k l - g.d i l - g.d k j| ≤ (δ / σ) * (g.d i k + g.d j l) := by
  have h₁ := g.ptolemy i j k l
  rw [g.symm j k] at h₁
  have h₂ := g.ptolemy i l k j
  rw [g.symm l j, g.symm l k] at h₂
  have hdet : |g.d i j * g.d k l - g.d i l * g.d k j| ≤ g.d i k * g.d j l :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hcol := g.variation j l k
  rw [g.symm j k, g.symm l k] at hcol
  have hprod : |(g.d i l - g.d k l) * (g.d k j - g.d k l)| ≤ g.d i k * g.d j l := by
    rw [abs_mul]
    exact mul_le_mul (g.variation i k l) hcol (abs_nonneg _) (g.nonneg _ _)
  let M := g.d i j + g.d k l - g.d i l - g.d k j
  have he : g.d k l * M = (g.d i j * g.d k l - g.d i l * g.d k j) +
      (g.d i l - g.d k l) * (g.d k j - g.d k l) := by dsimp [M]; ring
  have hm : σ * |M| ≤ δ * (g.d i k + g.d j l) := calc
    σ * |M| ≤ g.d k l * |M| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |g.d k l * M| := by rw [abs_mul, abs_of_nonneg (g.nonneg _ _)]
    _ ≤ 2 * (g.d i k * g.d j l) := by
      rw [he]; exact (abs_add_le ..).trans (by linarith)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hu (g.nonneg j l),
                            mul_le_mul_of_nonneg_left hv (g.nonneg i k)]
  calc
    |M| ≤ (δ * (g.d i k + g.d j l)) / σ := (le_div_iff₀ hσ).mpr (by linarith)
    _ = _ := by ring

/-- The endpoint perturbation only needs a bound on its local coefficient. -/
theorem endpoint (i a j z : V) (K : ℝ) (hp : 0 < g.d a j)
    (hK : g.d j z + |g.d a z - g.d a j / 2| ≤ K * g.d a j) :
    -(K * g.d i a) ≤ g.d i z - g.d a z - (g.d i j - g.d a j) / 2 := by
  have hpt := g.ptolemy i j a z
  rw [g.symm j a] at hpt
  have hh : |(g.d i j - g.d a j) * (g.d a z - g.d a j / 2)| ≤
      g.d i a * |g.d a z - g.d a j / 2| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (g.variation i a j) (abs_nonneg _)
  have hlo := (abs_le.mp hh).1
  have hmul := mul_le_mul_of_nonneg_left hK (g.nonneg i a)
  apply (mul_le_mul_iff_of_pos_left hp).mp
  nlinarith only [hpt, hlo, hmul]

end Table

/-- Both ends of each edge, oriented toward fixed sides. The exposed path vertices
are the A-end of edge a and the B-end of edge b. -/
structure Sample (E V : Type*) where
  A : E → V
  B : E → V
  a : E
  b : E
  z : V

section FiniteAverages

variable {E : Type*} [Fintype E] [Nonempty E]

/-- The row and column of an exposed edge contribute separately. Their sole
intersection is a diagonal zero, even if several edge endpoints have equal positions. -/
theorem endpoint_count (D : E → E → ℝ) (a : E)
    (hn : ∀ i j, 0 ≤ D i j) (hs : ∀ i j, D i j = D j i) (hz : D a a = 0) :
    2 * (𝔼 i, D i a) ≤ (Fintype.card E : ℝ) * (𝔼 i, 𝔼 j, D i j) := by
  classical
  have point (i j : E) :
      (if j = a then D i a else 0) + (if i = a then D j a else 0) ≤ D i j := by
    by_cases hi : i = a <;> by_cases hj : j = a
    · simp [hi, hj, hz]
    · simpa [hi, hj] using (hs j a).le
    · simp [hi, hj]
    · simp [hi, hj, hn]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => point i j))
  have col : (∑ i : E, ∑ j : E, if i = a then D j a else 0) = ∑ j : E, D j a := by
    rw [Finset.sum_comm]; simp
  simp only [Finset.sum_add_distrib] at bound
  rw [col] at bound
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at bound
  have hc : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_of_pos_left hc).mp
  calc
    (Fintype.card E : ℝ) * (2 * (𝔼 i, D i a)) = 2 * ∑ i, D i a := by
      rw [mul_left_comm, Fintype.card_mul_expect]
    _ ≤ ∑ i, ∑ j, D i j := by linarith
    _ = _ := by rw [Fintype.card_mul_expect, Finset.mul_sum]; simp only [Fintype.card_mul_expect]

/-- Symmetrization with two independent uniform edge samples. The swapped-edge
and original-edge terms each occur twice. -/
theorem correlation (p u v : E → E → ℝ) (c : ℝ)
    (hm : ∀ i k j l, |p i j + p k l - p i l - p k j| ≤ c * (u i k + v j l)) :
    |(𝔼 i, p i i) - (𝔼 i, 𝔼 j, p i j)| ≤
      c / 2 * ((𝔼 i, 𝔼 j, u i j) + (𝔼 i, 𝔼 j, v i j)) := by
  let M := fun i k => p i i + p k k - p i k - p k i
  have hmean : |𝔼 i, 𝔼 k, M i k| ≤ 𝔼 i, 𝔼 k, c * (u i k + v i k) := calc
    _ ≤ 𝔼 i, |𝔼 k, M i k| := Finset.abs_expect_le _ _
    _ ≤ _ := Finset.expect_le_expect (fun i _ => (Finset.abs_expect_le _ _).trans
      (Finset.expect_le_expect (fun k _ => hm i k i k)))
  have swap : (𝔼 i, 𝔼 k, p k i) = (𝔼 k, 𝔼 i, p k i) := Finset.expect_comm _ _ _
  have eqM : (𝔼 i, 𝔼 k, M i k) = 2 * ((𝔼 i, p i i) - (𝔼 i, 𝔼 k, p i k)) := by
    simp only [M, Finset.expect_sub_distrib, Finset.expect_add_distrib, Fintype.expect_const]
    rw [swap]; ring
  rw [eqM, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hmean
  simp only [← Finset.mul_expect, Finset.expect_add_distrib] at hmean
  linarith

end FiniteAverages

section Accounting

variable {E V : Type*} [Fintype E] [Nonempty E]

noncomputable def meanTo (g : Table V) (A : E → V) (v : V) : ℝ := 𝔼 i, g.d (A i) v

noncomputable def pairMean (g : Table V) (A B : E → V) : ℝ := 𝔼 i, 𝔼 j, g.d (A i) (B j)

omit [Nonempty E] in
private theorem meanFrom (g : Table V) (A : E → V) (v : V) :
    (𝔼 i, g.d v (A i)) = meanTo g A v := by
  simp only [meanTo, g.symm v]

omit [Nonempty E] in
private theorem swapMean (g : Table V) (A B : E → V) :
    pairMean g B A = pairMean g A B := by
  unfold pairMean
  rw [Finset.expect_comm]
  exact Finset.expect_congr rfl (fun _ _ => Finset.expect_congr rfl (fun _ _ => g.symm ..))

structure Statistics where
  paired : ℝ
  independent : ℝ
  within : ℝ
  toEnd : ℝ
  oneEnd : ℝ
  bothEnds : ℝ
  toCenter : ℝ
  endsToCenter : ℝ

noncomputable def statistics (g : Table V) (s : Sample E V) : Statistics where
  paired := 𝔼 i, g.d (s.A i) (s.B i)
  independent := pairMean g s.A s.B
  within := pairMean g s.A s.A + pairMean g s.B s.B
  toEnd := meanTo g s.A (s.A s.a) + meanTo g s.B (s.B s.b)
  oneEnd := meanTo g s.A (s.B s.b) + meanTo g s.B (s.A s.a)
  bothEnds := g.d (s.A s.a) (s.B s.b)
  toCenter := meanTo g s.A s.z + meanTo g s.B s.z
  endsToCenter := g.d (s.A s.a) s.z + g.d (s.B s.b) s.z

omit [Nonempty E] in
theorem meanTo_nonneg (g : Table V) (A : E → V) (v : V) : 0 ≤ meanTo g A v :=
  Finset.expect_nonneg (fun _ _ => g.nonneg ..)

omit [Nonempty E] in
theorem pairMean_nonneg (g : Table V) (A B : E → V) : 0 ≤ pairMean g A B :=
  Finset.expect_nonneg (fun _ _ => Finset.expect_nonneg (fun _ _ => g.nonneg ..))

theorem count_both_ends (g : Table V) (s : Sample E V) :
    2 * (statistics g s).toEnd ≤ (Fintype.card E : ℝ) * (statistics g s).within := by
  have h (A : E → V) (a : E) : 2 * meanTo g A (A a) ≤
      (Fintype.card E : ℝ) * pairMean g A A :=
    endpoint_count (fun i j => g.d (A i) (A j)) a (fun _ _ => g.nonneg ..)
      (fun _ _ => g.symm ..) (g.self _)
  dsimp only [statistics]
  linarith [h s.A s.a, h s.B s.b]

theorem independent_error (g : Table V) (s : Sample E V) (δ σ : ℝ)
    (hσ : 0 < σ) (within : ∀ i k, g.d (s.A i) (s.A k) ≤ δ ∧ g.d (s.B i) (s.B k) ≤ δ)
    (cross : ∀ i j, σ ≤ g.d (s.A i) (s.B j)) :
    |(statistics g s).paired - (statistics g s).independent| ≤
    (δ / σ) / 2 * (statistics g s).within := by
  exact correlation (fun i j => g.d (s.A i) (s.B j)) (fun i k => g.d (s.A i) (s.A k))
    (fun j l => g.d (s.B j) (s.B l)) _ (fun i k j l =>
      g.mixed _ _ _ _ δ σ hσ (cross k l) (within i k).1 (within j l).2)

theorem mixed_at_ends (g : Table V) (s : Sample E V) (δ σ : ℝ)
    (hσ : 0 < σ) (within : ∀ i k, g.d (s.A i) (s.A k) ≤ δ ∧ g.d (s.B i) (s.B k) ≤ δ)
    (cross : ∀ i j, σ ≤ g.d (s.A i) (s.B j)) :
    -((δ / σ) * (statistics g s).toEnd) ≤
      (statistics g s).bothEnds + (statistics g s).independent - (statistics g s).oneEnd := by
  have point (i j : E) := (abs_le.mp (g.mixed (s.A i) (s.A s.a) (s.B j) (s.B s.b)
    δ σ hσ (cross s.a s.b) (within i s.a).1 (within j s.b).2)).1
  have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun j _ => point i j))
  simp only [Finset.expect_neg_distrib, ← Finset.mul_expect, Finset.expect_add_distrib,
    Finset.expect_sub_distrib, Fintype.expect_const] at h
  rw [meanFrom g s.B (s.A s.a)] at h
  dsimp only [statistics]
  unfold meanTo pairMean at *
  linarith

private theorem average_endpoint (g : Table V) (A B : E → V) (a : E) (z : V) (K : ℝ)
    (sep : ∀ j, 0 < g.d (A a) (B j))
    (cost : ∀ j, g.d (B j) z + |g.d (A a) z - g.d (A a) (B j) / 2| ≤
      K * g.d (A a) (B j)) :
    -(K * meanTo g A (A a)) ≤ meanTo g A z - g.d (A a) z +
      (meanTo g B (A a) - pairMean g A B) / 2 := by
  have point (i j : E) := g.endpoint (A i) (A a) (B j) z K (sep j) (cost j)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun j _ => point i j))
  simp only [Finset.expect_neg_distrib, ← Finset.mul_expect, Finset.expect_sub_distrib,
    ← Finset.expect_div, Fintype.expect_const] at h
  rw [meanFrom g B (A a)] at h
  unfold meanTo pairMean at *
  linarith

theorem boundary_error (g : Table V) (s : Sample E V) (σ K : ℝ) (hσ : 0 < σ)
    (sep : ∀ i j, σ ≤ g.d (s.A i) (s.B j))
    (costA : ∀ j, g.d (s.B j) s.z + |g.d (s.A s.a) s.z - g.d (s.A s.a) (s.B j) / 2|
      ≤ K * g.d (s.A s.a) (s.B j))
    (costB : ∀ i, g.d (s.A i) s.z + |g.d (s.B s.b) s.z - g.d (s.A i) (s.B s.b) / 2|
      ≤ K * g.d (s.A i) (s.B s.b)) :
    -(K * (statistics g s).toEnd) ≤ (statistics g s).toCenter - (statistics g s).endsToCenter +
      ((statistics g s).oneEnd - 2 * (statistics g s).independent) / 2 := by
  have ha := average_endpoint g s.A s.B s.a s.z K (fun j => hσ.trans_le (sep s.a j)) costA
  have hb := average_endpoint g s.B s.A s.b s.z K
    (fun i => by rw [g.symm (s.B s.b)]; exact hσ.trans_le (sep i s.b))
    (fun i => by rw [g.symm (s.B s.b) (s.A i)]; exact costB i)
  rw [swapMean g s.A s.B] at hb
  dsimp only [statistics]
  linarith

variable [Fintype V] [DecidableEq V]

private def atom (v i : V) : ℝ := if v = i then 1 else 0

private def incidences (A : E → V) (i : V) : ℝ := ∑ e, atom (A e) i

/-- Each edge contributes 1-h at both of its ends; each exposed endpoint receives xh
more, and the distinguished vertex receives one. Weights live on the original vertices. -/
noncomputable def weight (s : Sample E V) (h : ℝ) (i : V) : ℝ :=
  (1 - h) * (incidences s.A i + incidences s.B i) +
    (Fintype.card E : ℝ) * h * (atom (s.A s.a) i + atom (s.B s.b) i) + atom s.z i

private theorem atom_eval (u : V) (f : V → ℝ) : (∑ i, atom u i * f i) = f u := by
  simp [atom, ite_mul]

omit [Nonempty E] in
private theorem incidences_eval (A : E → V) (f : V → ℝ) :
    (∑ i, incidences A i * f i) = ∑ e, f (A e) := by
  simp only [incidences, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [atom_eval]

noncomputable def massEval (s : Sample E V) (x h : ℝ) (f : V → ℝ) : ℝ :=
  x * (1 - h) * ((𝔼 i, f (s.A i)) + (𝔼 i, f (s.B i))) +
    x * h * (f (s.A s.a) + f (s.B s.b)) + f s.z

omit [Nonempty E] in
theorem weight_eval (s : Sample E V) (h : ℝ) (f : V → ℝ) :
    (∑ i, weight s h i * f i) = massEval s (Fintype.card E) h f := by
  simp only [weight, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    incidences_eval, atom_eval, massEval]
  have mult (A : E → V) := Fintype.card_mul_expect (fun i => f (A i))
  rw [← mult s.A, ← mult s.B]
  ring

theorem weight_sum (s : Sample E V) (h : ℝ) :
    (∑ i, weight s h i) = 2 * (Fintype.card E : ℝ) + 1 := by
  have he := weight_eval s h (fun _ => 1)
  simp only [mul_one, massEval, Fintype.expect_const] at he
  rw [he]; ring

omit [Nonempty E] [Fintype V] in
theorem weight_nonneg (s : Sample E V) (h : ℝ) (hh : 0 ≤ h) (hh' : h ≤ 1) (i : V) :
    0 ≤ weight s h i := by
  have ha (v i : V) : 0 ≤ atom v i := by simp [atom]; split <;> norm_num
  have hi (A : E → V) : 0 ≤ incidences A i := Finset.sum_nonneg (fun _ _ => ha ..)
  unfold weight
  exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hh') (add_nonneg (hi _) (hi _)))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hh) (add_nonneg (ha ..) (ha ..)))) (ha ..)

/-- Half the ordered weighted double sum. -/
noncomputable def energy (g : Table V) (s : Sample E V) (h : ℝ) : ℝ :=
  (∑ i, ∑ j, weight s h i * weight s h j * g.d i j) / 2

omit [Nonempty E] in
/-- Exact expansion of the honest mass sum. The six terms account respectively for
within-cluster pairs, independent cross pairs, one tilted endpoint, both tilted
endpoints, incidences at the center, and exposed endpoints at the center. -/
theorem energy_expansion (g : Table V) (s : Sample E V) (h : ℝ) :
    let x : ℝ := Fintype.card E
    let t := 1 - h
    let v := statistics g s
    2 * energy g s h =
      (x*t)^2 * (v.within + 2*v.independent) +
      2*(x*t)*(x*h)*(v.toEnd + v.oneEnd) + 2*(x*h)^2*v.bothEnds +
      2*(x*t)*v.toCenter + 2*(x*h)*v.endsToCenter := by
  let x : ℝ := Fintype.card E
  have hh : 2 * energy g s h = massEval s x h (fun i => massEval s x h (g.d i)) := calc
    _ = ∑ i, weight s h i * (∑ j, weight s h j * g.d i j) := by
      simp only [energy, Finset.mul_sum, mul_assoc]; ring
    _ = ∑ i, weight s h i * massEval s x h (g.d i) := by
      simp_rw [weight_eval]; rfl
    _ = _ := weight_eval _ _ _
  dsimp only
  rw [hh]
  dsimp only [massEval, statistics]
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect]
  have flip (A B : E → V) : (𝔼 i, 𝔼 j, g.d (B i) (A j)) = pairMean g A B := swapMean g A B
  rw [flip s.A s.B]
  simp only [meanFrom g s.A (s.A s.a), meanFrom g s.B (s.A s.a),
    meanFrom g s.A (s.B s.b), meanFrom g s.B (s.B s.b), meanFrom g s.A s.z,
    meanFrom g s.B s.z, g.self]
  rw [g.symm (s.B s.b) (s.A s.a), g.symm s.z (s.A s.a), g.symm s.z (s.B s.b)]
  unfold meanTo pairMean
  dsimp [x]
  ring

end Accounting

/-- The free allocation θ is the fraction of the within-cluster energy reserved
for the paired/independent correlation error. -/
private theorem transport_algebra (v : Statistics) (x h c K θ W : ℝ)
    (hx : 0 < x) (hh : 0 ≤ h) (ht : h ≤ 1) (tilt : 2*x*h = 1-h)
    (θle : θ ≤ 1) (corrBudget : c ≤ θ*(1-h)^2)
    (endBudget : K+h*c/2 ≤ (3/2-θ)*(1-h))
    (hT : 0 ≤ v.within) (hU : 0 ≤ v.toEnd) (count : 2*v.toEnd ≤ x*v.within)
    (corr : |v.paired-v.independent| ≤ c/2*v.within)
    (mixed : -(c*v.toEnd) ≤ v.bothEnds+v.independent-v.oneEnd)
    (boundary : -(K*v.toEnd) ≤ v.toCenter-v.endsToCenter+(v.oneEnd-2*v.independent)/2)
    (expansion : 2*W = (x*(1-h))^2*(v.within+2*v.independent) +
      2*(x*(1-h))*(x*h)*(v.toEnd+v.oneEnd) + 2*(x*h)^2*v.bothEnds +
      2*(x*(1-h))*v.toCenter + 2*(x*h)*v.endsToCenter) :
    0 ≤ W/x - (x*v.paired+v.endsToCenter) := by
  have expandW : W/x = x*(1-h)^2/2*v.within + x*(1-h)^2*v.independent +
      x*(1-h)*h*v.toEnd + x*(1-h)*h*v.oneEnd + x*h^2*v.bothEnds +
      (1-h)*v.toCenter + h*v.endsToCenter := by
    apply (div_eq_iff hx.ne').2
    linear_combination expansion / 2
  have h₁ : x*(1-h)*h = (1-h)^2/2 := by linear_combination (1-h)/2 * tilt
  have h₂ : x*h^2 = (1-h)*h/2 := by linear_combination h/2 * tilt
  have h₃ : x*(1-h)^2 = x-(1-h)+(1-h)*h/2 := by linear_combination (h-2)/2 * tilt
  have difference : W/x - (x*v.paired+v.endsToCenter) =
      x*(v.independent-v.paired) +
      (1-h)*(v.toCenter-v.endsToCenter+(v.oneEnd-2*v.independent)/2) +
      ((1-h)*h/2)*(v.bothEnds+v.independent-v.oneEnd) +
      x*(1-h)^2/2*v.within + (1-h)^2/2*v.toEnd := by
    rw [expandW]
    simp only [h₁, h₂, h₃]
    ring
  have tpos := sub_nonneg.mpr ht
  have hcov : -(c/2*v.within) ≤ v.independent-v.paired := by linarith [(abs_le.mp corr).2]
  have h₄ := mul_le_mul_of_nonneg_left hcov hx.le
  have h₅ := mul_le_mul_of_nonneg_left boundary tpos
  have h₆ := mul_le_mul_of_nonneg_left mixed (div_nonneg (mul_nonneg tpos hh) (by norm_num : (0:ℝ) ≤ 2))
  rw [difference]
  calc
    0 ≤ x*((θ*(1-h)^2-c)/2)*v.within +
        (1-h)*((3/2-θ)*(1-h)-(K+h*c/2))*v.toEnd +
        ((1-θ)*(1-h)^2/2)*(x*v.within-2*v.toEnd) := by
      exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hx.le
        (div_nonneg (sub_nonneg.mpr corrBudget) (by norm_num))) hT)
        (mul_nonneg (mul_nonneg tpos (sub_nonneg.mpr endBudget)) hU))
        (mul_nonneg (div_nonneg (mul_nonneg (sub_nonneg.mpr θle) (sq_nonneg _))
          (by norm_num)) (sub_nonneg.mpr count))
    _ ≤ _ := by linarith only [h₄, h₅, h₆]

section Transport

variable {E V : Type*} [Fintype E] [Nonempty E] [Fintype V] [DecidableEq V]

/-- Uniform finite-sample estimate before the single global mass test.
The coupling can be any list of edges with the distinguished endpoints in its marginals. -/
theorem transport (g : Table V) (s : Sample E V) (δ σ K θ h : ℝ)
    (hσ : 0 < σ) (hh : 0 ≤ h) (ht : h ≤ 1)
    (tilt : 2*(Fintype.card E : ℝ)*h = 1-h)
    (θle : θ ≤ 1) (corrBudget : δ/σ ≤ θ*(1-h)^2)
    (endBudget : K+h*(δ/σ)/2 ≤ (3/2-θ)*(1-h))
    (within : ∀ i j, g.d (s.A i) (s.A j) ≤ δ ∧ g.d (s.B i) (s.B j) ≤ δ)
    (sep : ∀ i j, σ ≤ g.d (s.A i) (s.B j))
    (costA : ∀ j, g.d (s.B j) s.z + |g.d (s.A s.a) s.z - g.d (s.A s.a) (s.B j) / 2|
      ≤ K * g.d (s.A s.a) (s.B j))
    (costB : ∀ i, g.d (s.A i) s.z + |g.d (s.B s.b) s.z - g.d (s.A i) (s.B s.b) / 2|
      ≤ K * g.d (s.A i) (s.B s.b)) :
    0 ≤ energy g s h / (Fintype.card E : ℝ) -
      ((∑ i, g.d (s.A i) (s.B i)) + g.d (s.A s.a) s.z + g.d (s.B s.b) s.z) := by
  have hcard : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hT : 0 ≤ (statistics g s).within := add_nonneg (pairMean_nonneg ..) (pairMean_nonneg ..)
  have hU : 0 ≤ (statistics g s).toEnd := add_nonneg (meanTo_nonneg ..) (meanTo_nonneg ..)
  have estimate := transport_algebra (statistics g s) _ h (δ/σ) K θ _ hcard hh ht tilt θle
    corrBudget endBudget hT hU (count_both_ends g s) (independent_error g s δ σ hσ within sep)
    (mixed_at_ends g s δ σ hσ within sep) (boundary_error g s σ K hσ sep costA costB)
    (energy_expansion g s h)
  simpa only [statistics, Fintype.card_mul_expect, add_assoc] using estimate

end Transport

/-- On the original labelled cycle, the endpoint tilt certifies the perimeter whenever the
two displayed scalar budgets hold. The only global price input is a single Zhou test. -/
theorem path_certificate :
∀ (x : ℕ), Odd x → 1 ≤ x → ∀ (d : Fin (x + 2) → Fin (x + 2) → ℝ),
  (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
  (∀ i j, 0 ≤ d i j) → (∀ i j t, d i t ≤ d i j + d j t) →
  (∀ i j p q, d i j * d p q ≤ d i p * d j q + d i q * d j p) →
  ∀ (A B : Fin x → Fin (x + 2)),
  A = (fun e => ite (Even e.val) e.castSucc.castSucc e.succ.castSucc) →
  B = (fun e => ite (Even e.val) e.succ.castSucc e.castSucc.castSucc) →
  ∀ (a b z : Fin (x + 2)), a = 0 → b = (Fin.last x).castSucc → z = Fin.last (x + 1) →
  ∀ (h : ℝ), h = 1 / (2 * (x : ℝ) + 1) →
  ∀ (w : Fin (x + 2) → ℝ),
  w = (fun v =>
    (1 - h) * (Finset.univ.sum (fun e => ite (A e = v) (1 : ℝ) 0) +
               Finset.univ.sum (fun e => ite (B e = v) (1 : ℝ) 0)) +
    (x : ℝ) * h * (ite (a = v) 1 0 + ite (b = v) 1 0) + ite (z = v) 1 0) →
  ∀ (W Y : ℝ),
  W = (Finset.univ.sum (fun i => Finset.univ.sum (fun j => w i * w j * d i j))) / 2 →
  Y = Finset.univ.sum (fun e : Fin x => d e.castSucc.castSucc e.succ.castSucc) + d a z + d b z →
  ∀ (δ σ K θ : ℝ), 0 < σ → θ ≤ 1 →
  δ / σ ≤ θ * (1 - h) ^ 2 → K + h * (δ / σ) / 2 ≤ (3 / 2 - θ) * (1 - h) →
  (∀ e f, d (A e) (A f) ≤ δ ∧ d (B e) (B f) ≤ δ) →
  (∀ e f, σ ≤ d (A e) (B f)) →
  (∀ j, d (B j) z + |d a z - d a (B j) / 2| ≤ K * d a (B j)) →
  (∀ i, d (A i) z + |d b z - d (A i) b / 2| ≤ K * d (A i) b) →
  (∀ v, 0 ≤ w v) ∧ Finset.univ.sum w = 2 * (x : ℝ) + 1 ∧
  0 ≤ W / (x : ℝ) - Y ∧
  (4 * W ≤ (Finset.univ.sum w) ^ 2 → Y ≤ (2 * (x : ℝ) + 1) ^ 2 / (4 * (x : ℝ))) := by
  intro x hodd hx d self symm nn triangle ptolemy A B Adef Bdef a b z adef bdef _zdef
    h hdef w wdef W Y Wdef Ydef δ σ K θ hσ θle corrBudget endBudget within sep costA costB
  obtain ⟨k, rfl⟩ := hodd
  let n := 2*k+1
  let g : Table (Fin (n+2)) := ⟨d, self, symm, nn, triangle, ptolemy⟩
  let s : Sample (Fin n) (Fin (n+2)) := ⟨A, B, 0, Fin.last (2*k), z⟩
  have left : s.A s.a = a := by
    change A 0 = a
    rw [Adef, adef]; simp
  have right : s.B s.b = b := by
    change B (Fin.last (2*k)) = b
    rw [Bdef, bdef]; simp
  have edge (e : Fin n) : d (A e) (B e) = d e.castSucc.castSucc e.succ.castSucc := by
    rw [Adef, Bdef]
    by_cases he : Even e.val
    · simp [he]
    · simpa [he] using symm e.succ.castSucc e.castSucc.castSucc
  have weights : w = weight s h := by
    funext i
    rw [wdef]
    simp only [weight, incidences, atom, left, right, Fintype.card_fin]
    rfl
  have he : energy g s h = W := by rw [Wdef, weights]; rfl
  have hy : (∑ i, g.d (s.A i) (s.B i)) + g.d (s.A s.a) s.z + g.d (s.B s.b) s.z = Y := by
    rw [left, right, Ydef]
    simp only [g, s, edge]
    rfl
  have hxR : 0 < (n : ℝ) := by positivity
  have den : 0 < 2*(n : ℝ)+1 := by positivity
  change h = 1 / (2*(n : ℝ)+1) at hdef
  have hh : 0 ≤ h := by rw [hdef]; positivity
  have ht : h ≤ 1 := by rw [hdef, div_le_iff₀ den]; linarith
  have balance : 2*(n : ℝ)*h = 1-h := by rw [hdef]; field_simp; ring
  have hcostA (j) : g.d (s.B j) s.z + |g.d (s.A s.a) s.z - g.d (s.A s.a) (s.B j)/2| ≤
      K*g.d (s.A s.a) (s.B j) := by simpa only [left] using costA j
  have hcostB (i) : g.d (s.A i) s.z + |g.d (s.B s.b) s.z - g.d (s.A i) (s.B s.b)/2| ≤
      K*g.d (s.A i) (s.B s.b) := by simpa only [right] using costB i
  have htlt := transport g s δ σ K θ h hσ hh ht (by simpa only [Fintype.card_fin] using balance)
    θle corrBudget endBudget within sep hcostA hcostB
  rw [he, hy, Fintype.card_fin] at htlt
  have mass : (∑ i, w i) = 2*(n : ℝ)+1 := by
    rw [weights]; simpa only [Fintype.card_fin] using weight_sum s h
  refine ⟨fun i => by rw [weights]; exact weight_nonneg s h hh ht i, mass, htlt, ?_⟩
  intro test
  rw [mass] at test
  have hW : W ≤ (2*(n : ℝ)+1)^2/4 := by linarith
  calc
    Y ≤ W/(n : ℝ) := sub_nonneg.mp htlt
    _ ≤ ((2*(n : ℝ)+1)^2/4)/n := div_le_div_of_nonneg_right hW hxR.le
    _ = _ := div_div ..

private theorem broad_cost (p qa qj : ℝ) (hp : 79/100 ≤ p) (hP : p ≤ 1)
    (ha : 34/100 ≤ qa) (hA : qa ≤ 66/100) (hJ : qj ≤ 66/100) :
    qj + |qa - p/2| ≤ (59/50) * p := by
  have hab : |qa-p/2| ≤ 53/200 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- The broad numerical box, derived directly from the single honest mass test. -/
theorem broad_path :
∀ (x : ℕ), Odd x → 999 ≤ x → ∀ (d : Fin (x + 2) → Fin (x + 2) → ℝ),
  (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
  (∀ i j, 0 ≤ d i j) → (∀ i j t, d i t ≤ d i j + d j t) →
  (∀ i j p q, d i j * d p q ≤ d i p * d j q + d i q * d j p) →
  ∀ (A B : Fin x → Fin (x + 2)),
  A = (fun e => ite (Even e.val) e.castSucc.castSucc e.succ.castSucc) →
  B = (fun e => ite (Even e.val) e.succ.castSucc e.castSucc.castSucc) →
  ∀ (a b z : Fin (x + 2)), a = 0 → b = (Fin.last x).castSucc → z = Fin.last (x + 1) →
  ∀ (h : ℝ), h = 1 / (2 * (x : ℝ) + 1) →
  ∀ (w : Fin (x + 2) → ℝ),
  w = (fun v =>
    (1 - h) * (Finset.univ.sum (fun e => ite (A e = v) (1 : ℝ) 0) +
               Finset.univ.sum (fun e => ite (B e = v) (1 : ℝ) 0)) +
    (x : ℝ) * h * (ite (a = v) 1 0 + ite (b = v) 1 0) + ite (z = v) 1 0) →
  ∀ (W Y : ℝ),
  W = (Finset.univ.sum (fun i => Finset.univ.sum (fun j => w i * w j * d i j))) / 2 →
  Y = Finset.univ.sum (fun e : Fin x => d e.castSucc.castSucc e.succ.castSucc) + d a z + d b z →
  (∀ e f, d (A e) (A f) ≤ 21 / 100 ∧ d (B e) (B f) ≤ 21 / 100) →
  (∀ e f, 79 / 100 ≤ d (A e) (B f) ∧ d (A e) (B f) ≤ 1) →
  (∀ e, 34 / 100 ≤ d (A e) z ∧ d (A e) z ≤ 66 / 100 ∧
        34 / 100 ≤ d (B e) z ∧ d (B e) z ≤ 66 / 100) →
  (∀ v, 0 ≤ w v) ∧ Finset.univ.sum w = 2 * (x : ℝ) + 1 ∧
  0 ≤ W / (x : ℝ) - Y ∧
  (4 * W ≤ (Finset.univ.sum w) ^ 2 → Y ≤ (2 * (x : ℝ) + 1) ^ 2 / (4 * (x : ℝ)))
:= by
  intro x hodd hx d self symm nn triangle ptolemy A B Adef Bdef a b z adef bdef zdef
    h hdef w wdef W Y Wdef Ydef within cross center
  have hxR : (999:ℝ) ≤ x := by exact_mod_cast hx
  have den : 0 < 2*(x : ℝ)+1 := by positivity
  have small : h ≤ 1/1000 := by rw [hdef, div_le_iff₀ den]; linarith
  have sq : (999/1000 : ℝ)^2 ≤ (1-h)^2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have ends : (∃ i, A i = a) ∧ (∃ j, B j = b) := by
    obtain ⟨k, rfl⟩ := hodd
    refine ⟨⟨0, ?_⟩, ⟨Fin.last (2*k), ?_⟩⟩
    · rw [Adef, adef]; simp
    · rw [Bdef, bdef]; simp
  obtain ⟨⟨ia, ha⟩, ⟨jb, hb⟩⟩ := ends
  apply path_certificate x hodd (by omega) d self symm nn triangle ptolemy A B Adef Bdef
    a b z adef bdef zdef h hdef w wdef W Y Wdef Ydef
    (21/100) (79/100) (59/50) (7/25) (by norm_num) (by norm_num) _ _ within
    (fun i j => (cross i j).1)
  · intro j
    rw [← ha]
    exact broad_cost _ _ _ (cross ia j).1 (cross ia j).2
      (center ia).1 (center ia).2.1 (center j).2.2.2
  · intro i
    rw [← hb]
    exact broad_cost _ _ _ (cross i jb).1 (cross i jb).2
      (center jb).2.2.1 (center jb).2.2.2 (center i).2.1
  · linarith only [sq]
  · linarith only [small]

/-- A second numerical box, allowing an endpoint coefficient of 5/4. -/
theorem path_193 :
∀ (x : ℕ), Odd x → 193 ≤ x → ∀ (d : Fin (x + 2) → Fin (x + 2) → ℝ),
  (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
  (∀ i j, 0 ≤ d i j) → (∀ i j t, d i t ≤ d i j + d j t) →
  (∀ i j p q, d i j * d p q ≤ d i p * d j q + d i q * d j p) →
  ∀ (A B : Fin x → Fin (x + 2)),
  A = (fun e => ite (Even e.val) e.castSucc.castSucc e.succ.castSucc) →
  B = (fun e => ite (Even e.val) e.succ.castSucc e.castSucc.castSucc) →
  ∀ (a b z : Fin (x + 2)), a = 0 → b = (Fin.last x).castSucc → z = Fin.last (x + 1) →
  ∀ (h : ℝ), h = 1 / (2 * (x : ℝ) + 1) →
  ∀ (w : Fin (x + 2) → ℝ),
  w = (fun v =>
    (1 - h) * (Finset.univ.sum (fun e => ite (A e = v) (1 : ℝ) 0) +
               Finset.univ.sum (fun e => ite (B e = v) (1 : ℝ) 0)) +
    (x : ℝ) * h * (ite (a = v) 1 0 + ite (b = v) 1 0) + ite (z = v) 1 0) →
  ∀ (W Y : ℝ),
  W = (Finset.univ.sum (fun i => Finset.univ.sum (fun j => w i * w j * d i j))) / 2 →
  Y = Finset.univ.sum (fun e : Fin x => d e.castSucc.castSucc e.succ.castSucc) + d a z + d b z →
  (∀ e f, d (A e) (A f) ≤ 16 / 100 ∧ d (B e) (B f) ≤ 16 / 100) →
  (∀ e f, 83 / 100 ≤ d (A e) (B f) ∧ d (A e) (B f) ≤ 1) →
  (∀ j, d (B j) z + |d a z - d a (B j) / 2| ≤ (5 / 4) * d a (B j)) →
  (∀ i, d (A i) z + |d b z - d (A i) b / 2| ≤ (5 / 4) * d (A i) b) →
  (∀ v, 0 ≤ w v) ∧ Finset.univ.sum w = 2 * (x : ℝ) + 1 ∧
  0 ≤ W / (x : ℝ) - Y ∧
  (4 * W ≤ (Finset.univ.sum w) ^ 2 → Y ≤ (2 * (x : ℝ) + 1) ^ 2 / (4 * (x : ℝ)))
:= by
  intro x hodd hx d self symm nn triangle ptolemy A B Adef Bdef a b z adef bdef zdef
    h hdef w wdef W Y Wdef Ydef within cross costA costB
  have hxR : (193:ℝ) ≤ x := by exact_mod_cast hx
  have den : 0 < 2*(x : ℝ)+1 := by positivity
  have small : h ≤ 3/1000 := by rw [hdef, div_le_iff₀ den]; linarith
  have sq : (997/1000 : ℝ)^2 ≤ (1-h)^2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  exact path_certificate x hodd (by omega) d self symm nn triangle ptolemy A B Adef Bdef
    a b z adef bdef zdef h hdef w wdef W Y Wdef Ydef
    (16/100) (83/100) (5/4) (1/5) (by norm_num) (by norm_num)
    (by linarith only [sq]) (by linarith only [small]) within (fun i j => (cross i j).1)
    costA costB

#print axioms broad_path
#print axioms path_193
#print axioms path_certificate

end OddCycleTarget.TiltedPath
