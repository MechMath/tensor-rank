import OddCycleTarget.SpectrumBridge
import OddCycleTarget.MassTests

/-! Transfer between the binary complete-graph rank bound and the real
quadratic constraint on actual spectral prices. The grouping calculation
extends the seven-site proof in the Stage 1 v1 C5Clique module. -/
namespace OddCycleTarget.Spectrum

open OAI.LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators NNReal
noncomputable section

private abbrev wire (F : Type*) [Field F] {n : ℕ} [NeZero n] (i j : Fin n) :
    TensorClass.{0} (Fin n) F :=
  ofRaw ((Raw.diagonal (Fin 2) F (Fin 2)).group ![i, j])

/-- Each unordered pair of original sites receives one independent binary wire. -/
def binaryClique (F : Type*) [Field F] (n : ℕ) [NeZero n] : TensorClass.{0} (Fin n) F :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, wire F i j

private theorem group_natCast_le (F : Type*) [Field F] {n m : ℕ} [NeZero n] [NeZero m]
    (p : Fin n → Fin m) (r : ℕ) :
    groupMulHom p (r : TensorClass.{0} (Fin n) F) ≤ (r : TensorClass.{0} (Fin m) F) := by
  rw [← ofRaw_diagonal_fin_eq_natCast (Fin n) F, ← ofRaw_diagonal_fin_eq_natCast (Fin m) F]
  change ofRaw ((Raw.diagonal (Fin n) F (Fin r)).group p) ≤ ofRaw (Raw.diagonal (Fin m) F (Fin r))
  calc
    _ ≤ ofRaw ((Raw.diagonal (Fin m) F (Fin r)).group id) :=
      Raw.group_diagonal_restricts_of_comp id p (Fin r)
    _ = _ := ofRaw_eq_iff.mpr (Raw.group_id_equivalent _)

/-- An arbitrary grouping, with possibly empty or colliding fibers, cannot
increase asymptotic rank over the same field. -/
theorem group_asymptoticRank_le (F : Type*) [Field F] {n m : ℕ} [NeZero n] [NeZero m]
    (p : Fin n → Fin m) (T : TensorClass.{0} (Fin n) F) :
    asymptoticRank (groupMulHom p T) ≤ asymptoticRank T := by
  unfold SiteTensor.asymptoticRank
  apply ciInf_mono ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  intro k
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
  rw [← map_pow]
  exact_mod_cast rank_le_of_le ((groupClass_mono p (le_rank (T ^ (k + 1)))).trans
    (group_natCast_le F p _))

private theorem group_wire (F : Type*) [Field F] {n m : ℕ} [NeZero n] [NeZero m]
    (p : Fin n → Fin m) (i j : Fin n) :
    groupMulHom p (wire F i j) = wire F (p i) (p j) := by
  have h : p ∘ ![i,j] = ![p i, p j] := by funext x; fin_cases x <;> rfl
  change ofRaw (((Raw.diagonal (Fin 2) F (Fin 2)).group ![i,j]).group p) = _
  rw [ofRaw_eq_iff.mpr (Raw.group_group_equivalent _ _ _), h]

private theorem log_value_grouped_clique (F : Type*) [Field F] {n m : ℕ} [NeZero n] [NeZero m]
    (φ : Point F m) (p : Fin n → Fin m) :
    Real.logb 2 (φ.val (groupMulHom p (binaryClique F n)) : ℝ) =
      ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, rawWireDistance φ 1 (p i) (p j) := by
  let g := normalizedSpectrum.toRingHom φ
  let f (i j : Fin n) := (g (wire F (p i) (p j)) : ℝ)
  have hf (i j : Fin n) : 0 < f i j :=
    NNReal.coe_pos.mpr (spectral_value_pos φ (binary_wire_nonzero F _ _))
  have eval : (φ.val (groupMulHom p (binaryClique F n)) : ℝ) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
    change (g (groupMulHom p (binaryClique F n)) : ℝ) = _
    simp only [binaryClique, map_prod, NNReal.coe_prod, group_wire, f]
  rw [eval, Real.logb_prod _ _ (fun i _ => (Finset.prod_pos (fun j _ => hf i j)).ne')]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.logb_prod _ _ (fun j _ => (hf i j).ne')]
  simp only [rawWireDistance, rawLogPrice, one_mul]
  rfl

/-- Bound on placements of a fixed complete graph, directly from its exact
asymptotic rank over F. -/
theorem placement_sum_le_clique_logrank (F : Type*) [Field F] {n m : ℕ} [NeZero n] [NeZero m]
    (φ : Point F m) (p : Fin n → Fin m) :
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, rawWireDistance φ 1 (p i) (p j)) ≤
      Real.logb 2 (asymptoticRank (binaryClique F n)) := by
  rw [← log_value_grouped_clique F φ p]
  apply Real.logb_le_logb_of_le (by norm_num) _
    ((spectral_value_le_asymptoticRank φ _).trans (group_asymptoticRank_le F p _))
  apply NNReal.coe_pos.mpr
  apply spectral_value_pos
  simp only [binaryClique, map_prod, group_wire]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => binary_wire_nonzero F _ _

/-- The ordered-pair mass inequality at integral weights only needs the
complete-graph bound for the sum of these weights. -/
theorem nat_mass_of_clique_upper (F : Type*) [Field F] {m : ℕ} [NeZero m]
    (φ : Point F m) (a : Fin m → ℕ)
    (hcl : ∀ (n : ℕ) [NeZero n], n = ∑ i, a i → 2 ≤ n →
      Real.logb 2 (asymptoticRank (binaryClique F n)) ≤ (n : ℝ)^2 / 4) :
    2 * (∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * rawWireDistance φ 1 i j) ≤
      (∑ i, (a i : ℝ)) ^ 2 := by
  apply nat_mass_of_placements _ (rawWireDistance_self φ 1 (by norm_num))
  intro hn p
  let N := ∑ i, a i
  let _ : NeZero N := ⟨by change (∑ i, a i) ≠ 0; omega⟩
  have hp := (placement_sum_le_clique_logrank (n := N) F φ p).trans (hcl N rfl hn)
  rw [ordered_sum_eq_twice_upper (fun i j : Fin N => rawWireDistance φ 1 (p i) (p j))
    (fun i => rawWireDistance_self φ 1 (by norm_num) (p i))
    (fun i j => rawWireDistance_symm φ 1 (p i) (p j))]
  linarith

/-- The upper direction of Zhou's complete-graph theorem implies the
all-mass inequality on the actual normalized spectrum on every site count. -/
theorem real_mass_of_clique_upper (F : Type*) [Field F]
    (hcl : ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      Real.logb 2 (asymptoticRank (binaryClique F n)) ≤ (n : ℝ)^2 / 4)
    {m : ℕ} [NeZero m] (φ : Point F m) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    2 * (∑ i, ∑ j, w i * w j * rawWireDistance φ 1 i j) ≤ (∑ i, w i) ^ 2 :=
  real_mass_of_nat_mass _ (fun a => nat_mass_of_clique_upper F φ a (fun n _ _ hn => hcl n hn)) w hw

/-- The upper bound on all binary clique ranks is equivalent, over the same
field, to the real quadratic constraint on every actual normalized point. -/
theorem clique_upper_iff_actual_mass (F : Type*) [Field F] :
    (∀ (n : ℕ) [NeZero n], 2 ≤ n →
      Real.logb 2 (asymptoticRank (binaryClique F n)) ≤ (n : ℝ)^2 / 4) ↔
    ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (φ : Point F m) (w : Fin m → ℝ), (∀ i, 0 ≤ w i) →
      2 * (∑ i, ∑ j, w i * w j * rawWireDistance φ 1 i j) ≤ (∑ i, w i)^2 := by
  constructor
  · intro h m _ _ φ w hw
    exact real_mass_of_clique_upper F h φ w hw
  · intro hall n _ hn
    let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨φ, hφ⟩ := exists_spectral_value_eq_asymptoticRank (binaryClique F n)
    have group_id : groupMulHom (id : Fin n → Fin n) (binaryClique F n) = binaryClique F n := by
      simp only [binaryClique, map_prod, group_wire, id_eq]
    have hlog := log_value_grouped_clique F φ (id : Fin n → Fin n)
    rw [group_id, hφ] at hlog
    have hmass : 2 * (∑ i, ∑ j, rawWireDistance φ 1 i j) ≤ (n : ℝ)^2 := by
      simpa using hall n hn φ (fun _ => 1) (fun _ => zero_le_one)
    rw [ordered_sum_eq_twice_upper _ (rawWireDistance_self φ 1 (by norm_num))
      (rawWireDistance_symm φ 1)] at hmass
    rw [hlog]
    simp only [id_eq]
    linarith

end
end OddCycleTarget.Spectrum
