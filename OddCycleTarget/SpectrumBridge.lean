import OddCycleTarget.RankBridge
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPower
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.StrassenRank
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.FinitePlacementDiameter
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

/-! Original-slot spectral duality for all site counts at least two. The
coordinate port and rank arguments extend Stage 1's RawCoordinates and
SpectralMaximum, using the same ground-field tensor restriction spectrum. -/
namespace OddCycleTarget.Spectrum

open OAI.LinearAlgebra.SpectralBooks SiteTensor
open Filter
open scoped BigOperators NNReal Topology
noncomputable section

def cycleRaw (F : Type*) [Field F] (m n : ℕ) : Raw.{0} (Fin m) F :=
  ⟨fun _ => IndexPair n, fun _ => inferInstance, coeff F m n⟩

theorem decomposition_iff_restricts_diagonal (F : Type*) [Field F] (m n r : ℕ) :
    HasDecomposition F m n r ↔
      (cycleRaw F m n).Restricts (Raw.diagonal (Fin m) F (Fin r)) := by
  classical
  have diag : (cycleRaw F m n).Restricts (Raw.diagonal (Fin m) F (Fin r)) ↔
      Crossing.IsRestriction (A := fun _ : Fin m => Fin r) (B := fun _ => IndexPair n)
        (coeff F m n) (Crossing.basisTensor (fun (s : Fin r) (_ : Fin m) => s)) := by
    unfold Raw.Restricts cycleRaw Raw.diagonal Crossing.basisTensor Crossing.IsRestriction
    dsimp
    congr! 7
    split <;> simp_all
  rw [diag, Crossing.restriction_basisTensor_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun i x s => u s i x, hu⟩
  · rintro ⟨M, hM⟩
    exact ⟨fun s i x => M i x s, hM⟩

private theorem nextSite_eq_rotate {m : ℕ} (i : Fin m) : nextSite i = finRotate m i := by
  let := i.neZero
  rw [finRotate_apply]
  apply Fin.ext
  change (i.val + 1) % m = (i.val + 1 % m) % m
  simp

private def ports (m : ℕ) : PortGraph (Fin m) (Fin m) := ⟨id, nextSite⟩

private def incoming {m : ℕ} (i : Fin m) : (ports m).Port i :=
  ⟨((finRotate m).symm i, true), show nextSite ((finRotate m).symm i) = i by
    rw [nextSite_eq_rotate, Equiv.apply_symm_apply]⟩

private def outgoing {m : ℕ} (i : Fin m) : (ports m).Port i := ⟨(i, false), rfl⟩

private def pairPortEquiv {m : ℕ} (n : ℕ) (i : Fin m) :
    IndexPair n ≃ (ports m).State (fun _ => Fin n) i where
  toFun x p := if p.val.2 then x.1 else x.2
  invFun y := (y (incoming i), y (outgoing i))
  left_inv _ := rfl
  right_inv y := by
    funext ⟨⟨j, b⟩, hj⟩
    cases b with
    | false =>
      change j = i at hj
      subst i
      rfl
    | true =>
      change nextSite j = i at hj
      subst i
      change y (incoming (nextSite j)) = y _
      apply congrArg y
      apply Subtype.ext
      change ((finRotate m).symm (nextSite j), true) = (j, true)
      rw [nextSite_eq_rotate, Equiv.symm_apply_apply]

abbrev Point (F : Type*) [Field F] (m : ℕ) [NeZero m] :=
  normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) F → _ → Prop)

theorem exactRank_eq_classRank (F : Type*) [Field F] (m : ℕ) [NeZero m] (n : ℕ) :
    exactRank F m n = rank (ofRaw (cycleRaw F m n)) := by
  have h (r : ℕ) : HasDecomposition F m n r ↔
      ofRaw (cycleRaw F m n) ≤ (r : TensorClass.{0} (Fin m) F) := by
    rw [← ofRaw_diagonal_fin_eq_natCast (Fin m) F r, ofRaw_le_iff]
    exact decomposition_iff_restricts_diagonal F m n r
  exact le_antisymm (exactRank_le_of_decomposition ((h _).mpr (le_rank _)))
    (rank_le_of_le ((h _).mp (exactRank_attained F m n)))

theorem class_eq_wire_product (F : Type*) [Field F] (m : ℕ) [NeZero m] (n : ℕ) :
    ofRaw (cycleRaw F m n) = ∏ i : Fin m,
      ofRaw ((Raw.diagonal (Fin 2) F (Fin n)).group ![i, nextSite i]) := by
  calc
    _ = ofRaw ((ports m).rawWiring F (fun _ => Fin n)) := by
      apply ofRaw_eq_iff.mpr
      apply Raw.reindex_equivalent (fun i => pairPortEquiv n i)
      intro x
      by_cases h : ∀ j, (x j).2 = (x (nextSite j)).1
      · change (if ∀ j, (x j).2 = (x (nextSite j)).1 then (1 : F) else 0) = _
        rw [ite_eq_left h]
        exact (ite_eq_left h).symm
      · change (if ∀ j, (x j).2 = (x (nextSite j)).1 then (1 : F) else 0) = _
        rw [ite_eq_right h]
        exact (ite_eq_right h).symm
    _ = _ := by
      rw [PortGraph.ofRaw_rawWiring]
      rfl

theorem dyadic_class_pow (F : Type*) [Field F] (m : ℕ) [NeZero m] (t : ℕ) :
    ofRaw (cycleRaw F m (2 ^ t)) = ofRaw (cycleRaw F m 2) ^ t := by
  rw [class_eq_wire_product, class_eq_wire_product]
  simp_rw [ofRaw_group_diagonal_fin_pow F _ 2 t]
  exact Finset.prod_pow _ _ _

theorem asymptoticRank_eq_two_rpow (F : Type*) [Field F] (m : ℕ) [NeZero m] :
    asymptoticRank (ofRaw (cycleRaw F m 2)) = (2 : ℝ) ^ exponent F m := by
  have h₁ := tendsto_rank_root (ofRaw (cycleRaw F m 2))
  have h₂ : Tendsto (fun t : ℕ => (2 : ℝ) ^ (Real.logb 2 (exactRank F m (2 ^ t) : ℝ) / t))
      atTop (𝓝 ((2 : ℝ) ^ exponent F m)) := by
    apply tendsto_const_nhds.rpow _ (Or.inl (by norm_num))
    simpa only [Real.logb, div_div] using tendsto_dyadic_rate F m
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro t
  have hp : 0 < (exactRank F m (2 ^ t) : ℝ) := by
    exact_mod_cast exactRank_pos F m (pow_pos (by decide : 0 < 2) t)
  rw [div_eq_mul_inv, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) hp, ← dyadic_class_pow F m t,
    ← exactRank_eq_classRank F m (2 ^ t)]

theorem binary_wire_nonzero (F : Type*) [Field F] {m : ℕ} [NeZero m] (i j : Fin m) :
    ofRaw ((Raw.diagonal (Fin 2) F (Fin 2)).group ![i,j]) ≠ 0 := by
  rw [ne_eq, ofRaw_eq_zero_iff]
  apply ((Raw.diagonal (Fin 2) F (Fin 2)).group_ne_zero_iff _).mpr
  intro h
  have hh := congrFun h (fun _ => (0 : Fin 2))
  change (Raw.diagonal (Fin 2) F (Fin 2)).coeff (fun _ => (0 : Fin 2)) = (0 : F) at hh
  simp [Raw.diagonal, funext_iff] at hh

theorem logb_value_eq_cycle (F : Type*) [Field F] {m : ℕ} [NeZero m] (φ : Point F m) :
    Real.logb 2 (φ.val (ofRaw (cycleRaw F m 2)) : ℝ) =
      ∑ i : Fin m, rawWireDistance φ 1 i (nextSite i) := by
  let f := normalizedSpectrum.toRingHom φ
  change Real.logb 2 (f (ofRaw (cycleRaw F m 2)) : ℝ) = _
  rw [class_eq_wire_product, map_prod, NNReal.coe_prod, Real.logb_prod]
  · simp only [rawWireDistance, rawLogPrice, one_mul, f]
    rfl
  · intro i _
    exact (NNReal.coe_pos.mpr (spectral_value_pos φ (binary_wire_nonzero F i (nextSite i)))).ne'

/-- The exact packet exponent is attained by an actual normalized point over F. -/
theorem spectralMaximum (F : Type*) [Field F] (m : ℕ) [NeZero m] (hm : 2 ≤ m) :
    IsGreatest (Set.range fun φ : Point F m => ∑ i : Fin m, rawWireDistance φ 1 i (nextSite i))
      (exponent F m) := by
  let _ : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let T := ofRaw (cycleRaw F m 2)
  have ranklog : Real.logb 2 (asymptoticRank T) = exponent F m := by
    rw [asymptoticRank_eq_two_rpow, Real.logb_rpow (by norm_num) (by norm_num)]
  constructor
  · obtain ⟨φ, hφ⟩ := exists_spectral_value_eq_asymptoticRank T
    exact ⟨φ, (logb_value_eq_cycle F φ).symm.trans ((congrArg (Real.logb 2) hφ).trans ranklog)⟩
  · rintro _ ⟨φ, rfl⟩
    change (∑ i : Fin m, rawWireDistance φ 1 i (nextSite i)) ≤ exponent F m
    rw [← logb_value_eq_cycle F φ, ← ranklog]
    apply Real.logb_le_logb_of_le (by norm_num) _ (spectral_value_le_asymptoticRank φ T)
    apply NNReal.coe_pos.mpr
    apply spectral_value_pos
    change ofRaw (cycleRaw F m 2) ≠ 0
    rw [class_eq_wire_product]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => binary_wire_nonzero F i (nextSite i)

theorem wire_le_one {F : Type*} [Field F] {m : ℕ} [NeZero m] (φ : Point F m) (i j : Fin m) :
    rawWireDistance φ 1 i j ≤ 1 := by
  have h := rawWireDistance_le_group_diagonal φ (by norm_num : (0 : ℝ) ≤ 1)
    (id : Fin m → Fin m) i j
  have he := ofRaw_eq_iff.mpr (Raw.group_id_equivalent (Raw.diagonal (Fin m) F (Fin 2)))
  simp only [id_eq, rawLogPrice, he, ofRaw_diagonal_fin_eq_natCast, one_mul] at h
  let f := normalizedSpectrum.toRingHom φ
  change rawWireDistance φ 1 i j ≤ Real.logb 2 (f (2 : TensorClass.{0} (Fin m) F) : ℝ) at h
  have htwo : f (2 : TensorClass.{0} (Fin m) F) = 2 := map_ofNat f 2
  rw [htwo] at h
  simpa only [NNReal.coe_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

theorem integerUpper_iff_all_prices (F : Type*) [Field F] (m : ℕ) [NeZero m] (hm : 3 ≤ m) :
    IntegerUpper F m ↔ ∀ φ : Point F m,
      (∑ i : Fin m, rawWireDistance φ 1 i (nextSite i)) ≤ (A m : ℝ) / (D m : ℝ) := by
  rw [integerUpper_iff_exponent_le F m hm]
  have h := spectralMaximum F m (by omega)
  constructor
  · intro hΓ φ
    exact (h.2 (Set.mem_range_self φ)).trans hΓ
  · intro hφ
    obtain ⟨φ, hmax⟩ := h.1
    rw [← hmax]
    exact hφ φ

end
end OddCycleTarget.Spectrum
