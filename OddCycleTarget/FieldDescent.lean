import OddCycleTarget.RankBridge

namespace OddCycleTarget

open Filter
open scoped BigOperators Topology
universe u

theorem hasDecomposition_map {F K : Type*} [Field F] [Field K] (f : F →+* K)
    {m n r : ℕ} (h : HasDecomposition F m n r) : HasDecomposition K m n r := by
  obtain ⟨u, hu⟩ := h
  refine ⟨fun s j x => f (u s j x), fun x => ?_⟩
  simpa [coeff, apply_ite] using congrArg f (hu x)

theorem integerUpper_map {F K : Type*} [Field F] [Field K] (f : F →+* K)
    {m : ℕ} (h : IntegerUpper F m) : IntegerUpper K m := by
  intro k hk
  obtain ⟨t, ht, r, hd, hr⟩ := h k hk
  exact ⟨t, ht, r, hasDecomposition_map f hd, hr⟩

theorem exponent_map_le {F K : Type*} [Field F] [Field K] (f : F →+* K) (m : ℕ) :
    exponent K m ≤ exponent F m := by
  apply le_of_tendsto_of_tendsto' (tendsto_dyadic_rate K m) (tendsto_dyadic_rate F m)
  intro t
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.log_nonneg (by norm_num)) t.cast_nonneg)
  apply Real.log_le_log
  · exact_mod_cast exactRank_pos K m (pow_pos (by decide : 0 < 2) t)
  · exact_mod_cast exactRank_le_of_decomposition (hasDecomposition_map f (exactRank_attained F m _))

/-- Descending each extension-field factor through a basis costs at most
the degree raised to the number of sites, independently of the edge side. -/
theorem descend_decomposition_finite (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {m : ℕ} [NeZero m] {n r : ℕ} (hd : HasDecomposition K m n r) :
    HasDecomposition F m n (r * Module.finrank F K ^ m) := by
  classical
  obtain ⟨u, hu⟩ := hd
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : K) ≠ 0)
  let D := Module.finrank F K
  let B := Module.finBasis F K
  let C := Fin m → Fin D
  have expand (v : Fin m → K) :
      (∏ j, v j) = ∑ c : C, (∏ j, B.repr (v j) (c j)) • (∏ j, B (c j)) := by
    calc
      _ = ∏ j, ∑ i : Fin D, B.repr (v j) i • B i :=
        Finset.prod_congr rfl (fun j _ => (B.sum_repr (v j)).symm)
      _ = ∑ c : C, ∏ j, B.repr (v j) (c j) • B (c j) := Fintype.prod_sum _
      _ = _ := by simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  have hcard : Fintype.card (Fin r × C) = r * D ^ m := by simp [C]
  let e : Fin (r * D ^ m) ≃ Fin r × C := (Fintype.equivFinOfCardEq hcard).symm
  let weight (c : C) : F := π (∏ j, B (c j))
  let U (a : Fin r × C) (j : Fin m) (z : IndexPair n) : F :=
    (if j = 0 then weight a.2 else 1) * B.repr (u a.1 j z) (a.2 j)
  refine ⟨fun a => U (e a), fun x => ?_⟩
  have hcoeff : π (coeff K m n x) = coeff F m n x := by
    by_cases h : ∀ j, (x j).2 = (x (nextSite j)).1 <;> simp [coeff, h, hπ]
  calc
    _ = π (∑ s, ∏ j, u s j (x j)) := hcoeff.symm.trans (congrArg π (hu x))
    _ = ∑ s, ∑ c : C, (∏ j, B.repr (u s j (x j)) (c j)) * weight c := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [expand (fun j => u s j (x j)), map_sum]
      simp only [map_smul, smul_eq_mul, weight]
    _ = ∑ a : Fin r × C, ∏ j, U a j (x j) := by
      rw [Fintype.sum_prod_type]
      simp only [U, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (weight _)]
    _ = _ := (e.sum_comp (fun a => ∏ j, U a j (x j))).symm

theorem exponent_eq_of_finiteExtension (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (m : ℕ) [NeZero m] : exponent F m = exponent K m := by
  apply le_antisymm _ (exponent_map_le (algebraMap F K) m)
  let c := Module.finrank F K ^ m
  have hc : 0 < c := pow_pos Module.finrank_pos m
  have eps := tendsto_const_div_atTop_nhds_zero_nat (Real.log (c : ℝ) / Real.log 2)
  have lim := (tendsto_dyadic_rate K m).add eps
  rw [add_zero] at lim
  apply le_of_tendsto_of_tendsto' (tendsto_dyadic_rate F m) lim
  intro t
  have hk : 0 < (exactRank K m (2^t) : ℝ) := by
    exact_mod_cast exactRank_pos K m (pow_pos (by decide : 0 < 2) t)
  have hf : 0 < (exactRank F m (2^t) : ℝ) := by
    exact_mod_cast exactRank_pos F m (pow_pos (by decide : 0 < 2) t)
  have hh : (exactRank F m (2^t) : ℝ) ≤ (exactRank K m (2^t) : ℝ) * c := by
    exact_mod_cast exactRank_le_of_decomposition
      (descend_decomposition_finite F K (exactRank_attained K m (2^t)))
  have h := div_le_div_of_nonneg_right (Real.log_le_log hf hh)
    (mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) t.cast_nonneg)
  rw [Real.log_mul hk.ne' (Nat.cast_ne_zero.mpr hc.ne'), add_div] at h
  simpa only [div_div] using h

/-- The finitely many coefficients of a fixed exact decomposition can be
specialized to a finite extension of the ground field without changing its
side, number of terms, or any compatible or incompatible coefficient. -/
theorem exponent_le_of_extension_decomposition (F K : Type*) [Field F] [Field K] [Algebra F K]
    {m : ℕ} [NeZero m] {n r : ℕ} (hn : 2 ≤ n) (hd : HasDecomposition K m n r) :
    exponent F m ≤ Real.log (r : ℝ) / Real.log (n : ℝ) := by
  classical
  obtain ⟨u, hu⟩ := hd
  let J := Fin r × Fin m × IndexPair n
  let g (a : J) : K := u a.1 a.2.1 a.2.2
  let S := Algebra.adjoin F (Set.range g)
  let _ : Algebra.FiniteType F S := Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  obtain ⟨I, hI⟩ := Ideal.exists_maximal S
  let _ : I.IsMaximal := hI
  let _ : Field (S ⧸ I) := Ideal.Quotient.field I
  let _ : FiniteDimensional F (S ⧸ I) := finite_of_finite_type_of_isJacobsonRing F (S ⧸ I)
  let b (s : Fin r) (j : Fin m) (z : IndexPair n) : S :=
    ⟨u s j z, Algebra.subset_adjoin ⟨⟨s, j, z⟩, rfl⟩⟩
  have hS (x : Fin m → IndexPair n) :
      (if ∀ j, (x j).2 = (x (nextSite j)).1 then (1 : S) else 0) = ∑ s, ∏ j, b s j (x j) := by
    apply (Subtype.val_injective : Function.Injective (S.val : S → K))
    simpa [coeff, apply_ite, b] using hu x
  let f : S →+* S ⧸ I := Ideal.Quotient.mk I
  have hE : HasDecomposition (S ⧸ I) m n r := by
    refine ⟨fun s j x => f (b s j x), fun x => ?_⟩
    simpa [coeff, apply_ite] using congrArg f (hS x)
  rw [exponent_eq_of_finiteExtension F (S ⧸ I) m]
  exact exponent_le_of_decomposition hn hE

/-- Arbitrary ground-field extensions preserve the dyadic exact-rank exponent. -/
theorem exponent_eq_of_extension (F K : Type*) [Field F] [Field K] [Algebra F K]
    (m : ℕ) [NeZero m] : exponent F m = exponent K m := by
  apply le_antisymm _ (exponent_map_le (algebraMap F K) m)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_dyadic_rate K m)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  have hn : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ t from ht)
  have h := exponent_le_of_extension_decomposition F K hn (exactRank_attained K m (2 ^ t))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_comm (t : ℝ)] using h

theorem integerUpper_iff_of_extension (F K : Type*) [Field F] [Field K] [Algebra F K]
    (m : ℕ) (hm : 3 ≤ m) : IntegerUpper F m ↔ IntegerUpper K m := by
  let _ : NeZero m := ⟨by omega⟩
  rw [integerUpper_iff_exponent_le F m hm, integerUpper_iff_exponent_le K m hm,
    exponent_eq_of_extension F K m]

/-- The exponent is constant on fields of a fixed characteristic, including
fields of different cardinalities and universes. -/
theorem exponent_eq_of_ringChar_eq (F K : Type*) [Field F] [Field K]
    (hchar : ringChar F = ringChar K) (m : ℕ) [NeZero m] : exponent F m = exponent K m := by
  have hK : CharP K (ringChar F) := hchar ▸ inferInstanceAs (CharP K (ringChar K))
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | hz
  · let _ : Fact (ringChar F).Prime := ⟨hp⟩
    let P := ZMod (ringChar F)
    let _ : Algebra P F := (ZMod.castHom (m := ringChar F) dvd_rfl F).toAlgebra
    let _ : Algebra P K := (ZMod.castHom (m := ringChar F) dvd_rfl K).toAlgebra
    exact (exponent_eq_of_extension P F m).symm.trans (exponent_eq_of_extension P K m)
  · have : CharP F 0 := hz ▸ inferInstanceAs (CharP F (ringChar F))
    have : CharP K 0 := hz ▸ hK
    have : CharZero F := CharP.charP_to_charZero F
    have : CharZero K := CharP.charP_to_charZero K
    exact (exponent_eq_of_extension ℚ F m).symm.trans (exponent_eq_of_extension ℚ K m)

/-- Checking all prime fields suffices for the universal packet predicate
in any specified universe. Each precision and field keeps its own witnesses. -/
theorem universalIntegerUpper_iff_prime_fields :
    UniversalIntegerUpper.{u} ↔
      (∀ m : ℕ, 3 ≤ m → Odd m → IntegerUpper ℚ m) ∧
      (∀ (p : ℕ) [Fact p.Prime] (m : ℕ), 3 ≤ m → Odd m → IntegerUpper (ZMod p) m) := by
  constructor
  · intro hall
    constructor
    · intro m hm ho
      exact integerUpper_map ULift.ringEquiv.toRingHom (hall (ULift.{u} ℚ) m hm ho)
    · intro p _ m hm ho
      exact integerUpper_map ULift.ringEquiv.toRingHom (hall (ULift.{u} (ZMod p)) m hm ho)
  · rintro ⟨hQ, hP⟩ F _ m hm ho
    rcases CharP.exists' F with h0 | ⟨p, hp, hc⟩
    · exact integerUpper_map (Rat.castHom F) (hQ m hm ho)
    · exact integerUpper_map (ZMod.castHom (m := p) dvd_rfl F) (hP p m hm ho)

end OddCycleTarget
