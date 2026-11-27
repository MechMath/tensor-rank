import OddCycleTarget
import Mathlib.Analysis.Subadditive

/-! Finite decompositions, dyadic convergence and integer witnesses in the
packet's original labelled coordinates. The finite-coordinate construction
generalizes the five-site arguments in the Stage 1 C5Rank module. -/
namespace OddCycleTarget

open scoped BigOperators

/-- One product of local basis coordinates for every labelling of the edges. -/
theorem basis_decomposition (F : Type*) [Field F] (m n : ℕ) :
    HasDecomposition F m n (n ^ m) := by
  classical
  let T := Fin m → Fin n
  have hcard : Fintype.card T = n ^ m := by simp [T]
  let e : Fin (n ^ m) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  let localPair (g : T) (j : Fin m) : IndexPair n := (g j, g (nextSite j))
  refine ⟨fun s j z => if localPair (e s) j = z then 1 else 0, ?_⟩
  intro x
  symm
  calc
    _ = ∑ g : T, ∏ j, (if localPair g j = x j then (1 : F) else 0) := e.sum_comp _
    _ = ∑ g : T, (if ∀ j, localPair g j = x j then (1 : F) else 0) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Fintype.prod_boole]
      split_ifs <;> simp_all
    _ = coeff F m n x := by
      by_cases hc : ∀ j, (x j).2 = (x (nextSite j)).1
      · let v : T := fun j => (x j).1
        have he (g : T) : (∀ j, localPair g j = x j) ↔ g = v := by
          constructor
          · intro h
            exact funext fun j => congrArg Prod.fst (h j)
          · rintro rfl j
            exact Prod.ext rfl (hc j).symm
        simp only [he, coeff, ite_eq_left hc]
        exact Fintype.sum_ite_eq' v (fun _ => (1 : F))
      · have he (g : T) : ¬ ∀ j, localPair g j = x j := by
          intro h
          apply hc
          intro j
          exact (congrArg Prod.snd (h j)).symm.trans (congrArg Prod.fst (h (nextSite j)))
        simp [he, coeff, hc]

theorem exactRank_attained (F : Type*) [Field F] (m n : ℕ) :
    HasDecomposition F m n (exactRank F m n) :=
  csInf_mem (s := {r : ℕ | HasDecomposition F m n r}) ⟨_, basis_decomposition F m n⟩

theorem exactRank_le_of_decomposition {F : Type*} [Field F] {m n r : ℕ}
    (h : HasDecomposition F m n r) : exactRank F m n ≤ r :=
  Nat.sInf_le h

theorem exactRank_pos (F : Type*) [Field F] (m : ℕ) {n : ℕ} (hn : 0 < n) :
    0 < exactRank F m n := by
  by_contra! h
  have hd : HasDecomposition F m n 0 := Nat.eq_zero_of_le_zero h ▸ exactRank_attained F m n
  obtain ⟨_, hzero⟩ := hd
  let z : Fin n := ⟨0, hn⟩
  simpa [coeff] using hzero (fun _ => (z, z))

private def splitPair {a b : ℕ} (x : IndexPair (a * b)) : IndexPair a × IndexPair b :=
  let e := (finProdFinEquiv (m := a) (n := b)).symm
  (((e x.1).1, (e x.2).1), ((e x.1).2, (e x.2).2))

private theorem coeff_mul (F : Type*) [Field F] {m a b : ℕ}
    (x : Fin m → IndexPair (a * b)) :
    coeff F m (a * b) x =
      coeff F m a (fun j => (splitPair (x j)).1) *
      coeff F m b (fun j => (splitPair (x j)).2) := by
  classical
  let e := (finProdFinEquiv (m := a) (n := b)).symm
  have hiff : (∀ j, (x j).2 = (x (nextSite j)).1) ↔
      (∀ j, (splitPair (x j)).1.2 = (splitPair (x (nextSite j))).1.1) ∧
      (∀ j, (splitPair (x j)).2.2 = (splitPair (x (nextSite j))).2.1) := by
    constructor
    · intro h
      exact ⟨fun j => congrArg (fun z => (e z).1) (h j),
        fun j => congrArg (fun z => (e z).2) (h j)⟩
    · rintro ⟨h₁, h₂⟩ j
      exact e.injective (Prod.ext (h₁ j) (h₂ j))
  by_cases h₁ : ∀ j, (splitPair (x j)).1.2 = (splitPair (x (nextSite j))).1.1 <;>
    by_cases h₂ : ∀ j, (splitPair (x j)).2.2 = (splitPair (x (nextSite j))).2.1 <;>
    simp [coeff, hiff, h₁, h₂]

/-- Pair the labels within each site and take every pair of summands. -/
theorem hasDecomposition_mul {F : Type*} [Field F] {m a b r s : ℕ}
    (hr : HasDecomposition F m a r) (hs : HasDecomposition F m b s) :
    HasDecomposition F m (a * b) (r * s) := by
  classical
  obtain ⟨u, hu⟩ := hr
  obtain ⟨v, hv⟩ := hs
  let e : Fin (r * s) ≃ Fin r × Fin s := finProdFinEquiv.symm
  refine ⟨fun k j z => u (e k).1 j (splitPair z).1 * v (e k).2 j (splitPair z).2, ?_⟩
  intro x
  rw [coeff_mul F x, hu, hv, Finset.sum_mul_sum]
  symm
  let f (k : Fin r × Fin s) : F :=
    ∏ j, u k.1 j (splitPair (x j)).1 * v k.2 j (splitPair (x j)).2
  calc
    _ = ∑ k : Fin r × Fin s, f k := e.sum_comp f
    _ = _ := by rw [Fintype.sum_prod_type]; simp [f, Finset.prod_mul_distrib]

theorem exactRank_submultiplicative (F : Type*) [Field F] (m a b : ℕ) :
    exactRank F m (a * b) ≤ exactRank F m a * exactRank F m b :=
  exactRank_le_of_decomposition (hasDecomposition_mul (exactRank_attained F m a)
    (exactRank_attained F m b))

/-- Restrict both endpoint labels in every slot along the same injection. -/
theorem hasDecomposition_restrict {F : Type*} [Field F] {m n N r : ℕ}
    (hn : n ≤ N) (hd : HasDecomposition F m N r) : HasDecomposition F m n r := by
  obtain ⟨u, hu⟩ := hd
  let pair (p : IndexPair n) : IndexPair N := (p.1.castLE hn, p.2.castLE hn)
  refine ⟨fun s j p => u s j (pair p), fun x => ?_⟩
  simpa only [coeff, pair, Fin.castLE_inj] using hu (fun j => pair (x j))

theorem hasDecomposition_pow {F : Type*} [Field F] {m n r : ℕ}
    (hd : HasDecomposition F m n r) (j : ℕ) : HasDecomposition F m (n ^ j) (r ^ j) := by
  induction j with
  | zero => simpa using basis_decomposition F m 1
  | succ j ih => simpa only [pow_succ] using hasDecomposition_mul ih hd

/-- A finite witness at half the requested tolerance gives a concrete dyadic
witness by taking powers and truncating the alphabet. -/
theorem dyadic_witness_of_finite {F : Type*} [Field F] {m n r k : ℕ}
    (hn : 2 ≤ n) (hd : HasDecomposition F m n r)
    (hpow : r ^ (D m * (2 * k)) ≤ n ^ (A m * (2 * k) + 1)) :
    let j := 2 * (A m * k) + 1
    let t := Nat.log 2 (n ^ j)
    0 < t ∧ HasDecomposition F m (2 ^ t) (r ^ j) ∧
      (r ^ j) ^ (D m * k) ≤ 2 ^ ((A m * k + 1) * t) := by
  let p := A m * k
  let j := 2 * p + 1
  let t := Nat.log 2 (n ^ j)
  have hdim : 2 ^ t ≤ n ^ j := Nat.pow_log_le_self 2 (pow_ne_zero j (by omega))
  have hnext : n ^ j ≤ 2 ^ (t + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
  have ht : j ≤ t := Nat.le_log_of_pow_le (by decide) (Nat.pow_le_pow_left hn j)
  refine ⟨Nat.lt_of_lt_of_le (Nat.succ_pos (2 * p)) ht,
    hasDecomposition_restrict hdim (hasDecomposition_pow hd j), ?_⟩
  apply (Nat.pow_le_pow_iff_left (n := 2) (by decide)).mp
  change ((r ^ j) ^ (D m * k)) ^ 2 ≤ (2 ^ ((p + 1) * t)) ^ 2
  calc
    _ = (r ^ (D m * (2 * k))) ^ j := by
      simp only [← pow_mul]
      congr 1
      ring
    _ ≤ (n ^ (A m * (2 * k) + 1)) ^ j := Nat.pow_le_pow_left hpow j
    _ = (n ^ j) ^ (2 * p + 1) := by
      simp only [← pow_mul, p]
      congr 1
      ring
    _ ≤ (2 ^ (t + 1)) ^ (2 * p + 1) := Nat.pow_le_pow_left hnext _
    _ ≤ _ := by
      simp only [← pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      change 2 * p + 1 ≤ t at ht
      nlinarith only [ht]

/-- The same approximation criterion may use any finite side at least two. -/
theorem integerUpper_iff_arbitrary_side (F : Type*) [Field F] (m : ℕ) :
    IntegerUpper F m ↔ ∀ k : ℕ, 0 < k → ∃ n : ℕ, 2 ≤ n ∧ ∃ r : ℕ,
      HasDecomposition F m n r ∧ r ^ (D m * k) ≤ n ^ (A m * k + 1) := by
  constructor
  · intro h k hk
    obtain ⟨t, ht, r, hd, hr⟩ := h k hk
    refine ⟨2 ^ t, ?_, r, hd, ?_⟩
    · simpa using (Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ t from ht))
    · simpa only [← pow_mul, mul_comm t] using hr
  · intro h k hk
    obtain ⟨n, hn, r, hd, hr⟩ := h (2 * k) (by omega)
    obtain ⟨ht, hdyad, hbound⟩ := dyadic_witness_of_finite hn hd hr
    exact ⟨_, ht, _, hdyad, hbound⟩

private noncomputable def dyadicRate (F : Type*) [Field F] (m t : ℕ) : ℝ :=
  Real.log (exactRank F m (2 ^ t) : ℝ) / (Real.log 2 * (t : ℝ))

private theorem dyadicRate_bddBelow (F : Type*) [Field F] (m : ℕ) :
    BddBelow (Set.range (dyadicRate F m)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, rfl⟩
  have h : 1 ≤ (exactRank F m (2 ^ t) : ℝ) := by
    exact_mod_cast (exactRank_pos F m (pow_pos (by decide : 0 < 2) t))
  exact div_nonneg (Real.log_nonneg h) (mul_nonneg (Real.log_nonneg (by norm_num)) t.cast_nonneg)

private theorem exponent_eq_sInf_image (F : Type*) [Field F] (m : ℕ) :
    exponent F m = sInf (dyadicRate F m '' Set.Ici 1) := by
  unfold exponent
  congr 1
  ext x
  constructor <;> rintro ⟨t, ht, rfl⟩ <;> exact ⟨t, ht, rfl⟩

theorem tendsto_dyadic_rate (F : Type*) [Field F] (m : ℕ) :
    Filter.Tendsto
      (fun t : ℕ => Real.log (exactRank F m (2 ^ t) : ℝ) / (Real.log 2 * (t : ℝ)))
      Filter.atTop (nhds (exponent F m)) := by
  let u (t : ℕ) : ℝ := Real.logb 2 (exactRank F m (2 ^ t) : ℝ)
  have hp (t : ℕ) : 0 < (exactRank F m (2 ^ t) : ℝ) := by
    exact_mod_cast (exactRank_pos F m (pow_pos (by decide : 0 < 2) t))
  have hu : Subadditive u := by
    intro i j
    calc
      _ ≤ Real.logb 2 ((exactRank F m (2 ^ i) : ℝ) * (exactRank F m (2 ^ j) : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (hp _)
        rw [pow_add]
        exact_mod_cast exactRank_submultiplicative F m (2 ^ i) (2 ^ j)
      _ = _ := Real.logb_mul (hp i).ne' (hp j).ne'
  have he : (fun t : ℕ => u t / (t : ℝ)) = dyadicRate F m := by
    funext t
    simp [u, dyadicRate, Real.logb, div_div]
  have hb : BddBelow (Set.range fun t : ℕ => u t / (t : ℝ)) := he ▸ dyadicRate_bddBelow F m
  have h := hu.tendsto_lim hb
  unfold Subadditive.lim at h
  rw [he, ← exponent_eq_sInf_image] at h
  exact h

private theorem dyadicRate_le_iff_power (F : Type*) [Field F] {m k t : ℕ}
    (hm : 3 ≤ m) (hk : 0 < k) (ht : 0 < t) :
    dyadicRate F m t ≤ ((A m : ℝ) * k + 1) / ((D m : ℝ) * k) ↔
      exactRank F m (2 ^ t) ^ (D m * k) ≤ 2 ^ ((A m * k + 1) * t) := by
  let r := exactRank F m (2 ^ t)
  have hr : 0 < (r : ℝ) := by exact_mod_cast (exactRank_pos F m (pow_pos (by decide : 0 < 2) t))
  have hd : 0 < (D m : ℝ) := by exact_mod_cast (show 0 < D m by unfold D; omega)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have cast_iff : (r : ℝ) ^ (D m * k) ≤ (2 : ℝ) ^ ((A m * k + 1) * t) ↔
      r ^ (D m * k) ≤ (2 : ℕ) ^ ((A m * k + 1) * t) := by norm_cast
  change Real.log (r : ℝ) / (Real.log 2 * (t : ℝ)) ≤ _ ↔ r ^ _ ≤ _
  rw [← cast_iff, ← Real.log_le_log_iff (x := (r : ℝ) ^ (D m * k))
    (y := (2 : ℝ) ^ ((A m * k + 1) * t)) (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow, div_le_div_iff₀ (mul_pos h₂ ht') (mul_pos hd hk')]
  push_cast
  constructor <;> intro h <;> linarith only [h]

private theorem divided_threshold {m k : ℕ} (hm : 3 ≤ m) (hk : 0 < k) :
    ((A m : ℝ) * k + 1) / ((D m : ℝ) * k) =
      (A m : ℝ) / (D m : ℝ) + 1 / ((D m : ℝ) * k) := by
  have hd : 0 < (D m : ℝ) := by exact_mod_cast (show 0 < D m by unfold D; omega)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hd.ne', hk']

/-- The packet's arbitrary-precision integer witnesses characterize the
exponent upper bound. The positivity of its denominator requires m ≥ 3. -/
theorem integerUpper_iff_exponent_le (F : Type*) [Field F] (m : ℕ) (hm : 3 ≤ m) :
    IntegerUpper F m ↔ exponent F m ≤ (A m : ℝ) / (D m : ℝ) := by
  have hd₁ : 1 ≤ (D m : ℝ) := by exact_mod_cast (show 1 ≤ D m by unfold D; omega)
  have hd : 0 < (D m : ℝ) := zero_lt_one.trans_le hd₁
  have hb : BddBelow (dyadicRate F m '' Set.Ici 1) :=
    (dyadicRate_bddBelow F m).mono (Set.image_subset_range _ _)
  have hn : (dyadicRate F m '' Set.Ici 1).Nonempty :=
    ⟨dyadicRate F m 1, 1, by simp, rfl⟩
  constructor
  · intro hUpper
    by_contra! hgap
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hgap)
    let k := j + 1
    have hk : 0 < k := Nat.succ_pos j
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have herr : 1 / ((D m : ℝ) * k) ≤ 1 / (k : ℝ) :=
      one_div_le_one_div_of_le hk' (le_mul_of_one_le_left hk'.le hd₁)
    have hj' : 1 / (k : ℝ) < exponent F m - (A m : ℝ) / (D m : ℝ) := by
      simpa [k] using hj
    obtain ⟨t, ht, r, hdec, hpow⟩ := hUpper k hk
    have hp := (Nat.pow_le_pow_left (exactRank_le_of_decomposition hdec) (D m * k)).trans hpow
    have hrate := (dyadicRate_le_iff_power F hm hk ht).mpr hp
    have hinf : exponent F m ≤ dyadicRate F m t := by
      rw [exponent_eq_sInf_image]
      exact csInf_le hb ⟨t, ht, rfl⟩
    rw [divided_threshold hm hk] at hrate
    linarith
  · intro hUpper k hk
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hslack : exponent F m < ((A m : ℝ) * k + 1) / ((D m : ℝ) * k) := by
      rw [divided_threshold hm hk]
      exact hUpper.trans_lt (lt_add_of_pos_right _ (by positivity))
    rw [exponent_eq_sInf_image] at hslack
    obtain ⟨_, ⟨t, ht, rfl⟩, hrate⟩ := exists_lt_of_csInf_lt hn hslack
    exact ⟨t, ht, _, exactRank_attained F m _, (dyadicRate_le_iff_power F hm hk ht).mp hrate.le⟩

/-- Every finite original-slot decomposition at an arbitrary side bounds the
dyadic exponent. Round down only after taking an arbitrarily large power. -/
theorem exponent_le_of_decomposition {F : Type*} [Field F] {m n r : ℕ}
    (hn : 2 ≤ n) (hd : HasDecomposition F m n r) :
    exponent F m ≤ Real.log (r : ℝ) / Real.log (n : ℝ) := by
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₀ : 0 ≤ exponent F m := by
    rw [exponent_eq_sInf_image]
    apply le_csInf (s := dyadicRate F m '' Set.Ici 1) ⟨dyadicRate F m 1, 1, by simp, rfl⟩
    rintro _ ⟨t, _, rfl⟩
    have h : 1 ≤ (exactRank F m (2 ^ t) : ℝ) := by
      exact_mod_cast exactRank_pos F m (pow_pos (by decide : 0 < 2) t)
    exact div_nonneg (Real.log_nonneg h) (mul_nonneg hlog₂.le t.cast_nonneg)
  apply (le_div_iff₀ hlogn).mpr
  by_contra! hgap
  have hgap' := sub_pos.mpr hgap
  obtain ⟨j, hj⟩ := exists_nat_gt
    (exponent F m * Real.log 2 / (exponent F m * Real.log (n : ℝ) - Real.log (r : ℝ)))
  have hjpos : 0 < j := by
    exact_mod_cast lt_of_le_of_lt (div_nonneg (mul_nonneg h₀ hlog₂.le) hgap'.le) hj
  let t := Nat.log 2 (n ^ j)
  have ht : 0 < t := hjpos.trans_le (Nat.le_log_of_pow_le (by decide : 1 < 2)
    (Nat.pow_le_pow_left hn j))
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hbound : exponent F m * (Real.log 2 * (t : ℝ)) ≤ Real.log (exactRank F m (2 ^ t) : ℝ) := by
    apply (le_div_iff₀ (mul_pos hlog₂ ht')).mp
    rw [exponent_eq_sInf_image]
    apply csInf_le ((dyadicRate_bddBelow F m).mono (Set.image_subset_range _ _))
    exact ⟨t, ht, rfl⟩
  have hcut : 2 ^ t ≤ n ^ j := Nat.pow_log_le_self 2 (pow_ne_zero j (by omega))
  have hR := exactRank_le_of_decomposition (hasDecomposition_restrict hcut (hasDecomposition_pow hd j))
  have hRlog : Real.log (exactRank F m (2 ^ t) : ℝ) ≤ (j : ℝ) * Real.log (r : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast exactRank_pos F m (pow_pos (by decide : 0 < 2) t)
    · exact_mod_cast hR
  have hpad : n ^ j ≤ 2 ^ (t + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
  have hdimlog : (j : ℝ) * Real.log (n : ℝ) ≤ ((t : ℝ) + 1) * Real.log 2 := by
    have hp : (0 : ℝ) < (n : ℝ) ^ j := pow_pos (by exact_mod_cast (show 0 < n by omega)) _
    have h := Real.log_le_log hp (show (n : ℝ) ^ j ≤ (2 : ℝ) ^ (t + 1) by exact_mod_cast hpad)
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h
  have hj' := (div_lt_iff₀ hgap').mp hj
  nlinarith only [hbound, hRlog, mul_le_mul_of_nonneg_left hdimlog h₀, hj']

end OddCycleTarget
