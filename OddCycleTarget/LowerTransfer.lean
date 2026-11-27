import OddCycleTarget.RankBridge

/-! Transfer sharp finite lower bounds to and from the packet's dyadic infimum. -/
namespace OddCycleTarget

/-- At any number of sites with positive D, a lower bound for all finite
witnesses is equivalent to the same lower bound on the dyadic exponent. -/
theorem allSidesLower_iff_exponent (F : Type*) [Field F] (m : ℕ) (hm : 3 ≤ m) :
    (∀ n r : ℕ, 2 ≤ n → HasDecomposition F m n r → n ^ A m ≤ r ^ D m) ↔
      (A m : ℝ) / (D m : ℝ) ≤ exponent F m := by
  have hD : 0 < (D m : ℝ) := by exact_mod_cast (show 0 < D m by unfold D; omega)
  constructor
  · intro hall
    unfold exponent
    apply le_csInf
    · exact ⟨_, 1, by decide, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
    have hn : 2 ≤ 2 ^ t := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ t from ht)
    let r := exactRank F m (2 ^ t)
    have hpow := hall _ _ hn (exactRank_attained F m (2 ^ t))
    have hc : ((2 : ℝ) ^ t) ^ (A m) ≤ (r : ℝ) ^ (D m) := by exact_mod_cast hpow
    have hlog := Real.log_le_log (by positivity) hc
    rw [Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    apply (div_le_div_iff₀ hD (mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) ht')).mpr
    change _ ≤ Real.log (r : ℝ) * _
    linarith only [hlog]
  · intro hexp n r hn hdec
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hr : 0 < (r : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (exactRank_pos F m (by omega : 0 < n))
        (exactRank_le_of_decomposition hdec))
    have hl := hexp.trans (exponent_le_of_decomposition hn hdec)
    have hl' := (div_le_div_iff₀ hD (Real.log_pos (by exact_mod_cast hn))).mp hl
    have hc : (n : ℝ) ^ (A m) ≤ (r : ℝ) ^ (D m) := by
      apply (Real.log_le_log_iff (pow_pos hn' _) (pow_pos hr _)).mp
      rw [Real.log_pow, Real.log_pow]
      linarith only [hl']
    exact_mod_cast hc

end OddCycleTarget
