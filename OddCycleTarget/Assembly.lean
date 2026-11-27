import OddCycleTarget.CliqueMass
import OddCycleTarget.SpectrumGeometry

namespace OddCycleTarget
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Fin.NatCast Fin.CommRing

/-- Assemble the packet's exact integer witnesses from the numerical
complete-graph rank bound and the real odd-cycle Ptolemy/mass inequality. -/
theorem integerUpper_of_clique_and_perimeter (F : Type*) [Field F] (m : ℕ) [NeZero m]
    (hm : 3 ≤ m)
    (clique : ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      Real.logb 2 (asymptoticRank (Spectrum.binaryClique F n)) ≤ (n : ℝ)^2 / 4)
    (perimeter : ∀ d : Fin m → Fin m → ℝ,
      (∀ i, d i i = 0) → (∀ i j, d i j = d j i) → (∀ i j, 0 ≤ d i j) →
      (∀ i j k, d i k ≤ d i j + d j k) →
      (∀ i j k l, d i j * d k l ≤ d i k * d j l + d i l * d j k) →
      (∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        2 * (∑ i, ∑ j, w i * w j * d i j) ≤ (∑ i, w i)^2) →
      4 * ((m : ℝ) - 2) * (∑ i, d i (i + 1)) ≤ (2 * (m : ℝ) - 3)^2) :
    IntegerUpper F m := by
  apply Spectrum.integerUpper_of_mass_geometry F m hm
  · exact fun φ w hw => Spectrum.real_mass_of_clique_upper F clique φ w hw
  · intro d hzero hsym h01 htri hpt hmass
    have h := perimeter d hzero hsym (fun i j => (h01 i j).1) htri
      (fun i j k l => (hpt i k j l).trans_eq (by rw [hsym k j])) hmass
    have hnext (i : Fin m) : nextSite i = i + 1 := by
      apply Fin.ext
      change (i.val + 1) % m = (i.val + 1 % m) % m
      simp
    have hm2 : 2 ≤ m := by omega
    have hm3 : 3 ≤ 2 * m := by omega
    have hD : (D m : ℝ) = 4 * ((m : ℝ) - 2) := by simp [D, Nat.cast_sub hm2]
    have hA : (A m : ℝ) = (2 * (m : ℝ) - 3)^2 := by simp [A, Nat.cast_sub hm3]
    have hpos : 0 < (D m : ℝ) := by exact_mod_cast (show 0 < D m by unfold D; omega)
    apply (le_div_iff₀ hpos).mpr
    simp_rw [hnext, hA, hD]
    linarith only [h]

end OddCycleTarget
