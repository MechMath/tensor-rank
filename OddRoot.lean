import OddCycleTarget.CliqueRankBridge
import OddCycleTarget.SharpPerimeter
import OddCycleTarget.SpectrumGeometry

namespace OddCycleTarget
universe u

/-- Complete-graph upper bound in the original OAI restriction classes. -/
theorem binaryClique_upper_step (F : Type*) [Field F] (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Real.logb 2 (OAI.LinearAlgebra.SpectralBooks.SiteTensor.asymptoticRank
      (Spectrum.binaryClique F n)) ≤ (n : ℝ)^2 / 4 :=
  Spectrum.binaryClique_logrank_le F n hn

/-- Exact dyadic decompositions over the original field, on all labelled sites. -/
theorem odd_upper_all : UniversalIntegerUpper.{u} := by
  intro F _ m hm ho
  let _ : NeZero m := ⟨by omega⟩
  apply Spectrum.integerUpper_of_mass_geometry F m hm
  · exact fun φ w hw => Spectrum.real_mass_of_clique_upper F (binaryClique_upper_step F) φ w hw
  · intro d hzero hsym hunit htri hpt hmass
    exact sharp_perimeter m hm ho d hzero hsym (fun i j => (hunit i j).1) htri hpt hmass

end OddCycleTarget
