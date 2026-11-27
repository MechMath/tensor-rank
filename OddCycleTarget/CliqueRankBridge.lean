import OddCycleTarget.CliqueCoordinates
import OddCycleTarget.CliqueMass
import OddCycleTarget.Lemmata.TensorRank.Main

/-! The complete-graph rank bound on the original OAI tensor-class model. -/
namespace OddCycleTarget.Spectrum

open OAI.LinearAlgebra.SpectralBooks SiteTensor

/-- All fields, all binary cliques with at least two original parties. -/
theorem binaryClique_logrank_le (F : Type*) [Field F] (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Real.logb 2 (asymptoticRank (binaryClique F n)) ≤ (n : ℝ)^2 / 4 := by
  change Real.logb 2 (asymptoticRank (CliqueCoordinates.product F n 2)) ≤ _
  rw [CliqueCoordinates.asymptoticRank_eq]
  have h := Lemmata.TensorRank.completeGraphBounds (𝕜 := F) n 2 hn (by decide)
  have hp : 0 < Lemmata.TensorRank.Tensor.asymptoticRank
      (Lemmata.TensorRank.completeGraph (𝕜 := F) n 2) :=
    lt_of_lt_of_le (by positivity) h.1
  exact (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hp).mpr (by simpa using h.2.1)

#print axioms binaryClique_logrank_le

end OddCycleTarget.Spectrum
