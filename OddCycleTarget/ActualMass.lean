import OddCycleTarget.CliqueRankBridge

namespace OddCycleTarget.Spectrum
open OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators

/-- Zhou's all-mass inequality on actual normalized wire prices. Each
unordered pair appears twice in the ordered double sum. -/
theorem actual_spectral_mass (F : Type*) [Field F] (m : ℕ) [NeZero m] (_hm : 2 ≤ m)
    (φ : Point F m) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) :
    2 * (∑ i, ∑ j, w i * w j * rawWireDistance φ 1 i j) ≤ (∑ i, w i)^2 :=
  real_mass_of_clique_upper F (binaryClique_logrank_le F) φ w hw

end OddCycleTarget.Spectrum
