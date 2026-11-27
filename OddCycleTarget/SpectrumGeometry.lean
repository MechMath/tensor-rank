import OddCycleTarget.SpectrumBridge
import OddCycleTarget.C5Target.C5Curvature
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.Theorem
import OddCycleTarget.C5Target.OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace

/-! The same maximizing point controls the cyclic score, Ptolemy and all
mass inequalities. Zhou's all-mass theorem is an explicit parameter in the
last implication. The Ptolemy realization is unconditional. -/
namespace OddCycleTarget.Spectrum

open OAI OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open HyperbolicObstruction
open scoped BigOperators

theorem actual_wire_ptolemy {F : Type*} [Field F] {m : ℕ} [NeZero m]
    (φ : Point F m) (i j k l : Fin m) :
    rawWireDistance φ 1 i k * rawWireDistance φ 1 j l ≤
      rawWireDistance φ 1 i j * rawWireDistance φ 1 k l +
      rawWireDistance φ 1 i l * rawWireDistance φ 1 j k := by
  obtain ⟨X, metricX, P, x, _, hd, _⟩ := exists_metric_price_realization φ 1 (by norm_num)
  let := metricX
  obtain ⟨Y, metricY, Q, ⟨f⟩, _, hY⟩ := P.exists_complete_catZero_extension
  let := metricY
  have h := FiveCertificate.ptolemyOfCN (CATZero.segment hY) (fun p q r t ht => by
      simpa only [dist_comm] using CATZero.segment_cn hY p q r ht)
    (f.map (x i)) (f.map (x j)) (f.map (x k)) (f.map (x l))
  simp only [f.isometry.dist_eq, hd] at h
  rwa [rawWireDistance_symm φ 1 l i] at h

/-- In the packet language, the exponent has a maximizing Ptolemy
pseudometric with values in [0,1]. Its witness is an actual spectral point's
table; the existential projection forgets that point. -/
theorem exists_maximizing_ptolemy_table (F : Type*) [Field F] (m : ℕ) (hm : 2 ≤ m) :
    ∃ d : Fin m → Fin m → ℝ, (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧
      (∀ i j, 0 ≤ d i j ∧ d i j ≤ 1) ∧ (∀ i j k, d i k ≤ d i j + d j k) ∧
      (∀ i j k l, d i k * d j l ≤ d i j * d k l + d i l * d j k) ∧
      exponent F m = ∑ i : Fin m, d i (nextSite i) := by
  let _ : NeZero m := ⟨by omega⟩
  obtain ⟨φ, hmax⟩ := (spectralMaximum F m hm).1
  refine ⟨rawWireDistance φ 1, rawWireDistance_self φ 1 (by norm_num), rawWireDistance_symm φ 1,
      ?_, rawWireDistance_triangle φ 1 (by norm_num), actual_wire_ptolemy φ, hmax.symm⟩
  intro i j
  exact ⟨rawLogPrice_nonneg φ (by norm_num) _, wire_le_one φ i j⟩

/-- Zhou's ordered all-mass inequality on actual points and a finite
Ptolemy-and-mass geometric bound suffice for exact dyadic witnesses. -/
theorem integerUpper_of_mass_geometry (F : Type*) [Field F] (m : ℕ) [NeZero m] (hm : 3 ≤ m)
    (hZhou : ∀ (φ : Point F m) (w : Fin m → ℝ), (∀ i, 0 ≤ w i) →
      2 * (∑ i, ∑ j, w i * w j * rawWireDistance φ 1 i j) ≤ (∑ i, w i) ^ 2)
    (hGeom : ∀ (d : Fin m → Fin m → ℝ), (∀ i, d i i = 0) → (∀ i j, d i j = d j i) →
      (∀ i j, 0 ≤ d i j ∧ d i j ≤ 1) → (∀ i j k, d i k ≤ d i j + d j k) →
      (∀ i j k l, d i k * d j l ≤ d i j * d k l + d i l * d j k) →
      (∀ (w : Fin m → ℝ), (∀ i, 0 ≤ w i) →
        2 * (∑ i, ∑ j, w i * w j * d i j) ≤ (∑ i, w i) ^ 2) →
      (∑ i, d i (nextSite i)) ≤ (A m : ℝ) / (D m : ℝ)) :
    IntegerUpper F m := by
  apply (integerUpper_iff_all_prices F m hm).mpr
  intro φ
  exact hGeom (rawWireDistance φ 1) (rawWireDistance_self φ 1 (by norm_num))
    (rawWireDistance_symm φ 1) (fun i j => ⟨rawLogPrice_nonneg φ (by norm_num) _, wire_le_one φ i j⟩)
    (rawWireDistance_triangle φ 1 (by norm_num)) (actual_wire_ptolemy φ) (hZhou φ)

end OddCycleTarget.Spectrum
