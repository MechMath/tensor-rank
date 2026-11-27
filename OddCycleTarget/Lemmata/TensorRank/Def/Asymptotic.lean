/-
Copyright (c) 2026 Kirill Khoruzhii. Licensed under Apache-2.0.
Modified for the arbitrary-field tensor-rank formalization; namespace and imports
adapted for Lemmata. See docs/tensor-rank/NOTICE.txt for upstream attribution
and modification notices, and docs/tensor-rank/LICENSE.txt for the license.
-/

import OddCycleTarget.Lemmata.TensorRank.Def.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed


set_option autoImplicit false

namespace Lemmata.TensorRank.Tensor

universe u v w

variable {R : Type u} [CommSemiring R] {I : Type v} [Fintype I]
variable {V : I → Type w} [∀ i, Finite (V i)]

noncomputable def rankRoot (T : Tensor R I V) (n : ℕ) : ℝ :=
  (rank (power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

/-- The infimum of ordinary rank roots over all positive Kronecker powers. -/
noncomputable def asymptoticRank (T : Tensor R I V) : ℝ :=
  ⨅ n : ℕ, rankRoot T n

end Lemmata.TensorRank.Tensor
