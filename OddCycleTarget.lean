import Mathlib

/-! Fin m indexes the original m labelled sites. Equality and IntegerUpper are
research targets; the numerical and logical lemmas below have no such assumption. -/
namespace OddCycleTarget
open scoped BigOperators
universe u
abbrev IndexPair (n : ℕ) := Fin n × Fin n

def nextSite {m : ℕ} (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ (by have hj := j.isLt; omega)⟩

def coeff (F : Type*) [Field F] (m n : ℕ) (x : Fin m → IndexPair n) : F :=
  if ∀ j, (x j).2 = (x (nextSite j)).1 then 1 else 0

def HasDecomposition (F : Type*) [Field F] (m n r : ℕ) : Prop :=
  ∃ u : Fin r → Fin m → IndexPair n → F,
    ∀ x : Fin m → IndexPair n, coeff F m n x = ∑ s, ∏ j, u s j (x j)

noncomputable def exactRank (F : Type*) [Field F] (m n : ℕ) : ℕ :=
  sInf {r : ℕ | HasDecomposition F m n r}

noncomputable def exponent (F : Type*) [Field F] (m : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ t : ℕ, 0 < t ∧
    z = Real.log (exactRank F m (2 ^ t) : ℝ) / (Real.log 2 * (t : ℝ))}

def A (m : ℕ) : ℕ := (2 * m - 3) ^ 2
def D (m : ℕ) : ℕ := 4 * (m - 2)
def Equality (F : Type*) [Field F] (m : ℕ) : Prop :=
  exponent F m = (A m : ℝ) / (D m : ℝ)
def IntegerUpper (F : Type*) [Field F] (m : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ t : ℕ, 0 < t ∧ ∃ r : ℕ,
    HasDecomposition F m (2 ^ t) r ∧ r ^ (D m * k) ≤ 2 ^ ((A m * k + 1) * t)

def UniversalEquality : Prop :=
  ∀ (F : Type u) [Field F] (m : ℕ), 3 ≤ m → Odd m → Equality F m
def UniversalIntegerUpper : Prop :=
  ∀ (F : Type u) [Field F] (m : ℕ), 3 ≤ m → Odd m → IntegerUpper F m

theorem integerUpper_fails_iff (F : Type*) [Field F] (m : ℕ) :
    ¬ IntegerUpper F m ↔
      ∃ k : ℕ, 0 < k ∧ ∀ t : ℕ, 0 < t → ∀ r : ℕ,
        HasDecomposition F m (2 ^ t) r → 2 ^ ((A m * k + 1) * t) < r ^ (D m * k) := by
  classical
  simp only [IntegerUpper, not_forall, not_exists, not_and, not_le, exists_prop]

theorem numerator_identity {m : ℕ} (h : 3 ≤ m) : A m = D m * (m - 1) + 1 := by
  let s := m - 3
  have hm : m = s + 3 := by dsimp [s]; omega
  rw [hm]
  dsimp [A, D]
  rw [show 2 * (s + 3) - 3 = 2 * s + 3 by omega,
      show s + 3 - 2 = s + 1 by omega]
  ring

theorem five_counterexample_refutes_all (F : Type u) [Field F] (h : ¬ Equality F 5) :
    ¬ UniversalEquality.{u} := by
  intro hall
  exact h (hall F 5 (by decide) (by decide))

theorem small_values :
    (A 3, D 3) = (9, 4) ∧ (A 5, D 5) = (49, 12) ∧
    (A 7, D 7) = (121, 20) ∧ (A 9, D 9) = (225, 28) := by decide

#print axioms integerUpper_fails_iff
#print axioms numerator_identity
#print axioms five_counterexample_refutes_all
#print axioms small_values
end OddCycleTarget
