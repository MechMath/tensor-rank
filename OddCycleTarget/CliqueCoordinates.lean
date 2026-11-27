import OddCycleTarget.SpectrumBridge
import OddCycleTarget.Lemmata.TensorRank.Proof.GraphRank

/-! Identification of complete-graph tensors in the Lemmata coordinate model and
the OAI restriction semiring. All maps act separately on the original vertex legs. -/
namespace OddCycleTarget.CliqueCoordinates

open OAI.LinearAlgebra.SpectralBooks SiteTensor
open Lemmata.TensorRank
open scoped BigOperators

noncomputable section

/-- The same coordinate array, considered as an OAI raw tensor. -/
def raw {I : Type} {V : I → Type} (F : Type*) [Field F] [∀ i, Fintype (V i)]
    (T : Lemmata.TensorRank.Tensor F I V) : Raw.{0} I F := ⟨V, inferInstance, T⟩

/-- Weighted CP summands and restrictions of a diagonal have the same rank.
A single distinguished party absorbs the coefficient of each weighted summand. -/
theorem rank_eq {I : Type} [Fintype I] [Nonempty I] {V : I → Type} [∀ i, Fintype (V i)]
    (F : Type*) [Field F] (T : Lemmata.TensorRank.Tensor F I V) :
    rank (ofRaw (raw F T)) = Lemmata.TensorRank.Tensor.rank T := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have iff (r : ℕ) : ofRaw (raw F T) ≤ (r : TensorClass.{0} I F) ↔
      Lemmata.TensorRank.Tensor.RankLE T r := by
    rw [← ofRaw_diagonal_fin_eq_natCast I F r, ofRaw_le_iff]
    have relative : (raw F T).Restricts (Raw.diagonal I F (Fin r)) ↔
        Crossing.IsRestriction (A := fun _ : I => Fin r) (B := V) T
          (Crossing.basisTensor (fun (s : Fin r) (_ : I) => s)) := by
      unfold Raw.Restricts raw Raw.diagonal Crossing.basisTensor Crossing.IsRestriction
      dsimp
      congr! 7
      split <;> simp_all
    rw [relative, Crossing.restriction_basisTensor_iff]
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨fun _ => 1, fun s i v => M i v s, ?_⟩
      funext v
      simpa only [one_mul, Tensor.pure_apply] using hM v
    · rintro ⟨c, v, hc⟩
      refine ⟨fun i u s => (if i = i₀ then c s else 1) * v s i u, ?_⟩
      intro u
      simpa only [Tensor.pure_apply, Finset.prod_mul_distrib, Finset.prod_ite_eq',
        Finset.mem_univ, ite_true] using congrFun hc u
  exact le_antisymm
    (rank_le_of_le ((iff _).mpr (Tensor.rankLE_rank T)))
    ((Tensor.rank_le_iff _ _).mpr ((iff _).mp (le_rank _)))

private abbrev Edge (n : ℕ) := (i : Fin n) × {j : Fin n // i < j}

private def graph (n : ℕ) : PortGraph (Fin n) (Edge n) := ⟨fun e => e.1, fun e => e.2.1⟩

private def neighbor {n : ℕ} {i : Fin n} : (graph n).Port i → Neighbors i
  | ⟨(⟨a, ⟨b, h⟩⟩, false), hi⟩ => ⟨b, by change a = i at hi; simpa [← hi] using h.ne'⟩
  | ⟨(⟨a, ⟨b, h⟩⟩, true), hi⟩ => ⟨a, by change b = i at hi; simpa [← hi] using h.ne⟩

private def port {n : ℕ} (i : Fin n) (j : Neighbors i) : (graph n).Port i :=
  if h : i < j.1 then ⟨(⟨i, ⟨j.1, h⟩⟩, false), rfl⟩
  else ⟨(⟨j.1, ⟨i, lt_of_le_of_ne (le_of_not_gt h) j.2⟩⟩, true), rfl⟩

/-- Each incident port remembers exactly the other endpoint of the edge. -/
private def portEquiv {n : ℕ} (i : Fin n) : (graph n).Port i ≃ Neighbors i where
  toFun := neighbor
  invFun := port i
  left_inv := by
    rintro ⟨⟨⟨a, ⟨b, hab⟩⟩, t⟩, hit⟩
    cases t with
    | false =>
      change a = i at hit
      subst i
      simp [neighbor, port, hab]
    | true =>
      change b = i at hit
      subst i
      simp [neighbor, port, not_lt_of_ge hab.le]
  right_inv := by
    rintro ⟨j, hj⟩
    by_cases h : i < j <;> simp [port, neighbor, h]

private def stateEquiv (n d : ℕ) (i : Fin n) :
    GraphCoordinate n d i ≃ (graph n).State (fun _ => Fin d) i :=
  Equiv.arrowCongr (portEquiv i).symm (Equiv.refl _)

/-- One independent d-symbol wire for each unordered pair i<j. -/
def product (F : Type*) [Field F] (n : ℕ) [NeZero n] (d : ℕ) : TensorClass.{0} (Fin n) F :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ofRaw ((Raw.diagonal (Fin 2) F (Fin d)).group ![i,j])

theorem class_eq_product (F : Type*) [Field F] (n : ℕ) [NeZero n] (d : ℕ) :
    ofRaw (raw F (completeGraph (𝕜 := F) n d)) = product F n d := by
  classical
  calc
    _ = ofRaw ((graph n).rawWiring F (fun _ => Fin d)) := by
      apply ofRaw_eq_iff.mpr
      apply Raw.reindex_equivalent (fun i => stateEquiv n d i)
      intro x
      let compatible := ∀ (i j : Fin n) (h : i ≠ j), x i ⟨j,h.symm⟩ = x j ⟨i,h⟩
      let wired := ∀ e : Edge n, x e.1 ⟨e.2.1,e.2.2.ne'⟩ = x e.2.1 ⟨e.1,e.2.2.ne⟩
      have hw : compatible ↔ wired := by
        constructor
        · intro h e
          exact h _ _ e.2.2.ne
        · intro h i j hij
          rcases lt_or_gt_of_ne hij with l | l
          · exact h ⟨i, ⟨j, l⟩⟩
          · exact (h ⟨j, ⟨i, l⟩⟩).symm
      have hr : (∀ e : Edge n,
          stateEquiv n d ((graph n).tail e) (x _) ⟨(e,false),rfl⟩ =
            stateEquiv n d ((graph n).head e) (x _) ⟨(e,true),rfl⟩) ↔ wired := by
        apply forall_congr'
        rintro ⟨i, ⟨j, hij⟩⟩
        rfl
      dsimp only [raw, completeGraph, PortGraph.rawWiring, PortGraph.wiring]
      by_cases hc : compatible
      · rw [ite_eq_left hc]
        split
        · rfl
        · rename_i hbad
          exact (hbad (hr.mpr (hw.mp hc))).elim
      · rw [ite_eq_right hc]
        split
        · rename_i hgood
          exact (hc (hw.mpr (hr.mp hgood))).elim
        · rfl
    _ = _ := by
      rw [PortGraph.ofRaw_rawWiring, Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_subtype (Finset.Ioi i) (fun j => Finset.mem_Ioi)
        (fun j => ofRaw ((Raw.diagonal (Fin 2) F (Fin d)).group ![i,j]))).symm

theorem product_pow (F : Type*) [Field F] (n : ℕ) [NeZero n] (d q : ℕ) :
    product F n (d^q) = product F n d ^ q := by
  unfold product
  simp_rw [ofRaw_group_diagonal_fin_pow F _ d q]
  simp only [Finset.prod_pow]

theorem asymptoticRank_eq (F : Type*) [Field F] (n : ℕ) [NeZero n] (d : ℕ) :
    SiteTensor.asymptoticRank (product F n d) = Tensor.asymptoticRank (completeGraph (𝕜 := F) n d) := by
  unfold SiteTensor.asymptoticRank Tensor.asymptoticRank Tensor.rankRoot
  apply iInf_congr
  intro q
  rw [← product_pow, ← class_eq_product, rank_eq, rank_completeGraph_power]

end
end OddCycleTarget.CliqueCoordinates
