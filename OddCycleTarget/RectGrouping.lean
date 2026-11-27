import OddCycleTarget

/-! Group an odd cycle into the three matrix factors, preserving every coefficient. -/
namespace OddCycleTarget

open scoped BigOperators

/-- The coefficient identity in the row, inner, column convention of
`OAI.LinearAlgebra.MatrixExponent.Rectangle.RankLE F a b c r`. -/
def RectangleDecomposition (F : Type*) [Field F] (a b c r : ℕ) : Prop :=
  ∃ (u : Fin r → Fin a × Fin c → F) (v : Fin r → Fin c × Fin b → F)
    (w : Fin r → Fin a × Fin b → F),
    ∀ x y z, ∑ s, u s x * v s y * w s z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

private theorem next_castSucc {k : ℕ} (i : Fin k) :
    nextSite i.castSucc = i.succ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)

private theorem next_last (k : ℕ) : nextSite (Fin.last k) = 0 := by
  apply Fin.ext
  exact Nat.mod_self _

/-- At a path vertex, the two incident labels come from the internal
edge word, with the supplied endpoint label used at either end. -/
private def pathPair {q n : ℕ} (w : Fin q → Fin n) (endLabel : Fin n)
    (i : Fin (q + 1)) : IndexPair n :=
  (if h : 0 < i.val then w ⟨i.val - 1, by have := i.isLt; omega⟩ else endLabel,
   if h : i.val < q then w ⟨i.val, h⟩ else endLabel)

private def cycleTuple {q n : ℕ} (a b : Fin q → Fin n) (l r : Fin n)
    (y : IndexPair n) : Fin (q + 2) → IndexPair n :=
  Fin.lastCases (y.2, y.1) fun i =>
    if i.val % 2 = 0 then pathPair a l i else pathPair b r i

private theorem internal_edge {q n : ℕ} (a b : Fin q → Fin n) (l r : Fin n)
    (y : IndexPair n) (i : Fin q) :
    let p := cycleTuple a b l r y
    (p i.castSucc.castSucc).2 = (p (nextSite i.castSucc.castSucc)).1 ↔ a i = b i := by
  dsimp only
  rw [next_castSucc, show i.castSucc.succ = i.succ.castSucc by rfl]
  simp only [cycleTuple, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_succ]
  by_cases h : i.val % 2 = 0
  · have hs : (i.val + 1) % 2 ≠ 0 := by omega
    rw [if_pos h, if_neg hs]
    simp [pathPair, i.isLt]
  · have hs : (i.val + 1) % 2 = 0 := by omega
    rw [if_neg h, if_pos hs]
    simpa [pathPair, i.isLt] using (eq_comm (a := b i) (b := a i))

private theorem cycleTuple_compatible {q n : ℕ} (hq : q % 2 = 1)
    (a b : Fin q → Fin n) (l r : Fin n) (y : IndexPair n) :
    let p := cycleTuple a b l r y
    (∀ j, (p j).2 = (p (nextSite j)).1) ↔ a = b ∧ l = y.1 ∧ y.2 = r := by
  let p := cycleTuple a b l r y
  have hwrap : (p (Fin.last (q + 1))).2 = (p (nextSite (Fin.last (q + 1)))).1 ↔
      l = y.1 := by
    rw [next_last, show (0 : Fin (q + 2)) = (0 : Fin (q + 1)).castSucc by rfl]
    simp only [p, cycleTuple, Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_zero]
    simp [pathPair, eq_comm]
  have hend : (p (Fin.last q).castSucc).2 = (p (nextSite (Fin.last q).castSucc)).1 ↔
      y.2 = r := by
    rw [next_castSucc, show (Fin.last q).succ = Fin.last (q + 1) by rfl]
    simp [p, cycleTuple, pathPair, hq, eq_comm]
  change (∀ j : Fin (q + 2), (p j).2 = (p (nextSite j)).1) ↔ _
  rw [Fin.forall_fin_succ', Fin.forall_fin_succ', hwrap, hend]
  simp only [p, internal_edge]
  constructor
  · rintro ⟨⟨h, he⟩, hw⟩
    exact ⟨funext h, hw, he⟩
  · rintro ⟨rfl, hw, he⟩
    exact ⟨⟨fun _ => rfl, he⟩, hw⟩

private theorem group_path {F : Type*} [Field F] {q n r : ℕ}
    (hq : q % 2 = 1) (d : HasDecomposition F (q + 2) n r) :
    RectangleDecomposition F (n ^ q) n n r := by
  classical
  obtain ⟨u, hu⟩ := d
  let e : Fin (n ^ q) ≃ (Fin q → Fin n) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin q → Fin n) = n ^ q)).symm
  let part (s : Fin r) (x : Fin (n ^ q) × Fin n) (i : Fin (q + 1)) :=
    u s i.castSucc (pathPair (e x.1) x.2 i)
  refine ⟨fun s x => ∏ i, if i.val % 2 = 0 then part s x i else 1,
    fun s y => u s (Fin.last (q + 1)) (y.2, y.1),
    fun s z => ∏ i, if i.val % 2 = 0 then 1 else part s z i, ?_⟩
  intro x y z
  let p := cycleTuple (e x.1) (e z.1) x.2 z.2 y
  have hcond : (∀ j, (p j).2 = (p (nextSite j)).1) ↔
      x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 := by
    simpa only [p, e.injective.eq_iff] using
      cycleTuple_compatible hq (e x.1) (e z.1) x.2 z.2 y
  have hc : coeff F (q + 2) n p =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0 := by
    simp only [coeff, hcond]
  rw [← hc, hu p]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_right_comm _ (u s (Fin.last (q + 1)) _), ← Finset.prod_mul_distrib,
    Fin.prod_univ_castSucc (fun j : Fin (q + 2) => u s j (p j))]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    by_cases h : i.val % 2 = 0 <;> simp [part, p, cycleTuple, h]
  · simp [p, cycleTuple]

/-- The q=m−2 internal edges of the alternating path form one packed matrix
index. Both remaining edges carry a single label. -/
theorem groupOddRectangle {F : Type*} [Field F] {m n r : ℕ}
    (hm : 3 ≤ m) (hodd : Odd m) (d : HasDecomposition F m n r) :
    ∃ (u : Fin r → Fin (n ^ (m - 2)) × Fin n → F) (v : Fin r → Fin n × Fin n → F)
      (w : Fin r → Fin (n ^ (m - 2)) × Fin n → F),
      ∀ x y z, ∑ s, u s x * v s y * w s z =
        if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0 := by
  let q := m - 2
  have he : m = q + 2 := by dsimp [q]; omega
  have hq : q % 2 = 1 := by obtain ⟨k, hk⟩ := hodd; omega
  exact group_path hq (he ▸ d : HasDecomposition F (q + 2) n r)

end OddCycleTarget
