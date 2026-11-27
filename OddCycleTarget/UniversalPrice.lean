import OddCycleTarget.OffsetSharp
import OddCycleTarget.OddCube

/-! Sharp perimeter for all odd Ptolemy price tables satisfying the Zhou
quadratic tests. The short odd windows are taken in the original cyclic order. -/
namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {m : ℕ} [NeZero m]

theorem offsetTriangle (D : Fin m → Fin m → ℝ)
    (tri : ∀ i j l, D i l ≤ D i j+D j l) (a b : Fin m) :
    R D (a+b) ≤ R D a+R D b := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => tri i (i+a) ((i+a)+b))
  rw [Finset.sum_add_distrib] at hs
  have hshift := sumShift (fun i => D i (i+b)) a
  rw [hshift] at hs
  simpa only [R, add_assoc] using hs

theorem offsetMultiples (D : Fin m → Fin m → ℝ) (diag : ∀ i, D i i=0)
    (tri : ∀ i j l, D i l ≤ D i j+D j l) (j : Fin m) (k : ℕ) :
    R D (k • j) ≤ (k:ℝ)*R D j := by
  induction k with
  | zero => simp [R, diag]
  | succ k ih =>
    rw [succ_nsmul, Nat.cast_succ]
    have h := offsetTriangle D tri (k • j) j
    linarith

private theorem windowEnds (D : Fin m → Fin m → ℝ) (a : Fin m) (n : ℕ) :
    ∑ i : Fin (n+1), D (a+(i.val : Fin m)) (a+(((i+1).val : ℕ) : Fin m)) =
      (∑ t ∈ Finset.range n, D (a+(t : Fin m)) ((a+(t : Fin m))+1))+D (a+(n : Fin m)) a := by
  rw [Fin.sum_univ_castSucc, ← Fin.sum_univ_eq_sum_range]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h : (i.castSucc+1 : Fin (n+1)).val = i.val+1 := by
      rw [Fin.val_add, Fin.val_castSucc, Fin.val_one']
      have hi := i.isLt
      by_cases hn : n=0
      · omega
      · simp [Nat.mod_eq_of_lt (show 1 < n+1 by omega),
          Nat.mod_eq_of_lt (show i.val+1 < n+1 by omega)]
    simp only [Fin.val_castSucc, h, Nat.cast_succ, add_assoc]
  · have h : (Fin.last n+1 : Fin (n+1)) = 0 := by
      ext; simp
    simp [h]

/-- Summing the usual Zhou bound over the m translates of an odd window
gives a lower bound for the last offset of that window. -/
theorem windowLower (D : Fin m → Fin m → ℝ) (l : ℕ) (hl : 0 < l) (odd : Odd l)
    (diag : ∀ i, D i i=0) (symm : ∀ i j, D i j=D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j t, D i t ≤ D i j+D j t)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    (l:ℝ)*((l:ℝ)+1)*R D 1 ≤ (m:ℝ)*(l:ℝ)^2+((l:ℝ)+1)*R D (l:Fin m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  let y := fun i : Fin m => D i (i+1)
  have localBound (a : Fin m) :
      ((n:ℝ)+2)*((∑ t ∈ Finset.range n, y (a+(t:Fin m)))+D a (a+(n:Fin m))) ≤ ((n:ℝ)+1)^2 := by
    have z := pulledOddWindowUpper D (fun i : Fin (n+1) => a+(i.val : Fin m))
      odd diag symm hn tri zhou
    rw [windowEnds D a n, symm (a+(n:Fin m)) a] at z
    simpa only [Nat.cast_add, Nat.cast_one, y, add_assoc, one_add_one_eq_two] using z
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => localBound a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at H
  have inner : (∑ a : Fin m, ∑ t ∈ Finset.range n, y (a+(t:Fin m))) = (n:ℝ)*R D 1 := by
    rw [Finset.sum_comm]
    calc (∑ t ∈ Finset.range n, ∑ a, y (a+(t:Fin m))) = ∑ _t ∈ Finset.range n, ∑ a, y a :=
           Finset.sum_congr rfl (fun t _ => sumShift y (t:Fin m))
         _ = _ := by simp [nsmul_eq_mul, R, y]
  rw [inner] at H
  change ((n:ℝ)+2)*((n:ℝ)*R D 1+R D (n:Fin m)) ≤ (m:ℝ)*((n:ℝ)+1)^2 at H
  have tr := offsetTriangle D tri (((n+1:ℕ):Fin m)) (-(n:Fin m))
  rw [reflected D symm] at tr
  have one : ((n+1:ℕ):Fin m)+(- (n:Fin m)) = 1 := by rw [Nat.cast_succ]; abel
  rw [one] at tr
  have rt := mul_le_mul_of_nonneg_left tr (show 0 ≤ (n:ℝ)+2 by positivity)
  simp only [Nat.cast_succ] at *
  nlinarith

/-- Under a score exceeding m-1, every nonzero directed offset has price
greater than 2, including when its step is not a generator. -/
theorem everyOffsetLarge (D : Fin m → Fin m → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (size : m=2*k+1) (diag : ∀ i, D i i=0) (symm : ∀ i j, D i j=D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j t, D i t ≤ D i j+D j t)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2)
    (high : (m:ℝ)-1 < R D 1) (j : Fin m) (hj : j ≠ 0) : 2 < R D j := by
  have hmR : (m:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast size
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have high' : 2*(k:ℝ) < R D 1 := by linarith
  have rev (l : ℕ) (small : l ≤ m) : ((m-l:ℕ):Fin m) = -(l:Fin m) := by
    rw [Nat.cast_sub small, Fin.natCast_self, zero_sub]
  have oddCase (l : ℕ) (odd : Odd l) (lt : l < m) : 2 < R D (l:Fin m) := by
    obtain ⟨t, ht⟩ := odd
    by_cases first : l=1
    · rw [first, Nat.cast_one]; linarith
    by_cases last : l=m-2
    · have hstep := offsetMultiples D diag tri (2:Fin m) k
      have ck : k • (2:Fin m) = -1 := by
        rw [nsmul_eq_mul, mul_comm, ← Nat.cast_ofNat (R:=Fin m) (n:=2), ← Nat.cast_mul]
        have he : 2*k=m-1 := by omega
        rw [he, rev 1 (by omega), Nat.cast_one]
      rw [ck, reflected D symm] at hstep
      rw [last, rev 2 (by omega), reflected D symm, Nat.cast_ofNat]
      by_contra! q
      nlinarith [mul_le_mul_of_nonneg_left q (Nat.cast_nonneg k : (0:ℝ)≤k)]
    · have h3 : 3 ≤ l := by omega
      have h4 : l+4 ≤ m := by omega
      have h3r : (3:ℝ) ≤ l := by exact_mod_cast h3
      have h4r : (l:ℝ)+4 ≤ m := by exact_mod_cast h4
      have z := windowLower D l (by omega) ⟨t, ht⟩ diag symm hn tri zhou
      have hcoef : 0 < (l:ℝ)*((l:ℝ)+1) := by positivity
      have strict := mul_lt_mul_of_pos_left high hcoef
      by_contra! q
      have qu := mul_le_mul_of_nonneg_left q (show 0 ≤ (l:ℝ)+1 by positivity)
      nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)-(l:ℝ)-4 by linarith) (Nat.cast_nonneg l : (0:ℝ)≤l)]
  by_cases hodd : Odd j.val
  · simpa only [Fin.cast_val_eq_self] using oddCase j.val hodd j.isLt
  · have hjv : 0 < j.val := by
      by_contra! h
      apply hj; apply Fin.ext; change j.val = 0; omega
    have ho : Odd (m-j.val) := by
      rw [Nat.odd_iff] at *
      have := j.isLt
      omega
    have H := oddCase (m-j.val) ho (by omega)
    rw [rev j.val j.isLt.le, Fin.cast_val_eq_self, reflected D symm] at H
    exact H

/-- A single Ptolemy price table satisfying the complete family of quadratic
mass inequalities has the rectangular perimeter bound at every odd length. -/
theorem oddSharp (D : Fin m → Fin m → ℝ) (A B : Fin m) {k : ℕ} (hk : 1 ≤ k)
    (size : m=2*k+1) (diag : ∀ i, D i i=0) (symm : ∀ i j, D i j=D j i)
    (hn : ∀ i j, 0 ≤ D i j) (unit : D A B ≤ 1) (diam : ∀ i j, D i j≤D A B)
    (tri : ∀ i j l, D i l ≤ D i j+D j l)
    (pt : ∀ a b c d, D a b*D c d ≤ D a c*D b d+D a d*D b c)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    4*(2*(k:ℝ)-1)*R D 1 ≤ (4*(k:ℝ)-1)^2 := by
  by_cases hk2 : 2 ≤ k
  · apply sharpPriceGeFive D A B hk2 size diag symm hn diam tri pt zhou
    · exact OddCycleCube.transition (by omega)
    · intro high j hj
      have h := everyOffsetLarge D hk2 size diag symm hn tri zhou high j hj
      linarith
  · have h : k=1 := by omega
    subst k
    norm_num at size
    subst m
    norm_num
    exact sharpPriceThree D diag symm zhou

end OddCycleOffset

namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {m : ℕ} [NeZero m]

/-- The two-site Zhou test supplies the unit upper for every price; the
isolated support formula also works when the two marked sites coincide. -/
theorem pairPriceLeOne (D : Fin m → Fin m → ℝ) (A B : Fin m)
    (diag : ∀ i, D i i=0) (symm : ∀ i j, D i j=D j i)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) : D A B ≤ 1 := by
  classical
  let w := fun i : Fin m => (if i=A then (1:ℝ) else 0)+(if i=B then (1:ℝ) else 0)
  have ev (f : Fin m → ℝ) : ∑ i, w i*f i = f A+f B := by
    simp [w, add_mul, ite_mul, Finset.sum_add_distrib]
  have mass := zhou w (fun i => by dsimp [w]; split_ifs <;> norm_num)
  have total : ∑ i, w i = 2 := by simpa only [mul_one, one_add_one_eq_two] using ev (fun _ => 1)
  have comb : ∑ i, ∑ j, w i*w j*D i j = D A A+D A B+(D B A+D B B) := by
    calc ∑ i, ∑ j, w i*w j*D i j = ∑ i, w i*(∑ j, w j*D i j) := by simp [Finset.mul_sum, mul_assoc]
         _ = (∑ j, w j*D A j)+(∑ j, w j*D B j) := ev _
         _ = _ := by rw [ev, ev]
  rw [total, comb, diag, diag, symm B A] at mass
  linarith

/-- For every odd number of sites at least three, the triangle, Ptolemy and
quadratic mass inequalities alone imply the sharp rectangular upper bound. -/
theorem universalPrice {m : ℕ} [NeZero m] (hm : 3 ≤ m) (odd : Odd m)
    (D : Fin m → Fin m → ℝ)
    (diag : ∀ i, D i i=0) (symm : ∀ i j, D i j=D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j l, D i l ≤ D i j+D j l)
    (pt : ∀ a b c d, D a b*D c d ≤ D a c*D b d+D a d*D b c)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    4*((m:ℝ)-2)*(∑ i, D i (i+1)) ≤ (2*(m:ℝ)-3)^2 := by
  obtain ⟨k, size⟩ := odd
  obtain ⟨ab, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun q : Fin m × Fin m => D q.1 q.2) Finset.univ_nonempty
  have H := oddSharp D ab.1 ab.2 (by omega : 1 ≤ k) size diag symm hn
    (pairPriceLeOne D ab.1 ab.2 diag symm zhou) (fun i j => hmax (i,j) (Finset.mem_univ _))
    tri pt zhou
  have sizeR : (m:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast size
  change 4*((m:ℝ)-2)*R D 1 ≤ _
  rw [sizeR]
  nlinarith

end OddCycleOffset
