import OddCycleTarget.TailDiameter

/-! Ptolemy offset estimates and the two-pole mass test on odd cycles. -/
namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing

variable {m : ℕ} [NeZero m]

def R (D : Fin m → Fin m → ℝ) (j : Fin m) : ℝ := ∑ i, D i (i+j)

theorem sumShift (f : Fin m → ℝ) (j : Fin m) : ∑ i, f (i+j) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight j) _ _ (fun _ => rfl)

theorem reflected (D : Fin m → Fin m → ℝ) (symm : ∀ i j, D i j = D j i) (j : Fin m) :
    R D (-j) = R D j := by
  calc R D (-j) = ∑ i, D (i+(-j)) i := Finset.sum_congr rfl (fun i _ => symm ..)
       _ = ∑ i, (fun l => D l (l+j)) (i+(-j)) := by simp
       _ = R D j := sumShift (fun l => D l (l+j)) (-j)

/-- The homogeneous consequence of the unit-cube transition estimate. -/
theorem scaledTransition (h : ℝ) (hp : 0 < h) (u : Fin m → ℝ)
    (hn : ∀ i, 0 ≤ u i) (hu : ∀ i, u i ≤ h)
    (hl : 2*h ≤ ∑ i, u i) (hr : ∑ i, u i ≤ ((m:ℝ)-2)*h)
    (transition : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → (∀ i, z i ≤ 1) →
      2 ≤ ∑ i, z i → ∑ i, z i ≤ (m:ℝ)-2 → 1 ≤ ∑ i, z i*(1-z (i+1))) :
    h^2 ≤ ∑ i, u i*(h-u (i+1)) := by
  let z := fun i => u i/h
  have sz : ∑ i, z i = (∑ i, u i)/h := (Finset.sum_div ..).symm
  have H := transition z (fun i => div_nonneg (hn i) hp.le)
    (fun i => (div_le_one hp).mpr (hu i)) (by rw [sz]; exact (le_div_iff₀ hp).mpr hl)
    (by rw [sz]; exact (div_le_iff₀ hp).mpr hr)
  have t : ∀ i : Fin m, z i*(1-z (i+1)) = (u i*(h-u (i+1)))/h^2 := by
    intro i; dsimp [z]; field_simp
  simp_rw [t] at H
  rw [← Finset.sum_div, one_le_div (sq_pos_of_pos hp)] at H
  exact H

/-- One chord orientation obeys the target lower bound whenever its price
lies in the interval where the cube transition applies. -/
theorem oriented (D : Fin m → Fin m → ℝ) {h : ℝ} (hp : 0 < h)
    (hn : ∀ i j, 0 ≤ D i j) (hu : ∀ i j, D i j ≤ h)
    (pt : ∀ a b c d, D a b * D c d ≤ D a c * D b d + D a d * D b c)
    (transition : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → (∀ i, z i ≤ 1) →
      2 ≤ ∑ i, z i → ∑ i, z i ≤ (m:ℝ)-2 → 1 ≤ ∑ i, z i*(1-z (i+1)))
    (j : Fin m) (hl : 2*h ≤ R D j) (hr : R D j ≤ ((m:ℝ)-2)*h) :
    2*R D 1-((m:ℝ)-1)*h ≤ R D j+R D (j+1) := by
  let y := fun i : Fin m => D i (i+1)
  let u := fun i : Fin m => D i (i+j)
  let v := fun i : Fin m => D i (i+(j+1))
  have ht := scaledTransition h hp u (fun i => hn ..) (fun i => hu ..) hl hr transition
  have hedge i : h*y i+h*y (i+j)-h^2+u i*(h-u (i+1)) ≤ h*(u i+v i) := by
    have hpt := pt i (i+1) (i+j) ((i+j)+1)
    have swap : i+j+1 = i+1+j := by abel
    change y i*y (i+j) ≤ u i*D (i+1) (i+j+1)+ D i (i+j+1)*D (i+1) (i+j) at hpt
    rw [show D (i+1) (i+j+1) = u (i+1) by dsimp [u]; rw [swap],
        show D i (i+j+1) = v i by dsimp [v]; rw [add_assoc]] at hpt
    have hb := mul_le_mul_of_nonneg_left (hu (i+1) (i+j)) (show 0 ≤ v i from hn ..)
    have hd := mul_nonneg (sub_nonneg.mpr (show y i ≤ h from hu ..))
      (sub_nonneg.mpr (show y (i+j) ≤ h from hu ..))
    nlinarith
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hedge i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
  rw [sumShift y j] at H
  change 2*(∑ i, y i)-((m:ℝ)-1)*h ≤ (∑ i, u i)+(∑ i, v i)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

theorem offsetPair (D : Fin m → Fin m → ℝ) {h : ℝ} (hp : 0 < h)
    (hm : 5 ≤ m) (symm : ∀ i j, D i j = D j i)
    (hn : ∀ i j, 0 ≤ D i j) (hu : ∀ i j, D i j ≤ h)
    (pt : ∀ a b c d, D a b * D c d ≤ D a c * D b d + D a d * D b c)
    (transition : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → (∀ i, z i ≤ 1) →
      2 ≤ ∑ i, z i → ∑ i, z i ≤ (m:ℝ)-2 → 1 ≤ ∑ i, z i*(1-z (i+1)))
    (lower : ∀ l : Fin m, l ≠ 0 → 2*h ≤ R D l)
    (j : Fin m) (jn : j ≠ 0) (jsn : j+1 ≠ 0) :
    2*R D 1-((m:ℝ)-1)*h ≤ R D j+R D (j+1) := by
  by_cases small : R D j ≤ ((m:ℝ)-2)*h
  · exact oriented D hp hn hu pt transition j (lower j jn) small
  by_cases next : R D (j+1) ≤ ((m:ℝ)-2)*h
  · have neg : -(j+1)+1 = -j := by abel
    have H := oriented D hp hn hu pt transition (-(j+1))
      (lower _ (neg_ne_zero.mpr jsn)) (by simpa only [reflected D symm] using next)
    rw [neg, reflected D symm, reflected D symm] at H
    linarith
  · have cap : R D 1 ≤ (m:ℝ)*h := by
      calc R D 1 ≤ ∑ _i : Fin m, h := Finset.sum_le_sum (fun i _ => hu i _)
           _ = _ := by simp [nsmul_eq_mul]
    have size : (5:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg (sub_nonneg.mpr size) hp.le]

private theorem rangePairs (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2*n), f i =
      ∑ i ∈ Finset.range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

theorem totalOffsets (D : Fin m → Fin m → ℝ) :
    ∑ j, R D j = ∑ i, ∑ j, D i j := by
  unfold R; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_comm i] using sumShift (D i) i

/-- Summing pairs of interior offsets counts every nonzero chord in both
directions and leaves exactly the two orientations of the perimeter. -/
theorem aggregate (D : Fin m → Fin m → ℝ) {h : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (size : m = 2*k+1) (diag : ∀ i, D i i = 0)
    (symm : ∀ i j, D i j = D j i)
    (pair : ∀ j : Fin m, j ≠ 0 → j+1 ≠ 0 →
      2*R D 1-((m:ℝ)-1)*h ≤ R D j+R D (j+1)) :
    (k:ℝ)*R D 1 ≤ (∑ i, ∑ j, D i j)/2+(k:ℝ)*((k:ℝ)-1)*h := by
  let f := fun n : ℕ => R D (n : Fin m)
  have val (n : ℕ) (lt : n < m) : (n : Fin m).val = n := by
    simp [Fin.val_natCast, Nat.mod_eq_of_lt lt]
  have nz (n : ℕ) (hp : 0 < n) (lt : n < m) : (n : Fin m) ≠ 0 := by
    intro eq
    have e := congrArg Fin.val eq
    rw [val n lt, Fin.val_zero] at e
    omega
  have small (r : ℕ) (hr : r < k-1) :
      2*R D 1-((m:ℝ)-1)*h ≤ f (2+2*r)+f (2+(2*r+1)) := by
    have hj := nz (2+2*r) (by omega) (by omega)
    have hj' := nz ((2+2*r)+1) (by omega) (by omega)
    have H := pair _ hj (by simpa only [Nat.cast_add, Nat.cast_one] using hj')
    simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc] using H
  have H := Finset.sum_le_sum (s:=Finset.range (k-1))
    (fun r hr => small r (Finset.mem_range.mp hr))
  rw [← rangePairs (fun j => f (2+j)) (k-1)] at H
  have sumAll : ∑ i, ∑ j, D i j = ∑ i ∈ Finset.range m, f i := by
    rw [← totalOffsets D]
    simpa only [f, Fin.cast_val_eq_self] using Fin.sum_univ_eq_sum_range f m
  have split : ∑ i ∈ Finset.range m, f i =
      f 0+f 1+(∑ i ∈ Finset.range (2*(k-1)), f (2+i))+f (2*k) := by
    conv_lhs => rw [size, Finset.sum_range_succ]
    rw [show 2*k = 2+2*(k-1) by omega, Finset.sum_range_add]
    simp [Finset.sum_range_succ]
  have f0 : f 0 = 0 := by simp [f, R, diag]
  have last : (2*k : ℕ) + 1 = m := size.symm
  have castLast : ((2*k:ℕ):Fin m) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_one (R:=Fin m), ← Nat.cast_add, last, Fin.natCast_self]
  have fLast : f (2*k) = R D 1 := by
    dsimp [f]; rw [castLast, reflected D symm]
  have f1 : f 1 = R D 1 := by simp [f]
  rw [sumAll, split, f0, f1, fLast]
  have castSize : (m:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast size
  have castK : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, castK, castSize] at H
  nlinarith

end OddCycleOffset

namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {m : ℕ} [NeZero m]

/-- The diameter endpoint A occurs on the cycle. Alternation forces its full
distance to B into the sum of the two rows. -/
theorem twoRows (D : Fin m → Fin m → ℝ) (A B : Fin m) (hm : Odd m)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j l, D i l ≤ D i j+D j l) :
    R D 1+D A B ≤ (∑ i, D A i)+(∑ i, D B i) := by
  let f := fun i : Fin m => D A i-D B i
  let p := fun i : Fin m => D A i+D B i
  let cost := fun i : Fin m => p i+p (i+1)-2*D i (i+1)
  have edge (i : Fin m) : |f i+f (i+1)| ≤ cost i := by
    have hA := tri i A (i+1)
    have hB := tri i B (i+1)
    rw [symm i A] at hA
    rw [symm i B] at hB
    apply abs_le.mpr; dsimp [f, cost, p]
    constructor <;> linarith
  let F := fun i : ℕ => f ((i : Fin m)+A)
  let C := fun i : ℕ => cost ((i : Fin m)+A)
  have H := OddCycleTail.pathTelescoping F C m (fun i _ => by
    simpa only [F, C, Nat.cast_add, Nat.cast_one, add_right_comm] using edge ((i:Fin m)+A))
  have alt : |F 0-(-1:ℝ)^m*F m| = 2*D A B := by
    rw [hm.neg_one_pow]
    simp only [F, Nat.cast_zero, zero_add, Fin.natCast_self, f, diag, zero_sub, neg_mul,
      one_mul, sub_neg_eq_add]
    rw [symm B A]
    convert (show |-(2*D A B)| = 2*D A B by rw [abs_neg, abs_of_nonneg (by linarith [hn A B])]) using 2; ring
  rw [alt, ← Fin.sum_univ_eq_sum_range] at H
  have H' : 2*D A B ≤ ∑ i, cost i := by
    simpa only [C, Fin.cast_val_eq_self, sumShift] using H
  simp only [cost, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sumShift p (1:Fin m)] at H'
  simp only [p, Finset.sum_add_distrib] at H'
  unfold R; linarith

section
omit [NeZero m]

private def spike (a i : Fin m) : ℝ := if i=a then 1 else 0

private theorem spikeLeft (a : Fin m) (f : Fin m → ℝ) :
    ∑ i, spike a i*f i = f a := by classical simp [spike, ite_mul]

/-- Ordered quadratic mass, linear in each set of weights. -/
private noncomputable def massBilin (D : Fin m → Fin m → ℝ) (u v : Fin m → ℝ) : ℝ :=
  ∑ i, u i*(∑ j, v j*D i j)

private theorem massAddL (D : Fin m → Fin m → ℝ) (u v z : Fin m → ℝ) :
    massBilin D (u+v) z = massBilin D u z+massBilin D v z := by
  simp [massBilin, add_mul, Finset.sum_add_distrib]

private theorem massAddR (D : Fin m → Fin m → ℝ) (u v z : Fin m → ℝ) :
    massBilin D u (v+z) = massBilin D u v+massBilin D u z := by
  simp [massBilin, add_mul, mul_add, Finset.sum_add_distrib]

private theorem massScaleL (D : Fin m → Fin m → ℝ) (t : ℝ) (u v : Fin m → ℝ) :
    massBilin D (t • u) v = t*massBilin D u v := by
  simp [massBilin, ← Finset.mul_sum, mul_assoc]

private theorem massScaleR (D : Fin m → Fin m → ℝ) (t : ℝ) (u v : Fin m → ℝ) :
    massBilin D u (t • v) = t*massBilin D u v := by
  simp only [massBilin, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  simp only [Finset.mul_sum, mul_left_comm]

private theorem massSpikeL (D : Fin m → Fin m → ℝ) (A : Fin m) (v : Fin m → ℝ) :
    massBilin D (spike A) v = ∑ j, v j*D A j := spikeLeft A _

private theorem massSpikeR (D : Fin m → Fin m → ℝ) (A : Fin m) (v : Fin m → ℝ) :
    massBilin D v (spike A) = ∑ i, v i*D i A := by
  simp [massBilin, spikeLeft]

/-- The all-ones mass with equal extra mass at A and B. All weights are
assigned to the original labelled sites, even when prices vanish. -/
theorem spikeMass (D : Fin m → Fin m → ℝ) (A B : Fin m) (t : ℝ) (ht : 0 ≤ t)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    2*((∑ i, ∑ j, D i j)+2*t*((∑ i, D A i)+(∑ i, D B i))+2*t^2*D A B)
      ≤ ((m:ℝ)+2*t)^2 := by
  let w : Fin m → ℝ := 1+t • spike A+t • spike B
  have hnon i : 0 ≤ w i := by
    dsimp [w, spike]; split_ifs <;> simp_all <;> linarith
  have hmass := zhou w hnon
  have hw : ∑ i, w i = (m:ℝ)+2*t := by
    simp [w, spike, Finset.sum_add_distrib]; ring
  rw [hw] at hmass
  have hbil : massBilin D w w = ∑ i, ∑ j, w i*w j*D i j := by
    simp [massBilin, Finset.mul_sum, mul_assoc]
  rw [← hbil] at hmass
  have hsymA : (∑ i, D i A) = ∑ i, D A i := Finset.sum_congr rfl (fun i _ => symm i A)
  have hsymB : (∑ i, D i B) = ∑ i, D B i := Finset.sum_congr rfl (fun i _ => symm i B)
  simp only [w, massAddL, massAddR, massScaleL, massScaleR] at hmass
  simp only [massSpikeL, massSpikeR,
    Pi.one_apply, one_mul, spikeLeft, diag, mul_zero, add_zero, hsymA, hsymB, symm B A] at hmass
  have baseline : massBilin D 1 1 = ∑ i, ∑ j, D i j := by simp [massBilin]
  rw [baseline] at hmass
  nlinarith

end

end OddCycleOffset

namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing
variable {m : ℕ} [NeZero m]

/-- Complete geometric assembly from the two independent scalar/combinatorial
inputs. All four-point and mass constraints use the original labelled prices. -/
theorem sharpPriceGeFive (D : Fin m → Fin m → ℝ) (A B : Fin m) {k : ℕ}
    (hk : 2 ≤ k) (size : m = 2*k+1)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (hn : ∀ i j, 0 ≤ D i j) (diam : ∀ i j, D i j ≤ D A B)
    (tri : ∀ i j l, D i l ≤ D i j+D j l)
    (pt : ∀ a b c d, D a b * D c d ≤ D a c * D b d + D a d * D b c)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2)
    (transition : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) → (∀ i, z i ≤ 1) →
      2 ≤ ∑ i, z i → ∑ i, z i ≤ (m:ℝ)-2 → 1 ≤ ∑ i, z i*(1-z (i+1)))
    (lower : (m:ℝ)-1 < R D 1 → ∀ j : Fin m, j ≠ 0 → 2*D A B ≤ R D j) :
    4*(2*(k:ℝ)-1)*R D 1 ≤ (4*(k:ℝ)-1)^2 := by
  have km : (2:ℝ) ≤ k := by exact_mod_cast hk
  have sizeR : (m:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast size
  by_cases high : (m:ℝ)-1 < R D 1
  · have cap : R D 1 ≤ (m:ℝ)*D A B := by
      calc R D 1 ≤ ∑ _i : Fin m, D A B := Finset.sum_le_sum (fun i _ => diam i _)
           _ = _ := by simp [nsmul_eq_mul]
    have hp : 0 < D A B := by
      by_contra! h
      have hz : D A B = 0 := le_antisymm h (hn ..)
      rw [hz, mul_zero] at cap
      linarith
    have pair := offsetPair D hp (by omega) symm hn diam pt transition (lower high)
    have agg := aggregate D hk size diag symm pair
    have rows := twoRows D A B (show Odd m from ⟨k, by omega⟩) diag symm hn tri
    have ht : 0 ≤ (k:ℝ)-1 := by linarith
    have boost := mul_le_mul_of_nonneg_left rows ht
    have mass := spikeMass D A B _ ht diag symm zhou
    rw [sizeR] at mass
    nlinarith
  · have low : R D 1 ≤ 2*(k:ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left low (show 0 ≤ 4*(2*(k:ℝ)-1) by linarith)]

theorem sharpPriceThree (D : Fin 3 → Fin 3 → ℝ)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (zhou : ∀ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    4*R D 1 ≤ 9 := by
  have H := zhou (fun _ => 1) (fun _ => zero_le_one)
  norm_num [R, Fin.sum_univ_three, diag] at *
  have s01 := symm 0 1
  have s12 := symm 1 2
  have s20 := symm 2 0
  rw [show (3 : Fin 3) = 0 by decide]
  linarith

end OddCycleOffset

namespace OddCycleOffset
open scoped BigOperators Fin.NatCast Fin.CommRing

/-- On an odd metric list, summing the adjacent choices of two rows saves one
additional row in the standard quadratic perimeter bound. -/
theorem oddWindowUpper {g : ℕ} [NeZero g] (D : Fin g → Fin g → ℝ) (odd : Odd g)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j l, D i l ≤ D i j+D j l)
    (mass : 2*(∑ i, ∑ j, D i j) ≤ (g:ℝ)^2) :
    ((g:ℝ)+1)*R D 1 ≤ (g:ℝ)^2 := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => twoRows D i (i+1) odd diag symm hn tri)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  rw [sumShift (fun i => ∑ j, D i j) (1:Fin g)] at hs
  unfold R at *
  linarith

private noncomputable def visitMass {m g : ℕ} (f : Fin g → Fin m) (j : Fin m) : ℝ :=
  ∑ i, if f i=j then 1 else 0

private theorem sumVisits {m g : ℕ} (f : Fin g → Fin m) (v : Fin m → ℝ) :
    ∑ a, visitMass f a*v a = ∑ i, v (f i) := by
  classical
  simp only [visitMass, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- The global mass tests restrict to any labelled window, including repeated
visits. The multiplicity of each visit is added at its original vertex. -/
theorem pulledOddWindowUpper {m g : ℕ} [NeZero g] (D : Fin m → Fin m → ℝ)
    (f : Fin g → Fin m) (odd : Odd g)
    (diag : ∀ i, D i i = 0) (symm : ∀ i j, D i j = D j i)
    (hn : ∀ i j, 0 ≤ D i j) (tri : ∀ i j l, D i l ≤ D i j+D j l)
    (zhou : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      2*(∑ i, ∑ j, w i*w j*D i j) ≤ (∑ i, w i)^2) :
    ((g:ℝ)+1)*(∑ i, D (f i) (f (i+1))) ≤ (g:ℝ)^2 := by
  have hpos a : 0 ≤ visitMass f a := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hz := zhou _ hpos
  have total : ∑ a, visitMass f a = (g:ℝ) := by simpa using sumVisits f (fun _ => 1)
  have wt : ∑ i, ∑ j, visitMass f i*visitMass f j*D i j = ∑ i, ∑ j, D (f i) (f j) := by
    calc ∑ i, ∑ j, visitMass f i*visitMass f j*D i j =
        ∑ i, visitMass f i*(∑ j, visitMass f j*D i j) := by simp [Finset.mul_sum, mul_assoc]
      _ = ∑ i, ∑ j, visitMass f j*D (f i) j := sumVisits f _
      _ = _ := Finset.sum_congr rfl (fun i _ => sumVisits f (D (f i)))
  rw [total, wt] at hz
  exact oddWindowUpper (fun i j => D (f i) (f j)) odd (fun _ => diag _) (fun _ _ => symm ..)
    (fun _ _ => hn ..) (fun _ _ _ => tri ..) hz

end OddCycleOffset
