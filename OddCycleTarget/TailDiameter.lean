import Mathlib

/-! Three-site mass tests and parity potentials for Ptolemy cycle prices. -/
namespace OddCycleTail

/-- The two normalized distances from a mark to the poles are c and 1-b, in
increasing order. The true distance between the poles is 1-s². -/
def ThreeSiteMass (s b c : ℝ) : Prop :=
  ∀ α β γ : ℝ, 0 ≤ α → 0 ≤ β → 0 ≤ γ →
    4 * ((1-s^2)*α*β + (1-s^2)*(1-b)*α*γ + (1-s^2)*c*β*γ) ≤ (α+β+γ)^2

/-- A single optimizing three-mark mass vector gives a quadratic profile
with no optimization or limiting operation left in its conclusion. -/
theorem threeSiteQuadratic {s b c : ℝ} (hs : 0 < s) (hp : 0 < 1-s^2)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1-b) (hmass : ThreeSiteMass s b c) :
    (c-b)^2 ≤ 4*s^2*(1-b)*c := by
  have h1b : 0 ≤ 1-b := le_trans (hb.trans hbc) hc
  by_cases hδ : c-b ≤ 2*s^2*(1-b)
  · have hd := mul_le_mul_of_nonneg_right hδ (sub_nonneg.mpr hbc)
    have ha := mul_nonneg (sq_nonneg s) h1b
    nlinarith [mul_nonneg ha hb, mul_nonneg ha (hb.trans hbc)]
  · let α := ((c-b)-2*s^2*c)/2
    let β := ((c-b)-2*s^2*(1-b))/2
    have hβ : 0 ≤ β := by dsimp [β]; linarith
    have hαβ : β ≤ α := by
      dsimp [α, β]
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hc)]
    have hw := hmass α β (s^2) (hβ.trans hαβ) hβ (sq_nonneg s)
    have hfac : (α+β+s^2)^2 -
        4*((1-s^2)*α*β+(1-s^2)*(1-b)*α*s^2+(1-s^2)*c*β*s^2) =
        (1-s^2)*s^2*(4*s^2*(1-b)*c-(c-b)^2) := by
      dsimp [α, β]; ring
    have hprod : 0 ≤ (1-s^2)*s^2*(4*s^2*(1-b)*c-(c-b)^2) := by
      rw [← hfac]; linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos hp (sq_pos_of_pos hs))).mp hprod)

theorem excessBound {s b c : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) (hhalf : b ≤ 1/2)
    (hq : (c-b)^2 ≤ 4*s^2*(1-b)*c) :
    c-b ≤ 2*s*Real.sqrt (b*(1-b))+4*s^2 := by
  let v := 2*s*Real.sqrt (b*(1-b))
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hb1 : 0 ≤ b*(1-b) := mul_nonneg hb (by linarith)
  have hv2 : v^2 = 4*s^2*b*(1-b) := by
    dsimp [v]
    rw [mul_pow, Real.sq_sqrt hb1]
    ring
  change c-b ≤ v+4*s^2
  by_contra! hf
  have hvd : v < c-b := by linarith [sq_nonneg s]
  have hcut : v < c-b-4*s^2*(1-b) := by
    nlinarith [mul_nonneg (sq_nonneg s) hb]
  have product := mul_lt_mul_of_pos_left hcut (lt_of_le_of_lt hv hvd)
  have low := mul_le_mul_of_nonneg_right hvd.le hv
  nlinarith

theorem sqrtProfile_le_half {b : ℝ} (hb : 0 ≤ b) (hh : b ≤ 1/2) :
    Real.sqrt (b*(1-b)) ≤ 1/2 := by
  have h2 := Real.sq_sqrt (mul_nonneg hb (show 0 ≤ 1-b by linarith))
  nlinarith [sq_nonneg (b-1/2), Real.sqrt_nonneg (b*(1-b)),
    sq_nonneg (Real.sqrt (b*(1-b))-1/2)]

theorem sqrtProfile_le_sqrt {b : ℝ} (_hb : 0 ≤ b) :
    Real.sqrt (b*(1-b)) ≤ Real.sqrt b :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])

theorem excessCoarse {s b c : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) (hh : b ≤ 1/2)
    (he : c-b ≤ 2*s*Real.sqrt (b*(1-b))+4*s^2) :
    c-b ≤ s+4*s^2 ∧ c ≤ 2*b+5*s^2 := by
  have h1 := mul_le_mul_of_nonneg_left (sqrtProfile_le_half hb hh) hs
  have h2 := mul_le_mul_of_nonneg_left (sqrtProfile_le_sqrt hb) hs
  constructor
  · linarith
  · nlinarith [sq_nonneg (Real.sqrt b-s), Real.sq_sqrt hb]

/-- Lower truncation compensates for marks sharing the maximal distance to
one pole without being the other pole. -/
noncomputable def clippedMinor (s b : ℝ) : ℝ := max 0 (b-8*s^2)

theorem oppositeEdge {s bi bj ci cj d : ℝ} (hbi : 0 ≤ bi) (hbj : 0 ≤ bj)
    (hi : bi ≤ 1/2) (hj : bj ≤ 1/2) (hci : 0 ≤ ci) (hcj : 0 ≤ cj)
    (hiu : ci ≤ 11/20) (hju : cj ≤ 11/20)
    (hic : ci ≤ 2*bi+5*s^2) (hjc : cj ≤ 2*bj+5*s^2)
    (hu : d ≤ 1) (hpt : d ≤ (1-bi)*(1-bj)+ci*cj) :
    |clippedMinor s bi-clippedMinor s bj| ≤ 1-d := by
  have oneDir : ∀ {a b c e : ℝ}, b ≤ a → a ≤ 1/2 → 0 ≤ b → 0 ≤ c →
      c ≤ 11/20 → e ≤ 2*b+5*s^2 → d ≤ (1-a)*(1-b)+c*e →
      clippedMinor s a-clippedMinor s b ≤ 1-d := by
    intro a b c e hba ha hb hc hcu heu hp
    have he := mul_le_mul_of_nonneg_left heu hc
    have hcb := mul_le_mul_of_nonneg_right hcu hb
    have hcs := mul_le_mul_of_nonneg_right hcu (sq_nonneg s)
    have hab := mul_le_mul_of_nonneg_right ha hb
    have hdiff : a-b+(2/5)*b-(11/4)*s^2 ≤ 1-d := by nlinarith
    unfold clippedMinor
    by_cases hlarge : 8*s^2 ≤ b
    · rw [max_eq_right (by linarith : 0 ≤ a-8*s^2),
          max_eq_right (by linarith : 0 ≤ b-8*s^2)]
      linarith [sq_nonneg s]
    · rw [max_eq_left (by linarith : b-8*s^2 ≤ 0), sub_zero]
      apply max_le (by linarith)
      linarith [sq_nonneg s]
  rcases le_total bj bi with h | h
  · have hmono : clippedMinor s bj ≤ clippedMinor s bi := max_le_max_left 0 (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    exact oneDir h hi hbj hci hiu hjc hpt
  · rw [abs_sub_comm]
    have hmono : clippedMinor s bi ≤ clippedMinor s bj := max_le_max_left 0 (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    exact oneDir h hj hbi hcj hju hic (by nlinarith)

theorem sameEdgeResidual {s ρ bi bj ci cj : ℝ}
    (hs : 0 ≤ s) (hr : 3/4 ≤ ρ) (hbi : 0 ≤ bi) (hbj : 0 ≤ bj)
    (hci : bi ≤ ci) (hcj : bj ≤ cj)
    (ei : ci-bi ≤ 2*s*Real.sqrt (bi*(1-bi))+4*s^2)
    (ej : cj-bj ≤ 2*s*Real.sqrt (bj*(1-bj))+4*s^2)
    (ri : 2*Real.sqrt (bi*(1-bi)) ≤ ρ) (rj : 2*Real.sqrt (bj*(1-bj)) ≤ ρ) :
    ci-clippedMinor s bi+(cj-clippedMinor s bj)-bi*cj-bj*ci ≤ ρ*s+40*s^2 := by
  have ordered : ∀ {a b ca cb : ℝ}, 0 ≤ a → 0 ≤ b → b ≤ a →
      ca-a ≤ 2*s*Real.sqrt (a*(1-a))+4*s^2 →
      cb-b ≤ 2*s*Real.sqrt (b*(1-b))+4*s^2 →
      2*Real.sqrt (a*(1-a)) ≤ ρ →
      (ca-a)+(cb-b)-2*a*b ≤ ρ*s+24*s^2 := by
    intro a b ca cb ha hb hba ea eb ra
    by_cases hlarge : 1/32 ≤ a
    · have h1 := mul_le_mul_of_nonneg_left ra hs
      have h2 := mul_le_mul_of_nonneg_left (sqrtProfile_le_sqrt hb) hs
      have h3 := mul_nonneg (sub_nonneg.mpr hlarge) hb
      nlinarith [sq_nonneg (Real.sqrt b/4-4*s), Real.sq_sqrt hb]
    · have small : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1/32 → Real.sqrt (v*(1-v)) ≤ 3/16 := by
        intro v hv hvu
        have hm := Real.sq_sqrt (mul_nonneg hv (show 0 ≤ 1-v by linarith))
        nlinarith [sq_nonneg v, sq_nonneg (Real.sqrt (v*(1-v))-3/16)]
      have h1 := mul_le_mul_of_nonneg_left (small ha (by linarith)) hs
      have h2 := mul_le_mul_of_nonneg_left (small hb (by linarith)) hs
      nlinarith [mul_nonneg ha hb, mul_nonneg (sub_nonneg.mpr hr) hs, sq_nonneg s]
  have hw : (ci-bi)+(cj-bj)-2*bi*bj ≤ ρ*s+24*s^2 := by
    rcases le_total bj bi with h | h
    · exact ordered hbi hbj h ei ej ri
    · have ht := ordered hbj hbi h ej ei rj
      linarith
  have gi : bi-8*s^2 ≤ clippedMinor s bi := le_max_right _ _
  have gj : bj-8*s^2 ≤ clippedMinor s bj := le_max_right _ _
  have hPi := mul_le_mul_of_nonneg_left hcj hbi
  have hPj := mul_le_mul_of_nonneg_left hci hbj
  nlinarith
end OddCycleTail

namespace OddCycleTail

/-- Coordinates of a mark along a fixed diameter. The Boolean records its
nearer endpoint, with arbitrary choices allowed at ties. -/
structure PoleMark (s : ℝ) where
  b : ℝ
  c : ℝ
  side : Bool
  b_nonneg : 0 ≤ b
  b_le_c : b ≤ c
  c_le_far : c ≤ 1-b
  mass : ThreeSiteMass s b c

theorem PoleMark.b_half {s : ℝ} (i : PoleMark s) : i.b ≤ 1/2 := by
  linarith [i.b_le_c, i.c_le_far]

theorem PoleMark.profile {s : ℝ} (i : PoleMark s) (hs : 0 < s) (hp : 0 < 1-s^2) :
    i.c-i.b ≤ 2*s*Real.sqrt (i.b*(1-i.b))+4*s^2 :=
  excessBound hs.le i.b_nonneg i.b_half
    (threeSiteQuadratic hs hp i.b_nonneg i.b_le_c i.c_le_far i.mass)

/-- Normalized endpoint distances, in the order of the two fixed poles. -/
def firstPole {s : ℝ} (i : PoleMark s) : ℝ := if i.side then i.c else 1-i.b
def secondPole {s : ℝ} (i : PoleMark s) : ℝ := if i.side then 1-i.b else i.c

noncomputable def potential {s : ℝ} (E : ℝ) (i : PoleMark s) : ℝ :=
  if i.side then (1-E)/2-clippedMinor s i.b else -((1-E)/2-clippedMinor s i.b)

theorem edgePotential {s ρ D : ℝ} (i j : PoleMark s) (hs : 0 < s) (hsu : s ≤ 1/50)
    (hρ : 3/4 ≤ ρ) (hρu : ρ ≤ 1) (hdu : D ≤ 1)
    (hpt : D ≤ firstPole i*secondPole j+firstPole j*secondPole i)
    (ri : 2*Real.sqrt (i.b*(1-i.b)) ≤ ρ) (rj : 2*Real.sqrt (j.b*(1-j.b)) ≤ ρ) :
    |potential (ρ*s+40*s^2) i+potential (ρ*s+40*s^2) j| ≤ 1-D := by
  have hs2 : s^2 ≤ s/50 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsu)]
  have hp : 0 < 1-s^2 := by linarith
  have ei := i.profile hs hp
  have ej := j.profile hs hp
  obtain ⟨di, ci⟩ := excessCoarse hs.le i.b_nonneg i.b_half ei
  obtain ⟨dj, cj⟩ := excessCoarse hs.le j.b_nonneg j.b_half ej
  let E := ρ*s+40*s^2
  have hE : E ≤ 9/250 := by dsimp [E]; nlinarith [mul_le_mul_of_nonneg_right hρu hs.le]
  have hsame (h : D ≤ i.c*(1-j.b)+j.c*(1-i.b)) :
      |1-E-clippedMinor s i.b-clippedMinor s j.b| ≤ 1-D := by
    have hres := sameEdgeResidual hs.le hρ i.b_nonneg j.b_nonneg i.b_le_c j.b_le_c ei ej ri rj
    have hprod := mul_nonneg (show 0 ≤ 1-2*i.b by linarith [i.b_half])
      (show 0 ≤ 1-2*j.b by linarith [j.b_half])
    have he1 := mul_le_mul_of_nonneg_right di (show 0 ≤ 1-j.b by linarith [j.b_half])
    have he2 := mul_le_mul_of_nonneg_right dj (show 0 ≤ 1-i.b by linarith [i.b_half])
    have hu : D ≤ 1/2+2*(s+4*s^2) := by
      nlinarith [mul_nonneg i.b_nonneg (show 0 ≤ s+4*s^2 by positivity),
        mul_nonneg j.b_nonneg (show 0 ≤ s+4*s^2 by positivity)]
    have gi : clippedMinor s i.b ≤ 1/2 := max_le (by norm_num) (by linarith [sq_nonneg s, i.b_half])
    have gj : clippedMinor s j.b ≤ 1/2 := max_le (by norm_num) (by linarith [sq_nonneg s, j.b_half])
    apply abs_le.mpr
    constructor
    · linarith
    · dsimp [E]; linarith
  have hopp (h : D ≤ (1-i.b)*(1-j.b)+i.c*j.c) :
      |clippedMinor s i.b-clippedMinor s j.b| ≤ 1-D :=
    oppositeEdge i.b_nonneg j.b_nonneg i.b_half j.b_half
      (i.b_nonneg.trans i.b_le_c) (j.b_nonneg.trans j.b_le_c)
      (by linarith [i.b_half]) (by linarith [j.b_half]) ci cj hdu h
  change |potential E i+potential E j| ≤ 1-D
  cases hi : i.side <;> cases hj : j.side
  · simp [firstPole, secondPole, hi, hj] at hpt
    have h := hsame (by linarith)
    simp only [potential, hi, hj, Bool.false_eq_true, ite_false]
    convert (show |-(1-E-clippedMinor s i.b-clippedMinor s j.b)| ≤ 1-D by rw [abs_neg]; exact h) using 2; ring
  · simp [firstPole, secondPole, hi, hj] at hpt
    have h := hopp (by linarith)
    simp only [potential, hi, hj, Bool.false_eq_true, ite_false, ite_true]
    convert h using 2; ring
  · simp [firstPole, secondPole, hi, hj] at hpt
    have h := hopp (by linarith)
    simp only [potential, hi, hj, Bool.false_eq_true, ite_false, ite_true]
    rw [abs_sub_comm] at h
    convert h using 2; ring
  · simp [firstPole, secondPole, hi, hj] at hpt
    have h := hsame (by linarith)
    simp only [potential, hi, hj, ite_true]
    convert h using 2; ring

theorem pathTelescoping (f cost : ℕ → ℝ) (n : ℕ)
    (he : ∀ i < n, |f i+f (i+1)| ≤ cost i) :
    |f 0-(-1:ℝ)^n*f n| ≤ ∑ i ∈ Finset.range n, cost i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun i hi => he i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    calc
      |f 0-(-1:ℝ)^(n+1)*f (n+1)| =
          |(f 0-(-1:ℝ)^n*f n)+(-1:ℝ)^n*(f n+f (n+1))| := by
            congr 1; rw [pow_succ]; ring
      _ ≤ |f 0-(-1:ℝ)^n*f n| + |(-1:ℝ)^n*(f n+f (n+1))| := abs_add_le _ _
      _ ≤ (∑ i ∈ Finset.range n, cost i)+cost n := by
            rw [abs_mul, abs_pow]; simpa using add_le_add h (he n n.lt_succ_self)
      _ = _ := (Finset.sum_range_succ _ _).symm

/-- Odd perimeter bound on normalized endpoint coordinates. The path starts
at either pole and closes there. The normalized edge prices only enter via
their diameter bound and the four-mark Ptolemy inequality with the poles. -/
theorem normalizedPerimeter {s ρ : ℝ} (hs : 0 < s) (hsu : s ≤ 1/50)
    (hρ : 3/4 ≤ ρ) (hρu : ρ ≤ 1) {m : ℕ} (hm : Odd m)
    (v : ℕ → PoleMark s) (d : ℕ → ℝ) (closed : v m = v 0) (start : (v 0).b = 0)
    (profile : ∀ i ≤ m, 2*Real.sqrt ((v i).b*(1-(v i).b)) ≤ ρ)
    (hu : ∀ i < m, d i ≤ 1)
    (pt : ∀ i < m, d i ≤ firstPole (v i)*secondPole (v (i+1))+
      firstPole (v (i+1))*secondPole (v i)) :
    ∑ i ∈ Finset.range m, d i ≤ (m:ℝ)-1+ρ*s+40*s^2 := by
  let E := ρ*s+40*s^2
  have he := pathTelescoping (fun i => potential E (v i)) (fun i => 1-d i) m
    (fun i hi => edgePotential _ _ hs hsu hρ hρu (hu i hi) (pt i hi) (profile i hi.le) (profile (i+1) (by omega)))
  have hs2 : s^2 ≤ s/50 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsu)]
  have hE : 0 ≤ 1-E := by dsimp [E]; nlinarith [mul_le_mul_of_nonneg_right hρu hs.le]
  have hg : clippedMinor s (v 0).b = 0 := by
    rw [start, clippedMinor, max_eq_left (by nlinarith [sq_nonneg s])]
  rw [hm.neg_one_pow, closed] at he
  have heq : |potential E (v 0)-(-1)*potential E (v 0)| = 1-E := by
    cases hc : (v 0).side
    · simp only [potential, hc, Bool.false_eq_true, ite_false, hg]
      convert (show |-(1-E)| = 1-E by rw [abs_neg, abs_of_nonneg hE]) using 2; ring
    · simp only [potential, hc, ite_true, hg]
      convert (abs_of_nonneg hE) using 2; ring
  rw [heq, Finset.sum_sub_distrib] at he
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at he
  dsimp [E] at he
  linarith

end OddCycleTail

namespace OddCycleTail

/-- Convert the normalized distances a and b to an actual ordered pole pair. -/
noncomputable def markOfDistances {s : ℝ} (a b : ℝ)
    (ha : a ≤ 1) (hb : b ≤ 1) (htri : 1 ≤ a+b)
    (mass : ∀ α β γ : ℝ, 0 ≤ α → 0 ≤ β → 0 ≤ γ →
      4*((1-s^2)*α*β+(1-s^2)*a*α*γ+(1-s^2)*b*β*γ) ≤ (α+β+γ)^2) : PoleMark s where
  b := 1-max a b
  c := min a b
  side := decide (a ≤ b)
  b_nonneg := sub_nonneg.mpr (max_le ha hb)
  b_le_c := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]; linarith
    · rw [min_eq_right h, max_eq_left h]; linarith
  c_le_far := by linarith [min_le_left a b, le_max_left a b]
  mass := by
    intro α β γ hα hβ hγ
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
      have hs := mass β α γ hβ hα hγ
      linarith
    · rw [min_eq_right h, max_eq_left h]
      have hs := mass α β γ hα hβ hγ
      linarith

@[simp] theorem firstPole_markOfDistances {s a b : ℝ} {ha hb htri mass} :
    firstPole (markOfDistances (s:=s) a b ha hb htri mass) = a := by
  by_cases h : a ≤ b
  · simp [firstPole, markOfDistances, h]
  · simp [firstPole, markOfDistances, h, max_eq_left (le_of_not_ge h)]

@[simp] theorem secondPole_markOfDistances {s a b : ℝ} {ha hb htri mass} :
    secondPole (markOfDistances (s:=s) a b ha hb htri mass) = b := by
  by_cases h : a ≤ b
  · simp [secondPole, markOfDistances, h]
  · simp [secondPole, markOfDistances, h, min_eq_right (le_of_not_ge h)]

/-- The perimeter estimate on the actual metric. Ptolemy need only be tested
on the two fixed poles and the endpoints of a path edge. All diagrams may
have repeated marks. The vertex map is extended arbitrarily past index m. -/
theorem diameterPerimeter {X : Type*} [PseudoMetricSpace X] (A B : X)
    {s ρ : ℝ} (hs : 0 < s) (hsu : s ≤ 1/50) (hρ : 3/4 ≤ ρ) (hρu : ρ ≤ 1)
    (hd : dist A B = 1-s^2) (diam : ∀ i j : X, dist i j ≤ dist A B)
    (mass : ∀ (i : X) (α β γ : ℝ), 0 ≤ α → 0 ≤ β → 0 ≤ γ →
      4*(dist A B*α*β+dist A i*α*γ+dist B i*β*γ) ≤ (α+β+γ)^2)
    {m : ℕ} (hm : Odd m) (v : ℕ → X) (start : v 0 = A) (closed : v m = v 0)
    (profile : ∀ i ≤ m, let b := 1-max (dist A (v i)) (dist B (v i))/dist A B
      2*Real.sqrt (b*(1-b)) ≤ ρ)
    (pt : ∀ i < m, dist A B*dist (v i) (v (i+1)) ≤
      dist A (v i)*dist B (v (i+1))+dist A (v (i+1))*dist B (v i)) :
    ∑ i ∈ Finset.range m, dist (v i) (v (i+1)) ≤
      dist A B*((m:ℝ)-1+ρ*s+40*s^2) := by
  let p := dist A B
  have hp : 0 < p := by
    dsimp [p]; rw [hd]; nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsu)]
  let a := fun i : X => dist A i/p
  let b := fun i : X => dist B i/p
  have ha i : a i ≤ 1 := (div_le_one hp).mpr (diam A i)
  have hb i : b i ≤ 1 := (div_le_one hp).mpr (diam B i)
  have ht i : 1 ≤ a i+b i := by
    dsimp [a, b]; rw [← add_div, one_le_div hp]
    calc p = dist A B := rfl
         _ ≤ dist A i+dist i B := dist_triangle _ _ _
         _ = _ := by rw [dist_comm i B]
  have unwrapA i : (1-s^2)*a i = dist A i := by
    change (1-s^2)*(dist A i/p) = _
    rw [← hd]; change p*(dist A i/p) = _; field_simp
  have unwrapB i : (1-s^2)*b i = dist B i := by
    change (1-s^2)*(dist B i/p) = _
    rw [← hd]; change p*(dist B i/p) = _; field_simp
  have hma i α β γ (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
      4*((1-s^2)*α*β+(1-s^2)*(a i)*α*γ+(1-s^2)*(b i)*β*γ) ≤ (α+β+γ)^2 := by
    rw [unwrapA, unwrapB, ← hd]
    exact mass i α β γ hα hβ hγ
  let mark := fun i : X => markOfDistances (s:=s) (a i) (b i) (ha i) (hb i) (ht i) (hma i)
  have hmax i : max (a i) (b i) = max (dist A i) (dist B i)/p := by
    dsimp [a, b]; rw [max_div_div_right hp.le]
  have hcal (i : X) : (mark i).b = 1-max (dist A i) (dist B i)/p := by
    change 1-max (a i) (b i) = _; rw [hmax]
  have hstart : (mark (v 0)).b = 0 := by
    rw [start, hcal, dist_self, dist_comm B A, max_eq_right dist_nonneg]
    change 1-p/p = 0
    rw [div_self hp.ne', sub_self]
  let nd := fun i : ℕ => dist (v i) (v (i+1))/p
  have he i (hi : i < m) : nd i ≤ firstPole (mark (v i))*secondPole (mark (v (i+1)))+
      firstPole (mark (v (i+1)))*secondPole (mark (v i)) := by
    simp only [mark, firstPole_markOfDistances, secondPole_markOfDistances]
    dsimp [a, b, nd]
    have h := pt i hi
    change p*_ ≤ _ at h
    field_simp [hp.ne']
    nlinarith
  have H := normalizedPerimeter hs hsu hρ hρu hm (fun i => mark (v i)) nd
    (congrArg mark closed) hstart (fun i hi => by rw [hcal]; exact profile i hi)
    (fun i _ => (div_le_one hp).mpr (diam _ _)) he
  dsimp only [nd] at H
  rw [← Finset.sum_div] at H
  exact (div_le_iff₀ hp).mp H |>.trans_eq (mul_comm _ _)

end OddCycleTail

namespace OddCycleTail

theorem poleMinorBounds {X : Type*} [PseudoMetricSpace X] (A B i : X)
    (hp : 0 < dist A B) (ha : dist A i ≤ dist A B) (hb : dist B i ≤ dist A B) :
    0 ≤ 1-max (dist A i) (dist B i)/dist A B ∧
    1-max (dist A i) (dist B i)/dist A B ≤ 1/2 := by
  have h1 := (div_le_one hp).mpr (max_le ha hb)
  have h2 : 1/2 ≤ max (dist A i) (dist B i)/dist A B := by
    apply (le_div_iff₀ hp).mpr
    have ht := dist_triangle A i B
    rw [dist_comm i B] at ht
    linarith [le_max_left (dist A i) (dist B i), le_max_right (dist A i) (dist B i)]
  constructor <;> linarith

theorem profileAwayFromMiddle {b : ℝ} (hb : 0 ≤ b) (hu : b ≤ 9/20) :
    2*Real.sqrt (b*(1-b)) ≤ Real.sqrt (99/100) := by
  have h1 := Real.sq_sqrt (mul_nonneg hb (show 0 ≤ 1-b by linarith))
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 99/100)
  have hprod := mul_nonneg (show 0 ≤ 9/20-b by linarith) (show 0 ≤ 11/20-b by linarith)
  have ha : 0 ≤ 2*Real.sqrt (b*(1-b)) := by positivity
  have hc := Real.sqrt_nonneg (99/100:ℝ)
  nlinarith [sq_nonneg (2*Real.sqrt (b*(1-b))-Real.sqrt (99/100)),
    mul_nonneg ha hc, (sq_le_sq₀ ha hc).mp (show (2*Real.sqrt (b*(1-b)))^2 ≤ (Real.sqrt (99/100:ℝ))^2 by nlinarith)]

/-- A counterexample above the rectangular perimeter must visit a mark whose
two normalized distances to the poles both exceed 9/20. The same argument
bounds the diameter defect independently of the number of distinct marks. -/
theorem midpointOfViolation {X : Type*} [PseudoMetricSpace X] (A B : X)
    {s : ℝ} (hs : 0 < s) (hd : dist A B = 1-s^2)
    (diam : ∀ i j : X, dist i j ≤ dist A B)
    (mass : ∀ (i : X) (α β γ : ℝ), 0 ≤ α → 0 ≤ β → 0 ≤ γ →
      4*(dist A B*α*β+dist A i*α*γ+dist B i*β*γ) ≤ (α+β+γ)^2)
    {m : ℕ} (hm : Odd m) (hsize : 3902 ≤ m) (v : ℕ → X)
    (start : v 0 = A) (closed : v m = v 0)
    (pt : ∀ i < m, dist A B*dist (v i) (v (i+1)) ≤
      dist A (v i)*dist B (v (i+1))+dist A (v (i+1))*dist B (v i))
    (bad : (m:ℝ)-1+1/(4*((m:ℝ)-2)) < ∑ i ∈ Finset.range m, dist (v i) (v (i+1))) :
    s < 1/((m:ℝ)-41) ∧ s+4*s^2 < 1/3800 ∧
      ∃ i < m, 9/20 < 1-max (dist A (v i)) (dist B (v i))/dist A B := by
  let Y := ∑ i ∈ Finset.range m, dist (v i) (v (i+1))
  have hmR : (3902:ℝ) ≤ m := by exact_mod_cast hsize
  have hM : 0 < (m:ℝ)-41 := by linarith
  have hM2 : 0 < 4*((m:ℝ)-2) := by linarith
  have base : (m:ℝ)-1 < Y := by dsimp [Y]; linarith [one_div_pos.mpr hM2]
  have cap : Y ≤ (m:ℝ)*(1-s^2) := by
    calc Y ≤ ∑ _i ∈ Finset.range m, dist A B := Finset.sum_le_sum (fun i _ => diam _ _)
         _ = _ := by simp [hd, nsmul_eq_mul]; ring
  have small : s ≤ 1/50 := by
    by_contra! h
    have bigsq : 1/2500 < s^2 := by nlinarith [sq_nonneg (s-1/50)]
    have hh := mul_nonneg (show 0 ≤ (m:ℝ)-3902 by linarith) (sq_nonneg s)
    nlinarith
  have hs2 : s^2 ≤ s/50 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr small)]
  have hp : 0 < dist A B := by rw [hd]; linarith
  let minor := fun i : ℕ => 1-max (dist A (v i)) (dist B (v i))/dist A B
  have hminor i : 0 ≤ minor i ∧ minor i ≤ 1/2 := poleMinorBounds A B _ hp (diam ..) (diam ..)
  have bound (ρ : ℝ) (hr : 3/4 ≤ ρ) (hu : ρ ≤ 1)
      (hprof : ∀ i ≤ m, 2*Real.sqrt (minor i*(1-minor i)) ≤ ρ) :
      Y ≤ (m:ℝ)-1+ρ*s-((m:ℝ)-41)*s^2 := by
    have h := diameterPerimeter A B hs small hr hu hd diam mass hm v start closed hprof pt
    change Y ≤ _ at h
    rw [hd] at h
    nlinarith [mul_nonneg (sq_nonneg s) (mul_nonneg (show 0 ≤ ρ by linarith) hs.le),
      sq_nonneg (s^2)]
  have h1 := bound 1 (by norm_num) le_rfl (fun i _ => by
    linarith [sqrtProfile_le_half (hminor i).1 (hminor i).2])
  have hop : 0 < (1-((m:ℝ)-41)*s)*s := by nlinarith
  have hcut : s < 1/((m:ℝ)-41) := by
    apply (lt_div_iff₀ hM).mpr
    have := (mul_pos_iff_of_pos_right hs).mp hop
    linarith
  have u : s < 1/3861 := by
    have h := (lt_div_iff₀ hM).mp hcut
    nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)-3902 by linarith) hs.le]
  refine ⟨hcut, ?_, ?_⟩
  · nlinarith [mul_nonneg hs.le (show 0 ≤ 1/3861-s by linarith)]
  · by_contra! no
    have nr (i : ℕ) (hi : i ≤ m) : minor i ≤ 9/20 := by
      rcases hi.lt_or_eq with hlt | rfl
      · exact no i hlt
      · dsimp [minor]; rw [closed]; exact no 0 (by omega)
    let ρ := Real.sqrt (99/100:ℝ)
    have hr2 : ρ^2 = 99/100 := Real.sq_sqrt (by norm_num)
    have hr0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρ : 3/4 ≤ ρ := by nlinarith [sq_nonneg (ρ-3/4)]
    have hρu : ρ ≤ 1 := by nlinarith [sq_nonneg (ρ-1), (sq_le_sq₀ hr0 (show (0:ℝ) ≤ 1 by norm_num)).mp (by nlinarith)]
    have hr := bound ρ hρ hρu (fun i hi => profileAwayFromMiddle (hminor i).1 (nr i hi))
    have complete : ρ*s-((m:ℝ)-41)*s^2 ≤ (99/100)/(4*((m:ℝ)-41)) := by
      apply (le_div_iff₀ (show (0:ℝ)<4*((m:ℝ)-41) by linarith)).mpr
      nlinarith [sq_nonneg (2*((m:ℝ)-41)*s-ρ)]
    have target : (99/100:ℝ)/(4*((m:ℝ)-41)) ≤ 1/(4*((m:ℝ)-2)) := by
      apply (div_le_div_iff₀ (show (0:ℝ)<4*((m:ℝ)-41) by linarith) hM2).mpr
      linarith
    change _ < Y at bad
    linarith

end OddCycleTail
