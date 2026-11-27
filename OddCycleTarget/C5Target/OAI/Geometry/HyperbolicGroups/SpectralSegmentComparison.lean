import OddCycleTarget.C5Target.OAI.Geometry.HyperbolicGroups.Basic

/-! Six metric declarations extracted with their original definitions and
proofs from IndexedFillingValue.lean at openai/math 92b516e (lines
6870–6917, 6928–6934 and 7418–7465). -/

namespace OAI.HyperbolicObstruction
open Set Real
namespace CurvatureComparison

lemma midpoint_nonpos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      f ((s+t)/2) ≤ (f s+f t)/2) (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0) :
    ∀ t ∈ Icc (0:ℝ) 1, f t ≤ 0 := by
  intro t ht
  by_contra! hpos
  let ε := f t / 2
  have he : 0 < ε := by dsimp [ε]; positivity
  let g : ℝ → ℝ := fun s => f s+ε*s^2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hg
  have hlarge : ε < g x := by
    have h := hm ht
    have hn : 0 ≤ ε*t^2 := mul_nonneg he.le (sq_nonneg t)
    dsimp [g,ε] at *
    linarith
  have hx0 : 0 < x := by
    by_contra hh
    have heq : x=0 := le_antisymm (not_lt.mp hh) hx.1
    subst x
    simp only [g,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hlarge
    linarith
  have hx1 : x < 1 := by
    by_contra hh
    have heq : x=1 := le_antisymm hx.2 (not_lt.mp hh)
    subst x
    simp only [g,one_pow,mul_one] at hlarge
    linarith
  let r := min x (1-x) / 2
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min hx0 (sub_pos.mpr hx1)) (by norm_num)
  have hrx : r ≤ x := by
    have h := min_le_left x (1-x)
    dsimp [r]
    linarith
  have hr1 : r ≤ 1-x := by
    have h := min_le_right x (1-x)
    dsimp [r]
    linarith
  have hl : x-r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hu : x+r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hcv := hmid (x-r) hl (x+r) hu
  rw [show ((x-r)+(x+r))/2=x by ring] at hcv
  have hml := hm hl
  have hmu := hm hu
  have hp : 0 < ε*r^2 := mul_pos he (sq_pos_of_pos hr)
  dsimp [g] at hml hmu
  nlinarith

end CurvatureComparison
variable {X : Type*} [MetricSpace X]

lemma IsSegment.continuousOn {γ : ℝ → X} {x y : X} (h : IsSegment γ x y) :
    ContinuousOn γ (Icc 0 1) := by
  apply LipschitzOnWith.continuousOn (K := ⟨dist x y,dist_nonneg⟩)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [h.2.2 s hs t ht,Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

lemma IsSegment.reparam {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsSegment (fun u => γ ((1-u)*s+u*t)) (γ s) (γ t) := by
  refine ⟨by simp,by simp,?_⟩
  intro u hu v hv
  have hm (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : (1-a)*s+a*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [ha.2]) hs.1) (mul_nonneg ha.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ha.1 (sub_nonneg.mpr ht.2)]
  rw [h.2.2 _ (hm u hu) _ (hm v hv),h.2.2 s hs t ht]
  rw [show (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) by ring,abs_mul,abs_sub_comm t s]
  ring

lemma IsSegment.dist_from_source {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : dist x (γ t)=t*dist x y := by
  have hh := h.2.2 0 (by norm_num) t ht
  simpa only [h.1,zero_sub,abs_neg,abs_of_nonneg ht.1] using hh

lemma catZero_of_segment_midpoint (g : IsGeodesic X)
    (h : ∀ {γ : ℝ → X} {x y : X}, IsSegment γ x y → ∀ z : X,
      dist z (γ (1/2))^2 ≤ (dist z x^2+dist z y^2)/2-dist x y^2/4) : CATZero X := by
  intro x y
  obtain ⟨γ,hγ⟩ := g x y
  refine ⟨γ,hγ,fun z t ht => ?_⟩
  let F : ℝ → ℝ := fun s => dist z (γ s)^2-
    ((1-s)*dist z x^2+s*dist z y^2-s*(1-s)*dist x y^2)
  have hF : ContinuousOn F (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)).pow 2
    · fun_prop
  have hf0 : F 0≤0 := by simp [F,hγ.1]
  have hf1 : F 1≤0 := by simp [F,hγ.2.1]
  have hm : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, F ((a+b)/2)≤(F a+F b)/2 := by
    intro a ha b hb
    have hh := h (hγ.reparam ha hb) z
    simp only [show (1-(1/2:ℝ))*a+(1/2)*b=(a+b)/2 by ring] at hh
    rw [hγ.2.2 a ha b hb,mul_pow,sq_abs] at hh
    dsimp [F]
    nlinarith
  have hh := CurvatureComparison.midpoint_nonpos hF hm hf0 hf1 t ht
  dsimp [F] at hh
  linarith

/-- Radial comparison for any two constant-speed geodesics with common start. -/
def RadialBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ (o x y : X) (α β : ℝ → X), IsSegment α o x → IsSegment β o y →
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) ≤ t*dist x y

end OAI.HyperbolicObstruction
