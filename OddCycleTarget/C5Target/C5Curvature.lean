import Mathlib

namespace FiveCertificate
open Set

private theorem weightedFour {X : Type*} [MetricSpace X] (g : X → X → ℝ → X)
    (cn : ∀ p q r t, t ∈ Icc (0:ℝ) 1 → dist (g p q t) r ^2 ≤
      (1-t)*dist p r^2 + t*dist q r^2 - t*(1-t)*dist p q^2)
    (x y z w : X) {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    t*(1-t)*dist x z^2 + s*(1-s)*dist y w^2 ≤
      (1-t)*(1-s)*dist x y^2 + t*(1-s)*dist y z^2 +
      t*s*dist z w^2 + (1-t)*s*dist w x^2 := by
  have p := cn x z (g y w s) t ht
  have a := cn y w x s hs
  have b := cn y w z s hs
  rw [dist_comm x (g y w s),dist_comm z (g y w s)] at p
  rw [dist_comm y x] at a
  rw [dist_comm w z] at b
  nlinarith only [p,sq_nonneg (dist (g x z t) (g y w s)),
    mul_le_mul_of_nonneg_left a (sub_nonneg.mpr ht.2),mul_le_mul_of_nonneg_left b ht.1]

private theorem homogeneousFour {a b c d e f : ℝ}
    (h : ∀ s t : ℝ, t ∈ Icc 0 1 → s ∈ Icc 0 1 →
      t*(1-t)*e^2 + s*(1-s)*f^2 ≤
      (1-t)*(1-s)*a^2+t*(1-s)*b^2+t*s*c^2+(1-t)*s*d^2)
    (u v w z : ℝ) (hu : 0<u) (hv : 0<v) (hw : 0<w) (hz : 0<z) :
    u*v*(w+z)^2*e^2 + w*z*(u+v)^2*f^2 ≤
      (u+v)*(w+z)*(u*w*a^2+v*w*b^2+v*z*c^2+u*z*d^2) := by
  have huv : 0<u+v := by positivity
  have hwz : 0<w+z := by positivity
  have frac {a b : ℝ} (ha : 0<a) (hb : 0<b) : b/(a+b) ∈ Icc 0 1 :=
    ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩
  have H := h _ _ (frac hu hv) (frac hw hz)
  convert mul_le_mul_of_nonneg_left H (sq_nonneg ((u+v)*(w+z))) using 1 <;>
    field_simp [huv.ne',hwz.ne'] <;> ring

private theorem ptolemyAlgebra {a b c d e f : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (h : ∀ s t : ℝ, t ∈ Icc 0 1 → s ∈ Icc 0 1 →
      t*(1-t)*e^2 + s*(1-s)*f^2 ≤
      (1-t)*(1-s)*a^2+t*(1-s)*b^2+t*s*c^2+(1-t)*s*d^2) :
    e*f ≤ a*c+b*d := by
  have M : 0<a*b*c*d := by positivity
  have R := homogeneousFour h (b*c) (a*d) (c*d) (a*b) (by positivity) (by positivity) (by positivity) (by positivity)
  have B : (c*d+a*b)^2*e^2 + (b*c+a*d)^2*f^2 ≤ 2*(b*c+a*d)*(c*d+a*b)*(a*c+b*d) := by
    apply (mul_le_mul_iff_right₀ M).mp
    linear_combination R
  have W : 0 < 2*(b*c+a*d)*(c*d+a*b) := by positivity
  apply (mul_le_mul_iff_right₀ W).mp
  nlinarith only [B,sq_nonneg ((c*d+a*b)*e-(b*c+a*d)*f)]

/-- CAT(0) squared geodesic comparison implies Ptolemy, including repeated labels. -/
theorem ptolemyOfCN {X : Type*} [MetricSpace X] (g : X → X → ℝ → X)
    (cn : ∀ p q r t, t ∈ Icc (0:ℝ) 1 → dist (g p q t) r ^2 ≤
      (1-t)*dist p r^2+t*dist q r^2-t*(1-t)*dist p q^2)
    (x y z w : X) :
    dist x z * dist y w ≤ dist x y * dist z w + dist w x * dist y z := by
  by_cases hxy : x=y
  · subst y; simp [dist_comm,mul_comm]
  by_cases hyz : y=z
  · subst z; simp [dist_comm,mul_comm]
  by_cases hzw : z=w
  · subst w; simp [dist_comm,mul_comm]
  by_cases hwx : w=x
  · subst w; simp [dist_comm,mul_comm]
  rw [mul_comm (dist w x)]
  exact ptolemyAlgebra (dist_pos.mpr hxy) (dist_pos.mpr hyz) (dist_pos.mpr hzw) (dist_pos.mpr hwx)
    (fun _ _ ht hs => weightedFour g cn x y z w ht hs)

#print axioms ptolemyOfCN
end FiveCertificate
