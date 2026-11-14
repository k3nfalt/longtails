import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothMollification
import LongTails.Proofs.GdConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SmoothConvexMollification

open CompactMollification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma field_continuous (g : E → E) (L : ℝ)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) : Continuous g := by
  have h : LipschitzWith (Real.toNNReal L) g := LipschitzWith.of_dist_le'
    (fun x y => by
      simpa [dist_eq_norm] using hl x y)
  exact h.continuous

lemma average_field_lipschitz (φ : ContDiffBump (0 : E)) (g : E → E)
    (L : ℝ) (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖average φ g x - average φ g y‖ ≤ L * ‖x - y‖ := by
  have hc := field_continuous g L hl
  have hx := average_integrable φ g hc x
  have hy := average_integrable φ g hc y
  unfold CompactMollification.average
  rw [← integral_sub hx hy]
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun u => g (x - noise φ u) - g (y - noise φ u))
      (probability φ : Measure E) := hx.sub hy
  have hp (u : E) : ‖g (x - noise φ u) - g (y - noise φ u)‖ ≤ L * ‖x - y‖ := by
    simpa only [sub_sub_sub_cancel_right] using hl (x - noise φ u) (y - noise φ u)
  have hm := integral_mono hi.norm (integrable_const (L * ‖x - y‖)) hp
  simp only [integral_const, probReal_univ, one_smul] at hm
  exact hm

lemma average_gradient (φ : ContDiffBump (0 : E)) (f : E → ℝ) (g : E → E)
    (L : ℝ) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E) :
    HasGradientAt (average φ f) (average φ g x) x := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  apply GeneralizedSmoothMollification.average_hasGradient_of_remainder
    (probability φ) (noise φ) f g (L / 2)
    (average_integrable φ f hf) (average_integrable φ g (field_continuous g L hl)) _ x
  intro y z
  constructor
  · linarith [OracleTemplate.Gradient.convex_support hc hg y z]
  · linarith [OracleTemplate.Gradient.smooth_upper_bound hg hl y z]

lemma average_field_differentiable (φ : ContDiffBump (0 : E)) (g : E → E)
    (L : ℝ) (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    Differentiable ℝ (average φ g) :=
  (average_contDiff φ g (field_continuous g L hl) 1).differentiable (by norm_num)

lemma average_curvature (φ : ContDiffBump (0 : E)) (g : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖fderiv ℝ (average φ g) x‖ ≤ L := by
  apply GeneralizedSmoothMollification.derivative_bound_of_quadratic_increment
    (average φ g) x _ L 0 (average_field_differentiable φ g L hl x).hasFDerivAt hL (by norm_num)
  intro y
  simpa using average_field_lipschitz φ g L hl y x

lemma average_at_minimum (φ : ContDiffBump (0 : E)) (f : E → ℝ) (g : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z : E) (hz : f z = 0) (hgz : g z = 0) :
    average φ f z ≤ L / 2 * φ.rOut ^ 2 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hp (u : E) : f (z - noise φ u) ≤ L / 2 * φ.rOut ^ 2 := by
    have hs := OracleTemplate.Gradient.smooth_upper_bound hg hl z (z - noise φ u)
    have hn := noise_norm φ u
    have hn2 := pow_le_pow_left₀ (norm_nonneg (noise φ u)) hn 2
    simp only [hz, hgz, inner_zero_left, zero_add, sub_sub_cancel_left, norm_neg] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hn2 (by positivity))
  have hh := integral_mono (average_integrable φ f hf z)
    (integrable_const (L / 2 * φ.rOut ^ 2)) hp
  simp only [integral_const, probReal_univ, one_smul] at hh
  exact hh

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_minimum_in_ball (f : E → ℝ) (R : ℝ) (hf : Continuous f)
    (z : E) (hz : ‖z‖ ≤ R) (hout : ∀ x, R < ‖x‖ → f z ≤ f x) :
    ∃ xstar, ‖xstar‖ ≤ R ∧ IsMinOn f univ xstar ∧ f xstar ≤ f z := by
  have hzmem : z ∈ closedBall (0 : E) R := by simpa only [mem_closedBall, dist_zero_right] using hz
  obtain ⟨xstar, hx, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨z, hzmem⟩ hf.continuousOn
  have hxnorm : ‖xstar‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  refine ⟨xstar, hxnorm, ?_, hmin hzmem⟩
  intro x _
  by_cases h : ‖x‖ ≤ R
  · exact hmin (by simpa only [mem_closedBall, dist_zero_right] using h)
  · exact (hmin hzmem).trans (hout x (lt_of_not_ge h))

end LongTails.Proofs.SmoothConvexMollification
