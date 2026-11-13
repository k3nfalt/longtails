import LongTails.Proofs.GeneralizedSmoothShieldGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothShieldBounds

open GeneralizedSmoothShield GeneralizedSmoothShieldCalculus GeneralizedSmoothShieldGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_control (f : E → ℝ) (g : E → E) (a S r : ℝ)
    (ha : 0 < a) (hS : 0 < S) (har : a * r ≤ S)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z x : E) (hz : f z = 0) (hzr : ‖z‖ ≤ r) (hf0 : 0 ≤ f x)
    (hf : f x ≤ S * ‖x‖ + S ^ 2 / a) :
    mixing f a (16 * S / a) (64 * S ^ 2 / a) x * ‖g x‖ ≤
      2 * ‖field f g a (16 * S / a) (64 * S ^ 2 / a) x‖ := by
  have hT : 0 < 64 * S ^ 2 / a := by positivity
  have hθ := mixing_bounds f a (16 * S / a) (64 * S ^ 2 / a) x
  by_cases hx : |f x - wall a (16 * S / a) x| ≤ 64 * S ^ 2 / a
  · have hr := (transition_bounds f a S ha hS x hf0 hf hx).1
    have hrad : 2 * r ≤ ‖x‖ := by
      apply (mul_le_mul_iff_of_pos_left ha).mp
      have hh := (div_le_iff₀ ha).mp hr
      nlinarith only [hh, har, hS]
    have hs := OracleTemplate.Gradient.convex_support hc hg x z
    have hmodel : f x + ⟪g x, z - x⟫ ≤ f z := by linarith
    have hmin : f z ≤ f x := by rw [hz]; exact hf0
    have hangle := radial_angle_of_minimizer f (g x) x z r hmodel hmin hzr hrad
    have hm := mul_le_mul_of_nonneg_left hangle ha.le
    have hscaled : -(‖g x‖ * ‖a • x‖) ≤ 2 * ⟪g x, a • x⟫ := by
      rw [norm_smul, Real.norm_of_nonneg ha.le, real_inner_smul_right]
      nlinarith only [hm]
    have hw := weighted_norm_control (g x) (a • x) _ hθ.1 hθ.2 hscaled
    rw [← field_convex_combination] at hw
    have hn := mul_nonneg (sub_nonneg.mpr hθ.2) (norm_nonneg (a • x))
    linarith only [hw, hn]
  · rcases (mixing_outside f a (16 * S / a) (64 * S ^ 2 / a) hT x hx).1 with h0 | h1
    · rw [h0, zero_mul]
      positivity
    · have he : field f g a (16 * S / a) (64 * S ^ 2 / a) x = g x := by
        rw [field, h1, one_smul]
        abel
      rw [h1, he, one_mul]
      linarith [norm_nonneg (g x)]

omit [CompleteSpace E] in
lemma cross_curvature_bound (f : E → ℝ) (g : E → E) (a S : ℝ)
    (ha : 0 < a) (hS : 0 < S) (x : E) (hgn : ‖g x‖ ≤ S) (hf0 : 0 ≤ f x)
    (hf : f x ≤ S * ‖x‖ + S ^ 2 / a) :
    mixingDerivative f a (16 * S / a) (64 * S ^ 2 / a) x * ‖g x - a • x‖ ^ 2 ≤ 8 * a := by
  have hT : 0 < 64 * S ^ 2 / a := by positivity
  have hχ := mixingDerivative_bounds f a (16 * S / a) (64 * S ^ 2 / a) hT x
  by_cases hx : |f x - wall a (16 * S / a) x| ≤ 64 * S ^ 2 / a
  · have hr := (transition_bounds f a S ha hS x hf0 hf hx).2
    have hn : ‖g x - a • x‖ ≤ 22 * S := by
      have hh := norm_sub_le (g x) (a • x)
      rw [norm_smul, Real.norm_of_nonneg ha.le] at hh
      have ht := (le_div_iff₀ ha).mp hr
      nlinarith only [hh, ht, hgn]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hh := mul_le_mul hχ.2 hs (sq_nonneg _) (show 0 ≤ 1 / (64 * S ^ 2 / a) by positivity)
    have he : 1 / (64 * S ^ 2 / a) * (22 * S) ^ 2 = 121 * a / 16 := by field_simp; ring
    rw [he] at hh
    linarith
  · rw [(mixing_outside f a (16 * S / a) (64 * S ^ 2 / a) hT x hx).2, zero_mul]
    positivity

lemma curvature_bound (f : E → ℝ) (g : E → E) (L₀ L₁ a S r : ℝ)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (ha : 0 < a) (hS : 0 < S) (har : a * r ≤ S)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g) (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L₀ + L₁ * ‖g x‖)
    (z x : E) (hz : f z = 0) (hzr : ‖z‖ ≤ r) (hgn : ‖g x‖ ≤ S) (hf0 : 0 ≤ f x)
    (hf : f x ≤ S * ‖x‖ + S ^ 2 / a) :
    ‖fderiv ℝ (field f g a (16 * S / a) (64 * S ^ 2 / a)) x‖ ≤
      L₀ + 10 * a + 2 * L₁ * ‖field f g a (16 * S / a) (64 * S ^ 2 / a) x‖ := by
  have hθ := mixing_bounds f a (16 * S / a) (64 * S ^ 2 / a) x
  have hd := field_derivative_norm_bound f g a (16 * S / a) (64 * S ^ 2 / a)
    ha.le (by positivity) x _ (hg x) (hgd x).hasFDerivAt
  have hcross := cross_curvature_bound f g a S ha hS x hgn hf0 hf
  have hgrad := gradient_control f g a S r ha hS har hc hg z x hz hzr hf0 hf
  have hcurv := mul_le_mul_of_nonneg_left (hH x) hθ.1
  have hzero := mul_le_mul_of_nonneg_right hθ.2 hL₀
  have ha' := mul_le_mul_of_nonneg_right hθ.2 ha.le
  have hlinear := mul_le_mul_of_nonneg_left hgrad hL₁
  nlinarith only [hd, hcross, hcurv, hzero, ha', hlinear]

end LongTails.Proofs.GeneralizedSmoothShieldBounds
