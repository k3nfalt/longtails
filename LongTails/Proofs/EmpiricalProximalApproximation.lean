import LongTails.Proofs.StrongGrowthBatchProx

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalApproximation

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma population_error {g h : E → E} {L μ : ℝ} (hμ : 0 ≤ μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v y z : E}
    (hy : g y = μ • (v - y)) (hz : h z = μ • (v - z)) :
    ‖g z - h z‖ ≤ (L + μ) * ‖z - y‖ := by
  have he : g z - h z = (g z - g y) + μ • (z - y) := by
    rw [hy, hz]
    module
  rw [he]
  have hn := norm_add_le (g z - g y) (μ • (z - y))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hn
  nlinarith [hlip z y]

omit [CompleteSpace E] in
lemma residual_bound {g : E → E} {L μ : ℝ} (hμ : 0 ≤ μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v z : E}
    (hz : g z = μ • (v - z)) (w : E) :
    ‖g w + μ • (w - v)‖ ≤ (L + μ) * ‖w - z‖ := by
  have he : g w + μ • (w - v) = (g w - g z) + μ • (w - z) := by
    rw [hz]
    module
  rw [he]
  have hn := norm_add_le (g w - g z) (μ • (w - z))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hn
  nlinarith [hlip w z]

lemma generalization_change {f h : E → ℝ} {g q : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hq : ∀ x, HasGradientAt h (q x) x)
    (hc : ConvexOn ℝ univ h)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z w : E) :
    f w - h w ≤ f z - h z + ‖g z - q z‖ * ‖w - z‖ + L / 2 * ‖w - z‖ ^ 2 := by
  have hu := Gradient.smooth_upper_bound hg hlip z w
  have hl := Gradient.convex_support hc hq z w
  have hi := real_inner_le_norm (g z - q z) (w - z)
  rw [inner_sub_left] at hi
  linarith

lemma generalization_change_quadratic {f h : E → ℝ} {g q : E → E} {L μ : ℝ}
    (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hq : ∀ x, HasGradientAt h (q x) x) (hc : ConvexOn ℝ univ h)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v y z : E}
    (hy : g y = μ • (v - y)) (hz : q z = μ • (v - z)) (w : E) :
    f w - h w ≤ f z - h z + μ / 2 * ‖z - y‖ ^ 2 +
      ((L + μ) ^ 2 / (2 * μ) + L / 2) * ‖w - z‖ ^ 2 := by
  have he := generalization_change hg hq hc hlip z w
  have hp := population_error hμ.le hlip hy hz
  have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg (w - z))
  have hyoung : (L + μ) * ‖z - y‖ * ‖w - z‖ ≤
      μ / 2 * ‖z - y‖ ^ 2 + (L + μ) ^ 2 / (2 * μ) * ‖w - z‖ ^ 2 := by
    have hs := sq_nonneg (μ * ‖z - y‖ - (L + μ) * ‖w - z‖)
    have hden : 2 * μ ≠ 0 := by positivity
    have hid : 2 * μ * ((L + μ) ^ 2 / (2 * μ)) = (L + μ) ^ 2 := by
      field_simp
    nlinarith
  linarith

lemma scaled_generalization_change {f h : E → ℝ} {g q : E → E} {L μ : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hq : ∀ x, HasGradientAt h (q x) x) (hc : ConvexOn ℝ univ h)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v y z : E}
    (hy : g y = μ • (v - y)) (hz : q z = μ • (v - z)) (w : E) :
    μ * (f w - h w) ≤ μ * (f z - h z) + μ ^ 2 / 2 * ‖z - y‖ ^ 2 +
      (L + μ) ^ 2 * ‖w - z‖ ^ 2 := by
  have he := generalization_change_quadratic hμ hg hq hc hlip hy hz w
  have hm := mul_le_mul_of_nonneg_left he hμ.le
  have hid : μ * ((L + μ) ^ 2 / (2 * μ)) = (L + μ) ^ 2 / 2 := by field_simp
  have hcoef : μ * ((L + μ) ^ 2 / (2 * μ) + L / 2) ≤ (L + μ) ^ 2 := by
    rw [mul_add, hid]
    nlinarith [mul_nonneg hL hμ.le, sq_nonneg L, sq_nonneg μ]
  have hs := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w - z‖)
  nlinarith only [hm, hs]

omit [CompleteSpace E] in
lemma scaled_residual_bound {g : E → E} {L μ : ℝ} (hμ : 0 < μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v z : E}
    (hz : g z = μ • (v - z)) (w : E) :
    μ ^ 2 * ‖μ⁻¹ • g w + w - v‖ ^ 2 ≤ (L + μ) ^ 2 * ‖w - z‖ ^ 2 := by
  have he : μ • (μ⁻¹ • g w + w - v) = g w + μ • (w - v) := by
    rw [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    module
  have hs := pow_le_pow_left₀ (norm_nonneg _) (residual_bound hμ.le hlip hz w) 2
  rw [← he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow] at hs
  exact hs

lemma regularized_initial_gap {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hμ : 0 < μ) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (v z : E) :
    2 * μ * (f v - regularized f μ v z) ≤ ‖g v‖ ^ 2 := by
  have hs := regularized_support hc hg μ v v z
  simp only [regularized, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, smul_zero] at hs
  have hi := real_inner_le_norm (-g v) (z - v)
  rw [inner_neg_left, norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * μ by positivity)
  have hm' := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * μ by positivity)
  unfold regularized
  nlinarith [sq_nonneg (‖g v‖ - μ * ‖z - v‖)]

omit [CompleteSpace E] in
lemma gradient_at_center {g : E → E} {L μ : ℝ} (hμ : 0 ≤ μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {v y : E}
    (hy : g y = μ • (v - y)) : ‖g v‖ ≤ (L + μ) * ‖v - y‖ := by
  have hn := norm_sub_le_norm_sub_add_norm_sub (g v) (g y) 0
  simp only [sub_zero] at hn
  rw [hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at hn
  rw [← hy] at hn
  nlinarith [hlip v y]

end LongTails.Proofs.EmpiricalProximalApproximation
