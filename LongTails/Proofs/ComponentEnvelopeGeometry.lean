import LongTails.Proofs.GdConvex

open InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.ComponentEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_gradient_gap {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {u : E} (hmin : ∀ x, f u ≤ f x) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (f x - f u) := by
  have hd := Gradient.descent hL hg hlip x
  have hm := hmin (x - (1 / L) • g x)
  have hh : ‖g x‖ ^ 2 / (2 * L) ≤ f x - f u := by linarith
  nlinarith [(div_le_iff₀ (by positivity : 0 < 2 * L)).mp hh]

lemma smooth_displacement_gap {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {u : E} (hmin : ∀ x, f u ≤ f x) (w d : E) :
    f (w + d) - f u ≤ 2 * (f w - f u) + L * ‖d‖ ^ 2 := by
  have hs := smooth_gradient_gap hL hg hlip hmin w
  have hu := Gradient.smooth_upper_bound hg hlip w (w + d)
  simp only [add_sub_cancel_left] at hu
  have hi := real_inner_le_norm (g w) d
  have hy := sq_nonneg (‖g w‖ - L * ‖d‖)
  nlinarith

lemma smooth_mixed_query_gap {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {u : E} (hmin : ∀ x, f u ≤ f x) (w z : E) (τ : ℝ) :
    f ((1 - τ) • w + τ • z) - f u ≤
      2 * (f w - f u) + L * τ ^ 2 * ‖z - w‖ ^ 2 := by
  have h := smooth_displacement_gap hL hg hlip hmin w (τ • (z - w))
  have he : w + τ • (z - w) = (1 - τ) • w + τ • z := by module
  rw [he] at h
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using h

lemma interpolated_step_distance {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {u : E} (hmin : ∀ x, f u ≤ f x) (x : E) :
    ‖x - (1 / (2 * L)) • g x - u‖ ^ 2 ≤
      ‖x - u‖ ^ 2 - (f x - f u) / (2 * L) := by
  have hs := smooth_gradient_gap hL hg hlip hmin x
  have hc' := Gradient.convex_support hc hg x u
  have he : x - (1 / (2 * L)) • g x - u =
      (x - u) - (1 / (2 * L)) • g x := by module
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right]
  have hi : ⟪x - u, g x⟫ = -⟪g x, u - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  rw [hi]
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * L ^ 2 by positivity)).mp
  field_simp
  nlinarith


end OracleTemplate.ComponentEnvelope
