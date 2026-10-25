import LongTails.Proofs.GdConvex
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.MatrixPolarCharacterization

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSospDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalized_alignment (g z : E) :
    ‖g‖ - 2 * ‖g - z‖ ≤ ⟪g, ‖z‖⁻¹ • z⟫ := by
  let v := ‖z‖⁻¹ • z
  have hv := MatrixPolarCharacterization.normalized_norm_le_one z
  have hz : ⟪z, v⟫ = ‖z‖ := by
    rw [real_inner_comm]
    exact MatrixPolarCharacterization.normalized_inner z
  have he := real_inner_le_norm (z - g) v
  have he' := mul_le_mul_of_nonneg_left hv (norm_nonneg (z - g))
  rw [inner_sub_left, hz, norm_sub_rev z g] at he
  rw [norm_sub_rev z g] at he'
  have ht := norm_le_norm_add_norm_sub z g
  rw [norm_sub_rev z g] at ht
  dsimp only [v] at he
  linarith

lemma normalized_step_descent [CompleteSpace E] {f : E → ℝ} {g : E → E}
    {L h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x z : E) :
    f (x - h • (‖z‖⁻¹ • z)) ≤ f x - h * ‖g x‖ + 2 * h * ‖g x - z‖ + L * h ^ 2 / 2 := by
  let v := ‖z‖⁻¹ • z
  have hd := OracleTemplate.Gradient.smooth_upper_bound hg hLip x (x - h • v)
  have heq : x - h • v - x = -(h • v) := by abel
  rw [heq, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hh] at hd
  have ha := mul_le_mul_of_nonneg_left (normalized_alignment (g x) z) hh
  have hv := MatrixPolarCharacterization.normalized_norm_sq_le z
  have hquad := mul_le_mul_of_nonneg_left hv (show 0 ≤ L * h ^ 2 / 2 by positivity)
  dsimp only [v] at hd
  nlinarith

lemma symmetric_curvature_descent {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    {ρ s γ : ℝ} (hs : 0 ≤ s) (hγ : 0 ≤ γ) (hρs : ρ * s ≤ γ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (x v : E) (hv : ‖v‖ = 1) (hc : ⟪v, A x v⟫ ≤ -3 * γ / 2) :
    (f (x + s • v) + f (x - s • v)) / 2 ≤ f x - γ * s ^ 2 / 2 := by
  have ht := CubicRegularization.symmetric_taylor hf hg hLip x (s • v)
  simp only [map_smul, real_inner_smul_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs, hv, mul_one] at ht
  have hcurv := mul_le_mul_of_nonneg_left hc (sq_nonneg s)
  have herr := mul_le_mul_of_nonneg_right hρs (sq_nonneg s)
  nlinarith [(abs_le.mp ht).2, mul_nonneg hγ (sq_nonneg s)]

end LongTails.Proofs.HeavyTailedSospDescent
