import LongTails.Algorithms.RelativeCurvatureSearch
import LongTails.Proofs.ReusedCurvatureCertificate

namespace LongTails.Proofs.RelativeCurvatureProducts

open OracleTemplate LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.RelativeCurvatureSearch
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma difference_step_pos (D : E →L[ℝ] E) {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ) (v : E) :
    0 < differenceStep D H τ v := by unfold differenceStep; positivity

omit [FiniteDimensional ℝ E] in
lemma difference_step_error (D : E →L[ℝ] E) {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ) (v : E) :
    ‖v‖ * (H * differenceStep D H τ v * ‖D‖ ^ 3) ≤ τ / 4 := by
  have hh := difference_step_pos D hH hτ v
  have hd : 4 * H * (1 + ‖D‖ ^ 3) * (1 + ‖v‖) * differenceStep D H τ v = τ := by
    unfold differenceStep
    field_simp
  have hb : ‖D‖ ^ 3 * ‖v‖ ≤ (1 + ‖D‖ ^ 3) * (1 + ‖v‖) := by
    nlinarith [norm_nonneg v, pow_nonneg (norm_nonneg D) 3]
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hH.le hh.le)
  nlinarith

lemma product_error {g : E → E} {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hg : Differentiable ℝ g)
    (hLip : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖)
    (D : E →L[ℝ] E) (x : Point E) (hx : x.gradient = g x.x)
    (O : Fin 2 × E → Reply E) (f : E → ℝ)
    (hO : ∀ y, O (0, y) = Sum.inl (f y, g y)) (v : E) :
    ‖(product D x H τ v).eval O - D.adjoint (fderiv ℝ g x.x (D v))‖ ≤ τ / 4 := by
  let h := differenceStep D H τ v
  let u := ‖v‖⁻¹ • v
  have hh : 0 < h := difference_step_pos D hH hτ v
  simp only [product, QueryPlan.eval, hO, readPoint, hx]
  change ‖‖v‖ • D.adjoint (h⁻¹ • (g (x.x + h • D u) - g x.x)) -
    D.adjoint (fderiv ℝ g x.x (D v))‖ ≤ τ / 4
  by_cases hv : v = 0
  · subst v
    simp [u]
    positivity
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hn]
  have hscale : ‖v‖ • u = v := by simp [u, smul_smul, hn]
  have he : D.adjoint (fderiv ℝ g x.x (D v)) =
      ‖v‖ • D.adjoint (fderiv ℝ g x.x (D u)) := by
    nth_rw 1 [← hscale]
    simp only [map_smul]
  rw [he, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_norm]
  have hb := ReusedCurvatureCertificate.adjoint_finite_difference_error hH.le hh hg hLip D x.x u
  rw [hu] at hb
  simp only [one_pow, mul_one] at hb
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg v)).trans (difference_step_error D hH hτ v)

end LongTails.Proofs.RelativeCurvatureProducts
