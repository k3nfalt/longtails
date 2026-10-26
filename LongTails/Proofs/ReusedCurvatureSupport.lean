import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.GuardedMetricDescent
import LongTails.Algorithms.QuarticMetricStage

namespace LongTails.Proofs.ReusedCurvatureSupport

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_taylor_lower {f : E → ℝ} {g : E → E}
    {A : E → E →L[ℝ] E} {H : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (c v d : E) :
    ⟪d, A c d⟫ / 2 - H * (‖v - c‖ / 2 + ‖d‖ / 6) * ‖d‖ ^ 2 ≤
      f (v + d) - f v - ⟪g v, d⟫ := by
  have ht := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip v d)).1
  have hn := ((A c - A v).le_opNorm d).trans
    (mul_le_mul_of_nonneg_right (hLip c v) (norm_nonneg d))
  have hi := real_inner_le_norm d ((A c - A v) d)
  have hb := mul_le_mul_of_nonneg_left hn (norm_nonneg d)
  simp only [sub_apply, inner_sub_right, norm_sub_rev c v] at hi hb
  nlinarith

lemma curvature_from_failed_model {q b r α μ δ e n : ℝ}
    (hα : 0 < α) (hμ : 0 ≤ μ) (hμ₁ : μ < 1) (hn : 0 ≤ n)
    (hscale : 3 * μ * δ + 2 * e ≤ α)
    (hlower : q / 2 - e * n ≤ r) (hB : b ≤ q + 3 * δ * n)
    (hfailure : r < μ / 2 * b - α * n) :
    q < -α * n := by
  have hb := mul_le_mul_of_nonneg_left hB hμ
  have he := mul_le_mul_of_nonneg_right hscale hn
  have hbase : (1 - μ) * q < -α * n := by nlinarith
  have hq : q < 0 := by
    by_contra hh
    have hm := mul_nonneg (by linarith : 0 ≤ 1 - μ) (le_of_not_gt hh)
    have ha := mul_nonneg hα.le hn
    linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hμ hq.le
  nlinarith

lemma failed_support_center_curvature
    {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E} {H δ : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (p : LongTails.Algorithms.QuarticMetricStage.Parameters E)
    (u v : LongTails.Algorithms.QuarticMetricStage.Point E)
    (hu : u.value = f u.x) (hv : v.value = f v.x) (hgv : v.gradient = g v.x)
    (hα : 0 < p.α) (hμ : 0 ≤ p.μ) (hμ₁ : p.μ < 1)
    (hB : ‖p.S (u.x - v.x)‖ ^ 2 ≤
      ⟪u.x - v.x, A p.center.x (u.x - v.x)⟫ + 3 * δ * ‖u.x - v.x‖ ^ 2)
    (hscale : 3 * p.μ * δ + 2 * (H * (‖v.x - p.center.x‖ / 2 + ‖u.x - v.x‖ / 6)) ≤ p.α)
    (hfail : ¬LongTails.Algorithms.QuarticMetricStage.supports p u v) :
    ⟪u.x - v.x, A p.center.x (u.x - v.x)⟫ < -p.α * ‖u.x - v.x‖ ^ 2 := by
  have ht := centered_taylor_lower hf hg hLip p.center.x v.x (u.x - v.x)
  rw [add_sub_cancel] at ht
  have hd := GuardedMetricDescent.regularization_difference p.α u.value v.value p.center.x u.x v.x v.gradient
  change ¬(LongTails.Algorithms.QuarticMetricStage.value p v +
    ⟪LongTails.Algorithms.QuarticMetricStage.gradient p v, u.x - v.x⟫ +
    p.μ / 2 * ‖p.S (u.x - v.x)‖ ^ 2 ≤ LongTails.Algorithms.QuarticMetricStage.value p u) at hfail
  have hf' := lt_of_not_ge hfail
  change LongTails.Algorithms.QuarticMetricStage.value p u -
    LongTails.Algorithms.QuarticMetricStage.value p v -
    ⟪LongTails.Algorithms.QuarticMetricStage.gradient p v, u.x - v.x⟫ = _ at hd
  rw [hu, hv, hgv] at hd
  exact curvature_from_failed_model hα hμ hμ₁ (sq_nonneg _) hscale ht hB (by linarith)

end LongTails.Proofs.ReusedCurvatureSupport
