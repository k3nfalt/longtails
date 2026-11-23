import LongTails.Proofs.CovarianceSoftCutLocalization
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyCutMoments

open LongTails.Setups.CovarianceBoundedConvex CovarianceSoftCutLocalization

lemma ball_shift (q : Params) (α : ℝ) (z : Space q) :
    MeasurePreserving (fun x => z+x) (targetMeasure q α 0) (targetMeasure q α z) := by
  let r := α / (4 * q.L)
  have hset : (fun x => z + x) ⁻¹' Metric.closedBall z r = Metric.closedBall 0 r := by
    ext x
    simp [Metric.mem_closedBall, dist_eq_norm]
  have h := (measurePreserving_add_left (volume : Measure (Space q)) z).restrict_preimage
    (Metric.isClosed_closedBall (x := z) (ε := r)).measurableSet
  rw [hset] at h
  have hv := (measurePreserving_add_left (volume : Measure (Space q)) z).measure_preimage
    (Metric.isClosed_closedBall (x := z) (ε := r)).measurableSet.nullMeasurableSet
  rw [hset] at hv
  change MeasurePreserving _ ((volume (Metric.closedBall 0 r))⁻¹ • _) _
  rw [hv]
  exact h.smul_measure _

lemma ball_rotate (q : Params) (α : ℝ) (U : Space q ≃ₗᵢ[ℝ] Space q) :
    MeasurePreserving U (targetMeasure q α 0) (targetMeasure q α 0) := by
  let r := α / (4 * q.L)
  have hset : U ⁻¹' Metric.closedBall 0 r = Metric.closedBall 0 r := by
    ext x
    simp [Metric.mem_closedBall]
  have h := U.measurePreserving.restrict_preimage
    (Metric.isClosed_closedBall (x := (0 : Space q)) (ε := r)).measurableSet
  rw [hset] at h
  exact h.smul_measure _

lemma directional_square (q : Params) (hL : 0 < q.L) {α : ℝ} (hα : 0 < α)
    (z u : Space q) (hu : ‖u‖ = 1) :
    (q.d : ℝ) * (∫ x, ⟪u,x-z⟫ ^ 2 ∂targetMeasure q α z) ≤ (α / (4*q.L))^2 := by
  let μ := targetMeasure q α (0 : Space q)
  let : IsProbabilityMeasure μ := targetMeasure_probability q hL α hα _
  have shift := (ball_shift q α z).integral_comp (Homeomorph.addLeft z).measurableEmbedding
    (fun x => ⟪u, x-z⟫ ^ 2)
  simp only [add_sub_cancel_left] at shift
  rw [← shift]
  have rot (i : Fin q.d) :
      (∫ x, ⟪u,x⟫ ^ 2 ∂μ) = ∫ x : Space q, (x i)^2 ∂μ := by
    let e : Space q := EuclideanSpace.single i 1
    let U := Submodule.reflection (ℝ ∙ (e - u))ᗮ
    have he : U e = u := Submodule.reflection_sub (by simp [e, hu])
    have hi := (ball_rotate q α U).integral_comp U.toHomeomorph.measurableEmbedding
      (fun x => ⟪u,x⟫ ^ 2)
    rw [← hi]
    apply integral_congr_ae
    filter_upwards with x
    rw [← he, U.inner_map_map]
    simp [e, PiLp.inner_apply]
  have hi (i : Fin q.d) : Integrable (fun x : Space q => (x i)^2) μ :=
    integrable_targetMeasure_of_continuous q hL α hα _ _ (by fun_prop)
  calc
    _ = ∑ i : Fin q.d, (∫ x : Space q, (x i)^2 ∂μ) := by simp only [← rot]; simp [μ]
    _ = ∫ x : Space q, ∑ i, (x i)^2 ∂μ := (integral_finsetSum _ (fun i _ => hi i)).symm
    _ ≤ ∫ _ : Space q, (α / (4*q.L))^2 ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ (fun i _ => hi i)) (integrable_const _)
      filter_upwards [targetMeasure_support q α (0 : Space q)] with x hx
      rw [sub_zero] at hx
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    _ = _ := by simp

end LongTails.Proofs.MintyCutMoments
