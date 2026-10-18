import LongTails.Proofs.QuarticEscapeGeometry
import LongTails.Proofs.GuardedMetricDescent

namespace LongTails.Proofs.QuarticWitnessGeometry

open scoped RealInnerProductSpace
open LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma failed_support {f : E → ℝ} (S : E ≃L[ℝ] E) (c u v : E) {α β μ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1 / 8)
    (htune : μ * β ≤ α / 64)
    (hlower : 7 / 16 * ‖S (u - v)‖ ^ 2 - 4 * β * ‖u - v‖ ^ 2 ≤
      f u - f v - ⟪gradient f v, u - v⟫)
    (hfailure : regularizedValue α c u (f u) < regularizedValue α c v (f v) +
      ⟪regularizedGradient α c v (gradient f v), u - v⟫ + μ / 2 * ‖S (u - v)‖ ^ 2) :
    u ≠ v ∧ ‖S (u - v)‖ ^ 2 ≤ 20 * β * ‖u - v‖ ^ 2 ∧
      f u - f v - ⟪gradient f v, u - v⟫ ≤ -α * ‖u - v‖ ^ 2 / 2 := by
  have hne : u ≠ v := by
    intro he
    subst u
    simp at hfailure
  have hid := GuardedMetricDescent.regularization_difference α (f u) (f v) c u v (gradient f v)
  have hf' : f u - f v - ⟪gradient f v, u - v⟫ + α * ‖u - v‖ ^ 2 <
      μ / 2 * ‖S (u - v)‖ ^ 2 := by linarith
  exact ⟨hne, GuardedMetricSupport.failed_support_conversion (sq_nonneg _) (sq_nonneg _)
    hα hβ hμ hμ₁ htune hlower hf'⟩

omit [FiniteDimensional ℝ E] in
lemma direction_geometry (u v : E) (hne : u ≠ v) :
    0 < ‖u - v‖ ∧ ‖‖u - v‖⁻¹ • (u - v)‖ = 1 ∧
      v + ‖u - v‖ • (‖u - v‖⁻¹ • (u - v)) = u := by
  have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  refine ⟨hn, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    abel

omit [FiniteDimensional ℝ E] in
lemma direction_metric (S : E ≃L[ℝ] E) (u v : E) {β : ℝ} (hne : u ≠ v)
    (hh : ‖S (u - v)‖ ^ 2 ≤ 20 * β * ‖u - v‖ ^ 2) :
    ‖S (‖u - v‖⁻¹ • (u - v))‖ ^ 2 ≤ 20 * β := by
  have hn := (direction_geometry u v hne).1
  rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hs := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖u - v‖⁻¹)
  convert hs using 1
  field_simp

lemma escape_values_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L α η : ℝ} (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (u v : E) (hne : u ≠ v)
    (hdeficit : f u - f v - ⟪gradient f v, u - v⟫ ≤ -α * ‖u - v‖ ^ 2 / 2)
    (hshort : 3 * L * ‖u - v‖ ^ 2 ≤ α / 4) (hη : L * η ^ 2 ≤ α / 16) :
    min (min (f (escapePoints η u v 0)) (f (escapePoints η u v 1)))
      (min (f (escapePoints η u v 2)) (f (escapePoints η u v 3))) ≤
      max (f u) (f v) - α * η ^ 2 / 4 := by
  let δ := ‖u - v‖
  let e := δ⁻¹ • (u - v)
  obtain ⟨hδ, he, hpoint⟩ := direction_geometry u v hne
  have hevec : δ • e = u - v := by
    dsimp [e, δ]
    rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  have hinner : ⟪gradient f v, e⟫ * δ = ⟪gradient f v, u - v⟫ := by
    calc
      _ = δ * ⟪gradient f v, e⟫ := mul_comm _ _
      _ = ⟪gradient f v, δ • e⟫ := (real_inner_smul_right _ _ _).symm
      _ = _ := congrArg (fun w => ⟪gradient f v, w⟫) hevec
  have hdef : f (v + δ • e) - f v - ⟪gradient f v, e⟫ * δ ≤ -α * δ ^ 2 / 2 := by
    simpa only [show v + δ • e = u from hpoint, hinner] using hdeficit
  have hh := QuarticEscapeGeometry.four_point_escape hf hL hα hδ hT v e he hdef hshort hη
  rw [show v + δ • e = u from hpoint] at hh
  simpa [escapePoints, e, δ, div_eq_mul_inv, smul_smul, min_comm, max_comm] using hh

end LongTails.Proofs.QuarticWitnessGeometry
