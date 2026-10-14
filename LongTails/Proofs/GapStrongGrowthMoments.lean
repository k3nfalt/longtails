import LongTails.Algorithms.GapStrongGrowthAccelerated
import LongTails.Proofs.GapStrongGrowthStep
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.HeavyTailedClipping

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma raw_moment_of_centered {v : Ω → E} (hv : Measurable v) (u : E)
    (hi : Integrable (fun ω => ‖v ω - u‖ ^ 2) P)
    (hb : (∫ ω, ‖v ω - u‖ ^ 2 ∂P) ≤ ‖u‖ ^ 2) :
    Integrable (fun ω => ‖v ω‖ ^ 2) P ∧ (∫ ω, ‖v ω‖ ^ 2 ∂P) ≤ 4 * ‖u‖ ^ 2 := by
  have hpoint (ω : Ω) : ‖v ω‖ ^ 2 ≤ 2 * ‖v ω - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    have hh := norm_sub_norm_le (v ω) u
    nlinarith [norm_nonneg (v ω), norm_nonneg (v ω - u), norm_nonneg u,
      sq_nonneg (‖v ω - u‖ - ‖u‖)]
  have hdom : Integrable (fun ω => 2 * ‖v ω - u‖ ^ 2 + 2 * ‖u‖ ^ 2) P :=
    (hi.const_mul 2).add (integrable_const _)
  have hraw : Integrable (fun ω => ‖v ω‖ ^ 2) P := hdom.mono'
    (hv.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω)
  refine ⟨hraw, (integral_mono hraw hdom hpoint).trans ?_⟩
  rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  linarith

omit [CompleteSpace E] in
lemma clipped_raw_moments {v : Ω → E} (hv : Measurable v) (hi : Integrable v P)
    (h2 : Integrable (fun ω => ‖v ω‖ ^ 2) P) {u : E}
    (hmean : (∫ ω, v ω ∂P) = u) {M C : ℝ} (hM : 0 < M)
    (hb : (∫ ω, ‖v ω‖ ^ 2 ∂P) ≤ C) :
    Integrable (fun ω => clip M (v ω)) P ∧
    Integrable (fun ω => ‖clip M (v ω)‖ ^ 2) P ∧
    ‖(∫ ω, clip M (v ω) ∂P) - u‖ ≤ C / M ∧
    (∫ ω, ‖clip M (v ω)‖ ^ 2 ∂P) ≤ C := by
  have hc := integrable_clip (P := P) hv hM.le
  have hpoint (ω : Ω) : ‖clip M (v ω)‖ ^ 2 ≤ ‖v ω‖ ^ 2 := by
    have hh := norm_clip_sub_le hM.le (u := (0 : E)) (by simpa using hM.le) (v ω)
    simp only [sub_zero] at hh
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hc2 : Integrable (fun ω => ‖clip M (v ω)‖ ^ 2) P := h2.mono'
    (((measurable_clip M).comp hv).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω)
  refine ⟨hc, hc2, ?_, (integral_mono hc2 h2 hpoint).trans hb⟩
  have hh := norm_integral_le_of_norm_le (h2.div_const M)
    (f := fun ω => clip M (v ω) - v ω)
    (Filter.Eventually.of_forall fun ω => by
      rw [norm_sub_rev]
      exact raw_clip_residual hM (v ω))
  rw [integral_sub hc hi, hmean, integral_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hb hM.le)

lemma batch_centered_moment (p : Params) (hρ : 1 ≤ p.ρ)
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] {f : p.E → ℝ} {g : p.E → p.Ω → p.E}
    (hg : IsStrongGrowthOracle μ f g p.ρ) (x : p.E) :
    Integrable (fun ξ : Fin (batchSize p) → p.Ω =>
      ‖StochasticGeneralized.batchReply g x ξ - gradient f x‖ ^ 2)
        (Measure.pi fun _ => μ) ∧
    (∫ ξ : Fin (batchSize p) → p.Ω,
      ‖StochasticGeneralized.batchReply g x ξ - gradient f x‖ ^ 2
      ∂Measure.pi (fun _ => μ)) ≤ ‖gradient f x‖ ^ 2 := by
  have hceil : p.ρ ≤ (batchSize p : ℝ) := Nat.le_ceil _
  have hbR : 0 < (batchSize p : ℝ) := by linarith
  have hb : 0 < batchSize p := by exact_mod_cast hbR
  have hx : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hh := RobustGradient.finite_mean_variance hx (hg.integrable x) (gradient f x)
    (hg.integrable_variance x) (hg.unbiased x) (batchSize p) hb
  refine ⟨hh.1, ?_⟩
  change (∫ ξ : Fin (batchSize p) → p.Ω,
    ‖(1 / (batchSize p : ℝ)) • ∑ i, g x (ξ i) - gradient f x‖ ^ 2
    ∂Measure.pi (fun _ => μ)) ≤ _
  rw [hh.2]
  apply (div_le_iff₀ hbR).mpr
  exact (hg.variance x).trans (by nlinarith [sq_nonneg ‖gradient f x‖])

end OracleTemplate.GapStrongGrowth
