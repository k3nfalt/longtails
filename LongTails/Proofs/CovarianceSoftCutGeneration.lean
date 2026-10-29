import LongTails.Proofs.CovarianceSoftCutProcess

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutGeneration

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Proofs.CovarianceSoftCutProcess
open LongTails.Proofs.CovarianceSoftCutLocalization
open OracleTemplate.StochasticGeneralized

lemma generator_failure_probability (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (hαR : α ≤ q.L * q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q) (hf : Measurable f)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x - f y| ≤ q.L * ‖x-y‖)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (b : ℕ) (hb : 0 < b)
    (hbatch : 1024 * q.σ ^ 2 * q.R ^ 2 ≤ (q.d : ℝ) * b * α ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) (ξ : ℕ → Ξ → q.Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T : ℕ) (hT : 0 < T)
    (horizon : (q.d : ℝ) * Real.log (8 * q.L * q.R / α) ≤ (T : ℝ) / 24) :
    P {ω | ∀ t, t < T → α < f (samplePoint q α (2 / α) b g t (fun i => ξ i ω)) - f xstar} ≤
      (1 / 4 : ENNReal) := by
  let μ := targetMeasure q α xstar
  have hμprob : IsProbabilityMeasure μ := targetMeasure_probability q hL α hα xstar
  let W : Ξ → ℝ := fun ω => accumulated (fun _ => b) (historyNext q α (2 / α) g)
    (historyPenalty q α (2 / α) g f (f xstar) μ) T (0, fun _ => (0, 0)) (fun i => ξ i ω)
  have hmean := cumulativePenalty_mean q hd hL hR α (2 / α) hα hαR p f v hf g hg hlip
    xstar hxstar μ (targetMeasure_support q α xstar) b hb hbatch P ξ h_samples T (0, fun _ => (0, 0))
  have hnon (ω : Ξ) : 0 ≤ W ω :=
    CovarianceSoftCutFreshness.accumulated_nonneg _ _ _
      (historyPenalty_nonneg q α (2 / α) hα g f (f xstar) μ) _ _ _
  have hT' : 0 < (T : ℝ) := by exact_mod_cast hT
  have hlarge (ω : Ξ)
      (hbad : ∀ t, t < T → α < f (samplePoint q α (2 / α) b g t (fun i => ξ i ω)) - f xstar) :
      (T : ℝ) / 8 ≤ W ω := by
    have hl := generator_targetLoss_lower q hd hL hR α hα hαR xstar hxstar b T
      (sampleReplies q α (2 / α) b g (fun i => ξ i ω))
    rw [← sampleCuts_eq_generatorCuts q α (2 / α) b hb g (fun i => ξ i ω) T] at hl
    rw [← cumulativePenalty_eq_loss_on_bad q hL α hα g f xstar b T (fun i => ξ i ω)
      (fun t ht => (hbad t ht).le)] at hl
    exact CovarianceSoftCutPotential.stoppedLoss_failure_bound _ _ _ horizon hl
  have hm := (hmean.1.mul_const (8 / (T : ℝ))).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (hnon ω) (by positivity)))
    (s := {ω | ∀ t, t < T → α < f (samplePoint q α (2 / α) b g t (fun i => ξ i ω)) - f xstar})
    (fun ω hω => by
      have hh := mul_le_mul_of_nonneg_right (hlarge ω hω) (by positivity : 0 ≤ 8 / (T : ℝ))
      have he : (T : ℝ) / 8 * (8 / (T : ℝ)) = 1 := by field_simp
      simpa only [he] using hh)
  apply hm.trans
  apply (ENNReal.ofReal_le_ofReal ?_).trans_eq (by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]; norm_num : ENNReal.ofReal (1 / 4 : ℝ) = 1 / 4)
  rw [integral_mul_const]
  calc
    (∫ ω, W ω ∂P) * (8 / (T : ℝ)) ≤ ((T : ℝ) / 32) * (8 / (T : ℝ)) :=
      mul_le_mul_of_nonneg_right hmean.2 (by positivity)
    _ = 1 / 4 := by field_simp; ring

end LongTails.Proofs.CovarianceSoftCutGeneration
