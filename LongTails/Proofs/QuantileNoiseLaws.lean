import LongTails.Setups.QuantileSymmetricRemainderConvex
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory

namespace LongTails.Proofs.QuantileNoiseLaws

open LongTails.Setups.QuantileSymmetricRemainderConvex

lemma remainder_nonneg {μ : Measure ℝ} {M : ℝ} (h : HasSymmetricRemainder μ M) :
    0 ≤ M := by
  obtain ⟨S, A, _, _, _, _, _, hM⟩ := h
  exact (integral_nonneg fun z => sq_nonneg z).trans hM

lemma remainder_reflection {μ : Measure ℝ} {M : ℝ} (h : HasSymmetricRemainder μ M) :
    HasSymmetricRemainder (μ.map (fun z : ℝ => -z)) M := by
  obtain ⟨S, A, hμ, hS, hi, hc, hi2, hM⟩ := h
  refine ⟨S, A.map (fun z : ℝ => -z), ?_, hS, ?_, ?_, ?_, ?_⟩
  · rw [hμ, Measure.map_add _ _ measurable_neg, hS]
  · apply (integrable_map_measure (by fun_prop) measurable_neg.aemeasurable).mpr
    change Integrable (fun z : ℝ => -z) A
    exact hi.neg
  · rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
    change (∫ z, -(fun z : ℝ => z) z ∂A) = 0
    rw [integral_neg, hc, neg_zero]
  · apply (integrable_map_measure (by fun_prop) measurable_neg.aemeasurable).mpr
    simpa only [Function.comp_def, neg_sq] using hi2
  · rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
    simpa only [neg_sq] using hM

lemma noise_reflection {μ : Measure ℝ} {r M : ℝ} (h : NoiseCondition μ r M) :
    NoiseCondition (μ.map (fun z : ℝ => -z)) r M := by
  refine ⟨remainder_reflection h.1, ?_⟩
  rw [Measure.map_apply measurable_neg
    (measurableSet_lt measurable_const continuous_abs.measurable)]
  simpa only [Set.preimage_ofPred_eq, abs_neg] using h.2

end LongTails.Proofs.QuantileNoiseLaws
