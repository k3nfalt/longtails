import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

variable {S Ω : Type*} [TopologicalSpace S] [TopologicalSpace Ω]

lemma iterateSamples_continuous {advance : S → Ω → S}
    (ha : Continuous (fun q : S × Ω => advance q.1 q.2)) (k : ℕ) :
    Continuous (fun q : S × (Fin k → Ω) => iterateSamples advance k q.1 q.2) := by
  induction k with
  | zero => simpa only [iterateSamples] using
      (continuous_fst : Continuous (fun q : S × (Fin 0 → Ω) => q.1))
  | succ k ih =>
      exact ih.comp ((ha.comp (continuous_fst.prodMk
        ((continuous_apply 0).comp continuous_snd))).prodMk
          (continuous_pi (fun i => (continuous_apply i.succ).comp continuous_snd)))

variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]

lemma iterateSamples_integral {advance : S → Ω → S}
    (ha : Continuous (fun q : S × Ω => advance q.1 q.2))
    (P : ProbabilityMeasure Ω) (V : S → ℝ) (hV : Continuous V) (hV0 : ∀ s, 0 ≤ V s)
    {q r : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ s, Integrable (fun a => V (advance s a)) (P : Measure Ω) ∧
      (∫ a, V (advance s a) ∂(P : Measure Ω)) ≤ q * V s + r)
    (k : ℕ) (s : S) :
    Integrable (fun samples => V (iterateSamples advance k s samples))
      (Measure.pi (fun _ : Fin k => (P : Measure Ω))) ∧
    (∫ samples, V (iterateSamples advance k s samples)
      ∂Measure.pi (fun _ : Fin k => (P : Measure Ω))) ≤
      q ^ k * V s + r * ∑ j ∈ Finset.range k, q ^ j := by
  induction k generalizing s with
  | zero =>
      constructor
      · change Integrable (fun _ : Fin 0 → Ω => V s)
          (Measure.pi (fun _ : Fin 0 => (P : Measure Ω)))
        exact integrable_const _
      · simp [iterateSamples, measureReal_def]
  | succ k ih =>
      let F := fun a : Ω × (Fin k → Ω) =>
        V (iterateSamples advance k (advance s a.1) a.2)
      have hFc : Continuous F := hV.comp ((iterateSamples_continuous ha k).comp
        ((ha.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd))
      have hFm : AEStronglyMeasurable F
          ((P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω)))) :=
        hFc.aestronglyMeasurable
      have hF0 (a : Ω × (Fin k → Ω)) : 0 ≤ F a := hV0 _
      have hNorm (a : Ω) :
          (∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin k => (P : Measure Ω))) =
            ∫ t, F (a, t) ∂Measure.pi (fun _ : Fin k => (P : Measure Ω)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖F (a, t)‖ = F (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (a, t))])
      have hBound : Integrable (fun a => q ^ k * V (advance s a) +
          r * ∑ j ∈ Finset.range k, q ^ j) (P : Measure Ω) :=
        ((hstep s).1.const_mul (q ^ k)).add (integrable_const _)
      have hOuter : Integrable
          (fun a => ∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin k => (P : Measure Ω)))
          (P : Measure Ω) := by
        apply hBound.mono' hFm.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hNorm]
        exact (ih (advance s a)).2
      have hFi : Integrable F
          ((P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω)))) :=
        (integrable_prod_iff hFm).mpr
          ⟨Filter.Eventually.of_forall (fun a => (ih (advance s a)).1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (k + 1) => (P : Measure Ω)) 0).symm
      have hPi : Integrable (fun samples => V (iterateSamples advance (k + 1) s samples))
          (Measure.pi (fun _ : Fin (k + 1) => (P : Measure Ω))) := by
        rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq] using hFi
      refine ⟨hPi, ?_⟩
      have he : (∫ samples, V (iterateSamples advance (k + 1) s samples)
          ∂Measure.pi (fun _ : Fin (k + 1) => (P : Measure Ω))) =
          ∫ a, F a ∂(P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω))) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      rw [he, integral_prod _ hFi]
      calc
        _ ≤ ∫ a, (q ^ k * V (advance s a) + r * ∑ j ∈ Finset.range k, q ^ j)
            ∂(P : Measure Ω) :=
          integral_mono_ae hFi.integral_prod_left hBound
            (Filter.Eventually.of_forall (fun a => (ih (advance s a)).2))
        _ = q ^ k * (∫ a, V (advance s a) ∂(P : Measure Ω)) +
            r * ∑ j ∈ Finset.range k, q ^ j := by
          rw [integral_add ((hstep s).1.const_mul _) (integrable_const _), integral_const_mul]
          simp
        _ ≤ q ^ k * (q * V s + r) + r * ∑ j ∈ Finset.range k, q ^ j :=
          add_le_add (mul_le_mul_of_nonneg_left (hstep s).2 (pow_nonneg hq k)) (le_refl _)
        _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring

end OracleTemplate.ContinuizedSimilarQuasar
