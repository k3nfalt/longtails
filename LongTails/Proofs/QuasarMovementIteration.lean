import LongTails.Proofs.FiniteProductIteration
import LongTails.Proofs.ContinuizedQuasarContinuity
import LongTails.Algorithms.MovementQuasar
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

variable {S Ω : Type*} [TopologicalSpace S] [TopologicalSpace Ω]

variable [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]

lemma iterateSamples_backward_integral {advance : S → Ω → S}
    (ha : Continuous (fun q : S × Ω => advance q.1 q.2))
    (P : ProbabilityMeasure Ω) (V : ℕ → S → ℝ)
    (hV : ∀ k, Continuous (V k)) (hV0 : ∀ k s, 0 ≤ V k s)
    {q : ℝ} (hq : 0 ≤ q) (m : ℕ)
    (hstep : ∀ k < m, ∀ s, Integrable (fun a => V k (advance s a)) (P : Measure Ω) ∧
      (∫ a, V k (advance s a) ∂(P : Measure Ω)) ≤ q * V (k + 1) s)
    (k : ℕ) (hk : k ≤ m) (s : S) :
    Integrable (fun samples => V 0 (iterateSamples advance k s samples))
      (Measure.pi (fun _ : Fin k => (P : Measure Ω))) ∧
    (∫ samples, V 0 (iterateSamples advance k s samples)
      ∂Measure.pi (fun _ : Fin k => (P : Measure Ω))) ≤
      q ^ k * V k s := by
  induction k generalizing s with
  | zero =>
      constructor
      · change Integrable (fun _ : Fin 0 → Ω => V 0 s)
          (Measure.pi (fun _ : Fin 0 => (P : Measure Ω)))
        exact integrable_const _
      · simp [iterateSamples, measureReal_def]
  | succ k ih =>
      let F := fun a : Ω × (Fin k → Ω) =>
        V 0 (iterateSamples advance k (advance s a.1) a.2)
      have hFc : Continuous F := (hV 0).comp ((iterateSamples_continuous ha k).comp
        ((ha.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd))
      have hFm : AEStronglyMeasurable F
          ((P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω)))) :=
        hFc.aestronglyMeasurable
      have hF0 (a : Ω × (Fin k → Ω)) : 0 ≤ F a := hV0 0 _
      have hNorm (a : Ω) :
          (∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin k => (P : Measure Ω))) =
            ∫ t, F (a, t) ∂Measure.pi (fun _ : Fin k => (P : Measure Ω)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖F (a, t)‖ = F (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (a, t))])
      have hBound : Integrable (fun a => q ^ k * V k (advance s a)) (P : Measure Ω) :=
        ((hstep k (by omega) s).1.const_mul (q ^ k))
      have hOuter : Integrable
          (fun a => ∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin k => (P : Measure Ω)))
          (P : Measure Ω) := by
        apply hBound.mono' hFm.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hNorm]
        exact (ih (by omega) (advance s a)).2
      have hFi : Integrable F
          ((P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω)))) :=
        (integrable_prod_iff hFm).mpr
          ⟨Filter.Eventually.of_forall (fun a => (ih (by omega) (advance s a)).1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (k + 1) => (P : Measure Ω)) 0).symm
      have hPi : Integrable (fun samples => V 0 (iterateSamples advance (k + 1) s samples))
          (Measure.pi (fun _ : Fin (k + 1) => (P : Measure Ω))) := by
        rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq] using hFi
      refine ⟨hPi, ?_⟩
      have he : (∫ samples, V 0 (iterateSamples advance (k + 1) s samples)
          ∂Measure.pi (fun _ : Fin (k + 1) => (P : Measure Ω))) =
          ∫ a, F a ∂(P : Measure Ω).prod (Measure.pi (fun _ : Fin k => (P : Measure Ω))) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      rw [he, integral_prod _ hFi]
      calc
        _ ≤ ∫ a, (q ^ k * V k (advance s a))
            ∂(P : Measure Ω) :=
          integral_mono_ae hFi.integral_prod_left hBound
            (Filter.Eventually.of_forall (fun a => (ih (by omega) (advance s a)).2))
        _ = q ^ k * (∫ a, V k (advance s a) ∂(P : Measure Ω)) := by
          rw [integral_const_mul]
        _ ≤ q ^ k * (q * V (k + 1) s) :=
          mul_le_mul_of_nonneg_left (hstep k (by omega) s).2 (pow_nonneg hq k)
        _ = _ := by rw [pow_succ]; ring

lemma sampleUpdate_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) :
    Continuous (fun q : p.E × ((p.E × p.E) × (ℝ × Fin p.n)) =>
      sampleUpdate p.γ (theta p) p.μ g q.1 q.2.1 q.2.2) := by
  have hgc : Continuous g := continuous_prod_of_discrete_left.mpr hg
  unfold sampleUpdate jump FiniteSum.estimator FiniteSum.fullGradient flow flowWeight
  fun_prop

lemma innerRun_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) (k : ℕ) :
    Continuous (fun q : p.E × ((p.E × p.E) × (Fin k → ℝ × Fin p.n)) =>
      innerRun p g q.1 k q.2.1 q.2.2) :=
  parameter_iterate_continuous (sampleUpdate p.γ (theta p) p.μ g)
    (sampleUpdate_continuous p g hg) k

lemma epochRun_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) :
    Continuous (fun q : (p.E × p.E) × (Fin p.n → ℝ × Fin p.n) =>
      epochRun p g q.1 q.2) :=
  (innerRun_continuous p g hg _).comp
    ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.prodMk continuous_snd))

end OracleTemplate.ContinuizedSimilarQuasar.Movement
