import LongTails.Proofs.ClippedExtragradientStage
import LongTails.Setups.StochasticGeneralizedMonotone
import LongTails.Proofs.RobustEstimatorMoments

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma measurable_trialOutput {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) (anchor center : E) :
    Measurable (trialOutput t s anchor center g) :=
  (measurable_iterateSamples (measurable_batchStep hg _ _ _ _ _ _ _)
    (innerSteps t s)).comp measurable_prodMk_left

set_option maxHeartbeats 1200000 in
omit [CompleteSpace E] in
lemma measurable_trialOutput_joint {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × TrialSamples t s Ω =>
      trialOutput t s w.1.1 w.1.2 g w.2) := by
  have ha : Measurable (fun w : (E × E) × E ×
      ((Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω)) =>
      batchStep (batchSize t s) (clippingScale t s) (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g w.2.1 w.2.2) :=
    measurable_batchStep_of hg _ _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  change Measurable (fun w : (E × E) × TrialSamples t s Ω =>
    ContinuizedSimilarQuasar.iterateSamples
      (batchStep (batchSize t s) (clippingScale t s) (localScale t s)
        (radius t s) (regularization t s) w.1.1 w.1.2 g) (innerSteps t s) w.1.2 w.2)
  exact (measurable_iterateSamples_parameter (A := E × E) (S := E)
    (Ω := (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω))
    (advance := fun a : E × E => batchStep (batchSize t s) (clippingScale t s)
      (localScale t s) (radius t s) (regularization t s) a.1 a.2 g) ha (innerSteps t s)).comp
    (measurable_fst.prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

set_option maxHeartbeats 1200000 in
omit [CompleteSpace E] in
lemma measurable_confidenceOutput_joint {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × StageSamples t s Ω =>
      confidenceOutput t s w.1.1 w.1.2 g w.2) := by
  have ht := measurable_finite_replies (measurable_trialOutput_joint hg t s) (repetitions t)
  have hp := (RobustGradient.measurable_pilotCenter (repetitions t)).comp
    ((measurable_const (a := radius t s)).prodMk ht)
  exact RobustGradient.measurable_centeredClip_joint.comp
    (measurable_const.prodMk ((measurable_snd.comp measurable_fst).prodMk hp))

lemma trialOutput_moment {g : E → Ω → E} {F : E → E} (t : Tuning)
    (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (s : ℕ) {anchor center p : E}
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hF : ‖F p‖ ≤ t.ε) (hcroot : ‖p - center‖ ≤ radius t s) :
    Integrable (fun samples => ‖trialOutput t s anchor center g samples - p‖ ^ 2)
      (Measure.pi fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => P))) ∧
    (∫ samples, ‖trialOutput t s anchor center g samples - p‖ ^ 2
      ∂Measure.pi (fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => P)))) ≤ radius t s ^ 2 / 4096 := by
  have hd := radius_pos t hR s
  have ha := measurable_batchStep hg.measurable (batchSize t s) (clippingScale t s)
    (localScale t s) (radius t s) (regularization t s) anchor center
  have hball := batchStep_ball (batchSize t s) (clippingScale t s) (localScale t s)
    (radius t s) (regularization t s) hd.le anchor center g
  refine ⟨iterate_distance_integrable ha hd.le center p hball hcroot (innerSteps t s), ?_⟩
  apply iterate_distance_bound ha (regularization_pos t hR hε s)
    (localScale_lower t h0 h1 hR hε s) hd.le (by positivity)
    (batchSize_variance t h0 h1 hR hε s) center p hball hcroot
    (fun x hx => tuned_step_integral t h0 h1 hR hε hc hmono hlip
      hg.measurable hg.integrable hg.unbiased hg.variance_integrable hg.variance s hp hF hcroot hx)
    (innerSteps_lower t s)

lemma stage_confidence {g : E → Ω → E} {F : E → E} (t : Tuning)
    (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (s : ℕ) {anchor center p : E}
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hF : ‖F p‖ ≤ t.ε) (hcroot : ‖p - center‖ ≤ radius t s) :
    (Measure.pi fun _ : Fin (repetitions t) =>
      Measure.pi fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => P)))
      {samples | radius t s / 2 < ‖confidenceOutput t s anchor center g samples - p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ repetitions t) := by
  have hm := trialOutput_moment t h0 h1 hR hε hc hmono hlip hg s hp hF hcroot
  exact projected_pilot_failure (measurable_trialOutput hg.measurable t s anchor center)
    (radius_pos t hR s) center p hcroot hm.1 hm.2 (repetitions t)

end OracleTemplate.ClippedExtragradient
