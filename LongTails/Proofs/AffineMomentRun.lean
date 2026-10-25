import LongTails.Proofs.AffineMomentProbability
import LongTails.Proofs.AffineMomentExecution

open MeasureTheory
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Setups.AffineMomentConvex

namespace LongTails.Proofs.AffineMomentRun

lemma normalized_accuracy (p : Params) (hp : spec.valid p)
    (ν : ProbabilityMeasure p.Ω) (f : p.E → ℝ) (g : p.E → p.Ω → p.E)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : IsMinOn f Set.univ u) (hR : ‖p.x0 - u‖ ≤ p.R)
    (ho : IsFiniteMomentOracle (ν : Measure p.Ω) f g p.α p.σ p.σ0) :
    (Measure.infinitePi fun _ : ℕ => (ν : Measure p.Ω))
      {ξ | p.ε < f (p.x0 + p.R • (sampledIterate (tuning p)
        (AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (iterations (tuning p))).1) - f u} ≤
        ENNReal.ofReal p.δ := by
  have ht := AffineMomentParameters.tuning_valid p hp
  have hL := hp.1
  have hRp := hp.2.1
  let F := AffineMomentNormalization.objective p.L p.R p.x0 f
  let G := AffineMomentNormalization.derivative p.L p.R p.x0 f
  let O := AffineMomentNormalization.oracle p.L p.R p.x0 g
  let v := AffineMomentNormalization.minimizer p.R p.x0 u
  have hv : ‖v‖ ≤ 1 := AffineMomentNormalization.minimizer_norm hRp p.x0 u hR
  have hFm : Measurable F := (AffineMomentNormalization.objective_continuous p.L p.R p.x0 f hg).measurable
  have hGm : Measurable G := (AffineMomentNormalization.derivative_continuous hL hRp p.x0 f hlip).measurable
  have hOm : Measurable (Function.uncurry O) := AffineMomentNormalization.oracle_measurable p.x0 g ho.measurable
  have hOi := AffineMomentNormalization.oracle_integrable (L := p.L) (R := p.R) p.x0 g ho.integrable
  have hOmean := AffineMomentNormalization.oracle_mean (L := p.L) (R := p.R) p.x0 f g ho.unbiased
  have hOp := AffineMomentNormalization.oracle_moment_integrable hL hRp p.x0 f g ho.integrable_moment
  have hOmom := AffineMomentNormalization.oracle_moment hL hRp hp.2.2.2.1 p.x0 f g ho.moment
  have hs := AffineMomentNormalization.support hL hRp p.x0 f hc hg
  have hsm := AffineMomentNormalization.smooth_model hL hRp p.x0 f hg hlip
  have hmin := AffineMomentNormalization.minimized hL hRp p.x0 f u hu
  have hzero := AffineMomentNormalization.derivative_at_minimizer hL hRp p.x0 f hg hlip u hu
  have hGlip := AffineMomentNormalization.derivative_lipschitz hL hRp p.x0 f hlip
  have hstep := AffineMomentProcess.increment_mgf ht v hv hs hsm hmin hzero hGlip
    hOm hOi hOmean hOp hOmom
  have hfail := AffineMomentFailures.failure_mean ht hOm hOi hOmean hOp hOmom
  have hb := AffineMomentProbability.sampled_accuracy ht hFm hGm v hv hOm hstep hfail
  apply (measure_mono ?_).trans hb
  intro ξ hξ
  change (tuning p).ε < F (sampledIterate (tuning p) O ξ (iterations (tuning p))).1 - F v
  have he : F (sampledIterate (tuning p) O ξ (iterations (tuning p))).1 - F v =
      (f (p.x0 + p.R • (sampledIterate (tuning p) O ξ (iterations (tuning p))).1) - f u) /
        (p.L * p.R ^ 2) := by
    dsimp [F, v, AffineMomentNormalization.objective]
    rw [AffineMomentNormalization.physical_minimizer hRp, sub_div]
  rw [he]
  apply lt_of_le_of_lt (min_le_left _ _)
  exact (div_lt_div_iff_of_pos_right (by positivity : 0 < p.L * p.R ^ 2)).mpr hξ

lemma successful_execution (p : Params) (hp : spec.valid p)
    (ν : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (ν : Measure p.Ω) (P : Measure _))
    (f : p.E → ℝ) (g : p.E → p.Ω → p.E)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : IsMinOn f Set.univ u) (hR : ‖p.x0 - u‖ ≤ p.R)
    (ho : IsFiniteMomentOracle (ν : Measure p.Ω) f g p.α p.σ p.σ0)
    (N : ℕ) (hN : iterations (tuning p) * blockSize (tuning p) ≤ N) :
    spec.successful p f
      (fun w : Unit × (ℕ → p.Ω) => OracleTemplate.execute
        { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) z => g x z }
        (algorithm p) (fun _ => N) w.1 w.2)
      ⟨(Measure.dirac ()).prod (P : Measure _), inferInstance⟩ := by
  classical
  let output := fun ξ : ℕ → p.Ω => p.x0 + p.R • (sampledIterate (tuning p)
    (AffineMomentNormalization.oracle p.L p.R p.x0 g) ξ (iterations (tuning p))).1
  have hm : Measurable output := measurable_const.add (measurable_const.smul
    (AffineMomentProbability.measurable_sampledIterate (tuning p)
      (AffineMomentNormalization.oracle_measurable p.x0 g ho.measurable) (iterations (tuning p))).fst)
  have he : (fun w : Unit × (ℕ → p.Ω) => OracleTemplate.execute
        { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) z => g x z }
        (algorithm p) (fun _ => N) w.1 w.2) = fun w => output w.2 := by
    funext w
    cases w.1
    exact AffineMomentExecution.execute_calls p (AffineMomentParameters.tuning_valid p hp) P g w.2 N hN
  rw [he]
  refine ⟨hm.comp measurable_snd, u, hu, ?_⟩
  have hPlaw : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (ν : Measure p.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change (P : Measure (ℕ → p.Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  have hb : (P : Measure _) {ξ | p.ε < f (output ξ) - f u} ≤ ENNReal.ofReal p.δ := by
    rw [hPlaw]
    exact normalized_accuracy p hp ν f g hc hg hlip u hu hR ho
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hset : MeasurableSet {ξ | p.ε < f (output ξ) - f u} :=
    measurableSet_lt measurable_const ((hf.measurable.comp hm).sub_const _)
  have hsnd : ProbabilityTheory.HasLaw (Prod.snd : Unit × (ℕ → p.Ω) → ℕ → p.Ω) (P : Measure _)
      ((Measure.dirac ()).prod (P : Measure _)) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have hb' := hsnd.measure_eq hset
  have hset' : MeasurableSet {w : Unit × (ℕ → p.Ω) | p.ε < f (output w.2) - f u} :=
    hset.preimage measurable_snd
  have hi := integral_indicator_one (μ := (Measure.dirac ()).prod (P : Measure _)) hset'
  change (∫ w : Unit × (ℕ → p.Ω),
    (if p.ε < f (output w.2) - f u then (1 : ℝ) else 0) ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.δ
  change (∫ w, {w : Unit × (ℕ → p.Ω) | p.ε < f (output w.2) - f u}.indicator 1 w
    ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.δ
  rw [hi]
  change (((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) | p.ε < f (output w.2) - f u}).toReal ≤ p.δ
  rw [hb']
  exact ((ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hb).trans_eq
    (ENNReal.toReal_ofReal hp.2.2.2.2.2.2.2.1.le)

end LongTails.Proofs.AffineMomentRun
