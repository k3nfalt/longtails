import LongTails.Proofs.AffineMomentTrajectory
import LongTails.Proofs.AffineMomentConfidence
import LongTails.Proofs.StochasticGeneralizedConcentration

open MeasureTheory
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentParameters
open LongTails.Proofs.AffineMomentProcess
open LongTails.Proofs.AffineMomentFailures

namespace LongTails.Proofs.AffineMomentProbability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
lemma measurable_sampledIterate (t : Tuning) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (k : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledIterate t oracle ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hy : Measurable (fun ξ : ℕ → Ω => point t k (sampledIterate t oracle ξ k)) := by
      unfold point couplingPoint
      exact (measurable_const.smul ih.snd).add (measurable_const.smul ih.fst)
    have hr : Measurable (fun ξ : ℕ → Ω => fun i => oracle
        (point t k (sampledIterate t oracle ξ k)) (ξ (blockSize t * k + i))) :=
      Measurable.of_eval (fun i => ho.comp (hy.prodMk (measurable_pi_apply _)))
    have hp := (measurable_pilotEstimate t).comp hr
    have hm := (OracleTemplate.RobustGeneralized.measurable_meanBlock (sampleSize t) (sampleSize t)).comp hr
    change Measurable (fun ξ : ℕ → Ω => advance t k (sampledIterate t oracle ξ k)
      (pilotEstimate t (fun i => oracle (point t k (sampledIterate t oracle ξ k)) (ξ (blockSize t * k + i))))
      (OracleTemplate.RobustGeneralized.meanBlock (sampleSize t) (sampleSize t)
        (fun i => oracle (point t k (sampledIterate t oracle ξ k)) (ξ (blockSize t * k + i)))))
    have hpair : Measurable (fun ξ : ℕ → Ω => ((k, sampledIterate t oracle ξ k),
        (pilotEstimate t (fun i => oracle (point t k (sampledIterate t oracle ξ k)) (ξ (blockSize t * k + i))),
        OracleTemplate.RobustGeneralized.meanBlock (sampleSize t) (sampleSize t)
          (fun i => oracle (point t k (sampledIterate t oracle ξ k)) (ξ (blockSize t * k + i)))))) :=
      (measurable_const.prodMk ih).prodMk (hp.prodMk hm)
    have hresult := (measurable_advance (E := E) t).comp hpair
    exact hresult

lemma sampled_accuracy {t : Tuning} (ht : Valid t)
    {f : E → ℝ} (hf : Measurable f) {g : E → E} (hg : Measurable g)
    (u : E) (hu : ‖u‖ ≤ 1) {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle))
    (hstep : ∀ s : ProofState E,
      Integrable (fun ξ => Real.exp (increment t f g u oracle (sampleSize t) s ξ))
        (Measure.pi fun _ : Fin (sampleSize t) => P) ∧
      (∫ ξ, Real.exp (increment t f g u oracle (sampleSize t) s ξ)
        ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤ 1)
    (hfail : ∀ s : ProofState E,
      (∫ ξ, failure t g oracle (sampleSize t) s ξ ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤
        (1 / 2 : ℝ) ^ pilotGroups t) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | t.ε < f (sampledIterate t oracle ξ (iterations t)).1 - f u} ≤ ENNReal.ofReal t.δ := by
  let s : ProofState E := (0, (0, 0), false, 0, false)
  let B := {ξ | 1 ≤ OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
    (next t g oracle) (failure t g oracle) (2 * iterations t) s ξ}
  let C := {ξ | 2 * confidence t < OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
    (next t g oracle) (increment t f g u oracle) (2 * iterations t) s ξ}
  have hb := accumulated_failure_bound t hg ho hfail (2 * iterations t) s
  have hm := accumulated_mgf t hf hg u ho hstep (2 * iterations t) s
  have hc := OracleTemplate.StochasticGeneralized.exponential_tail
    (P := Measure.infinitePi fun _ : ℕ => P) (t := 1) (C := 0) (r := 2 * confidence t)
    (by norm_num) (by simpa only [one_mul] using hm.1)
    (by simpa only [one_mul, Real.exp_zero] using hm.2)
  have hB : (Measure.infinitePi fun _ : ℕ => P) B ≤ ENNReal.ofReal (t.δ / 2) := by
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using AffineMomentConfidence.pilot_tail ht
  have hC : (Measure.infinitePi fun _ : ℕ => P) C ≤ ENNReal.ofReal (t.δ / 2) := by
    apply hc.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_mul, zero_sub] using AffineMomentConfidence.energy_tail ht
  have hsub : {ξ | t.ε < f (sampledIterate t oracle ξ (iterations t)).1 - f u} ⊆ B ∪ C := by
    intro ξ hξ
    by_contra hn
    have hn' : ξ ∉ B ∧ ξ ∉ C := by simpa only [Set.mem_union, not_or] using hn
    have hfail' : OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
        (next t g oracle) (failure t g oracle) (2 * iterations t) s ξ < 1 := lt_of_not_ge hn'.1
    have hacc : OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
        (next t g oracle) (increment t f g u oracle) (2 * iterations t) s ξ ≤ 2 * confidence t := le_of_not_gt hn'.2
    have ha := AffineMomentTrajectory.trace_agreement ht g oracle ξ (iterations t) hfail'
      (iterations t) le_rfl le_rfl
    have hround := congrArg (fun v : ProofState E => v.1) ha
    have he := trace_accuracy ht f g u hu oracle (2 * iterations t) ξ hround hacc
    rw [ha] at he
    exact (not_lt_of_ge he) hξ
  calc
    _ ≤ (Measure.infinitePi fun _ : ℕ => P) (B ∪ C) := measure_mono hsub
    _ ≤ (Measure.infinitePi fun _ : ℕ => P) B + (Measure.infinitePi fun _ : ℕ => P) C := measure_union_le _ _
    _ ≤ ENNReal.ofReal (t.δ / 2) + ENNReal.ofReal (t.δ / 2) := add_le_add hB hC
    _ = ENNReal.ofReal t.δ := by rw [← ENNReal.ofReal_add (by linarith [ht.confidence_pos]) (by linarith [ht.confidence_pos])]; congr 1; ring

end LongTails.Proofs.AffineMomentProbability
