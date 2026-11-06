import LongTails.Algorithms.StochasticQuasarProgram
import LongTails.Proofs.StochasticQuasarTailTuning
import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.StochasticQuasarProgramExecution
import LongTails.Proofs.StochasticQuasarCleanupExecution

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma program_clock_preserving (q : Params) :
    MeasurePreserving (fun seed : ProgramSeed q => fun i => (seed i).1)
      (programLaw q : Measure _) (RelativeQuasar.samplesLaw (outerCount q) : Measure _) := by
  have hh := measurePreserving_arrowProdEquivProdArrow ℝ
    (Fin (estimatorDepth (outerDeviation q) (outerBias q) + 1)) (Fin (outerCount q))
    (fun _ => (RelativeQuasar.holdingLaw : Measure ℝ))
    (fun _ => (mlmcLevelLaw (estimatorDepth (outerDeviation q) (outerBias q)) : Measure _))
  exact measurePreserving_fst.comp hh

lemma program_level_preserving (q : Params) :
    MeasurePreserving (fun seed : ProgramSeed q => fun i => (seed i).2)
      (programLaw q : Measure _)
      (Measure.pi fun _ : Fin (outerCount q) =>
        (mlmcLevelLaw (estimatorDepth (outerDeviation q) (outerBias q)) : Measure _)) := by
  have hh := measurePreserving_arrowProdEquivProdArrow ℝ
    (Fin (estimatorDepth (outerDeviation q) (outerBias q) + 1)) (Fin (outerCount q))
    (fun _ => (RelativeQuasar.holdingLaw : Measure ℝ))
    (fun _ => (mlmcLevelLaw (estimatorDepth (outerDeviation q) (outerBias q)) : Measure _))
  exact measurePreserving_snd.comp hh

lemma outer_calls_sum (q : Params) (seed : ProgramSeed q) :
    outerCalls q seed = ∑ i : Fin (outerCount q),
      accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q) (seed i).2.val := by
  unfold outerCalls
  rw [LongTails.Proofs.StochasticEnvelopeExecution.slotCalls_sum, ← Fin.sum_univ_eq_sum_range]
  simp [extendOuterSeeds]

lemma measurable_outer_calls (q : Params) : Measurable (outerCalls q) := by
  change Measurable (fun seed : ProgramSeed q => outerCalls q seed)
  simp_rw [outer_calls_sum]
  exact Finset.measurable_sum _ (fun i _ => (measurable_of_finite
    (fun j : Fin (estimatorDepth (outerDeviation q) (outerBias q) + 1) =>
      accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q) j.val)).comp
        (measurable_snd.comp (measurable_pi_apply i)))

lemma program_work_cap_failure {q : Params} (hv : spec.valid q) :
    (programLaw q : Measure _) {seed | workCap q < outerCalls q seed} ≤ ENNReal.ofReal (q.δ / 8) := by
  let bad : Set (Fin (outerCount q) → Fin (estimatorDepth (outerDeviation q) (outerBias q) + 1)) :=
    {levels | 2 * (outerCount q : ℝ) * outerMeanCost q + outerMaxCost q * outerOrder q <
      ∑ i, (accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q) (levels i).val : ℝ)}
  have hm : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hp := program_level_preserving q
  have ht := acceleration_work_tail hv.1 (outer_deviation_pos hv) (outer_bias_pos hv)
    q.σ q.D (outerCount q) (outerOrder q)
  have hsub : {seed : ProgramSeed q | workCap q < outerCalls q seed} ⊆
      (fun seed : ProgramSeed q => fun i => (seed i).2) ⁻¹' bad := by
    intro seed hs
    have hh : (workCap q : ℝ) < outerCalls q seed := by exact_mod_cast hs
    have hc := Nat.le_ceil (2 * (outerCount q : ℝ) * outerMeanCost q + outerMaxCost q * outerOrder q)
    change 2 * (outerCount q : ℝ) * outerMeanCost q + outerMaxCost q * outerOrder q <
      ∑ i : Fin (outerCount q), (accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q)
        (seed i).2.val : ℝ)
    rw [outer_calls_sum, Nat.cast_sum] at hh
    exact hc.trans_lt hh
  apply (measure_mono hsub).trans
  rw [hp.measure_preimage hm.nullMeasurableSet]
  exact ht.trans (ENNReal.ofReal_le_ofReal (outer_order_exponential_tail hv))

lemma outer_clock_lower_failure {q : Params} (hv : spec.valid q)
    (μ : Measure q.Ω) [IsProbabilityMeasure μ] (P : q.E → q.E) (g : q.E → q.Ω → q.E) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (outerPlan q w.1) 0).1 < 2 * outerHorizon q} ≤ ENNReal.ofReal (q.δ / 8) := by
  have hp := (program_clock_preserving q).comp
    (measurePreserving_fst (μ := (programLaw q : Measure (ProgramSeed q)))
      (ν := Measure.infinitePi fun _ : ℕ => μ))
  have hm : MeasurableSet {samples : Fin (outerCount q) → ℝ |
      GradientOnlyQuasar.clockSum samples < 2 * outerHorizon q} :=
    measurableSet_lt (GradientOnlyQuasar.continuous_clockSum _).measurable measurable_const
  have hh := (hp.measure_preimage hm.nullMeasurableSet).trans_le (outer_clock_lower_bound hv)
  simpa only [Set.preimage_ofPred_eq, Function.comp_apply, sampled_outer_clock,
    GradientOnlyQuasar.clockSum] using hh

lemma outer_clock_upper_failure {q : Params} (hv : spec.valid q)
    (μ : Measure q.Ω) [IsProbabilityMeasure μ] (P : q.E → q.E) (g : q.E → q.Ω → q.E) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | 2 * (outerCount q : ℝ) < (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (outerPlan q w.1) 0).1} ≤ ENNReal.ofReal (q.δ / 8) := by
  have hp := (program_clock_preserving q).comp
    (measurePreserving_fst (μ := (programLaw q : Measure (ProgramSeed q)))
      (ν := Measure.infinitePi fun _ : ℕ => μ))
  have hm : MeasurableSet {samples : Fin (outerCount q) → ℝ |
      2 * (outerCount q : ℝ) < GradientOnlyQuasar.clockSum samples} :=
    measurableSet_lt measurable_const (GradientOnlyQuasar.continuous_clockSum _).measurable
  have hh := (hp.measure_preimage hm.nullMeasurableSet).trans_le (outer_clock_upper_bound hv)
  simpa only [Set.preimage_ofPred_eq, Function.comp_apply, sampled_outer_clock,
    GradientOnlyQuasar.clockSum] using hh

lemma measurable_complete_execution {q : Params} (hv : spec.valid q)
    {P : q.E → q.E} {g : q.E → q.Ω → q.E} (hP : Measurable P) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : ProgramSeed q × (ℕ → q.Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (completePlan q w.1) 0) := by
  have hX := (measurable_outer_execution hv hP hg).snd.fst
  have htail := LongTails.Proofs.StochasticEnvelopeFreshness.measurable_seed_shift (Ω := q.Ω) (measurable_outer_calls q)
  simp_rw [sampled_complete_shift]
  exact (measurable_cleanup_joint hP hg q.L q.σ q.D (outputRadius q) (outputBatch q) (outerOrder q) 0).comp
    ((hX.prodMk (measurable_const (a := q.x0))).prodMk htail)

lemma measurable_initial_execution (q : Params) {P : q.E → q.E} {g : q.E → q.Ω → q.E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ξ : ℕ → q.Ω => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (initialCleanupPlan q.L q.x0 (outputBatch q) (outerOrder q)) 0) := by
  simp_rw [sampled_initial_cleanup]
  have hR := (measurable_robust_gradient_joint P hg (outputBatch q) (outerOrder q) 0).comp
    ((measurable_const (a := q.x0)).prodMk measurable_id)
  exact hP.comp (measurable_const.sub (hR.const_smul _))

lemma measurable_program_execution {q : Params} (hv : spec.valid q)
    {P : q.E → q.E} {g : q.E → q.Ω → q.E} (hP : Measurable P) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : ProgramSeed q × (ℕ → q.Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (program q w.1).2 0) := by
  simp_rw [sampled_program]
  by_cases he : 4 * q.L * q.D ^ 2 ≤ q.ε
  · simp only [he, ite_true]
    exact (measurable_initial_execution q hP hg).comp measurable_snd
  · simp only [he, ite_false]
    apply Measurable.ite _ (measurable_complete_execution hv hP hg) measurable_const
    exact measurableSet_le ((measurable_outer_calls q).comp measurable_fst) measurable_const

end OracleTemplate.StochasticQuasar
