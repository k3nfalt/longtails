import LongTails.Proofs.CoarseGeneralizedOracle
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
open StochasticGeneralized (accumulated accumulated_measurable)

open Classical in
noncomputable def coarseFailure (p : Params) (f : p.E → ℝ) (oracle : p.E → p.Ω → p.E)
    (n : ℕ) (s : Search p.E) (ξ : Fin n → p.Ω) : ℝ :=
  if coarseTolerance p < ‖warmEstimate p (RobustGeneralized.sampleReplies oracle (searchPoint s) ξ) -
      gradient f (searchPoint s)‖ then 1 else 0

lemma measurable_coarseNext (p : Params) {oracle : p.E → p.Ω → p.E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (coarseNext p oracle n)) := by
  have hs : Measurable (fun w : Search p.E × (Fin n → p.Ω) =>
      RobustGeneralized.sampleReplies oracle (searchPoint w.1) w.2) :=
    (RobustGeneralized.measurable_sampleReplies p ho n).comp
      ((measurable_searchPoint.comp measurable_fst).prodMk measurable_snd)
  exact (measurable_searchUpdate (warmTuning p)).comp
    (measurable_fst.prodMk ((measurable_warmEstimate p).comp hs))

lemma measurable_coarseFailure (p : Params) {f : p.E → ℝ}
    (hg : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (coarseFailure p f oracle n)) := by
  have hs : Measurable (fun w : Search p.E × (Fin n → p.Ω) =>
      RobustGeneralized.sampleReplies oracle (searchPoint w.1) w.2) :=
    (RobustGeneralized.measurable_sampleReplies p ho n).comp
      ((measurable_searchPoint.comp measurable_fst).prodMk measurable_snd)
  have hm := ((measurable_warmEstimate p).comp hs).sub
    (hg.comp (measurable_searchPoint.comp measurable_fst))
  exact Measurable.ite (measurableSet_lt measurable_const hm.norm) measurable_const measurable_const

lemma coarseFailure_bounds (p : Params) (f : p.E → ℝ) (oracle : p.E → p.Ω → p.E)
    (n : ℕ) (s : Search p.E) (ξ : Fin n → p.Ω) :
    0 ≤ coarseFailure p f oracle n s ξ ∧ coarseFailure p f oracle n s ξ ≤ 1 := by
  unfold coarseFailure
  split_ifs <;> norm_num

lemma coarseFailure_mean (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (s : Search p.E) :
    (∫ ξ, coarseFailure p f oracle (warmBatch p) s ξ
      ∂Measure.pi (fun _ : Fin (warmBatch p) => μ)) ≤ (1 / 2 : ℝ) ^ warmGroups p := by
  let A := {ξ : Fin (warmBatch p) → p.Ω |
    coarseTolerance p < ‖warmEstimate p (RobustGeneralized.sampleReplies oracle (searchPoint s) ξ) -
      gradient f (searchPoint s)‖}
  have hm := (measurable_warmEstimate p).comp
    ((RobustGeneralized.measurable_sampleReplies p ho.measurable (warmBatch p)).comp
      ((measurable_const (a := searchPoint s)).prodMk measurable_id))
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hm.sub measurable_const).norm
  change (∫ ξ, A.indicator (1 : (Fin (warmBatch p) → p.Ω) → ℝ) ξ ∂Measure.pi (fun _ => μ)) ≤ _
  rw [integral_indicator_one hA]
  have hb := warmEstimate_failure p hp μ ho (searchPoint s)
  exact (ENNReal.toReal_mono (by finiteness) hb).trans_eq (ENNReal.toReal_ofReal (by positivity))

lemma coarseFailure_accumulated_measurable (p : Params) {f : p.E → ℝ}
    (hg : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) (s : Search p.E) :
    Measurable (accumulated (fun _ => warmBatch p) (coarseNext p oracle)
      (coarseFailure p f oracle) n s) :=
  (accumulated_measurable measurable_const (measurable_coarseNext p ho)
    (measurable_coarseFailure p hg ho) n).comp (measurable_const.prodMk measurable_id)

lemma coarseFailure_tail (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hg : Measurable (gradient f)) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (n : ℕ) (s : Search p.E) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 1 ≤ accumulated (fun _ => warmBatch p) (coarseNext p oracle)
        (coarseFailure p f oracle) n s ξ} ≤ ENNReal.ofReal (n * (1 / 2 : ℝ) ^ warmGroups p) := by
  exact RobustGradient.accumulated_failure_probability μ measurable_const
    (measurable_coarseNext p ho.measurable) (measurable_coarseFailure p hg ho.measurable)
    (coarseFailure_bounds p f oracle) (coarseFailure_mean p hp ho) n s

lemma coarseFailure_tail_iid (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hg : Measurable (gradient f)) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} {ξ : ℕ → Ξ → p.Ω}
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    (s : Search p.E) :
    P {ω | 1 ≤ accumulated (fun _ => warmBatch p) (coarseNext p oracle)
      (coarseFailure p f oracle) (warmCalls p) s (fun k => ξ k ω)} ≤ ENNReal.ofReal (p.δ / 4) := by
  have hm := coarseFailure_accumulated_measurable p hg ho.measurable (warmCalls p) s
  have hl : HasLaw (fun ω k => ξ k ω) (Measure.infinitePi fun _ : ℕ => μ) P :=
    ⟨hξ.stream_law.measurable.aemeasurable, hξ.stream_law.map_eq⟩
  rw [hl.measure_eq (measurableSet_le measurable_const hm)]
  exact (coarseFailure_tail p hp hg ho (warmCalls p) s).trans
    (ENNReal.ofReal_le_ofReal (warm_failure_bound p hp))

lemma coarseFailure_zero_of_accumulated_lt (p : Params) (f : p.E → ℝ)
    (oracle : p.E → p.Ω → p.E) (s : Search p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (h : accumulated (fun _ => warmBatch p) (coarseNext p oracle)
      (coarseFailure p f oracle) n s ξ < 1) (i : ℕ) (hi : i < n) :
    let q := StochasticGeneralized.blockTrace (fun _ => warmBatch p) (coarseNext p oracle) s ξ i
    coarseFailure p f oracle (warmBatch p) q.1 (fun j => q.2 j) = 0 := by
  classical
  rw [StochasticGeneralized.accumulated_eq_sum] at h
  let q := StochasticGeneralized.blockTrace (fun _ => warmBatch p) (coarseNext p oracle) s ξ
  have hm := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range n) => (coarseFailure_bounds p f oracle
      (warmBatch p) (q j).1 (fun k => (q j).2 k)).1) (Finset.mem_range.mpr hi)
  have hh := hm.trans_lt h
  change coarseFailure p f oracle (warmBatch p) (q i).1 (fun j => (q i).2 j) = 0
  unfold coarseFailure at hh ⊢
  split_ifs with hb
  · simp only [ite_eq_left hb, lt_self_iff_false] at hh
  · rfl

end OracleTemplate.CoarseGeneralized
