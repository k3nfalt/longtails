import LongTails.Proofs.StochasticCompositeGeneralizedSampling

open MeasureTheory
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

noncomputable def pilotPoint (p : Public) (s : State p.E) : p.E :=
  if s.stage = 0 then s.x else queryPoint p s

noncomputable def finitePilot (p : Public) (g : p.E → p.Ω → p.E) (n : ℕ)
    (s : State p.E) (ξ : Fin n → p.Ω) : p.E :=
  RobustGradient.pilotCenter (192 * p.σ) (fun i => g (pilotPoint p s) (ξ i))

noncomputable def finiteError (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E) (n : ℕ)
    (s : State p.E) (ξ : Fin n → p.Ω) : p.E :=
  (1 / (n : ℝ)) • (∑ i, RobustGradient.centeredClip (clipRadius p s.iteration) s.center
    (g (queryPoint p s) (ξ i))) - I.grad (queryPoint p s)

def EvaluationReady (p : Public) (I : Instance p) (s : State p.E) : Prop :=
  0 < s.A ∧ 0 < s.M ∧ s.A < 4 * p.R ^ 2 / p.ε ∧
    ‖I.grad (queryPoint p s) - s.center‖ ≤ 96 * p.σ

noncomputable def phaseFailure (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if n = phaseCost p s then
    if s.stage ≤ 1 then
      if 96 * p.σ < ‖finitePilot p g n s ξ - I.grad (pilotPoint p s)‖ then 1 else 0
    else if s.stage = 2 ∧ EvaluationReady p I s then
      if p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) <
        ‖finiteError p I g n s ξ‖ then 1 else 0
    else 0
  else 0

lemma phaseFailure_range (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) :
    0 ≤ phaseFailure p I g n s ξ ∧ phaseFailure p I g n s ξ ≤ 1 := by
  unfold phaseFailure
  split_ifs <;> norm_num

lemma measurable_pilotPoint (p : Public) : Measurable (pilotPoint p) :=
  Measurable.ite (measurableSet_eq_fun measurable_state_stage measurable_const)
    measurable_state_x (measurable_queryPoint p)

lemma measurable_finitePilot (p : Public) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (finitePilot p g n)) := by
  have hv : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
      fun i => g (pilotPoint p w.1) (w.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hg.comp (((measurable_pilotPoint p).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact (RobustGradient.measurable_pilotCenter n).comp (measurable_const.prodMk hv)

lemma measurable_finiteError (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable I.grad) (n : ℕ) :
    Measurable (Function.uncurry (finiteError p I g n)) := by
  have hfst : Measurable (Prod.fst : State p.E × (Fin n → p.Ω) → State p.E) := measurable_fst
  have hq := (measurable_queryPoint p).comp hfst
  have hB := (measurable_of_countable (clipRadius p)).comp
    ((measurable_state_iteration (E := p.E)).comp
      hfst)
  have hc := (measurable_state_center (E := p.E)).comp
    hfst
  have ht (i : Fin n) : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
      RobustGradient.centeredClip (clipRadius p w.1.iteration) w.1.center
        (g (queryPoint p w.1) (w.2 i))) :=
    RobustGradient.measurable_centeredClip_joint.comp
      (hB.prodMk (hc.prodMk (hg.comp (hq.prodMk ((measurable_pi_apply i).comp measurable_snd)))))
  exact ((Finset.measurable_sum Finset.univ (fun i _ => ht i)).const_smul (1 / (n : ℝ))).sub
    (hgrad.comp hq)

lemma measurableSet_EvaluationReady (p : Public) (I : Instance p) (hg : Measurable I.grad) :
    MeasurableSet {s : State p.E | EvaluationReady p I s} :=
  (measurableSet_lt measurable_const measurable_state_A).inter
    ((measurableSet_lt measurable_const measurable_state_M).inter
      ((measurableSet_lt measurable_state_A measurable_const).inter
        (measurableSet_le (((hg.comp (measurable_queryPoint p)).sub measurable_state_center).norm)
          measurable_const)))

lemma measurable_phaseFailure (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable I.grad) (n : ℕ) :
    Measurable (Function.uncurry (phaseFailure p I g n)) := by
  have hfst : Measurable (Prod.fst : State p.E × (Fin n → p.Ω) → State p.E) := measurable_fst
  have hs := (measurable_state_stage (E := p.E)).comp hfst
  have hi := (measurable_state_iteration (E := p.E)).comp hfst
  have ha := (measurable_stepWeight p).comp hfst
  have hell := (measurable_of_countable (confidence p)).comp hi
  have hr : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
      p.R / (32 * stepWeight p w.1 * Real.sqrt (confidence p w.1.iteration))) :=
    measurable_const.div ((measurable_const.mul ha).mul hell.sqrt)
  have hp := ((measurable_finitePilot p hg n).sub
    ((hgrad.comp (measurable_pilotPoint p)).comp hfst)).norm
  have he := (measurable_finiteError p I hg hgrad n).norm
  unfold Function.uncurry phaseFailure
  apply Measurable.ite (measurableSet_eq_fun measurable_const ((measurable_phaseCost p).comp hfst))
  · apply Measurable.ite (measurableSet_le hs measurable_const)
    · exact Measurable.ite (measurableSet_lt measurable_const hp) measurable_const measurable_const
    · apply Measurable.ite ((measurableSet_eq_fun hs measurable_const).inter
        ((measurableSet_EvaluationReady p I hgrad).preimage hfst))
      · exact Measurable.ite (measurableSet_lt hr he) measurable_const measurable_const
      · exact measurable_const
  · exact measurable_const

lemma finiteError_tail_positive (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 < p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) (hr : EvaluationReady p I s) :
    (Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ).real
      {ξ | p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) <
        ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖} ≤
      Real.exp (-confidence p s.iteration) := by
  have hgrad' : gradient I.f (queryPoint p s) = I.grad (queryPoint p s) :=
    (hgrad _).gradient
  have hg : Measurable (g (queryPoint p s)) :=
    ho.measurable.comp measurable_prodMk_left
  have hmean : (∫ ω, g (queryPoint p s) ω ∂μ) = I.grad (queryPoint p s) := by
    rw [ho.unbiased, hgrad']
  have hmi := ho.moment_integrable (queryPoint p s)
  have hmoment := ho.moment (queryPoint p s)
  rw [hgrad'] at hmi hmoment
  have hb : 384 * p.σ ≤ clipRadius p s.iteration := le_max_left _ _
  have hB : 0 < clipRadius p s.iteration := lt_of_lt_of_le (by positivity) hb
  have hw := CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R)
    hr.1 hr.2.1
  have ha : 0 < stepWeight p s := hw.1
  have haT : stepWeight p s ≤ 4 * p.R ^ 2 / p.ε :=
    (stepWeight_le_A p hL1 hR hr.1).trans hr.2.2.1.le
  have hbatch : 1099511627776 *
      (varianceBound p s.iteration * stepWeight p s * confidence p s.iteration ^ 2 / p.ε +
        clipRadius p s.iteration * stepWeight p s * confidence p s.iteration ^ 2 / p.R) ≤
      (batchSize p s.iteration (stepWeight p s) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have ht := RobustGradient.finite_centered_clip_heavy_tail hg (ho.integrable _) hmean hB hσ
    hα hα2 hmi hmoment s.center (by linarith [hr.2.2.2]) ha hR hε
    (confidence_lower p hδ hδ1 s.iteration) haT _ (batchSize_pos p _ _)
    (le_max_right _ _) hbatch
  exact ht

lemma finiteError_tail (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) (hr : EvaluationReady p I s) :
    (Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ).real
      {ξ | p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) <
        ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖} ≤
      Real.exp (-confidence p s.iteration) := by
  by_cases hp : 0 < p.σ
  · exact finiteError_tail_positive p I μ ho hgrad hL1 hR hp hα hα2 hε hδ hδ1 s hr
  · have hz : p.σ = 0 := le_antisymm (not_lt.mp hp) hσ
    have hc : s.center = I.grad (queryPoint p s) := by
      have hh := hr.2.2.2
      rw [hz, mul_zero] at hh
      exact (sub_eq_zero.mp (norm_le_zero_iff.mp hh)).symm
    have he (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
        finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ = 0 := by
      unfold finiteError
      simp_rw [clipRadius_zero_noise p hz hα, centeredClip_zero_radius p]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, batchSize_zero_noise p hz hα]
      simp [hc]
    have ha : 0 < stepWeight p s :=
      (CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R) hr.1 hr.2.1).1
    have ht : 0 ≤ p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) := by positivity
    simp only [he, norm_zero, not_lt.mpr ht, Set.ofPred_false, measureReal_empty]
    exact Real.exp_nonneg _

lemma phaseFailure_mean (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) :
    (∫ ξ, phaseFailure p I g (phaseCost p s) s ξ
      ∂Measure.pi (fun _ : Fin (phaseCost p s) => μ)) ≤ phaseAllowance p s := by
  classical
  by_cases hp : s.stage ≤ 1
  · have hcost : phaseCost p s = pilotSize p s.iteration := by
      have hh : s.stage = 0 ∨ s.stage = 1 := by omega
      simp [phaseCost, hh]
    let A : Set (Fin (pilotSize p s.iteration) → p.Ω) :=
      {ξ | 96 * p.σ < ‖finitePilot p g (pilotSize p s.iteration) s ξ - I.grad (pilotPoint p s)‖}
    have hP : Measurable (fun ξ => finitePilot p g (pilotSize p s.iteration) s ξ) :=
      (measurable_finitePilot p ho.measurable _).comp measurable_prodMk_left
    have hA : MeasurableSet A := measurableSet_lt measurable_const (hP.sub_const _).norm
    rw [hcost]
    have he : (fun ξ => phaseFailure p I g (pilotSize p s.iteration) s ξ) =
        A.indicator (fun _ => (1 : ℝ)) := by
      funext ξ
      simp [phaseFailure, hcost, hp, A, Set.indicator]
    rw [he]
    change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (pilotSize p s.iteration) => μ)) ≤ _
    rw [integral_indicator_one hA]
    have hb := pilot_failure p I μ ho hgrad hσ hα hδ hδ1 (pilotPoint p s) s.iteration
    have hh := ENNReal.toReal_mono (by finiteness) hb
    simpa only [phaseAllowance, show s.stage ≤ 2 by omega, ite_true, Measure.real,
      ENNReal.toReal_ofReal (Real.exp_nonneg _), A, finitePilot] using hh
  · by_cases heval : s.stage = 2 ∧ EvaluationReady p I s
    · have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by
        simp [phaseCost, heval.1]
      let A : Set (Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :=
        {ξ | p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) <
          ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖}
      have hinput : Measurable (fun ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω =>
          (s, ξ)) := measurable_const.prodMk measurable_id
      have hE := (measurable_finiteError p I ho.measurable hgm
        (batchSize p s.iteration (stepWeight p s))).comp hinput
      simp only [Function.comp_def, Function.uncurry_apply_pair] at hE
      have hA : MeasurableSet A := measurableSet_lt measurable_const hE.norm
      rw [hcost]
      have he : (fun ξ => phaseFailure p I g (batchSize p s.iteration (stepWeight p s)) s ξ) =
          A.indicator (fun _ => (1 : ℝ)) := by
        funext ξ
        simp [phaseFailure, hcost, heval, A, Set.indicator]
      rw [he]
      change (∫ ξ, A.indicator 1 ξ
        ∂Measure.pi (fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ)) ≤ _
      rw [integral_indicator_one hA]
      simpa only [phaseAllowance, heval.1, Nat.reduceLeDiff, ite_true, A] using
        finiteError_tail p I μ ho hgrad hL1 hR hσ hα hα2 hε hδ hδ1 s heval.2
    · have he : (fun ξ => phaseFailure p I g (phaseCost p s) s ξ) = fun _ => (0 : ℝ) := by
        funext ξ
        simp [phaseFailure, hp, heval]
      rw [he, integral_zero]
      exact (phaseAllowance_range p hδ hδ1 s).1

lemma phaseFailure_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real
      {ξ | 1 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (phaseFailure p I g) n (initialState p) ξ} ≤ 3 * p.δ / (32 * Real.exp 1) := by
  exact RobustGradient.adaptive_failure_count_bound μ (measurable_phaseCost p)
    (measurable_phaseNext p I ho.measurable hprox) (measurable_phaseFailure p I ho.measurable hgm)
    (measurable_phaseAllowance p) (fun k s b => (phaseFailure_range p I g k s b).1)
    (fun k s b => (phaseFailure_range p I g k s b).2)
    (fun s => (phaseAllowance_range p hδ hδ1 s).1)
    (fun s => (phaseAllowance_range p hδ hδ1 s).2)
    (phaseFailure_mean p I μ ho hgrad hgm hL1 hR hσ hα hα2 hε hδ hδ1) n (initialState p)
    (fun ξ => accumulated_phaseAllowance_bound p I g hL0 hL1 hR hσ hΔ hδ ξ n)

lemma iid_phaseFailure_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (n : ℕ)
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    (ξ : ℕ → Ξ → p.Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P) :
    P.real {ω | 1 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseFailure p I g) n (initialState p) (fun k => ξ k ω)} ≤ 3 * p.δ / (32 * Real.exp 1) := by
  have hinput : Measurable (fun stream : ℕ → p.Ω => (initialState p, stream)) :=
    measurable_const.prodMk measurable_id
  have hm := (StochasticGeneralized.accumulated_measurable (measurable_phaseCost p)
    (measurable_phaseNext p I ho.measurable hprox)
    (measurable_phaseFailure p I ho.measurable hgm) n).comp hinput
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hm
  have hset : MeasurableSet {ω : ℕ → p.Ω | 1 ≤ StochasticGeneralized.accumulated
      (phaseCost p) (phaseNext p I g) (phaseFailure p I g) n (initialState p) ω} :=
    measurableSet_le measurable_const hm
  have ht := phaseFailure_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ
    hα hα2 hΔ hε hδ hδ1 n
  rw [← h_samples.stream_law.measureReal_preimage hset.nullMeasurableSet] at ht
  exact ht

lemma phaseFailure_zero_or_one (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) :
    phaseFailure p I g n s ξ = 0 ∨ phaseFailure p I g n s ξ = 1 := by
  unfold phaseFailure
  split_ifs <;> simp

lemma phaseFailure_zero_of_count_lt (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (s : State p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (hcount : StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseFailure p I g) n s ξ < 1) (j : ℕ) (hj : j < n) :
    let w := StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ j
    phaseFailure p I g (phaseCost p w.1) w.1 (fun i => w.2 i) = 0 := by
  dsimp only
  have hsum := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range n) => (phaseFailure_range p I g
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ i).1)
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ i).1
      (fun k => (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ i).2 k)).1)
    (Finset.mem_range.mpr hj)
  rw [← StochasticGeneralized.accumulated_eq_sum] at hsum
  rcases phaseFailure_zero_or_one p I g _
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ j).1
    (fun i => (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ j).2 i) with hz | ho
  · exact hz
  · rw [ho] at hsum
    linarith

lemma phaseFailure_pilot_accuracy (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (s : State p.E) (hs : s.stage ≤ 1) (ξ : Fin (phaseCost p s) → p.Ω)
    (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    ‖finitePilot p g (phaseCost p s) s ξ - I.grad (pilotPoint p s)‖ ≤ 96 * p.σ := by
  by_contra hn
  have hh := lt_of_not_ge hn
  simp [phaseFailure, hs, hh] at hf

lemma phaseFailure_evaluation_accuracy (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (s : State p.E) (hs : s.stage = 2) (hr : EvaluationReady p I s)
    (ξ : Fin (phaseCost p s) → p.Ω) (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    ‖finiteError p I g (phaseCost p s) s ξ‖ ≤
      p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) := by
  by_contra hn
  have hh := lt_of_not_ge hn
  simp [phaseFailure, hs, hr, hh] at hf

lemma phaseNext_first_pilot (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 0)
    (hreceived : s.received = 0) (hreplies : s.replies = fun _ => 0)
    (ξ : Fin (pilotSize p s.iteration) → p.Ω) :
    phaseNext p I g (pilotSize p s.iteration) s ξ =
      { s with
        stage := 1, M := p.L0 + p.L1 * (‖finitePilot p g (pilotSize p s.iteration) s ξ‖ + 96 * p.σ),
        received := 0, replies := fun _ => 0 } := by
  let m := pilotSize p s.iteration
  let ξ' : ℕ → p.Ω := fun k => if hk : k < m then ξ ⟨k, hk⟩ else ξ ⟨0, pilotSize_pos p s.iteration⟩
  have hpref : (fun i : Fin m => ξ' i) = ξ := by
    funext i
    simp only [ξ', dite_eq_left i.isLt]
    rfl
  rw [← hpref, phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ ξ' m hs]
  have he : { s with stage := 0, received := 0, replies := fun _ => 0 } = s := by
    cases s
    simp_all
  have hh := rawAdvance_first_pilot p I g ξ' s 0
  rw [he] at hh
  rw [hh]
  simp [samplePilot, finitePilot, pilotPoint, hstage]

lemma phaseNext_second_pilot (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 1)
    (hreceived : s.received = 0) (hreplies : s.replies = fun _ => 0)
    (ξ : Fin (pilotSize p s.iteration) → p.Ω) :
    phaseNext p I g (pilotSize p s.iteration) s ξ =
      { s with
        stage := 2, center := finitePilot p g (pilotSize p s.iteration) s ξ,
        total := 0, received := 0, replies := fun _ => 0 } := by
  let m := pilotSize p s.iteration
  let ξ' : ℕ → p.Ω := fun k => if hk : k < m then ξ ⟨k, hk⟩ else ξ ⟨0, pilotSize_pos p s.iteration⟩
  have hpref : (fun i : Fin m => ξ' i) = ξ := by
    funext i
    simp only [ξ', dite_eq_left i.isLt]
    rfl
  rw [← hpref, phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ ξ' m hs]
  have he : { s with stage := 1, received := 0, replies := fun _ => 0 } = s := by
    cases s
    simp_all
  have hh := rawAdvance_second_pilot p I g ξ' s 0
  rw [he] at hh
  rw [hh]
  simp [samplePilot, finitePilot, pilotPoint, hstage]


lemma phaseNext_evaluation_error (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hreceived : s.received = 0) (htotal : s.total = 0)
    (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
    evaluationError p I (phaseNext p I g (batchSize p s.iteration (stepWeight p s)) s ξ) =
      finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ := by
  rw [phaseNext_evaluation p I g hL0 hL1 hR hσ s hs hstage hreceived htotal]
  rfl

lemma first_pilot_curvature_bounds (p : Public) (I : Instance p) (s : State p.E)
    (hL1 : 0 ≤ p.L1) (v : p.E) (hv : ‖v - I.grad s.x‖ ≤ 96 * p.σ) :
    p.L0 + p.L1 * ‖I.grad s.x‖ ≤ p.L0 + p.L1 * (‖v‖ + 96 * p.σ) ∧
    p.L0 + p.L1 * (‖v‖ + 96 * p.σ) ≤
      p.L0 + p.L1 * ‖I.grad s.x‖ + 192 * p.L1 * p.σ := by
  have h1 : ‖I.grad s.x‖ ≤ ‖v‖ + 96 * p.σ := by
    have hv' : ‖I.grad s.x - v‖ ≤ 96 * p.σ := by
      rw [norm_sub_rev]
      exact hv
    have ht := norm_add_le (I.grad s.x - v) v
    rw [sub_add_cancel] at ht
    linarith
  have h2 : ‖v‖ ≤ ‖I.grad s.x‖ + 96 * p.σ := by
    have ht := norm_add_le (v - I.grad s.x) (I.grad s.x)
    rw [sub_add_cancel] at ht
    linarith
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hL1,
    mul_le_mul_of_nonneg_left h2 hL1]


lemma second_pilot_ready (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (hstage : s.stage = 1)
    (ha : s.A < 4 * p.R ^ 2 / p.ε)
    (ξ : Fin (pilotSize p s.iteration) → p.Ω)
    (hv : ‖finitePilot p g (pilotSize p s.iteration) s ξ -
      I.grad (pilotPoint p s)‖ ≤ 96 * p.σ) :
    EvaluationReady p I (phaseNext p I g (pilotSize p s.iteration) s ξ) := by
  rw [phaseNext_second_pilot p I g hL0 hL1 hR hσ s hs hstage
    (he.1 (Or.inr hstage)).1 (he.1 (Or.inr hstage)).2]
  refine ⟨hs.1, hs.2 (by omega), ha, ?_⟩
  change ‖I.grad (queryPoint p s) - finitePilot p g (pilotSize p s.iteration) s ξ‖ ≤ _
  rw [norm_sub_rev]
  simpa only [pilotPoint, hstage, Nat.reduceEqDiff, ite_false] using hv


lemma evaluation_accuracy_weighted (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hr : EvaluationReady p I s) (ξ : Fin (phaseCost p s) → p.Ω)
    (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    stepWeight p s * ‖finiteError p I g (phaseCost p s) s ξ‖ ≤
      p.R / (32 * Real.sqrt (confidence p s.iteration)) := by
  have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inl hstage))
  have hb := phaseFailure_evaluation_accuracy p I g s hstage hr ξ hf
  have hl := confidence_lower p hδ hδ1 s.iteration
  have hl0 : 0 < Real.sqrt (confidence p s.iteration) := Real.sqrt_pos.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hb ha.le
  have hid : stepWeight p s * (p.R /
      (32 * stepWeight p s * Real.sqrt (confidence p s.iteration))) =
      p.R / (32 * Real.sqrt (confidence p s.iteration)) := by
    field_simp
  rwa [hid] at hh

end OracleTemplate.StochasticCompositeGeneralized
