import LongTails.Proofs.StochasticCompositeGeneralizedFailures

open MeasureTheory
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

noncomputable def phaseEnergy (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if n = phaseCost p s ∧ s.stage = 2 ∧ EvaluationReady p I s then
    min (stepWeight p s ^ 2 * ‖finiteError p I g n s ξ‖ ^ 2)
      (p.R ^ 2 / (1024 * confidence p 0)) else 0

noncomputable def phaseEnergyMean (p : Public) (I : Instance p) (s : State p.E) : ℝ := by
  classical
  exact if s.stage = 2 ∧ EvaluationReady p I s then
    10 * p.ε * stepWeight p s / (1099511627776 * confidence p 0 ^ 2) else 0

lemma phaseEnergy_range (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) :
    0 ≤ phaseEnergy p I g n s ξ ∧ phaseEnergy p I g n s ξ ≤
      p.R ^ 2 / (1024 * confidence p 0) := by
  have hl := confidence_lower p hδ hδ1 0
  have hB : 0 ≤ p.R ^ 2 / (1024 * confidence p 0) := by positivity
  unfold phaseEnergy
  split_ifs
  · exact ⟨le_min (by positivity) hB, min_le_right _ _⟩
  · exact ⟨le_refl _, hB⟩

lemma measurable_phaseEnergy (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable I.grad) (n : ℕ) :
    Measurable (Function.uncurry (phaseEnergy p I g n)) := by
  have hs : MeasurableSet {w : State p.E × (Fin n → p.Ω) |
      n = phaseCost p w.1 ∧ w.1.stage = 2 ∧ EvaluationReady p I w.1} :=
    (measurableSet_eq_fun measurable_const ((measurable_phaseCost p).comp measurable_fst)).inter
      ((measurableSet_eq_fun (measurable_state_stage.comp measurable_fst) measurable_const).inter
        ((measurableSet_EvaluationReady p I hgrad).preimage measurable_fst))
  exact Measurable.ite hs (((measurable_stepWeight p).comp measurable_fst).pow_const 2 |>.mul
    ((measurable_finiteError p I hg hgrad n).norm.pow_const 2) |>.min measurable_const) measurable_const

lemma measurable_phaseEnergyMean (p : Public) (I : Instance p) (hgrad : Measurable I.grad) :
    Measurable (phaseEnergyMean p I) := by
  have hs : MeasurableSet {s : State p.E | s.stage = 2 ∧ EvaluationReady p I s} :=
    (measurableSet_eq_fun (measurable_state_stage (E := p.E)) measurable_const).inter
    (measurableSet_EvaluationReady p I hgrad)
  exact Measurable.ite hs (((measurable_stepWeight p).const_mul (10 * p.ε)).div_const _) measurable_const


lemma finiteError_energy_mean_positive (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 < p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) (hr : EvaluationReady p I s) :
    let Q := Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ
    Integrable (fun ξ => stepWeight p s ^ 2 *
      ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖ ^ 2) Q ∧
    (∫ ξ, stepWeight p s ^ 2 *
      ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖ ^ 2 ∂Q) ≤
      10 * p.ε * stepWeight p s / (1099511627776 * confidence p s.iteration ^ 2) := by
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
  have hn : 0 ≤ clipRadius p s.iteration * stepWeight p s * confidence p s.iteration ^ 2 / p.R := by positivity
  have hm : 1099511627776 * (2 * clipRadius p s.iteration) ^ (2 - p.α) *
      p.σ ^ p.α * stepWeight p s * confidence p s.iteration ^ 2 / p.ε ≤
      (batchSize p s.iteration (stepWeight p s) : ℝ) := by
    dsimp only [varianceBound] at hbatch
    ring_nf at hbatch hn ⊢
    linarith
  exact RobustGradient.finite_clipped_energy_mean hg (ho.integrable _) hmean hB hσ
    hα hα2 hmi hmoment s.center (by linarith [hr.2.2.2]) ha hR hε
    (by linarith [confidence_lower p hδ hδ1 s.iteration]) haT _ (batchSize_pos p _ _)
    (le_max_right _ _) hm


lemma finiteError_energy_mean (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) (hr : EvaluationReady p I s) :
    let Q := Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ
    Integrable (fun ξ => stepWeight p s ^ 2 *
      ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖ ^ 2) Q ∧
    (∫ ξ, stepWeight p s ^ 2 *
      ‖finiteError p I g (batchSize p s.iteration (stepWeight p s)) s ξ‖ ^ 2 ∂Q) ≤
      10 * p.ε * stepWeight p s / (1099511627776 * confidence p s.iteration ^ 2) := by
  by_cases hp : 0 < p.σ
  · exact finiteError_energy_mean_positive p I μ ho hgrad hL1 hR hp hα hα2 hε hδ hδ1 s hr
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
    dsimp only
    simp only [he, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      integral_zero]
    exact ⟨integrable_const 0, by positivity⟩


lemma phaseEnergyMean_le_weight (p : Public) (I : Instance p)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (s : State p.E) (hs : WellFormed s) :
    0 ≤ phaseEnergyMean p I s ∧ phaseEnergyMean p I s ≤
      (10 * p.ε / (1099511627776 * confidence p 0 ^ 2)) * phaseWeight p s := by
  classical
  by_cases hstage : s.stage = 2
  · have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inl hstage))
    simp only [phaseEnergyMean, phaseWeight, hstage, true_and, ite_true]
    split_ifs
    · constructor
      · positivity
      · exact le_of_eq (by ring)
    · exact ⟨le_refl _, by positivity⟩
  · simp [phaseEnergyMean, phaseWeight, hstage]

lemma accumulated_phaseEnergyMean_bound (p : Public.{0}) (I : Instance p)
    (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (fun _ s _ => phaseEnergyMean p I s) n (initialState p) ξ ≤
        80 * p.R ^ 2 / (1099511627776 * confidence p 0 ^ 2) := by
  let C := 10 * p.ε / (1099511627776 * confidence p 0 ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw := accumulated_phaseWeight_bound p I g hL0 hL1 hR hσ hΔ hε ξ n
  have hm : StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (fun _ s _ => phaseEnergyMean p I s) n (initialState p) ξ ≤
      C * StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (fun _ s _ => phaseWeight p s) n (initialState p) ξ := by
    simp only [StochasticGeneralized.accumulated_eq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact (phaseEnergyMean_le_weight p I hL1 hR hε _
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ (initialState p)
        (initialState_wellFormed p hR hΔ) j)).2
  apply hm.trans ((mul_le_mul_of_nonneg_left hw hC).trans_eq ?_)
  dsimp only [C]
  field_simp
  ring


lemma phaseEnergy_mean (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) :
    (∫ ξ, phaseEnergy p I g (phaseCost p s) s ξ
      ∂Measure.pi (fun _ : Fin (phaseCost p s) => μ)) ≤ phaseEnergyMean p I s := by
  classical
  by_cases hs : s.stage = 2 ∧ EvaluationReady p I s
  · have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by
      simp [phaseCost, hs.1]
    have ht := finiteError_energy_mean p I μ ho hgrad hL1 hR hσ hα hα2 hε hδ hδ1 s hs.2
    dsimp only at ht
    have hi : Integrable (fun ξ => phaseEnergy p I g (phaseCost p s) s ξ)
        (Measure.pi fun _ : Fin (phaseCost p s) => μ) := by
      apply Integrable.of_bound ((measurable_phaseEnergy p I ho.measurable hgm _).comp
        measurable_prodMk_left).aestronglyMeasurable (p.R ^ 2 / (1024 * confidence p 0))
      apply Filter.Eventually.of_forall
      intro ξ
      dsimp only [Function.comp_def, Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseEnergy_range p I g hδ hδ1 _ s ξ).1]
      exact (phaseEnergy_range p I g hδ hδ1 _ s ξ).2
    rw [hcost] at hi ⊢
    have hle : (∫ ξ, phaseEnergy p I g (batchSize p s.iteration (stepWeight p s)) s ξ
        ∂Measure.pi (fun _ => μ)) ≤
        10 * p.ε * stepWeight p s / (1099511627776 * confidence p s.iteration ^ 2) := by
      apply (integral_mono hi ht.1 ?_).trans ht.2
      intro ξ
      simp only [phaseEnergy, ← hcost, hs.1, hs.2, and_self, ite_true]
      exact min_le_left _ _
    apply hle.trans
    simp only [phaseEnergyMean, hs]
    have ha : 0 < stepWeight p s :=
      (CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R) hs.2.1 hs.2.2.1).1
    have hl := confidence_lower p hδ hδ1 0
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    exact confidence_mono p hδ (Nat.zero_le _)
  · have he : (fun ξ => phaseEnergy p I g (phaseCost p s) s ξ) = fun _ => (0 : ℝ) := by
      funext ξ
      simp [phaseEnergy, hs]
    rw [he, integral_zero]
    simp [phaseEnergyMean, hs]


lemma phaseEnergy_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real
      {ξ | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (phaseEnergy p I g) n (initialState p) ξ} ≤ Real.exp (-confidence p 0) := by
  have hl := confidence_lower p hδ hδ1 0
  have hl0 : 0 < confidence p 0 := by linarith
  have hθ : 0 ≤ 64 * confidence p 0 / p.R ^ 2 := by positivity
  have hsmall : (64 * confidence p 0 / p.R ^ 2) *
      (p.R ^ 2 / (1024 * confidence p 0)) ≤ 1 := by
    have he : (64 * confidence p 0 / p.R ^ 2) *
        (p.R ^ 2 / (1024 * confidence p 0)) = 1 / 16 := by field_simp; norm_num
    rw [he]
    norm_num
  have ht := RobustGradient.adaptive_nonnegative_energy_tail μ (measurable_phaseCost p)
    (measurable_phaseNext p I ho.measurable hprox) (measurable_phaseEnergy p I ho.measurable hgm)
    (measurable_phaseEnergyMean p I hgm) hθ hsmall
    (fun s ξ => (phaseEnergy_range p I g hδ hδ1 _ s ξ).1)
    (fun s ξ => (phaseEnergy_range p I g hδ hδ1 _ s ξ).2)
    (phaseEnergy_mean p I μ ho hgrad hgm hL1 hR hσ hα hα2 hε hδ hδ1) n (initialState p)
    (fun ξ => accumulated_phaseEnergyMean_bound p I g hL0 hL1 hR hσ hΔ hε ξ n)
    (t := p.R ^ 2 / 10)
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  field_simp
  nlinarith [sq_nonneg (confidence p 0 - 1)]

lemma iid_phaseEnergy_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
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
    P.real {ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseEnergy p I g) n (initialState p) (fun k => ξ k ω)} ≤ Real.exp (-confidence p 0) := by
  have hinput : Measurable (fun stream : ℕ → p.Ω => (initialState p, stream)) :=
    measurable_const.prodMk measurable_id
  have hm := (StochasticGeneralized.accumulated_measurable (measurable_phaseCost p)
    (measurable_phaseNext p I ho.measurable hprox)
    (measurable_phaseEnergy p I ho.measurable hgm) n).comp hinput
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hm
  have hset : MeasurableSet {ω : ℕ → p.Ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated
      (phaseCost p) (phaseNext p I g) (phaseEnergy p I g) n (initialState p) ω} :=
    measurableSet_le measurable_const hm
  have ht := phaseEnergy_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ
    hα hα2 hΔ hε hδ hδ1 n
  rw [← h_samples.stream_law.measureReal_preimage hset.nullMeasurableSet] at ht
  exact ht


lemma phaseEnergy_eq_square (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hr : EvaluationReady p I s) (ξ : Fin (phaseCost p s) → p.Ω)
    (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    phaseEnergy p I g (phaseCost p s) s ξ =
      stepWeight p s ^ 2 * ‖finiteError p I g (phaseCost p s) s ξ‖ ^ 2 := by
  have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inl hstage))
  have hl := confidence_lower p hδ hδ1 s.iteration
  have hl0 := confidence_lower p hδ hδ1 0
  have hw := evaluation_accuracy_weighted p I g hL1 hR hδ hδ1 s hs hstage hr ξ hf
  have hsq := pow_le_pow_left₀ (mul_nonneg ha.le (norm_nonneg _)) hw 2
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by linarith)] at hsq
  norm_num only [show (32 : ℝ) ^ 2 = 1024 by norm_num] at hsq
  have hb : stepWeight p s ^ 2 * ‖finiteError p I g (phaseCost p s) s ξ‖ ^ 2 ≤
      p.R ^ 2 / (1024 * confidence p 0) := by
    apply hsq.trans
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    gcongr
    exact confidence_mono p hδ (Nat.zero_le _)
  simp [phaseEnergy, hstage, hr, min_eq_left hb]

lemma phaseEnergy_prefix_le (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) (ξ : ℕ → p.Ω)
    {j n : ℕ} (hjn : j ≤ n) :
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseEnergy p I g) j s ξ ≤
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (phaseEnergy p I g) n s ξ := by
  simp only [StochasticGeneralized.accumulated_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
  intro i hi hj
  exact (phaseEnergy_range p I g hδ hδ1 _ _ _).1


end OracleTemplate.StochasticCompositeGeneralized
