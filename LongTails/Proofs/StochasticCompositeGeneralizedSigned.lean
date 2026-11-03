import LongTails.Proofs.StochasticCompositeGeneralizedFailures



open MeasureTheory
open scoped RealInnerProductSpace
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

noncomputable def guardedOracleError (p : Public) (I : Instance p)
    (g : p.E → p.Ω → p.E) (s : State p.E) (ω : p.Ω) : p.E :=
  RobustGradient.guardedError (clipRadius p s.iteration) (I.grad (queryPoint p s)) s.center
    (g (queryPoint p s) ω)

noncomputable def oracleBias (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (s : State p.E) : p.E :=
  ∫ ω, guardedOracleError p I g s ω ∂μ

noncomputable def centeredOracleError (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (s : State p.E) (ω : p.Ω) : p.E :=
  guardedOracleError p I g s ω - oracleBias p I μ g s

lemma measurable_guardedOracleError (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable I.grad) :
    Measurable (Function.uncurry (guardedOracleError p I g)) := by
  have hx : Measurable (fun w : State p.E × p.Ω => queryPoint p w.1) :=
    (measurable_queryPoint p).comp measurable_fst
  exact RobustGradient.measurable_guardedError.comp
    (((measurable_clipRadius p).comp (measurable_state_iteration.comp measurable_fst)).prodMk
      ((hgrad.comp hx).prodMk ((measurable_state_center.comp measurable_fst).prodMk
        (hg.comp (hx.prodMk measurable_snd)))))

lemma measurable_oracleBias (p : Public) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable I.grad) : Measurable (oracleBias p I μ g) :=
  (measurable_guardedOracleError p I hg hgrad).stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_centeredOracleError (p : Public) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable I.grad) : Measurable (Function.uncurry (centeredOracleError p I μ g)) :=
  (measurable_guardedOracleError p I hg hgrad).sub
    ((measurable_oracleBias p I μ hg hgrad).comp measurable_fst)


lemma centeredOracleError_moments_positive (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hσ : 0 < p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (s : State p.E) :
    Measurable (centeredOracleError p I μ g s) ∧
    Integrable (centeredOracleError p I μ g s) μ ∧
    Integrable (fun ω => ‖centeredOracleError p I μ g s ω‖ ^ 2) μ ∧
    (∫ ω, centeredOracleError p I μ g s ω ∂μ) = 0 ∧
    (∀ ω, ‖centeredOracleError p I μ g s ω‖ ≤ 3 * clipRadius p s.iteration) ∧
    (∫ ω, ‖centeredOracleError p I μ g s ω‖ ^ 2 ∂μ) ≤ varianceBound p s.iteration := by
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
  exact RobustGradient.guarded_centered_heavy_moments hg (ho.integrable _) hmean hB
    hα.le hα2 hmi hmoment s.center


lemma guardedOracleError_zero_noise (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hσ : p.σ = 0) (hα : 1 < p.α) (s : State p.E) (ω : p.Ω) :
    guardedOracleError p I g s ω = 0 := by
  unfold guardedOracleError
  rw [clipRadius_zero_noise p hσ hα]
  apply norm_le_zero_iff.mp
  simpa using RobustGradient.guardedError_bound (le_refl (0 : ℝ))
    (I.grad (queryPoint p s)) s.center (g (queryPoint p s) ω)

lemma centeredOracleError_zero_noise (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (hσ : p.σ = 0) (hα : 1 < p.α) (s : State p.E) (ω : p.Ω) :
    centeredOracleError p I μ g s ω = 0 := by
  simp [centeredOracleError, oracleBias, guardedOracleError_zero_noise p I g hσ hα]

lemma centeredOracleError_moments (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (s : State p.E) :
    Measurable (centeredOracleError p I μ g s) ∧
    Integrable (centeredOracleError p I μ g s) μ ∧
    Integrable (fun ω => ‖centeredOracleError p I μ g s ω‖ ^ 2) μ ∧
    (∫ ω, centeredOracleError p I μ g s ω ∂μ) = 0 ∧
    (∀ ω, ‖centeredOracleError p I μ g s ω‖ ≤ 3 * clipRadius p s.iteration) ∧
    (∫ ω, ‖centeredOracleError p I μ g s ω‖ ^ 2 ∂μ) ≤ varianceBound p s.iteration := by
  by_cases hp : 0 < p.σ
  · exact centeredOracleError_moments_positive p I μ ho hgrad hp hα hα2 s
  · have hz : p.σ = 0 := le_antisymm (not_lt.mp hp) hσ
    have he : centeredOracleError p I μ g s = fun _ => 0 := by
      funext ω
      exact centeredOracleError_zero_noise p I μ g hz hα s ω
    rw [he]
    simp only [measurable_const, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, true_and]
    refine ⟨integrable_const 0, integrable_const 0, ?_, ?_⟩
    · intro ω
      rw [clipRadius_zero_noise p hz hα]
      norm_num
    · simp [varianceBound, hz, Real.zero_rpow (by linarith : p.α ≠ 0)]


noncomputable def finiteSignedError (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) : ℝ :=
  stepWeight p s * ⟪xs - s.z, (1 / (n : ℝ)) • ∑ i, centeredOracleError p I μ g s (ξ i)⟫

lemma measurable_finiteSignedError (p : Public) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable I.grad) (xs : p.E) (n : ℕ) :
    Measurable (Function.uncurry (finiteSignedError p I μ g xs n)) := by
  have ht (i : Fin n) : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
      centeredOracleError p I μ g w.1 (w.2 i)) := by
    have hinput : Measurable (fun w : State p.E × (Fin n → p.Ω) => (w.1, w.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    have hh := (measurable_centeredOracleError p I μ hg hgrad).comp hinput
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hh
  exact ((measurable_stepWeight p).comp measurable_fst).mul
    ((measurable_const.sub (measurable_state_z.comp measurable_fst)).inner
      ((Finset.measurable_sum Finset.univ (fun i _ => ht i)).const_smul (1 / (n : ℝ))))


lemma batchSize_component_bounds (p : Public) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hσ : 0 ≤ p.σ) (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    1099511627776 * varianceBound p k * a * confidence p k ^ 2 / p.ε ≤ (batchSize p k a : ℝ) ∧
    1099511627776 * clipRadius p k * a * confidence p k ^ 2 / p.R ≤ (batchSize p k a : ℝ) := by
  have hB : 0 ≤ clipRadius p k := le_trans (by positivity) (le_max_left _ _)
  have hV : 0 ≤ varianceBound p k := mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hσ _)
  have h1 : 0 ≤ varianceBound p k * a * confidence p k ^ 2 / p.ε := by positivity
  have h2 : 0 ≤ clipRadius p k * a * confidence p k ^ 2 / p.R := by positivity
  have hb : 1099511627776 * (varianceBound p k * a * confidence p k ^ 2 / p.ε +
      clipRadius p k * a * confidence p k ^ 2 / p.R) ≤ (batchSize p k a : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  constructor
  · have hh := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2)
      (show (0 : ℝ) ≤ 1099511627776 by norm_num)).trans hb
    convert hh using 1; ring
  · have hh := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h1)
      (show (0 : ℝ) ≤ 1099511627776 by norm_num)).trans hb
    convert hh using 1; ring

lemma finiteSignedError_mgf (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (s : State p.E)
    (hr : EvaluationReady p I s) (hd : ‖xs - s.z‖ ≤ 4 * p.R) :
    let θ := 64 * confidence p 0 / p.R ^ 2
    let Q := Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ
    Integrable (fun ξ => Real.exp (θ * finiteSignedError p I μ g xs
      (batchSize p s.iteration (stepWeight p s)) s ξ)) Q ∧
      (∫ ξ, Real.exp (θ * finiteSignedError p I μ g xs
        (batchSize p s.iteration (stepWeight p s)) s ξ) ∂Q) ≤
      Real.exp (16 * θ ^ 2 * p.R ^ 2 * p.ε * stepWeight p s /
        (1099511627776 * confidence p 0 ^ 2)) := by
  have ha : 0 < stepWeight p s :=
    (CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R) hr.1 hr.2.1).1
  have hm : 0 < (batchSize p s.iteration (stepWeight p s) : ℝ) := by
    exact_mod_cast batchSize_pos p s.iteration (stepWeight p s)
  have hB : 0 ≤ clipRadius p s.iteration := le_trans (by positivity) (le_max_left _ _)
  have hV : 0 ≤ varianceBound p s.iteration := mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hσ _)
  have hl := confidence_lower p hδ hδ1 0
  have hlm := confidence_mono p hδ (Nat.zero_le s.iteration)
  have hb := batchSize_component_bounds p hR hε hσ s.iteration ha.le
  have hsmall := RobustGradient.signed_batch_smallness ha.le hR hl hlm hB hm hd hb.2
  have hX := centeredOracleError_moments p I μ ho hgrad hσ hα hα2 s
  have ht := RobustGradient.finite_centered_inner_mgf hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1
    (by positivity : 0 ≤ 64 * confidence p 0 / p.R ^ 2) ha.le (xs - s.z)
    hX.2.2.2.2.1 hX.2.2.2.2.2 (batchSize_pos p _ _) hsmall
  dsimp only
  have he (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
      (64 * confidence p 0 / p.R ^ 2) * finiteSignedError p I μ g xs
        (batchSize p s.iteration (stepWeight p s)) s ξ =
      (64 * confidence p 0 / p.R ^ 2) * stepWeight p s *
        ⟪xs - s.z, (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) •
          ∑ i, centeredOracleError p I μ g s (ξ i)⟫ := by
    unfold finiteSignedError
    ring
  simp_rw [he]
  refine ⟨ht.1, ht.2.trans (Real.exp_le_exp.mpr ?_)⟩
  exact RobustGradient.signed_batch_compensation ha hR hε (by linarith) hlm hV hm
    (norm_nonneg _) hd hb.1


def SignedReady (p : Public) (I : Instance p) (xs : p.E) (w : State p.E × ℝ) : Prop :=
  w.1.stage = 2 ∧ EvaluationReady p I w.1 ∧ ‖xs - w.1.z‖ ≤ 4 * p.R ∧ w.2 < p.R ^ 2 / 10

noncomputable def phaseSigned (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (w : State p.E × ℝ) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if n = phaseCost p w.1 ∧ SignedReady p I xs w then
    finiteSignedError p I μ g xs n w.1 ξ else 0

noncomputable def phaseSignedNext (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (w : State p.E × ℝ) (ξ : Fin n → p.Ω) :
    State p.E × ℝ :=
  (phaseNext p I g n w.1 ξ, w.2 + phaseSigned p I μ g xs n w ξ)

lemma measurableSet_SignedReady (p : Public) (I : Instance p) (hgrad : Measurable I.grad)
    (xs : p.E) : MeasurableSet {w | SignedReady p I xs w} :=
  (measurableSet_eq_fun (measurable_state_stage.comp measurable_fst) measurable_const).inter
    (((measurableSet_EvaluationReady p I hgrad).preimage measurable_fst).inter
      ((measurableSet_le (measurable_const.sub (measurable_state_z.comp measurable_fst)).norm
        measurable_const).inter (measurableSet_lt measurable_snd measurable_const)))

lemma measurable_phaseSigned (p : Public) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable I.grad) (xs : p.E) (n : ℕ) :
    Measurable (Function.uncurry (phaseSigned p I μ g xs n)) := by
  have hinput : Measurable (fun w : (State p.E × ℝ) × (Fin n → p.Ω) => (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hh := (measurable_finiteSignedError p I μ hg hgrad xs n).comp hinput
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hh
  exact Measurable.ite
    ((measurableSet_eq_fun measurable_const ((measurable_phaseCost p).comp
      (measurable_fst.comp measurable_fst))).inter
      ((measurableSet_SignedReady p I hgrad xs).preimage measurable_fst)) hh measurable_const

lemma measurable_phaseSignedNext (p : Public) (I : Instance p) (μ : Measure p.Ω) [SFinite μ]
    {g : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry g))
    (hgrad : Measurable I.grad) (xs : p.E)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (n : ℕ) :
    Measurable (Function.uncurry (phaseSignedNext p I μ g xs n)) := by
  have hinput : Measurable (fun w : (State p.E × ℝ) × (Fin n → p.Ω) => (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hh := (measurable_phaseNext p I hg hprox n).comp hinput
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hh
  exact hh.prodMk ((measurable_snd.comp measurable_fst).add
    (measurable_phaseSigned p I μ hg hgrad xs n))


lemma phaseSigned_zero_after_crossing (p : Public) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (n : ℕ) (w : State p.E × ℝ) (ξ : Fin n → p.Ω)
    (ht : p.R ^ 2 / 10 ≤ w.2) : phaseSigned p I μ g xs n w ξ = 0 := by
  simp [phaseSigned, SignedReady, not_lt.mpr ht]

lemma signedTrace_projection (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (s : State p.E) (r : ℝ) (ξ : ℕ → p.Ω) (n : ℕ) :
    let w := StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ n
    (w.1.1, w.2) = StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n := by
  let π : ((State p.E × ℝ) × (ℕ → p.Ω)) → State p.E × (ℕ → p.Ω) :=
    fun w => (w.1.1, w.2)
  have hh : Function.Semiconj π
      (StochasticGeneralized.blockAdvance (fun w : State p.E × ℝ => phaseCost p w.1)
        (phaseSignedNext p I μ g xs))
      (StochasticGeneralized.blockAdvance (phaseCost p) (phaseNext p I g)) := fun _ => rfl
  exact hh.iterate_right n ((s, r), ξ)

lemma signedTrace_accumulated (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (s : State p.E) (r : ℝ) (ξ : ℕ → p.Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ n).1.2 = r +
    StochasticGeneralized.accumulated (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (phaseSigned p I μ g xs) n (s, r) ξ := by
  simp only [StochasticGeneralized.accumulated_eq_sum]
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ, Finset.sum_range_succ]
    dsimp only [StochasticGeneralized.blockAdvance, phaseSignedNext]
    rw [ih]
    ring

lemma signedTrace_crossing_persists (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (s : State p.E) (r : ℝ) (ξ : ℕ → p.Ω)
    {j n : ℕ} (hjn : j ≤ n)
    (hj : p.R ^ 2 / 10 ≤ (StochasticGeneralized.blockTrace
      (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ j).1.2) :
    p.R ^ 2 / 10 ≤ (StochasticGeneralized.blockTrace
      (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ n).1.2 := by
  induction n, hjn using Nat.le_induction with
  | base => exact hj
  | succ n hn ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance, phaseSignedNext]
    rw [phaseSigned_zero_after_crossing p I μ g xs _ _ _ ih, add_zero]
    exact ih


noncomputable def phaseSignedComp (p : Public) (I : Instance p) (xs : p.E) (w : State p.E × ℝ) : ℝ := by
  classical
  exact if SignedReady p I xs w then
    16 * (64 * confidence p 0 / p.R ^ 2) ^ 2 * p.R ^ 2 * p.ε * stepWeight p w.1 /
      (1099511627776 * confidence p 0 ^ 2) else 0

lemma measurable_phaseSignedComp (p : Public) (I : Instance p) (hgrad : Measurable I.grad)
    (xs : p.E) : Measurable (phaseSignedComp p I xs) :=
  Measurable.ite (measurableSet_SignedReady p I hgrad xs)
    ((((measurable_stepWeight p).comp measurable_fst).const_mul _).div_const _) measurable_const

lemma phaseSigned_mgf (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (w : State p.E × ℝ) :
    let θ := 64 * confidence p 0 / p.R ^ 2
    let Q := Measure.pi fun _ : Fin (phaseCost p w.1) => μ
    Integrable (fun ξ => Real.exp (θ * phaseSigned p I μ g xs (phaseCost p w.1) w ξ)) Q ∧
      (∫ ξ, Real.exp (θ * phaseSigned p I μ g xs (phaseCost p w.1) w ξ) ∂Q) ≤
      Real.exp (phaseSignedComp p I xs w) := by
  classical
  dsimp only
  by_cases hw : SignedReady p I xs w
  · have he (ξ : Fin (phaseCost p w.1) → p.Ω) :
        phaseSigned p I μ g xs (phaseCost p w.1) w ξ =
        finiteSignedError p I μ g xs (phaseCost p w.1) w.1 ξ := by
      simp [phaseSigned, hw]
    simp only [he, phaseSignedComp, hw, ite_true]
    have hcost : phaseCost p w.1 = batchSize p w.1.iteration (stepWeight p w.1) := by
      simp [phaseCost, hw.1]
    rw [hcost]
    exact finiteSignedError_mgf p I μ ho hgrad hL1 hR hσ hα hα2 hε hδ hδ1 xs w.1 hw.2.1 hw.2.2.1
  · have he (ξ : Fin (phaseCost p w.1) → p.Ω) :
        phaseSigned p I μ g xs (phaseCost p w.1) w ξ = 0 := by simp [phaseSigned, hw]
    simp only [he, phaseSignedComp, hw, ite_false, mul_zero, Real.exp_zero,
      integral_const, probReal_univ, smul_eq_mul, one_mul, le_refl, and_true]
    exact integrable_const 1

lemma phaseSignedComp_le_weight (p : Public) (I : Instance p) (xs : p.E)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hε : 0 < p.ε)
    (w : State p.E × ℝ) (hs : WellFormed w.1) :
    phaseSignedComp p I xs w ≤
      (16 * (64 * confidence p 0 / p.R ^ 2) ^ 2 * p.R ^ 2 * p.ε /
        (1099511627776 * confidence p 0 ^ 2)) * phaseWeight p w.1 := by
  classical
  by_cases hw : SignedReady p I xs w
  · simp only [phaseSignedComp, hw, ite_true, phaseWeight, hw.1]
    exact le_of_eq (by ring)
  · simp only [phaseSignedComp, hw, ite_false]
    have hh := phaseWeight_nonneg p hL1 hR hs
    positivity


lemma accumulated_phaseSignedComp_bound (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    StochasticGeneralized.accumulated (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (fun _ w _ => phaseSignedComp p I xs w)
      n (initialState p, 0) ξ ≤ 1 / 2097152 := by
  let C := 16 * (64 * confidence p 0 / p.R ^ 2) ^ 2 * p.R ^ 2 * p.ε /
    (1099511627776 * confidence p 0 ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw := accumulated_phaseWeight_bound p I g hL0 hL1 hR hσ hΔ hε ξ n
  have hm : StochasticGeneralized.accumulated (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (fun _ w _ => phaseSignedComp p I xs w)
      n (initialState p, 0) ξ ≤ C *
      StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (fun _ s _ => phaseWeight p s) n (initialState p) ξ := by
    simp only [StochasticGeneralized.accumulated_eq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp := congrArg Prod.fst (signedTrace_projection p I μ g xs (initialState p) 0 ξ i)
    have hwf := blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ (initialState p)
      (initialState_wellFormed p hR hΔ) i
    have hwf' : WellFormed (StochasticGeneralized.blockTrace
        (fun w : State p.E × ℝ => phaseCost p w.1)
        (phaseSignedNext p I μ g xs) (initialState p, 0) ξ i).1.1 := by
      rw [hp]
      exact hwf
    have hh := phaseSignedComp_le_weight p I xs hL1 hR hε _ hwf'
    rw [hp] at hh
    exact hh
  apply hm.trans ((mul_le_mul_of_nonneg_left hw hC).trans_eq ?_)
  have hl : 0 < confidence p 0 := by linarith [confidence_lower p hδ hδ1 0]
  dsimp only [C]
  field_simp
  norm_num


lemma phaseSigned_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real
      {ξ | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated
        (fun w : State p.E × ℝ => phaseCost p w.1) (phaseSignedNext p I μ g xs)
        (phaseSigned p I μ g xs) n (initialState p, 0) ξ} ≤ Real.exp (-confidence p 0) := by
  have hl := confidence_lower p hδ hδ1 0
  have hθ : 0 ≤ 64 * confidence p 0 / p.R ^ 2 := by positivity
  have ht := RobustGradient.adaptive_compensated_tail μ
    ((measurable_phaseCost p).comp measurable_fst)
    (measurable_phaseSignedNext p I μ ho.measurable hgm xs hprox)
    (measurable_phaseSigned p I μ ho.measurable hgm xs)
    (measurable_phaseSignedComp p I hgm xs) hθ
    (phaseSigned_mgf p I μ ho hgrad hL1 hR hσ hα hα2 hε hδ hδ1 xs) n (initialState p, 0)
    (fun ξ => accumulated_phaseSignedComp_bound p I μ g xs hL0 hL1 hR hσ hΔ hε hδ hδ1 ξ n)
    (t := p.R ^ 2 / 10)
  apply ht.trans (Real.exp_le_exp.mpr ?_)
  field_simp
  nlinarith [sq_pos_of_pos hR]

lemma iid_phaseSigned_probability (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hgm : Measurable I.grad)
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (xs : p.E) (n : ℕ)
    {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    (ξ : ℕ → Ξ → p.Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P) :
    P.real {ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated (fun w : State p.E × ℝ => phaseCost p w.1) (phaseSignedNext p I μ g xs)
      (phaseSigned p I μ g xs) n (initialState p, 0) (fun k => ξ k ω)} ≤ Real.exp (-confidence p 0) := by
  have hinput : Measurable (fun stream : ℕ → p.Ω => ((initialState p, (0 : ℝ)), stream)) :=
    measurable_const.prodMk measurable_id
  have hm := (StochasticGeneralized.accumulated_measurable ((measurable_phaseCost p).comp measurable_fst)
    (measurable_phaseSignedNext p I μ ho.measurable hgm xs hprox)
    (measurable_phaseSigned p I μ ho.measurable hgm xs) n).comp hinput
  simp only [Function.comp_def, Function.uncurry_apply_pair] at hm
  have hset : MeasurableSet {ω : ℕ → p.Ω | p.R ^ 2 / 10 ≤ StochasticGeneralized.accumulated
      (fun w : State p.E × ℝ => phaseCost p w.1) (phaseSignedNext p I μ g xs) (phaseSigned p I μ g xs) n (initialState p, 0) ω} :=
    measurableSet_le measurable_const hm
  have ht := phaseSigned_probability p I μ ho hgrad hgm hprox hL0 hL1 hR hσ
    hα hα2 hΔ hε hδ hδ1 xs n
  rw [← h_samples.stream_law.measureReal_preimage hset.nullMeasurableSet] at ht
  exact ht

end OracleTemplate.StochasticCompositeGeneralized
