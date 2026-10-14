import LongTails.Proofs.AdaptiveEntropicLinear
import LongTails.Proofs.AdaptiveEntropicBias

open MeasureTheory
open scoped OracleTemplate.AdaptiveList RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def clippingResidual (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ω : Ω) : Fin q.d → ℝ :=
  fun i => (clippedReply (clippingThreshold q s) (historyCenter q s)
    (g (queryPoint q s) ω) - historyCenter q s) i

noncomputable def clippingMean (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (P : Measure Ω) (s : State q) : Fin q.d → ℝ :=
  ∫ ω, clippingResidual q g s ω ∂P

noncomputable def oracleFluctuation (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (P : Measure Ω) (s : State q) (ω : Ω) : Vector q.d :=
  WithLp.toLp 2 (clippingResidual q g s ω - clippingMean q g P s)

noncomputable def oracleBias (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (P : Measure Ω) (s : State q) : Vector q.d :=
  historyCenter q s + WithLp.toLp 2 (clippingMean q g P s) - μ (queryPoint q s)

lemma oracle_error_identity (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (P : Measure Ω) (s : State q) (ω : Ω) :
    μ (queryPoint q s) - clippedReply (clippingThreshold q s) (historyCenter q s)
      (g (queryPoint q s) ω) = -oracleFluctuation q g P s ω - oracleBias q g μ P s := by
  ext i
  simp only [oracleFluctuation, oracleBias, clippingResidual, PiLp.sub_apply, PiLp.add_apply,
    PiLp.neg_apply, Pi.sub_apply]
  ring

lemma integrable_clippingResidual (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (s : State q) (hlambda : 0 ≤ clippingThreshold q s) :
    Integrable (clippingResidual q g s) P := by
  have hG : Measurable (fun ω : Ω => fun i => (g (queryPoint q s) ω - historyCenter q s) i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((PiLp.continuous_apply 2 (fun _ : Fin q.d => ℝ) i).measurable).comp
      ((hg.comp (measurable_const.prodMk measurable_id)).sub measurable_const)
  have hi := GeneralNormClipping.integrable_clip (P := P) hG hlambda
  have he : clippingResidual q g s = fun ω => clip (clippingThreshold q s)
      (fun i => (g (queryPoint q s) ω - historyCenter q s) i) := by
    funext ω
    exact clippedReply_coordinates _ _ _
  rw [he]
  exact hi

lemma weightedNoise_eq_fluctuation (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ) (s : State q)
    (hs : boundedActive q μ σ A T s) (ω : Ω) :
    weightedNoise q g μ σ A T P s ω = ((s.completed + 1 : ℕ) : ℝ) •
      (fun i => oracleFluctuation q g P s ω i) := by
  have he : (fun z => weightedResidual q μ σ A T s (g (queryPoint q s) z)) =
      fun z => ((s.completed + 1 : ℕ) : ℝ) • clippingResidual q g s z := by
    funext z
    unfold weightedResidual
    rw [ite_eq_left hs]
    rfl
  unfold weightedNoise
  rw [congrFun he ω, he, integral_smul]
  change ((s.completed + 1 : ℕ) : ℝ) • clippingResidual q g s ω -
    ((s.completed + 1 : ℕ) : ℝ) • clippingMean q g P s = _
  rw [← smul_sub]
  rfl

lemma scalarNoise_eq_fluctuation (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ) (s : State q)
    (hs : boundedActive q μ σ A T s) (xstar : simplex q.d) (ω : Ω) :
    scalarNoise q g μ σ A T P xstar s ω =
      -((s.completed + 1 : ℕ) : ℝ) *
        ⟪oracleFluctuation q g P s ω, (predictableProx q s).val - xstar.val⟫ := by
  unfold scalarNoise
  rw [weightedNoise_eq_fluctuation q g μ σ A T s hs ω, map_smul,
    smul_eq_mul, simplexPairing_eq_inner]
  have he : WithLp.toLp 2 (fun i => oracleFluctuation q g P s ω i) =
      oracleFluctuation q g P s ω := rfl
  rw [he, inner_sub_right, inner_sub_right]
  ring

lemma quadraticNoise_eq_fluctuation (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ) (s : State q)
    (hs : boundedActive q μ σ A T s) (ω : Ω) :
    ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 / regularization q s =
      ((s.completed + 1 : ℕ) : ℝ) ^ 2 * dualNorm (oracleFluctuation q g P s ω) ^ 2 /
        regularization q s := by
  rw [weightedNoise_eq_fluctuation q g μ σ A T s hs ω, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  unfold dualNorm
  rw [mul_pow]

lemma accumulated_pairScore_congr_prefix (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (X Y : State q → Ω → Ω → ℝ)
    (N : ℕ) (ξ : ℕ → Ω)
    (he : ∀ j < N,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → ∀ a b, X s a b = Y s a b) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairScore X) N (initialState q) ξ =
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairScore Y) N (initialState q) ξ := by
  rw [StochasticGeneralized.accumulated_eq_sum, StochasticGeneralized.accumulated_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ j
  change pairScore X (analysisCost q tr.1) tr.1 (fun i => tr.2 i) =
    pairScore Y (analysisCost q tr.1) tr.1 (fun i => tr.2 i)
  by_cases hw : tr.1.warmup = 0
  · unfold pairScore
    split_ifs
    · exact he j (Finset.mem_range.mp hj) hw _ _
    · rfl
  · have hc : analysisCost q tr.1 = 1 := by simp [analysisCost, hw]
    rw [hc]
    simp [pairScore]

lemma accumulated_linearNoiseScore_eq_fluctuation (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω}
    (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ)
    (xstar : simplex q.d) (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + T)).1 ≤ A) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (linearNoiseScore q g μ σ A T P xstar) (preload q + T) (initialState q) ξ =
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairScore (fun s a _ => -((s.completed + 1 : ℕ) : ℝ) *
        ⟪oracleFluctuation q g P s a, (predictableProx q s).val - xstar.val⟫))
      (preload q + T) (initialState q) ξ := by
  unfold linearNoiseScore
  apply accumulated_pairScore_congr_prefix q g
  intro j hj s hw a b
  have hs := boundedActive_prefix q g μ σ A T ξ hc hQ j hj hw
  exact scalarNoise_eq_fluctuation q g μ σ A T s hs xstar a

lemma accumulated_quadraticNoiseScore_eq_fluctuation (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω}
    (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ)
    (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + T)).1 ≤ A) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (quadraticNoiseScore q g μ σ A T P) (preload q + T) (initialState q) ξ =
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairScore (fun s a _ => ((s.completed + 1 : ℕ) : ℝ) ^ 2 *
        dualNorm (oracleFluctuation q g P s a) ^ 2 / regularization q s))
      (preload q + T) (initialState q) ξ := by
  unfold quadraticNoiseScore
  apply accumulated_pairScore_congr_prefix q g
  intro j hj s hw a b
  have hs := boundedActive_prefix q g μ σ A T ξ hc hQ j hj hw
  exact quadraticNoise_eq_fluctuation q g μ σ A T s hs a

lemma integrable_vector_coordinates {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {G : Ω → Vector d} (hi : Integrable G P) :
    Integrable (fun ω => fun i => G ω i) P :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.integrable_comp hi

lemma integral_vector_coordinates {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {G : Ω → Vector d} (hi : Integrable G P) :
    (∫ ω, (fun i => G ω i) ∂P) = fun i => (∫ ω, G ω ∂P) i :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.integral_comp_comm hi

lemma weighted_bias_le_expected_residual (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) (s : State q)
    (hi : Integrable (g (queryPoint q s)) P)
    (hu : (∫ ω, g (queryPoint q s) ω ∂P) = μ (queryPoint q s))
    (hlambda : 0 ≤ clippingThreshold q s) :
    ((s.completed + 1 : ℕ) : ℝ) * dualNorm (oracleBias q g μ P s) ≤
      ∫ ω, ((s.completed + 1 : ℕ) : ℝ) *
        dualNorm (g (queryPoint q s) ω - clippedReply (clippingThreshold q s)
          (historyCenter q s) (g (queryPoint q s) ω)) ∂P := by
  let C : Fin q.d → ℝ := fun i => historyCenter q s i
  let G : Ω → Fin q.d → ℝ := fun ω i => g (queryPoint q s) ω i
  let R := clippingResidual q g s
  have hiG : Integrable G P := integrable_vector_coordinates hi
  have hiA : Integrable (fun ω => G ω - C) P := hiG.sub (integrable_const C)
  have hiR : Integrable R P := integrable_clippingResidual q hg s hlambda
  have hG : (∫ ω, G ω ∂P) = fun i => μ (queryPoint q s) i := by
    rw [integral_vector_coordinates hi, hu]
  have hB : (∫ ω, R ω - (G ω - C) ∂P) =
      C + clippingMean q g P s - (fun i => μ (queryPoint q s) i) := by
    rw [integral_sub hiR hiA, integral_sub hiG (integrable_const C), hG, integral_const]
    simp only [probReal_univ, one_smul]
    change clippingMean q g P s - ((fun i => μ (queryPoint q s) i) - C) = _
    abel
  have hn := norm_integral_le_integral_norm (μ := P) (fun ω => R ω - (G ω - C))
  have hb := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (s.completed + 1) :
    (0 : ℝ) ≤ (s.completed + 1 : ℕ))
  rw [hB, ← integral_const_mul] at hb
  have he (ω : Ω) : ‖R ω - (G ω - C)‖ =
      dualNorm (g (queryPoint q s) ω - clippedReply (clippingThreshold q s)
        (historyCenter q s) (g (queryPoint q s) ω)) := by
    have hv : R ω - (G ω - C) =
        -(fun i => (g (queryPoint q s) ω - clippedReply (clippingThreshold q s)
          (historyCenter q s) (g (queryPoint q s) ω)) i) := by
      funext i
      simp only [R, clippingResidual, G, C, Pi.sub_apply, Pi.neg_apply, PiLp.sub_apply]
      ring
    rw [hv, norm_neg]
    rfl
  simp_rw [he] at hb
  change ((s.completed + 1 : ℕ) : ℝ) * dualNorm (oracleBias q g μ P s) ≤ _ at hb
  exact hb

lemma weighted_bias_le_expected_excess (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) (s : State q)
    (hi : Integrable (g (queryPoint q s)) P)
    (hu : (∫ ω, g (queryPoint q s) ω ∂P) = μ (queryPoint q s))
    (hL : 0 ≤ q.L) (hQ : 0 ≤ empiricalQuantile q s) :
    ((s.completed + 1 : ℕ) : ℝ) * dualNorm (oracleBias q g μ P s) ≤
      ∫ ω, max 0 (weightedInnovation q s (g (queryPoint q s) ω) - empiricalQuantile q s) ∂P := by
  have h := weighted_bias_le_expected_residual q hg μ s hi hu (clippingThreshold_nonneg q hL s hQ)
  have he (ω : Ω) : ((s.completed + 1 : ℕ) : ℝ) *
      dualNorm (g (queryPoint q s) ω - clippedReply (clippingThreshold q s)
        (historyCenter q s) (g (queryPoint q s) ω)) =
      max 0 (weightedInnovation q s (g (queryPoint q s) ω) - empiricalQuantile q s) := by
    have ht : 0 < ((s.completed + 1 : ℕ) : ℝ) := by positivity
    have hx := clippedReply_weighted_residual ht hQ
      (show 0 ≤ driftRadius q s by unfold driftRadius; positivity)
      (historyCenter q s) (g (queryPoint q s) ω)
    simpa only [clippingThreshold, weightedInnovation, historyCenter, Nat.cast_add, Nat.cast_one] using hx
  simpa only [he] using h

lemma weighted_bias_le_capped_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (s : State q) (hs : cappedActive q μ σ A s)
    (hgi : Integrable (g (queryPoint q s)) P)
    (hgu : (∫ ω, g (queryPoint q s) ω ∂P) = μ (queryPoint q s)) :
    ((s.completed + 1 : ℕ) : ℝ) * dualNorm (oracleBias q g μ P s) ≤
      A * (∫ ω, cappedBiasScore q g μ σ A s ω ∂P) +
        130 * ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p / A ^ (p - 1) := by
  have ht := weightedInnovation_tail_mean q hg μ hσ hp hp2 hA hi hm s hs.1.2
  have hS : Measurable (fun ω => cappedBiasScore q g μ σ A s ω) :=
    (measurable_cappedBiasScore q hg hμ σ A).comp measurable_prodMk_left
  have hiS := AdaptiveEntropicConcentration.unit_integrable (P := P) hS
    (fun ω => cappedBiasScore_unit q g μ σ hA s ω)
  have hcap (ω : Ω) : cappedExcess q A s (g (queryPoint q s) ω) =
      A * cappedBiasScore q g μ σ A s ω := by
    unfold cappedBiasScore
    rw [ite_eq_left hs]
    field_simp
  have hbound (ω : Ω) : max 0 (weightedInnovation q s (g (queryPoint q s) ω) - empiricalQuantile q s) ≤
      A * cappedBiasScore q g μ σ A s ω +
        max 0 (weightedInnovation q s (g (queryPoint q s) ω) - A) := by
    rw [← hcap ω]
    unfold cappedExcess
    rw [ite_eq_left hs.1.1]
    exact QuantileClipping.excess_split _ _ _
  have hb := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => le_max_left 0
      (weightedInnovation q s (g (queryPoint q s) ω) - empiricalQuantile q s)))
    ((hiS.const_mul A).add ht.1) (Filter.Eventually.of_forall hbound)
  simp only [Pi.add_apply] at hb
  rw [integral_add (hiS.const_mul A) ht.1, integral_const_mul] at hb
  exact (weighted_bias_le_expected_excess q hg μ s hgi hgu hL hs.2.1).trans
    (hb.trans (add_le_add le_rfl ht.2))

end OracleTemplate.AdaptiveHeavyTailSimplex
