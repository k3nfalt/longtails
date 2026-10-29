import LongTails.Proofs.GradientOnlyQuasarFlow
import LongTails.Proofs.ExponentialHolding
import LongTails.Proofs.RelativeQuasarIteration

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

noncomputable section

def potential (q : Params) (f : q.E → ℝ) (u : q.E) (s : ℝ × q.E × q.E) : ℝ :=
  barrier ((weightedEnergy f u (weight q s.1) s.2.1 s.2.2 / energyLevel q) ^ momentOrder q)

def potentialDrift (q : Params) (f : q.E → ℝ) (u : q.E) (s : ℝ × q.E × q.E) : ℝ :=
  barrierSlope ((weightedEnergy f u (weight q s.1) s.2.1 s.2.2 / energyLevel q) ^ momentOrder q) *
    ((momentOrder q : ℝ) *
      (weightedEnergy f u (weight q s.1) s.2.1 s.2.2 / energyLevel q) ^ (momentOrder q - 1) *
      ((q.γ * mirrorStep q s.1 * (f s.2.1 - f u) +
        mirrorStep q s.1 * ⟪gradient f s.2.1, s.2.2 - s.2.1⟫) / energyLevel q))

lemma potential_nonneg {q : Params} (hv : spec.valid q) {f : q.E → ℝ} {u : q.E}
    (hm : IsMinOn f univ u) (s : ℝ × q.E × q.E) : 0 ≤ potential q f u s := by
  apply barrier_nonneg
  apply pow_nonneg
  exact div_nonneg (weightedEnergy_nonneg (weight_pos hv s.1).le hm) (energyLevel_pos hv).le

lemma potential_le_one (q : Params) (f : q.E → ℝ) (u : q.E) (s : ℝ × q.E × q.E) :
    potential q f u s ≤ 1 := barrier_le_one _

lemma continuous_potential (q : Params) {f : q.E → ℝ} (hf : Continuous f) (u : q.E) :
    Continuous (potential q f u) := by
  have hw := continuous_weight q
  unfold potential weightedEnergy
  apply continuous_barrier.comp
  fun_prop

lemma continuous_potentialDrift (q : Params) {f : q.E → ℝ} (hf : Continuous f)
    (hg : Continuous (gradient f)) (u : q.E) : Continuous (potentialDrift q f u) := by
  have hw := continuous_weight q
  have ha := continuous_mirrorStep q
  have hb := continuous_barrierSlope
  unfold potentialDrift weightedEnergy
  fun_prop

lemma potential_flow_hasDerivAt {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (s : ℝ × q.E × q.E) (u : q.E) (t : ℝ) :
    HasDerivAt (fun h => potential q f u (flow q s h))
      (potentialDrift q f u (flow q s t)) t := by
  have he := ((flow_energy_hasDerivAt hv hf s u t).div_const (energyLevel q)).pow (momentOrder q)
  have hb := (hasDerivAt_barrier
    ((weightedEnergy f u (weight q (s.1 + t)) (flow q s t).2.1 s.2.2 / energyLevel q) ^
      momentOrder q)).comp t he
  convert! hb using 1

lemma potentialDrift_after {q : Params} (hv : spec.valid q) (f : q.E → ℝ) (u : q.E)
    {s : ℝ × q.E × q.E} (ht : stageStart q (stageCount q) ≤ s.1) :
    potentialDrift q f u s = 0 := by
  simp [potentialDrift, mirrorStep_after hv ht]

lemma potential_generator {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (hg : Continuous (gradient f))
    (hs : CompositeGeneralized.SymmetricSmooth (gradient f) q.L0 q.L1)
    {u : q.E} (hm : IsMinOn f univ u)
    (hq : ∀ y, q.γ * (f y - f u) ≤ ⟪gradient f y, y - u⟫)
    (s : ℝ × q.E × q.E) :
    potentialDrift q f u s + potential q f u (jump q s (gradient f s.2.1)) -
      potential q f u s ≤ 0 := by
  exact energy_barrier_generator (momentOrder_pos q) (weight_pos hv s.1) (curvature_pos hv s.1)
    (energyLevel_pos hv) (mirrorStep_nonneg hv s.1) hm (hq s.2.1)
    (scheduled_descent hv hf hg hs hm) (mirrorStep_tuning_all hv s.1)

lemma bounded_of_continuous_eventually_zero {F : ℝ → ℝ} {T : ℝ}
    (hF : Continuous F) (hz : ∀ t, T ≤ t → F t = 0) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖F t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max 0 T))).bddAbove_image
    hF.norm.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (F 0)).trans
    (hC ⟨0, ⟨le_rfl, le_max_left _ _⟩, rfl⟩)
  refine ⟨C, fun t ht => ?_⟩
  by_cases hh : t ≤ max 0 T
  · exact hC ⟨t, ⟨ht, hh⟩, rfl⟩
  · rw [hz t ((le_max_right _ _).trans (le_of_not_ge hh)), norm_zero]
    exact hC0

lemma exponential_holding_nonincrease {B D J : ℝ → ℝ} {CB CD CJ : ℝ}
    (hB : Continuous B) (hD : Continuous D) (hJ : Continuous J)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ 0) :
    (∫ t, J t ∂expMeasure 1) ≤ B 0 := by
  have hBi := ContinuizedSimilarQuasar.weighted_integrable hB hb
  have hDi := ContinuizedSimilarQuasar.weighted_integrable hD hd
  have hJi := ContinuizedSimilarQuasar.weighted_integrable hJ hj
  have he := ContinuizedSimilarQuasar.weighted_derivative_integral hB hD hderiv hb hd
  have hh : (∫ t in Ioi 0,
      Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t ≤ 0
    have hg := mul_le_mul_of_nonneg_left (hgen t ht.le) (Real.exp_pos (-t)).le
    nlinarith
  rw [integral_sub (f := fun t => Real.exp (-t) * D t + Real.exp (-t) * J t)
    (hDi.add hJi) hBi, integral_add hDi hJi] at hh
  rw [ContinuizedSimilarQuasar.integral_expMeasure_one]
  linarith

lemma sample_potential_step {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (hg : Continuous (gradient f))
    (hs : CompositeGeneralized.SymmetricSmooth (gradient f) q.L0 q.L1)
    {u : q.E} (hm : IsMinOn f univ u)
    (hq : ∀ y, q.γ * (f y - f u) ≤ ⟪gradient f y, y - u⟫)
    (s : ℝ × q.E × q.E) :
    Integrable (fun t => potential q f u (advance q (gradient f) s t))
      (RelativeQuasar.holdingLaw : Measure ℝ) ∧
    (∫ t, potential q f u (advance q (gradient f) s t)
      ∂(RelativeQuasar.holdingLaw : Measure ℝ)) ≤ potential q f u s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr
    (fun y => (hf y).hasFDerivAt.continuousAt)
  have hV := continuous_potential q hfc u
  have hD := continuous_potentialDrift q hfc hg u
  have hflow : Continuous (fun t => flow q s t) :=
    (flow_continuous hv).comp (continuous_const.prodMk continuous_id)
  have hJ : Continuous (fun v : ℝ × q.E × q.E =>
      potential q f u (jump q v (gradient f v.2.1))) :=
    hV.comp ((jump_continuous hv).comp (continuous_id.prodMk
      (hg.comp continuous_snd.fst)))
  have hbound (v : ℝ × q.E × q.E) : ‖potential q f u v‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hv hm v)]
    exact potential_le_one q f u v
  obtain ⟨CD, hCD⟩ := bounded_of_continuous_eventually_zero
    (T := stageStart q (stageCount q) - s.1) (hD.comp hflow)
    (fun t ht => potentialDrift_after hv f u (by change _ ≤ s.1 + t; linarith))
  have hInt : Integrable (fun t => potential q f u (advance q (gradient f) s t))
      (RelativeQuasar.holdingLaw : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono'
      (hV.comp ((advance_continuous hv hg).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    exact Eventually.of_forall (fun t => hbound _)
  have hc := exponential_holding_nonincrease (hV.comp hflow) (hD.comp hflow) (hJ.comp hflow)
    (potential_flow_hasDerivAt hv hf s u) (fun t _ => hbound _) hCD
    (fun t _ => hbound _) (fun t _ => potential_generator hv hf hg hs hm hq (flow q s t))
  have hi : (∫ t, potential q f u (advance q (gradient f) s t)
      ∂(RelativeQuasar.holdingLaw : Measure ℝ)) =
      ∫ t, potential q f u (jump q (flow q s t) (gradient f (flow q s t).2.1))
        ∂expMeasure 1 := by
    change (∫ t, potential q f u (advance q (gradient f) s t) ∂expMeasure 1) = _
    rw [ContinuizedSimilarQuasar.integral_expMeasure_one,
      ContinuizedSimilarQuasar.integral_expMeasure_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [advance, max_eq_right (mem_Ioi.mp ht).le]
  refine ⟨hInt, ?_⟩
  rw [hi]
  simpa only [Function.comp_apply, flow_zero hv] using hc

lemma run_potential_nonincrease {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (hg : Continuous (gradient f))
    (hs : CompositeGeneralized.SymmetricSmooth (gradient f) q.L0 q.L1)
    {u : q.E} (hm : IsMinOn f univ u)
    (hq : ∀ y, q.γ * (f y - f u) ≤ ⟪gradient f y, y - u⟫)
    (k : ℕ) (s : ℝ × q.E × q.E) :
    Integrable (fun samples => potential q f u (run q (gradient f) k s samples))
      (RelativeQuasar.samplesLaw k : Measure _) ∧
    (∫ samples, potential q f u (run q (gradient f) k s samples)
      ∂(RelativeQuasar.samplesLaw k : Measure _)) ≤ potential q f u s := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr
    (fun y => (hf y).hasFDerivAt.continuousAt)
  have hsingle (v : ℝ × q.E × q.E) := sample_potential_step hv hf hg hs hm hq v
  have hh := ContinuizedSimilarQuasar.measurable_iterateSamples_integral
    (advance_continuous hv hg).measurable RelativeQuasar.holdingLaw
    (potential q f u) (continuous_potential q hfc u).measurable (potential_nonneg hv hm)
    (q := 1) (r := 0) (by norm_num) (fun v => by simpa using hsingle v) k s
  simpa only [run, RelativeQuasar.samplesLaw, ProbabilityMeasure.coe_mk,
    one_pow, one_mul, zero_mul, add_zero] using hh

lemma initial_potential_bound {q : Params} (hv : spec.valid q) {f : q.E → ℝ} {u : q.E}
    (hm : IsMinOn f univ u) (hR : ‖q.x0 - u‖ ≤ q.R) (hΔ : f q.x0 - f u ≤ q.Δ) :
    potential q f u (0, q.x0, q.x0) ≤ 2 * (1 / 2 : ℝ) ^ momentOrder q := by
  have hE := energyLevel_pos hv
  have hA := initialWeight_pos hv
  have hnorm := pow_le_pow_left₀ (norm_nonneg (q.x0 - u)) hR 2
  have hgap := mul_le_mul_of_nonneg_left hΔ hA.le
  have heq : initialWeight q * q.Δ = q.R ^ 2 / 2 := by
    unfold initialWeight
    field_simp [ne_of_gt hv.2.2.2.1]
  have hP : weightedEnergy f u (weight q 0) q.x0 q.x0 ≤ q.R ^ 2 := by
    rw [weight_of_nonpos hv le_rfl]
    unfold weightedEnergy
    rw [heq] at hgap
    linarith
  have hp0 := weightedEnergy_nonneg (weight_pos hv 0).le (y := q.x0) (z := q.x0) hm
  have hratio : weightedEnergy f u (weight q 0) q.x0 q.x0 / energyLevel q ≤ 1 / 2 := by
    apply (div_le_iff₀ hE).2
    unfold energyLevel
    linarith
  have hpow := pow_le_pow_left₀ (div_nonneg hp0 hE.le) hratio (momentOrder q)
  exact (barrier_le_twice _).trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

end

end OracleTemplate.GradientOnlyQuasar
