import LongTails.Proofs.StochasticCompositeGeneralizedTrajectory
import LongTails.Proofs.StochasticCompositeGeneralizedConcentration
import LongTails.Proofs.HiddenConvexBudget

open MeasureTheory
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

lemma confidence_lower (p : Public) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (k : ℕ) :
    1 ≤ confidence p k := by
  have hk : 1 ≤ ((k : ℝ) + 1) ^ 2 := by have := Nat.cast_nonneg (α := ℝ) k; nlinarith
  have he := Real.exp_pos (1 : ℝ)
  have hnum : Real.exp 1 ≤ 64 * Real.exp 1 * ((k : ℝ) + 1) ^ 2 / p.δ := by
    apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 64 * Real.exp 1 by positivity)
    have hd := mul_le_mul_of_nonneg_left hδ1.le he.le
    nlinarith
  have hh := Real.log_le_log he hnum
  simpa only [Real.log_exp, confidence] using hh

lemma confidence_mono (p : Public) (hδ : 0 < p.δ) {j k : ℕ} (hjk : j ≤ k) :
    confidence p j ≤ confidence p k := by
  apply Real.log_le_log
  · have hj : 0 < (j : ℝ) + 1 := by positivity
    positivity
  · apply div_le_div_of_nonneg_right _ hδ.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hk := Nat.cast_nonneg (α := ℝ) k
    nlinarith

lemma exp_neg_confidence (p : Public) (hδ : 0 < p.δ) (k : ℕ) :
    Real.exp (-confidence p k) = p.δ / (64 * Real.exp 1 * ((k : ℝ) + 1) ^ 2) := by
  have hnum : 0 < 64 * Real.exp 1 * ((k : ℝ) + 1) ^ 2 := by positivity
  rw [confidence, Real.exp_neg, Real.exp_log (div_pos hnum hδ)]
  simp only [inv_div]

lemma evaluation_phase_tail (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 < p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hreceived : s.received = 0) (htotal : s.total = 0)
    (hA : s.A < 4 * p.R ^ 2 / p.ε)
    (hc : ‖I.grad (queryPoint p s) - s.center‖ ≤ 96 * p.σ) :
    (Measure.pi fun _ : Fin (batchSize p s.iteration (stepWeight p s)) => μ).real
      {ξ | p.R / (32 * stepWeight p s * Real.sqrt (confidence p s.iteration)) <
        ‖evaluationError p I
          (phaseNext p I g (batchSize p s.iteration (stepWeight p s)) s ξ)‖} ≤
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
    hs.1 (hs.2 (Or.inr (Or.inl hstage)))
  have ha : 0 < stepWeight p s := hw.1
  have haT : stepWeight p s ≤ 4 * p.R ^ 2 / p.ε :=
    (stepWeight_le_A p hL1 hR hs.1).trans hA.le
  have hbatch : 1099511627776 *
      (varianceBound p s.iteration * stepWeight p s * confidence p s.iteration ^ 2 / p.ε +
        clipRadius p s.iteration * stepWeight p s * confidence p s.iteration ^ 2 / p.R) ≤
      (batchSize p s.iteration (stepWeight p s) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have ht := RobustGradient.finite_centered_clip_heavy_tail hg (ho.integrable _) hmean hB hσ
    hα hα2 hmi hmoment s.center (by linarith) ha hR hε
    (confidence_lower p hδ hδ1 s.iteration) haT _ (batchSize_pos p _ _)
    (le_max_right _ _) hbatch
  have he (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
      evaluationError p I (phaseNext p I g (batchSize p s.iteration (stepWeight p s)) s ξ) =
        (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) •
          ∑ i, RobustGradient.centeredClip (clipRadius p s.iteration) s.center
            (g (queryPoint p s) (ξ i)) - I.grad (queryPoint p s) := by
    rw [phaseNext_evaluation p I g hL0 hL1 hR hσ.le s hs hstage hreceived htotal ξ]
    rfl
  simp_rw [he]
  exact ht

lemma clipRadius_zero_noise (p : Public) (hσ : p.σ = 0) (hα : 1 < p.α) (k : ℕ) :
    clipRadius p k = 0 := by
  have hα0 : p.α ≠ 0 := by linarith
  have he : (p.α - 1)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  simp [clipRadius, hσ, Real.zero_rpow hα0, Real.zero_rpow he]

lemma batchSize_zero_noise (p : Public) (hσ : p.σ = 0) (hα : 1 < p.α)
    (k : ℕ) (a : ℝ) : batchSize p k a = 1 := by
  have hα0 : p.α ≠ 0 := by linarith
  simp [batchSize, varianceBound, clipRadius_zero_noise p hσ hα, hσ, Real.zero_rpow hα0]

lemma centeredClip_zero_radius (p : Public) (c v : p.E) : RobustGradient.centeredClip 0 c v = c := by
  have hh : clip 0 (v - c) = 0 := norm_le_zero_iff.mp (norm_clip_le (le_refl 0) _)
  simp [RobustGradient.centeredClip, hh]

lemma evaluation_phase_zero_noise (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : p.σ = 0)
    (hα : 1 < p.α) (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hreceived : s.received = 0) (htotal : s.total = 0)
    (hc : s.center = I.grad (queryPoint p s))
    (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
    evaluationError p I (phaseNext p I g (batchSize p s.iteration (stepWeight p s)) s ξ) = 0 := by
  rw [phaseNext_evaluation p I g hL0 hL1 hR (by rw [hσ]) s hs hstage hreceived htotal ξ]
  change (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) •
    ∑ i, RobustGradient.centeredClip (clipRadius p s.iteration) s.center
      (g (queryPoint p s) (ξ i)) - I.grad (queryPoint p s) = 0
  simp_rw [clipRadius_zero_noise p hσ hα, centeredClip_zero_radius p]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, batchSize_zero_noise p hσ hα]
  simp [hc]

lemma pilot_zero_noise_ae (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hσ : p.σ = 0) (hα : 1 < p.α)
    (x : p.E) (k : ℕ) :
    (fun ξ : Fin (pilotSize p k) → p.Ω =>
      RobustGradient.pilotCenter (192 * p.σ) (fun i => g x (ξ i))) =ᵐ[
        Measure.pi fun _ => μ] fun _ => I.grad x := by
  have hα0 : p.α ≠ 0 := by linarith
  have he : gradient I.f x = I.grad x := (hgrad x).gradient
  have hm := ho.moment x
  have hi := ho.moment_integrable x
  rw [he] at hm hi
  have hz := RobustGradient.zero_central_moment_ae hα0 hi
    (by simpa only [hσ, Real.zero_rpow hα0] using hm)
  have hall := Measure.ae_eq_pi (fun _ : Fin (pilotSize p k) => hz)
  filter_upwards [hall] with ξ hξ
  rw [hξ]
  exact RobustGradient.pilotCenter_constant (pilotSize_pos p k) (by rw [hσ]; norm_num) _

lemma pilot_moment_ratio {σ α : ℝ} (hσ : 0 < σ) (hα : 1 ≤ α) :
    σ ^ α / (192 * σ / 6) ^ α ≤ 1 / 16 := by
  have he : 192 * σ / 6 = 32 * σ := by ring
  rw [he, ← Real.div_rpow hσ.le (by positivity)]
  have hr : σ / (32 * σ) = (1 / 32 : ℝ) := by field_simp
  rw [hr]
  have hh := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 32)
    (by norm_num : (1 / 32 : ℝ) ≤ 1) hα
  norm_num at hh ⊢
  linarith

lemma half_pow_pilotSize (p : Public) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (k : ℕ) :
    (1 / 2 : ℝ) ^ pilotSize p k ≤ Real.exp (-confidence p k) := by
  have hell := confidence_lower p hδ hδ1 k
  have hm : 16 * confidence p k ≤ (pilotSize p k : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hh : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  calc
    _ ≤ Real.exp (-(1 / 2 : ℝ)) ^ pilotSize p k :=
      pow_le_pow_left₀ (by norm_num) hh _
    _ = Real.exp (-(pilotSize p k : ℝ) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-confidence p k) := Real.exp_le_exp.mpr (by linarith)

lemma pilot_failure_positive (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hσ : 0 < p.σ) (hα : 1 < p.α)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (x : p.E) (k : ℕ) :
    (Measure.pi fun _ : Fin (pilotSize p k) => μ)
      {ξ | 96 * p.σ < ‖RobustGradient.pilotCenter (192 * p.σ)
        (fun i => g x (ξ i)) - I.grad x‖} ≤ ENNReal.ofReal (Real.exp (-confidence p k)) := by
  have he : gradient I.f x = I.grad x := (hgrad x).gradient
  have hm := ho.moment x
  have hi := ho.moment_integrable x
  rw [he] at hm hi
  have ht := RobustGradient.pilotCenter_heavy_failure
    (ho.measurable.comp measurable_prodMk_left) (I.grad x)
    (by positivity : 0 < 192 * p.σ) (by linarith : 0 ≤ p.α) hi hm
    (pilot_moment_ratio hσ hα.le) (pilotSize p k)
  have hscale : 192 * p.σ / 2 = 96 * p.σ := by ring
  rw [hscale] at ht
  exact ht.trans (ENNReal.ofReal_le_ofReal (half_pow_pilotSize p hδ hδ1 k))

lemma pilot_failure (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x) (hσ : 0 ≤ p.σ) (hα : 1 < p.α)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (x : p.E) (k : ℕ) :
    (Measure.pi fun _ : Fin (pilotSize p k) => μ)
      {ξ | 96 * p.σ < ‖RobustGradient.pilotCenter (192 * p.σ)
        (fun i => g x (ξ i)) - I.grad x‖} ≤ ENNReal.ofReal (Real.exp (-confidence p k)) := by
  by_cases hp : 0 < p.σ
  · exact pilot_failure_positive p I μ ho hgrad hp hα hδ hδ1 x k
  · have hz : p.σ = 0 := le_antisymm (not_lt.mp hp) hσ
    have ha := pilot_zero_noise_ae p I μ ho hgrad hz hα x k
    have he : (Measure.pi fun _ : Fin (pilotSize p k) => μ)
        {ξ | 96 * p.σ < ‖RobustGradient.pilotCenter (192 * p.σ)
          (fun i => g x (ξ i)) - I.grad x‖} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ha] with ξ hξ
      rw [hξ]
      simp [hz]
    rw [he]
    exact zero_le


lemma sum_inverse_square_shift_one (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_pow, div_one]
    simp_rw [show ∀ k : ℕ, (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by intro k; ring]
    have hh := LocalHiddenConvex.sum_inv_sq_le n
    have hp : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma sum_exp_neg_confidence (p : Public) (hδ : 0 < p.δ) (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-confidence p k)) ≤ p.δ / (32 * Real.exp 1) := by
  calc
    _ = (p.δ / (64 * Real.exp 1)) *
        ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [exp_neg_confidence p hδ k]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ ≤ (p.δ / (64 * Real.exp 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_inverse_square_shift_one n) (by positivity)
    _ = p.δ / (32 * Real.exp 1) := by ring


noncomputable def failureAllowance (p : Public) (s : State p.E) : ℝ :=
  if s.stage = 0 ∨ s.stage = 1 then
    if pilotSize p s.iteration ≤ s.received + 1 then Real.exp (-confidence p s.iteration) else 0
  else if s.stage = 2 then
    if batchSize p s.iteration (stepWeight p s) ≤ s.received + 1 then
      Real.exp (-confidence p s.iteration) else 0
  else 0

noncomputable def allowanceLedger (p : Public) (s : State p.E) : ℝ :=
  3 * (∑ k ∈ Finset.range s.iteration, Real.exp (-confidence p k)) +
    (if s.stage ≤ 3 then (s.stage : ℝ) else 0) * Real.exp (-confidence p s.iteration)

lemma update_allowanceLedger (p : Public) (s : State p.E) (v : p.E) :
    allowanceLedger p (update p s v) = allowanceLedger p s + failureAllowance p s := by
  by_cases h3 : s.stage = 3
  · simp only [update, h3, Nat.reduceEqDiff, ite_false, ite_true]
    split_ifs <;> simp [allowanceLedger, failureAllowance, h3, Finset.sum_range_succ] <;> ring
  · unfold update allowanceLedger failureAllowance
    split_ifs <;> simp_all [stepWeight]
    all_goals first | omega | ring

lemma allowanceLedger_bound (p : Public) (hδ : 0 < p.δ) (s : State p.E) :
    allowanceLedger p s ≤ 3 * p.δ / (32 * Real.exp 1) := by
  have hs : (if s.stage ≤ 3 then (s.stage : ℝ) else 0) ≤ 3 := by
    split_ifs with h
    · exact_mod_cast h
    · norm_num
  have hh := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (-confidence p s.iteration))
  have hsum := sum_exp_neg_confidence p hδ (s.iteration + 1)
  rw [Finset.sum_range_succ] at hsum
  unfold allowanceLedger
  rw [show 3 * p.δ / (32 * Real.exp 1) = 3 * (p.δ / (32 * Real.exp 1)) by ring]
  linarith

noncomputable def phaseAllowance (p : Public) (s : State p.E) : ℝ :=
  if s.stage ≤ 2 then Real.exp (-confidence p s.iteration) else 0

lemma rawAdvance_phase_allowanceLedger (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : PhaseEntry s) (call : ℕ) :
    allowanceLedger p (rawAdvance p I g ξ (phaseCost p s) call s) =
      allowanceLedger p s + phaseAllowance p s := by
  by_cases h0 : s.stage = 0
  · have he : { s with stage := 0, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inl h0)
      cases s
      simp_all
    have hh := rawAdvance_first_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h0, true_or, ite_true]
    rw [hh]
    simp [allowanceLedger, phaseAllowance, h0]
  by_cases h1 : s.stage = 1
  · have he : { s with stage := 1, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inr h1)
      cases s
      simp_all
    have hh := rawAdvance_second_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h1, or_true, ite_true]
    rw [hh]
    simp [allowanceLedger, phaseAllowance, h1]
    ring
  by_cases h2 : s.stage = 2
  · have he : { s with stage := 2, received := 0, total := 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.2 h2
      cases s
      simp_all
    have hh := rawAdvance_evaluation p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h2, Nat.reduceEqDiff, false_or, ite_false, ite_true]
    rw [hh]
    simp [allowanceLedger, phaseAllowance, h2]
    ring
  by_cases h3 : s.stage = 3
  · simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    rw [rawAdvance_one, update_allowanceLedger]
    simp [failureAllowance, phaseAllowance, h3]
  · have hstage : 4 ≤ s.stage := by omega
    simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    rw [rawAdvance_frozen p I g ξ s hstage]
    simp [phaseAllowance, show ¬s.stage ≤ 2 by omega]


lemma phaseAllowance_range (p : Public) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) (s : State p.E) :
    0 ≤ phaseAllowance p s ∧ phaseAllowance p s ≤ 1 := by
  unfold phaseAllowance
  split_ifs
  · refine ⟨Real.exp_nonneg _, ?_⟩
    apply Real.exp_le_one_iff.mpr
    linarith [confidence_lower p hδ hδ1 s.iteration]
  · norm_num

lemma measurable_phaseAllowance (p : Public) : Measurable (phaseAllowance p) := by
  have hh := (measurable_of_countable (fun k => Real.exp (-confidence p k))).comp
    (measurable_state_iteration (E := p.E))
  exact Measurable.ite (measurableSet_le measurable_state_stage measurable_const) hh measurable_const

lemma blockTrace_allowanceLedger (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (n : ℕ) :
    allowanceLedger p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 =
      allowanceLedger p s + ∑ j ∈ Finset.range n, phaseAllowance p
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ j).1 := by
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    rw [phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).2
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1)
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ s hs n)]
    rw [rawAdvance_phase_allowanceLedger p I g _ _
      (blockTrace_phaseEntry p I g hL0 hL1 hR hσ ξ s hs he n) 0]
    rw [ih, Finset.sum_range_succ]
    ring

lemma accumulated_phaseAllowance_bound (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hδ : 0 < p.δ) (ξ : ℕ → p.Ω) (n : ℕ) :
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (fun _ s _ => phaseAllowance p s) n (initialState p) ξ ≤ 3 * p.δ / (32 * Real.exp 1) := by
  have he := blockTrace_allowanceLedger p I g hL0 hL1 hR hσ ξ (initialState p)
    (initialState_wellFormed p hR hΔ) (initialState_phaseEntry p) n
  have hb := allowanceLedger_bound p hδ
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1
  have hz : allowanceLedger p (initialState p) = 0 := by
    unfold allowanceLedger initialState
    split_ifs <;> simp_all
  rw [he, hz, zero_add] at hb
  rw [StochasticGeneralized.accumulated_eq_sum]
  exact hb


end OracleTemplate.StochasticCompositeGeneralized
