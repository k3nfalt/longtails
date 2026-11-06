import LongTails.Proofs.StochasticQuasarProgramExecution
import LongTails.Proofs.StochasticQuasarProgramSampling
import LongTails.Proofs.StochasticQuasarRunMoments
import LongTails.Proofs.StochasticQuasarNoiseTuning
import LongTails.Proofs.StochasticQuasarTerminal

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma tuned_run_barrier (q : Params) (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ]
    {Q : Set q.E} {P : q.E → q.E} {f : q.E → ℝ} {G : q.E → q.E} {g : q.E → q.Ω → q.E}
    {u : q.E} (hP : ConstrainedMonotone.Proj Q P) (hx0 : q.x0 ∈ Q) (hu : u ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ q.D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ q.L * ‖y - w‖)
    (hmin : IsMinOn f Q u)
    (hquasar : ∀ y ∈ Q, q.γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ q.σ ^ 2) :
    (∫⁻ seed : ProgramSeed q, ∫⁻ ξ,
      ENNReal.ofReal (compensatedEnergyBarrier (constrainedEnvelope Q f q.L) u (outerWeight q)
        (8 * q.D ^ 2) ((outerOrder q : ℝ) / (1024 * outerHorizon q)) (outerOrder q)
        (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ (outerPlan q seed) 0))
      ∂Measure.infinitePi (fun _ : ℕ => μ) ∂(programLaw q : Measure _)) ≤
      ENNReal.ofReal (2 * (9 / 16 : ℝ) ^ outerOrder q) := by
  have hL := hv.1
  have hD0 := hv.2.1
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  have hh := sampled_acceleration_run_barrier hP hL hD0 (outer_deviation_pos hv) (outer_bias_pos hv)
    hx0 hu hx0 hQ hcv hD hG hlip hmin hv.2.2.1 hv.2.2.2.1 hquasar hgm hgi hmean hg2 hvar
    (outer_step_pos hv) (outer_damping_pos q).le (by positivity : 0 < 8 * q.D ^ 2)
    (outer_order_two q) (by positivity : 0 ≤ (outerOrder q : ℝ) / (1024 * outerHorizon q))
    (by norm_num : (0 : ℝ) ≤ 0) (continuous_outer_weight q) (continuous_outer_mirror q)
    (continuous_outer_threshold hv).measurable (outer_weight_pos hv) (outer_mirror_nonneg hv)
    (outer_threshold_pos hv) (outer_weight_deriv hv) (fun t ht => outer_mirror_after hv ht)
    (outer_curvature_step hv) (fun t => by nlinarith [outer_mirror_tuning hv t]) (outer_damping_small q) (outer_damping_cap q)
    (outer_threshold_balance hv) (outer_noise_drift_bound hv he) (outerCount q) (x := q.x0)
  simp only [← sampled_outer_seeded] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [compensatedEnergyBarrier, mul_zero, neg_zero, Real.exp_zero, one_mul, outer_weight_initial]
  have hMu : constrainedEnvelope Q f q.L u = f u := by
    have hh := constrainedEnvelope_bounds hL.le hQ hG hu hmin u
    exact le_antisymm (by simpa using hh.2) hh.1
  have hb := constrainedEnvelope_bounds hL.le hQ hG hu hmin q.x0
  have hd := pow_le_pow_left₀ (norm_nonneg _) (hD q.x0 hx0 u hu) 2
  apply initial_shifted_barrier_bound hL hD0
  · rw [hMu]
    linarith [hb.1]
  · rw [hMu]
    have hh := mul_le_mul_of_nonneg_left hd hL.le
    linarith [hb.2]
  · exact hD q.x0 hx0 u hu

lemma tuned_terminal_energy (q : Params) (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ]
    {Q : Set q.E} {P : q.E → q.E} {f : q.E → ℝ} {G : q.E → q.E} {g : q.E → q.Ω → q.E}
    {u : q.E} (hP : ConstrainedMonotone.Proj Q P) (hx0 : q.x0 ∈ Q) (hu : u ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ q.D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ q.L * ‖y - w‖)
    (hmin : IsMinOn f Q u)
    (hquasar : ∀ y ∈ Q, q.γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ q.σ ^ 2) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | let state := QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0
           state.1 ≤ 2 * (outerCount q : ℝ) ∧ 8 * q.D ^ 2 ≤
             GradientOnlyQuasar.weightedEnergy (constrainedEnvelope Q f q.L) u
               (outerWeight q state.1) state.2.1 state.2.2} ≤ ENNReal.ofReal (q.δ / 4) := by
  let M := constrainedEnvelope Q f q.L
  let S := fun w : ProgramSeed q × (ℕ → q.Ω) =>
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0
  have hS : Measurable S := measurable_outer_execution hv hP.lipschitz.continuous.measurable hgm
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun y =>
    (constrainedEnvelope_hasGradient hv.1 hQ ⟨u, hu⟩ hcv hG hlip y).hasFDerivAt.continuousAt
  have hVm := (continuous_compensated_barrier hMc (continuous_outer_weight q) u (8 * q.D ^ 2)
    ((outerOrder q : ℝ) / (1024 * outerHorizon q)) (outerOrder q)).measurable.comp hS
  have hm := tuned_run_barrier q hv he hP hx0 hu hQ hcv hD hG hlip hmin hquasar hgm hgi hmean hg2 hvar
  have hD0 := hv.2.1
  have hT := outer_horizon_pos hv
  have hp := outer_order_pos q
  have hm' : (∫⁻ w, ENNReal.ofReal (compensatedEnergyBarrier M u (outerWeight q) (8 * q.D ^ 2)
      ((outerOrder q : ℝ) / (1024 * outerHorizon q)) (outerOrder q) (S w))
      ∂(programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ)) ≤
      ENNReal.ofReal (2 * (9 / 16 : ℝ) ^ outerOrder q) := by
    have heq := lintegral_prod _ (ENNReal.measurable_ofReal.comp hVm).aemeasurable
      (μ := (programLaw q : Measure _)) (ν := Measure.infinitePi fun _ : ℕ => μ)
    exact heq.trans_le hm
  have hh := terminal_energy_probability hMc (continuous_outer_weight q) u
    (by positivity : 0 < 8 * q.D ^ 2)
    (by positivity : 0 ≤ (outerOrder q : ℝ) / (1024 * outerHorizon q)) (outerOrder q) S hS hm'
    (T := 2 * (outerCount q : ℝ))
  apply hh.trans
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)).trans
    (outer_energy_tail_constant hv)
  have ht := outer_compensation_bound hv he
  nlinarith

lemma outer_envelope_failure (q : Params) (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ]
    {Q : Set q.E} {P : q.E → q.E} {f : q.E → ℝ} {G : q.E → q.E} {g : q.E → q.Ω → q.E}
    {u : q.E} (hP : ConstrainedMonotone.Proj Q P) (hx0 : q.x0 ∈ Q) (hu : u ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ q.D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ q.L * ‖y - w‖)
    (hmin : IsMinOn f Q u)
    (hquasar : ∀ y ∈ Q, q.γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ q.σ ^ 2) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | q.ε / 8 < constrainedEnvelope Q f q.L
        (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0).2.1 - f u} ≤
      ENNReal.ofReal (q.δ / 2) := by
  let M := constrainedEnvelope Q f q.L
  let S := fun w : ProgramSeed q × (ℕ → q.Ω) =>
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0
  let A : Set (ProgramSeed q × (ℕ → q.Ω)) := {w | (S w).1 < 2 * outerHorizon q}
  let B : Set (ProgramSeed q × (ℕ → q.Ω)) := {w | 2 * (outerCount q : ℝ) < (S w).1}
  let C : Set (ProgramSeed q × (ℕ → q.Ω)) := {w | (S w).1 ≤ 2 * (outerCount q : ℝ) ∧
    8 * q.D ^ 2 ≤ GradientOnlyQuasar.weightedEnergy M u (outerWeight q (S w).1) (S w).2.1 (S w).2.2}
  have hA := outer_clock_lower_failure hv μ P g
  have hB := outer_clock_upper_failure hv μ P g
  have hC := tuned_terminal_energy q hv he hP hx0 hu hQ hcv hD hG hlip hmin hquasar hgm hgi hmean hg2 hvar
  have hMu : M u = f u := by
    have hh := constrainedEnvelope_bounds hv.1.le hQ hG hu hmin u
    exact le_antisymm (by simpa [M] using hh.2) hh.1
  have hsub : {w : ProgramSeed q × (ℕ → q.Ω) | q.ε / 8 < M (S w).2.1 - f u} ⊆ A ∪ (B ∪ C) := by
    intro w hw
    by_cases ha : w ∈ A
    · exact Or.inl ha
    by_cases hb : w ∈ B
    · exact Or.inr (Or.inl hb)
    right
    right
    have ht : 2 * outerHorizon q ≤ (S w).1 := le_of_not_gt ha
    have hupp : (S w).1 ≤ 2 * (outerCount q : ℝ) := le_of_not_gt hb
    refine ⟨hupp, energy_large_of_terminal_gap hv ht ?_⟩
    rw [hMu]
    exact hw
  apply (measure_mono hsub).trans
  apply (measure_union_le A (B ∪ C)).trans
  apply (add_le_add hA ((measure_union_le B C).trans (add_le_add hB hC))).trans
  have hd := hv.2.2.2.2.2.2.1
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 8) (by positivity : 0 ≤ q.δ / 4),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 8) (by positivity : 0 ≤ q.δ / 8 + q.δ / 4)]
  apply ENNReal.ofReal_le_ofReal
  linarith

end OracleTemplate.StochasticQuasar
