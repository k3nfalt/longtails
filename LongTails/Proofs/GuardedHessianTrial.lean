import LongTails.Proofs.GuardedHessianOutput
import LongTails.Proofs.GuardedHessianTuning

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.GuardedHessianExecution
open LongTails.Proofs.GuardedHessianEstimator

namespace LongTails.Proofs.GuardedHessianTrial

lemma oracle_estimator_bound (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (hgm : Measurable (fun w : Space p × Ω => answer (w.1, none) w.2))
    (hhm : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hq : 1 ≤ p.q) (hq2 : p.q ≤ 2)
    (hσg : 0 ≤ p.σg) (hαg : 0 ≤ p.αg) (hσh : 0 ≤ p.σh) (hαh : 0 ≤ p.αh)
    {M K : ℝ} (hM : 0 < M) (hη : 0 ≤ c.η)
    (hK : p.L0 + p.L1 * M + p.σh + p.αh * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hgi : ∀ y, Integrable (answer (y, none)) P)
    (hgmean : ∀ y, (∫ ω, answer (y, none) ω ∂P) = g y)
    (hgpi : ∀ y, Integrable (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p) P)
    (hgb : ∀ y, (∫ ω, ‖answer (y, none) ω - g y‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p)
    (hhi : ∀ y v, Integrable (answer (y, some v)) P)
    (hhmean : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hhpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hhb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (hsmall : p.L1 * c.η ≤ 1 / 4) (hbase : p.L0 * c.η ≤ M / 4)
    (h0 : ‖g p.x0‖ ≤ M) (hthreshold : c.threshold = 3 * M / 2)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (target : Fin (c.steps + 1)) (t : ℕ) (ht : t ≤ c.steps) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let F := fun ξ : ℕ → ℝ × Ω => if (iterState p c answer target ξ t).alive then
      ‖(iterState p c answer target ξ t).estimate - g (iterState p c answer target ξ t).point‖ else 0
    Integrable F (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      54 * (p.σg + p.αg * M) *
        (((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹ +
      3840 * (K * c.η) * ((c.epoch + 1 : ℕ) : ℝ) ^ p.q⁻¹ := by
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let Q := U.prod P
  let S := Measure.infinitePi fun _ : ℕ => Q
  let X := fun j (ξ : ℕ → ℝ × Ω) => iterState p c answer target ξ j
  have hgm' : Measurable (fun w : Space p × (ℝ × Ω) => answer (w.1, none) w.2.2) :=
    hgm.comp (f := fun w : Space p × (ℝ × Ω) => (w.1, w.2.2)) (by fun_prop)
  have hgi' (y : Space p) : Integrable (fun z : ℝ × Ω => answer (y, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgi y)
  have hgmean' (y : Space p) : (∫ z : ℝ × Ω, answer (y, none) z.2 ∂Q) = g y := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hgmean y
  have hgpi' (y : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (y, none) z.2 - g y‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgpi y)
  have hgb' (y : Space p) : (∫ z : ℝ × Ω, ‖answer (y, none) z.2 - g y‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p := by
    have he := integral_fun_snd (μ := U) (ν := P)
      (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p)
    simp only [probReal_univ, one_smul] at he
    exact he.trans_le (hgb y)
  have hGi (j : ℕ) : Integrable (fun ξ => if (X j ξ).alive then ‖g (X j ξ).point‖ ^ 2 else 0) S :=
    GuardedHessianIntegration.trajectory_alive_integrable p c hη S answer hstep
      (⟨p.x0, 0, 0, target, p.x0, true, .reset 0 0⟩ : State p c) le_rfl le_rfl
      (fun y => ‖g y‖ ^ 2) (hg.continuous.norm.pow 2) (transportTime c j)
  have hGb (j : ℕ) (hj : j ≤ c.steps) :
      (∫ ξ, if (X j ξ).alive then ‖g (X j ξ).point‖ ^ 2 else 0 ∂S) ≤ 8 * M ^ 2 :=
    GuardedHessianIntegration.oracle_alive_second_moment p c hη Q answer g hg hstep
      hL0 hL1 hH hsmall hbase h0 hp hp2 hσg hαg hM hthreshold
      (fun y => hgm'.comp (measurable_const.prodMk measurable_id)) hgi' hgmean' hgpi' hgb'
      hsize hgroups target j hj
  have heq (j : ℕ) : (fun ξ => (if (X j ξ).alive then ‖g (X j ξ).point‖ else 0) ^ 2) =
      (fun ξ => if (X j ξ).alive then ‖g (X j ξ).point‖ ^ 2 else 0) := by
    funext ξ
    split_ifs <;> simp
  let a := (c.epoch + 1) * (t / (c.epoch + 1))
  have hat : a ≤ t := by
    have hh := Nat.mod_add_div t (c.epoch + 1)
    dsimp only [a]
    omega
  have hr := actual_reset_moment p c Q answer g hgm' hg.continuous.measurable hstep
    hp hp2 hσg hαg hM hgi' hgmean' hgpi' hgb' target a (hat.trans ht)
    (by simp [a]) (by rw [heq]; exact hGi a) (by rw [heq]; exact hGb a (hat.trans ht))
  have hh := oracle_epoch_transport_moment p c P answer g hhm hstep hL0 hL1 hq hq2 hσh hαh
    hM hη hK hg hD hH hhi hhmean hhpi hhb hsmall hbase target a t
    (fun j _ => by rw [heq]; exact hGi j)
    (fun j hj => by rw [heq]; exact hGb j (le_trans (Finset.mem_Ico.mp hj).2.le ht))
  have hK0 : 0 ≤ K := (by positivity : 0 ≤ p.L0 + p.L1 * M + p.σh + p.αh * M).trans hK
  exact expected_estimator_bound p c Q answer g hhm hg.continuous.measurable hstep hp hq
    hσg hαg hM.le hK0 hη target t ht hr.1 hr.2 hh.1 hh.2

lemma tuned_trial_guarantees (p : Params) (hv : spec.valid p) (c : Config) (hc : c = tunedConfig p)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p) {m : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (reference : Fin (c.steps + 1))
    (hEi : ∀ t ≤ c.steps, Integrable (fun ξ => if (iterState p c answer reference ξ t).alive then
      ‖(iterState p c answer reference ξ t).estimate - g (iterState p c answer reference ξ t).point‖ else 0) Q)
    (hEb : ∀ t ≤ c.steps, (∫ ξ, if (iterState p c answer reference ξ t).alive then
      ‖(iterState p c answer reference ξ t).estimate - g (iterState p c answer reference ξ t).point‖ else 0 ∂Q) ≤ p.ε / 128)
    (hGi : ∀ t ≤ c.steps, Integrable (fun ξ => if (iterState p c answer reference ξ t).alive then
      ‖g (iterState p c answer reference ξ t).point‖ ^ 2 else 0) Q)
    (hGb : ∀ t ≤ c.steps, (∫ ξ, if (iterState p c answer reference ξ t).alive then
      ‖g (iterState p c answer reference ξ t).point‖ ^ 2 else 0 ∂Q) ≤ 8 * guardRadius p ^ 2)
    (hfalse : ∀ t ≤ c.steps, Q.real
      {ξ | (path p c answer reference ξ (transportTime c t + 1)).alive = true ∧
        ‖g (path p c answer reference ξ (transportTime c t + 1)).point‖ ≤ guardRadius p ∧
        (path p c answer reference ξ (transportTime c t + cycleCalls c)).alive = false} ≤
        (1 / 2 : ℝ) ^ (c.groups + 1)) :
    let F := fun w : Fin (c.steps + 1) × (ℕ → ℝ × Ω) =>
      ‖g (if (path p c answer w.1 w.2 (trialCalls c)).alive then
        (path p c answer w.1 w.2 (trialCalls c)).selected else p.x0)‖
    let R := (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure.prod Q
    Integrable (fun w => F w ^ 2) R ∧ (∫ w, F w ^ 2 ∂R) ≤ 9 * guardRadius p ^ 2 ∧
      R.real {w | p.ε / 4 < F w} ≤ 1 / 3 := by
  have hη : 0 < c.η := by simpa only [hc, tunedConfig] using GuardedHessianTuning.stepSize_pos p hv
  have hsteps : c.steps + 1 = stepCount p := by simpa only [hc] using GuardedHessianTuning.tuned_steps p
  have hgroups : c.groups + 1 = guardGroupCount p := by simpa only [hc] using GuardedHessianTuning.tuned_groups p
  have hconditions := GuardedHessianTuning.tuned_step_conditions p hv
  have hsmall : p.L1 * c.η ≤ 1 / 4 := by simpa only [hc, tunedConfig] using hconditions.1
  have hcurv : p.L0 * c.η ≤ p.ε / 1048576 := by simpa only [hc, tunedConfig] using hconditions.2.2.1
  have hN := GuardedHessianTuning.stepCount_bounds p hv
  have hNlo : 1024 * p.Δ ≤ c.η * (c.steps + 1 : ℕ) * p.ε := by
    rw [hsteps, hc]
    exact hN.1
  have hNhi : (c.steps + 1 : ℕ) ≤ 1024 * p.Δ / (c.η * p.ε) + 2 := by
    rw [hsteps, hc]
    exact hN.2
  have h0 := GuardedHessianTuning.initial_gradient_bound p hv f g hf hg hH hm hgap
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := GuardedHessianTuning.radius_estimates p hL0 hL1 hΔ hε
  have hd := GuardedHessianDescent.expected_gap_and_gradient p c Q answer f g hL0 hL1 hη.le hf hg hH
    hsmall hstep reference (c.steps + 1) le_rfl hEi hEb hm hgap
  have hD : (∫ ξ, f (GuardedHessianDescent.stoppedPoint p c answer reference ξ (c.steps + 1)) - m ∂Q) ≤
      33 * p.Δ + c.η * p.ε / 16 :=
    GuardedHessianTuning.stopped_gap_tuning hη (by positivity) hε le_rfl hcurv hNhi hd.1
  have htrue := GuardedHessianDescent.true_rejection_probability p c Q answer f g hL0 hL1 hη.le hM.1
    hf hg hH hm hstep reference (c.steps + 1)
  have htrueb := GuardedHessianTuning.true_abort_tuning hL0 hL1 hM.1 hε.le hM.2.1 hM.2.2.1 hM.2.2.2
    (by simpa only [hc, tunedConfig] using hconditions.2.2.2) hD
  have hfalseb (t : ℕ) (ht : t ≤ c.steps) : Q.real
      {ξ | (path p c answer reference ξ (transportTime c t + 1)).alive = true ∧
        ‖g (path p c answer reference ξ (transportTime c t + 1)).point‖ ≤ guardRadius p ∧
        (path p c answer reference ξ (transportTime c t + cycleCalls c)).alive = false} ≤
      1 / (128 * (c.steps + 1 : ℕ)) := by
    exact (hfalse t ht).trans (by simpa only [hgroups, hsteps] using GuardedHessianTuning.guardGroupCount_bound p)
  have habort := GuardedHessianDescent.abort_probability_split p c Q answer g reference
    (guardRadius p) (1 / (128 * (c.steps + 1 : ℕ))) (1 / 128) hfalseb (htrue.trans htrueb)
  have hab : Q.real {ξ | (path p c answer reference ξ (trialCalls c)).alive = false} ≤ 1 / 64 := by
    convert habort using 1; field_simp; ring
  let G := ∑ t ∈ Finset.range (c.steps + 1), ∫ ξ,
    if (iterState p c answer reference ξ t).alive then ‖g (iterState p c answer reference ξ t).point‖ else 0 ∂Q
  have hhalf : (∑ t ∈ Finset.range (c.steps + 1), ∫ ξ,
      if GuardedHessianDescent.trialAlive p c answer reference ξ t then
        ‖g (iterState p c answer reference ξ t).point‖ / 2 else 0 ∂Q) = G / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t ht
    have hts : t ≤ c.steps := by have := Finset.mem_range.mp ht; omega
    simp only [GuardedHessianDescent.trialAlive, hts, ↓reduceIte]
    rw [← integral_div]
    congr 1
    funext ξ
    split_ifs <;> simp
  have hdescent : c.η * G / 2 ≤ p.Δ + 2 * c.η * (c.steps + 1 : ℕ) * (p.ε / 128) +
      (c.steps + 1 : ℕ) * (p.L0 * c.η ^ 2) := by
    have hh := hd.2
    rw [hhalf] at hh
    simpa only [mul_div_assoc] using hh
  have hsum := GuardedHessianTuning.gradient_sum_tuning hη (by positivity) hε.le le_rfl hcurv hNlo hdescent
  have hsum' : G ≤ p.ε * (c.steps + 1 : ℕ) / 16 := by
    have hh := (div_le_iff₀ (show (0 : ℝ) < (c.steps + 1 : ℕ) by positivity)).mp hsum
    nlinarith
  have hGfirst (t : ℕ) (ht : t ≤ c.steps) : Integrable (fun ξ =>
      if (iterState p c answer reference ξ t).alive then ‖g (iterState p c answer reference ξ t).point‖ else 0) Q := by
    simpa only [GuardedHessianDescent.trialAlive, ht, ↓reduceIte] using
      GuardedHessianDescent.trial_alive_integrable p c Q answer hη.le hstep reference
        (fun x => ‖g x‖) hg.continuous.norm t
  have hprob := GuardedHessianOutput.selected_failure_probability p c Q answer g hg.continuous.measurable
    hstep reference (by positivity : 0 < p.ε / 4) hGfirst hsum' hab
  have hprob' : _ ≤ (1 / 3 : ℝ) := hprob.trans (by
    have he : (1 / 64 : ℝ) + (p.ε * (c.steps + 1 : ℕ) / 16) /
        ((c.steps + 1 : ℕ) * (p.ε / 4)) = 17 / 64 := by field_simp; ring
    rw [he]
    norm_num)
  have hmom := GuardedHessianOutput.uniform_selected_second_moment p c Q answer g hg.continuous.measurable
    hstep reference hM.1.le h0 hGi hGb
  exact ⟨hmom.1, hmom.2, hprob'⟩

lemma oracle_tuned_trial (p : Params) (hv : spec.valid p) (c : Config) (hc : c = tunedConfig p) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hgm : Measurable (fun w : Space p × Ω => answer (w.1, none) w.2))
    (hhm : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hgi : ∀ y, Integrable (answer (y, none)) P)
    (hgmean : ∀ y, (∫ ω, answer (y, none) ω ∂P) = g y)
    (hgpi : ∀ y, Integrable (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p) P)
    (hgb : ∀ y, (∫ ω, ‖answer (y, none) ω - g y‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p)
    (hhi : ∀ y v, Integrable (answer (y, some v)) P)
    (hhmean : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hhpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hhb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    {m : ℝ} (hf : ∀ x, HasGradientAt f (g x) x)
    (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (reference : Fin (c.steps + 1)) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let S := Measure.infinitePi fun _ : ℕ => Q
    let F := fun w : Fin (c.steps + 1) × (ℕ → ℝ × Ω) =>
      ‖g (if (path p c answer w.1 w.2 (trialCalls c)).alive then
        (path p c answer w.1 w.2 (trialCalls c)).selected else p.x0)‖
    let R := (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure.prod S
    Integrable (fun w => F w ^ 2) R ∧ (∫ w, F w ^ 2 ∂R) ≤ 9 * guardRadius p ^ 2 ∧
      R.real {w | p.ε / 4 < F w} ≤ 1 / 3 := by
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let Q := U.prod P
  let S := Measure.infinitePi fun _ : ℕ => Q
  have hη : 0 < c.η := by simpa only [hc, tunedConfig] using GuardedHessianTuning.stepSize_pos p hv
  have hcond := GuardedHessianTuning.tuned_step_conditions p hv
  have hsmall : p.L1 * c.η ≤ 1 / 4 := by simpa only [hc, tunedConfig] using hcond.1
  have hbase : p.L0 * c.η ≤ guardRadius p / 4 := by simpa only [hc, tunedConfig] using hcond.2.1
  have h0 := GuardedHessianTuning.initial_gradient_bound p hv f g hf hg hH hm hgap
  have hR : c.resetBatch + 1 = batchCount p := by simpa only [hc] using GuardedHessianTuning.tuned_resetBatch p
  have hE : c.epoch + 1 = batchCount p := by simpa only [hc] using GuardedHessianTuning.tuned_epoch p
  have hB : c.guardBatch + 1 = guardBatchCount p := by simpa only [hc] using GuardedHessianTuning.tuned_guardBatch p
  have hJ : c.groups + 1 = guardGroupCount p := by simpa only [hc] using GuardedHessianTuning.tuned_groups p
  have hsize : 6 * (p.σg / guardRadius p + p.αg) ^ p.p /
      ((c.guardBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p := by
    rw [hB]
    exact GuardedHessianTuning.tuned_guard_batch p hv
  have hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16 := by
    rw [hJ]
    exact GuardedHessianTuning.guardGroupCount_small p
  have hthreshold : c.threshold = 3 * guardRadius p / 2 := by rw [hc]; rfl
  have herr := GuardedHessianTuning.tuned_estimator_small p hv
  obtain ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩ := hv
  have hM := (GuardedHessianTuning.radius_estimates p hL0 hL1 hΔ hε).1
  have hK : p.L0 + p.L1 * guardRadius p + p.σh + p.αh * guardRadius p ≤ transportScale p := by
    unfold transportScale
    exact le_add_of_nonneg_right (div_nonneg hε.le hM.le)
  have he (t : ℕ) (ht : t ≤ c.steps) := oracle_estimator_bound p c P answer g hgm hhm hstep
    hL0 hL1 hp.le hp2 hq.le hq2 hσg hαg hσh hαh hM hη.le hK hg hD hH
    hgi hgmean hgpi hgb hhi hhmean hhpi hhb hsmall hbase h0 hthreshold hsize hgroups reference t ht
  have hgm' : Measurable (fun w : Space p × (ℝ × Ω) => answer (w.1, none) w.2.2) :=
    hgm.comp (f := fun w : Space p × (ℝ × Ω) => (w.1, w.2.2)) (by fun_prop)
  have hgi' (y : Space p) : Integrable (fun z : ℝ × Ω => answer (y, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgi y)
  have hgmean' (y : Space p) : (∫ z : ℝ × Ω, answer (y, none) z.2 ∂Q) = g y := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hgmean y
  have hgpi' (y : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (y, none) z.2 - g y‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgpi y)
  have hgb' (y : Space p) : (∫ z : ℝ × Ω, ‖answer (y, none) z.2 - g y‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p := by
    have heq := integral_fun_snd (μ := U) (ν := P) (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p)
    simp only [probReal_univ, one_smul] at heq
    exact heq.trans_le (hgb y)
  apply tuned_trial_guarantees p ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
    c hc S answer f g hf hg hH hm hgap hstep reference
  · intro t ht
    exact (he t ht).1
  · intro t ht
    apply (he t ht).2.trans
    rw [hR, hE]
    simpa only [hc, tunedConfig] using herr
  · intro t _
    exact GuardedHessianIntegration.trajectory_alive_integrable p c hη.le S answer hstep
      (⟨p.x0, 0, 0, reference, p.x0, true, .reset 0 0⟩ : State p c) le_rfl le_rfl
      (fun y => ‖g y‖ ^ 2) (hg.continuous.norm.pow 2) (transportTime c t)
  · intro t ht
    exact GuardedHessianIntegration.oracle_alive_second_moment p c hη.le Q answer g hg hstep
      hL0 hL1 hH hsmall hbase h0 hp.le hp2 hσg hαg hM hthreshold
      (fun y => hgm'.comp (measurable_const.prodMk measurable_id)) hgi' hgmean' hgpi' hgb'
      hsize hgroups reference t ht
  · intro t ht
    exact GuardedHessianIntegration.oracle_guard_false_alarm p c Q answer g hg.continuous.measurable
      hstep hp.le hp2 hσg hαg hM hthreshold
      (fun y => hgm'.comp (measurable_const.prodMk measurable_id)) hgi' hgmean' hgpi' hgb'
      hsize reference t ht

end LongTails.Proofs.GuardedHessianTrial
