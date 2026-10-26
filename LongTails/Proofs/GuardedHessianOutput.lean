import LongTails.Proofs.GuardedHessianDescent

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.GuardedHessianExecution
open LongTails.Proofs.GuardedHessianEstimator
open LongTails.Proofs.GuardedHessianDescent

namespace LongTails.Proofs.GuardedHessianOutput

lemma path_sameDynamics (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target reference : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    SameDynamics p c (path p c answer target ξ n) (path p c answer reference ξ n) :=
  sameDynamics_trajectory p c answer (by simp [SameDynamics]) ξ n

lemma trial_output_representation (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (target reference : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    (if (path p c answer target ξ (trialCalls c)).alive then
      (path p c answer target ξ (trialCalls c)).selected else p.x0) =
    if (path p c answer reference ξ (trialCalls c)).alive then
      (iterState p c answer reference ξ target.val).point else p.x0 := by
  have hd := path_sameDynamics p c answer target reference ξ (trialCalls c)
  have hx := path_sameDynamics p c answer target reference ξ (transportTime c target.val)
  by_cases ha : (path p c answer target ξ (trialCalls c)).alive = true
  · have hr : (path p c answer reference ξ (trialCalls c)).alive = true := hd.2.2.2.1.symm.trans ha
    simp only [ha, hr, ↓reduceIte]
    exact (trial_selected_on_survival p c answer target ξ ha).trans hx.1
  · have hr : ¬(path p c answer reference ξ (trialCalls c)).alive = true := by
      simpa only [hd.2.2.2.1] using ha
    simp [ha, hr]

lemma selected_second_moment_pointwise (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (target reference : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) :
    ‖g (if (path p c answer target ξ (trialCalls c)).alive then
      (path p c answer target ξ (trialCalls c)).selected else p.x0)‖ ^ 2 ≤
      (if (iterState p c answer reference ξ target.val).alive then
        ‖g (iterState p c answer reference ξ target.val).point‖ ^ 2 else 0) + ‖g p.x0‖ ^ 2 := by
  rw [trial_output_representation p c answer target reference ξ]
  by_cases ha : (path p c answer reference ξ (trialCalls c)).alive = true
  · have ht : transportTime c target.val ≤ trialCalls c := by
      have hh := transportTime_remaining c (show target.val ≤ c.steps by omega)
      omega
    have hp := path_alive_mono p c answer reference ξ ht ha
    change (iterState p c answer reference ξ target.val).alive = true at hp
    simp only [ha, hp, ↓reduceIte]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    have hn : 0 ≤ if (iterState p c answer reference ξ target.val).alive then
        ‖g (iterState p c answer reference ξ target.val).point‖ ^ 2 else 0 := by
      split_ifs <;> positivity
    linarith

lemma measurable_trial_candidate (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target : Fin (c.steps + 1)) :
    Measurable (fun ξ => if (path p c answer target ξ (trialCalls c)).alive then
      (path p c answer target ξ (trialCalls c)).selected else p.x0) := by
  have ht : Measurable (fun ξ => path p c answer target ξ (trialCalls c)) :=
    (HeavyTailedProductProcess.trajectory_measurable hstep _).comp
      (measurable_const.prodMk measurable_id)
  exact Measurable.ite (measurableSet_eq_fun
    ((GuardedHessianMeasurable.measurable_alive p c).comp ht) measurable_const)
    ((GuardedHessianMeasurable.measurable_selected p c).comp ht) measurable_const

lemma selected_second_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (target reference : Fin (c.steps + 1)) {M : ℝ} (hM : 0 ≤ M) (h0 : ‖g p.x0‖ ≤ M)
    (hi : Integrable (fun ξ => if (iterState p c answer reference ξ target.val).alive then
      ‖g (iterState p c answer reference ξ target.val).point‖ ^ 2 else 0) Q)
    (hb : (∫ ξ, if (iterState p c answer reference ξ target.val).alive then
      ‖g (iterState p c answer reference ξ target.val).point‖ ^ 2 else 0 ∂Q) ≤ 8 * M ^ 2) :
    let F := fun ξ => ‖g (if (path p c answer target ξ (trialCalls c)).alive then
      (path p c answer target ξ (trialCalls c)).selected else p.x0)‖ ^ 2
    Integrable F Q ∧ (∫ ξ, F ξ ∂Q) ≤ 9 * M ^ 2 := by
  let F := fun ξ => ‖g (if (path p c answer target ξ (trialCalls c)).alive then
    (path p c answer target ξ (trialCalls c)).selected else p.x0)‖ ^ 2
  let G := fun ξ => (if (iterState p c answer reference ξ target.val).alive then
    ‖g (iterState p c answer reference ξ target.val).point‖ ^ 2 else 0) + ‖g p.x0‖ ^ 2
  have hFi : Integrable F Q := (hi.add (integrable_const _)).mono'
    ((hg.comp (measurable_trial_candidate p c answer hstep target)).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact selected_second_moment_pointwise p c answer g target reference ξ))
  refine ⟨hFi, ?_⟩
  have hh := integral_mono hFi (hi.add (integrable_const _))
    (selected_second_moment_pointwise p c answer g target reference)
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul] at hh
  dsimp only [F] at *
  nlinarith [sq_le_sq₀ (norm_nonneg (g p.x0)) hM |>.mpr h0]

lemma uniform_joint_integral {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (F : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (F i) Q) :
    Integrable (fun w : ι × Ω => F w.1 w.2) ((PMF.uniformOfFintype ι).toMeasure.prod Q) ∧
      (∫ w : ι × Ω, F w.1 w.2 ∂((PMF.uniformOfFintype ι).toMeasure.prod Q)) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ ω, F i ω ∂Q := by
  have hme : Measurable (fun w : ι × Ω => F w.1 w.2) :=
    measurable_from_prod_countable_right hm
  have hint : Integrable (fun w : ι × Ω => F w.1 w.2)
      ((PMF.uniformOfFintype ι).toMeasure.prod Q) :=
    (integrable_prod_iff hme.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hi, Integrable.of_finite⟩
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  exact OracleTemplate.MixedNoise.integral_uniform_finite _

lemma uniform_joint_bound {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (F : ι → Ω → ℝ) (C : ℝ)
    (hm : ∀ i, Measurable (F i))
    (hb : ∀ i, Integrable (F i) Q ∧ (∫ ω, F i ω ∂Q) ≤ C) :
    Integrable (fun w : ι × Ω => F w.1 w.2) ((PMF.uniformOfFintype ι).toMeasure.prod Q) ∧
      (∫ w : ι × Ω, F w.1 w.2 ∂((PMF.uniformOfFintype ι).toMeasure.prod Q)) ≤ C := by
  have hh := uniform_joint_integral Q F hm (fun i => (hb i).1)
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hb i).2)
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι * C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using hsum
    _ = C := by field_simp

lemma uniform_selected_second_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (reference : Fin (c.steps + 1)) {M : ℝ} (hM : 0 ≤ M) (h0 : ‖g p.x0‖ ≤ M)
    (hi : ∀ t ≤ c.steps, Integrable (fun ξ => if (iterState p c answer reference ξ t).alive then
      ‖g (iterState p c answer reference ξ t).point‖ ^ 2 else 0) Q)
    (hb : ∀ t ≤ c.steps, (∫ ξ, if (iterState p c answer reference ξ t).alive then
      ‖g (iterState p c answer reference ξ t).point‖ ^ 2 else 0 ∂Q) ≤ 8 * M ^ 2) :
    let F := fun w : Fin (c.steps + 1) × (ℕ → ℝ × Ω) =>
      ‖g (if (path p c answer w.1 w.2 (trialCalls c)).alive then
        (path p c answer w.1 w.2 (trialCalls c)).selected else p.x0)‖ ^ 2
    Integrable F ((PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure.prod Q) ∧
      (∫ w, F w ∂((PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure.prod Q)) ≤ 9 * M ^ 2 := by
  dsimp only
  apply uniform_joint_bound Q (fun (t : Fin (c.steps + 1)) ξ =>
    ‖g (if (path p c answer t ξ (trialCalls c)).alive then
      (path p c answer t ξ (trialCalls c)).selected else p.x0)‖ ^ 2) (9 * M ^ 2)
  · intro t
    exact ((hg.comp (measurable_trial_candidate p c answer hstep t)).norm.pow_const 2)
  · intro t
    exact selected_second_moment p c Q answer g hg hstep t reference hM h0
      (hi t.val (by omega)) (hb t.val (by omega))

lemma selected_failure_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℕ → ℝ × Ω)) [IsProbabilityMeasure Q]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (reference : Fin (c.steps + 1)) {ρ a S : ℝ} (hρ : 0 < ρ)
    (hGi : ∀ t ≤ c.steps, Integrable (fun ξ => if (iterState p c answer reference ξ t).alive then
      ‖g (iterState p c answer reference ξ t).point‖ else 0) Q)
    (hGb : (∑ t ∈ Finset.range (c.steps + 1), ∫ ξ,
      if (iterState p c answer reference ξ t).alive then
        ‖g (iterState p c answer reference ξ t).point‖ else 0 ∂Q) ≤ S)
    (hA : Q.real {ξ | (path p c answer reference ξ (trialCalls c)).alive = false} ≤ a) :
    ((PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure.prod Q).real
      {w | ρ < ‖g (if (path p c answer w.1 w.2 (trialCalls c)).alive then
        (path p c answer w.1 w.2 (trialCalls c)).selected else p.x0)‖} ≤
      a + S / ((c.steps + 1 : ℕ) * ρ) := by
  let U := (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure
  let F := fun (t : Fin (c.steps + 1)) (ξ : ℕ → ℝ × Ω) =>
    if (iterState p c answer reference ξ t.val).alive then
      ‖g (iterState p c answer reference ξ t.val).point‖ else 0
  let A := {ξ | (path p c answer reference ξ (trialCalls c)).alive = false}
  have hFm (t : Fin (c.steps + 1)) : Measurable (F t) := by
    have ht : Measurable (fun ξ => iterState p c answer reference ξ t.val) :=
      (HeavyTailedProductProcess.trajectory_measurable hstep _).comp
        (measurable_const.prodMk measurable_id)
    exact Measurable.ite (measurableSet_eq_fun
      ((GuardedHessianMeasurable.measurable_alive p c).comp ht) measurable_const)
      ((hg.comp ((GuardedHessianMeasurable.measurable_point p c).comp ht)).norm) measurable_const
  have hjoint := uniform_joint_integral Q F hFm (fun t => hGi t.val (by omega))
  have hmean : (∫ w, F w.1 w.2 ∂U.prod Q) ≤ S / (c.steps + 1 : ℕ) := by
    rw [hjoint.2, Fintype.card_fin]
    simp only [F]
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => ∫ ξ,
      if (iterState p c answer reference ξ t).alive then
        ‖g (iterState p c answer reference ξ t).point‖ else 0 ∂Q)]
    exact (mul_le_mul_of_nonneg_left hGb (by positivity)).trans_eq (by ring)
  have hAm : MeasurableSet A := measurableSet_eq_fun
    ((GuardedHessianMeasurable.measurable_alive p c).comp
      ((HeavyTailedProductProcess.trajectory_measurable hstep _).comp
        (measurable_const.prodMk measurable_id))) measurable_const
  have hpre : (U.prod Q).real (Prod.snd ⁻¹' A) = Q.real A :=
    measurePreserving_snd.measureReal_preimage hAm.nullMeasurableSet
  have hsub : {w : Fin (c.steps + 1) × (ℕ → ℝ × Ω) |
      ρ < ‖g (if (path p c answer w.1 w.2 (trialCalls c)).alive then
        (path p c answer w.1 w.2 (trialCalls c)).selected else p.x0)‖} ⊆
      (Prod.snd ⁻¹' A) ∪ {w | ρ ≤ F w.1 w.2} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    by_cases ha : (path p c answer reference w.2 (trialCalls c)).alive = true
    · right
      rw [trial_output_representation p c answer w.1 reference w.2] at hw
      have ht : transportTime c w.1.val ≤ trialCalls c := by
        have hh := transportTime_remaining c (show w.1.val ≤ c.steps by omega)
        omega
      have hp := path_alive_mono p c answer reference w.2 ht ha
      change (iterState p c answer reference w.2 w.1.val).alive = true at hp
      simpa only [Set.mem_ofPred_eq, F, ha, hp, ↓reduceIte] using hw.le
    · left
      exact Bool.eq_false_iff.mpr ha
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := U.prod Q) (f := fun w => F w.1 w.2)
    (Filter.Eventually.of_forall (fun w => by dsimp only [F]; split_ifs <;> positivity)) hjoint.1 ρ
  have hprob : (U.prod Q).real {w | ρ ≤ F w.1 w.2} ≤ S / ((c.steps + 1 : ℕ) * ρ) := by
    apply (le_div_iff₀ (mul_pos (by positivity) hρ)).mpr
    have hh := hmark.trans hmean
    have hT : (0 : ℝ) < (c.steps + 1 : ℕ) := by positivity
    have he := (le_div_iff₀ hT).mp hh
    nlinarith
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add (hpre ▸ hA) hprob))

end LongTails.Proofs.GuardedHessianOutput
