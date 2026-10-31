import LongTails.Proofs.HeavyTailedSospWorkIntegration

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedSospConvergence

set_option backward.isDefEq.respectTransparency false

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedProductProcess HeavyTailedSospExecution HeavyTailedSospWork
open HeavyTailedSospOutput HeavyTailedSospWorkIntegration

lemma capped_success_from_aggregate_bounds (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (f : Space p → ℝ) (hG : Continuous (gradient f))
    (hA : Continuous (fun x => fderiv ℝ (gradient f) x))
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (hd : 0 < p.d) (hρ : 0 ≤ p.ρ) (hε : 0 < p.ε)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hh : 0 ≤ c.h) (hs : 0 < c.s) (hhs : c.h ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hMh : (max 1 c.ncSegments : ℕ) * c.h ≤ 2 * c.s)
    (hρh : p.ρ * c.h ≤ c.γ) (hγ : 5 * c.γ = Real.sqrt (p.ρ * p.ε))
    (N C : ℕ) (hT : 0 < c.cycles) (hC : 0 < C)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδu : δ ≤ 1 / 100)
    (hmiss : ∀ x ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p
      (fun x => fderiv ℝ (gradient f) x) (-4 * c.γ),
      (Measure.infinitePi fun _ : ℕ => Q).real
        {ξ | HeavyTailedSospDetection.detectorChoice p c H x ξ (max 1 c.repeats) = none} ≤ δ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hgrad : (∫ ξ, HeavyTailedSospForecastIntegration.markedGradientTotal p c (gradient f) g H 0 N ξ
      ∂(Measure.infinitePi fun _ : ℕ => Q)) / c.cycles ≤ p.ε / 500)
    (hacc : (∫ ξ, ∑ k ∈ Finset.range N,
      (ncCharge p (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ => Q)) / c.cycles ≤ c.h / (5 * c.s))
    (hWC : 10 * ((2 * (c.cycles : ℝ) / (max 1 c.epoch : ℕ) + 1) * (max 1 c.resetBatch : ℕ) +
      2 * c.cycles * (max 1 c.transportBatch : ℕ) + c.cycles * (detectorCalls c : ℝ)) ≤ C) :
    2 / 3 ≤ ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => Q)).real
      {z | secondOrderAccurate p f (trajectory (sampleStep p c g H) C (initial p z.1.val) z.2).selected} := by
  let P := Measure.infinitePi fun _ : ℕ => Q
  let R := (PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure
  let Y := fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
    (trajectory (sampleStep p c g H) N (initial p z.1.val) z.2).selected
  let Z := fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
    (trajectory (sampleStep p c g H) C (initial p z.1.val) z.2).selected
  let W := {z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) | C < unpaddedWork p c g H 0 N z.2}
  have hZ : Measurable Z :=
    (HeavyTailedSospMeasurable.measurable_trajectory_output p c g H hg hH C).comp
      (((measurable_of_finite (fun j : Fin (max 1 c.cycles) => j.val)).comp measurable_fst).prodMk measurable_snd)
  have he : ∀ z, z ∉ W → Z z = Y z := by
    intro z hz
    exact capped_selected_eq_completed p c g H z.1.val N C z.2 (hdone z.2) (Nat.le_of_not_gt hz)
  have hgf := completed_gradient_failure_bound p c g hg H hH P (gradient f) hG hd hh
    (le_of_lt hs) hseg N hT hε hdone hgrad
  have ha : (∫ ξ, ∑ k ∈ Finset.range N,
      (ncCharge p (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase : ℝ) ∂P) /
        c.cycles ≤ 1 / 5 := by
    refine hacc.trans ?_
    apply (div_le_iff₀ (by positivity : 0 < 5 * c.s)).mpr
    linarith
  have hcf := completed_curvature_failure_bound p c g hg H hH
    (fun x => fderiv ℝ (gradient f) x) hA hρ hLip hρh Q hd hh (le_of_lt hs) hseg
    N hT hδ hδu hmiss hdone ha
  have hthreshold : -5 * c.γ = -Real.sqrt (p.ρ * p.ε) := by linarith
  rw [hthreshold] at hcf
  have hwf := completed_joint_cap_failure_bound p c g hg H hH Q N C hT hs hC hMh hdone hacc hWC
  exact success_probability_of_failure_bounds p f hG hA (R.prod P) Y Z hZ W he hgf hcf hwf

lemma execute_success_of_paired_probability (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (f : Space p → ℝ) (hG : Continuous (gradient f))
    (hA : Continuous (fun x => fderiv ℝ (gradient f) x))
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _)) (C : ℕ)
    (hp : 2 / 3 ≤ ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod (P0 : Measure p.Ω))).real
      {z | secondOrderAccurate p f (trajectory (sampleStep p c g H) C (initial p z.1.val) z.2).selected}) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, x, v) ω => match v with | none => g x ω | some u => H x ω u }
    spec.successful p f
      (fun w : (algorithm p c).Seed × (ℕ → p.Ω) =>
        OracleTemplate.execute O (algorithm p c) (fun _ => C) w.1 w.2)
      ⟨((algorithm p c).law : Measure _).prod (P : Measure _), inferInstance⟩ := by
  intro O
  refine ⟨?_, ?_⟩
  · have hm := HeavyTailedSospMeasurable.measurable_execute_sosp p c g H hg hH P C
    have hsm := hm.stronglyMeasurable
    let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
    exact hsm.measurable
  let R := (PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure
  let F := fun z : (Fin (max 1 c.cycles) × (ℕ → Aux p c)) × (ℕ → p.Ω) =>
    (z.1.1, fun k => (z.1.2 k, z.2 k))
  let B := {z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) |
    secondOrderAccurate p f (trajectory (sampleStep p c g H) C (initial p z.1.val) z.2).selected}
  have hout : Measurable (fun z : Fin (max 1 c.cycles) × (ℕ → Aux p c × p.Ω) =>
      (trajectory (sampleStep p c g H) C (initial p z.1.val) z.2).selected) :=
    (HeavyTailedSospMeasurable.measurable_trajectory_output p c g H hg hH C).comp
      (((measurable_of_finite (fun j : Fin (max 1 c.cycles) => j.val)).comp measurable_fst).prodMk measurable_snd)
  have hB : MeasurableSet B := (secondOrderAccurate_measurableSet p f hG hA).preimage hout
  have hm := target_paired_streams_preserving p c R (P0 : Measure _) (P : Measure _) hiid
  have he := hm.measure_preimage hB.nullMeasurableSet
  have hr := congrArg ENNReal.toReal he
  change (((R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)))).prod
      (P : Measure _)).real (F ⁻¹' B)) =
    (R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod (P0 : Measure p.Ω))).real B at hr
  have hevent : {w : (algorithm p c).Seed × (ℕ → p.Ω) |
      secondOrderAccurate p f (OracleTemplate.execute O (algorithm p c) (fun _ => C) w.1 w.2)} = F ⁻¹' B := by
    ext w
    change secondOrderAccurate p f (OracleTemplate.execute O (algorithm p c) (fun _ => C) w.1 w.2) ↔ _
    have hx := execute_sosp p c g H P w.1 w.2 C
    change OracleTemplate.execute O (algorithm p c) (fun _ => C) w.1 w.2 = _ at hx
    rw [hx]
    rfl
  rw [hevent]
  change 2 / 3 ≤ ((R.prod (Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)))).prod
    (P : Measure _)).real (F ⁻¹' B)
  rw [hr]
  exact hp

end LongTails.Proofs.HeavyTailedSospConvergence
