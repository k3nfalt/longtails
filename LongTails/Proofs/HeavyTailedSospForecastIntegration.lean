import LongTails.Proofs.HeavyTailedSospForecast
import LongTails.Proofs.HeavyTailedSospDetectionIntegration
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSospForecastIntegration

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedSospForecast

lemma aux_sign_preserving (p : Params) (c : Config) :
    MeasurePreserving (fun a : Aux p c => a.2.1) (auxLaw p c : Measure (Aux p c))
      (PMF.uniformOfFintype Bool).toMeasure := by
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let S := (PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
    (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure
  exact (measurePreserving_fst (μ := (PMF.uniformOfFintype Bool).toMeasure) (ν := S)).comp
    (measurePreserving_snd (μ := U) (ν := (PMF.uniformOfFintype Bool).toMeasure.prod S))

lemma paired_sign_preserving (p : Params) (c : Config)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0] :
    MeasurePreserving (fun z : Aux p c × p.Ω => z.1.2.1)
      ((auxLaw p c : Measure (Aux p c)).prod P0) (PMF.uniformOfFintype Bool).toMeasure :=
  (aux_sign_preserving p c).comp measurePreserving_fst

lemma integral_uniform_bool (F : Bool → ℝ) :
    (∫ b, F b ∂(PMF.uniformOfFintype Bool).toMeasure) = (F true + F false) / 2 := by
  rw [OracleTemplate.MixedNoise.integral_uniform_finite]
  simp only [Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  ring

lemma curvatureJump_ncInit_integral (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (v : Space p) (hv : s.phase = .ncInit v)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0] :
    Integrable (fun z : Aux p c × p.Ω => curvatureJump p c f s z.1)
      ((auxLaw p c : Measure (Aux p c)).prod P0) ∧
    (∫ z : Aux p c × p.Ω, curvatureJump p c f s z.1
      ∂(auxLaw p c : Measure (Aux p c)).prod P0) =
      (f (s.point + c.s • v) + f (s.point - c.s • v)) / 2 - f s.point := by
  let F := fun b : Bool => f (s.point + ((if b then (1 : ℝ) else -1) * c.s) • v) - f s.point
  have hF : Measurable F := measurable_of_finite F
  have hFi : Integrable F (PMF.uniformOfFintype Bool).toMeasure := Integrable.of_finite
  have hp := paired_sign_preserving p c P0
  have heq : (fun z : Aux p c × p.Ω => curvatureJump p c f s z.1) =
      F ∘ (fun z => z.1.2.1) := by
    funext z
    exact curvatureJump_ncInit p c f s z.1 v hv
  rw [heq]
  refine ⟨hp.integrable_comp_of_integrable hFi, ?_⟩
  have he := integral_map (μ := (auxLaw p c : Measure (Aux p c)).prod P0)
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at he
  change (∫ z : Aux p c × p.Ω, F z.1.2.1 ∂(auxLaw p c : Measure (Aux p c)).prod P0) = _
  rw [← he, integral_uniform_bool]
  simp [F, sub_eq_add_neg]
  ring

lemma symmetric_smooth_upper_bound (p : Params) (f : Space p → ℝ) (G : Space p → Space p)
    (L s : ℝ) (hs : 0 ≤ s) (hG : ∀ x, HasGradientAt f (G x) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x v : Space p) (hv : ‖v‖ = 1) :
    (f (x + s • v) + f (x - s • v)) / 2 ≤ f x + L * s ^ 2 / 2 := by
  have hp := OracleTemplate.Gradient.smooth_upper_bound hG hLip x (x + s • v)
  have hm := OracleTemplate.Gradient.smooth_upper_bound hG hLip x (x - s • v)
  have he : x - s • v - x = -(s • v) := by abel
  rw [he, inner_neg_right, norm_neg] at hm
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs, hv, mul_one] at hp hm
  linarith

lemma curvatureJump_fiber_bound (p : Params) (c : Config)
    (f : Space p → ℝ) (G : Space p → Space p) (A : Space p → Space p →L[ℝ] Space p)
    (L ρ : ℝ) (hs : 0 ≤ c.s) (hγ : 0 ≤ c.γ) (hρs : ρ * c.s ≤ c.γ)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGA : ∀ x, HasFDerivAt G (A x) x)
    (hALip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (s : State p) (hsbound : HeavyTailedSospGeometry.PhaseBound p c.h s.phase)
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0] :
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    Integrable (fun z : Aux p c × p.Ω => curvatureJump p c f s z.1)
      ((auxLaw p c : Measure (Aux p c)).prod P0) ∧
    (∫ z : Aux p c × p.Ω, curvatureJump p c f s z.1 ∂(auxLaw p c : Measure (Aux p c)).prod P0) ≤
      -(c.γ * c.s ^ 2 / 2) * HeavyTailedSospWork.ncCharge p s.phase +
        ((L + c.γ) * c.s ^ 2 / 2) *
          (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator (fun _ => (1 : ℝ)) s := by
  classical
  intro S
  cases hp : s.phase
  case ncInit v =>
    have hv : ‖v‖ = 1 := by simpa only [hp, HeavyTailedSospGeometry.PhaseBound] using hsbound
    obtain ⟨hi, he⟩ := curvatureJump_ncInit_integral p c f s v hp P0
    refine ⟨hi, ?_⟩
    rw [he]
    by_cases hbad : -3 * c.γ / 2 < inner ℝ v (A s.point v)
    · have hu := symmetric_smooth_upper_bound p f G L c.s hs hG hGLip s.point v hv
      simp only [HeavyTailedSospWork.ncCharge, hp, Nat.cast_one, mul_one,
        HeavyTailedSospDetectionIntegration.ncSelectedEvent, Set.indicator_apply,
        Set.mem_ofPred_eq, Phase.ncInit.injEq, exists_eq_left', S, hbad, ↓reduceIte]
      nlinarith
    · have hu := HeavyTailedSospDescent.symmetric_curvature_descent hs hγ hρs
        (fun x => (hG x).hasFDerivAt) hGA hALip s.point v hv (le_of_not_gt hbad)
      simp only [HeavyTailedSospWork.ncCharge, hp, Nat.cast_one, mul_one,
        HeavyTailedSospDetectionIntegration.ncSelectedEvent, Set.indicator_apply,
        Set.mem_ofPred_eq, Phase.ncInit.injEq, exists_eq_left', S, hbad, ↓reduceIte, mul_zero, add_zero]
      linarith
  all_goals simp [curvatureJump, hp, HeavyTailedSospWork.ncCharge,
    HeavyTailedSospDetectionIntegration.ncSelectedEvent]

lemma curvatureJump_measurable (p : Params) (c : Config) (f : Space p → ℝ)
    (hf : Measurable f) :
    Measurable (fun z : State p × Aux p c => curvatureJump p c f z.1 z.2) := by
  have hm : Measurable (Function.uncurry (fun ph (z : State p × Aux p c) =>
      curvatureJump p c f {z.1 with phase := ph} z.2)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · simp only [curvatureJump, full_signedSegment]
      have hsign : Measurable (fun w : Space p × (State p × Aux p c) =>
          if w.2.2.2.1 then (1 : ℝ) else -1) :=
        (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp (by fun_prop)
      fun_prop
    · exact measurable_const
  have hc := hm.comp (((HeavyTailedSospMeasurable.measurable_phase p).comp measurable_fst).prodMk measurable_id)
  convert hc using 1
  funext z
  rfl

lemma continuous_comp_integrable_of_bounded_range (p : Params)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Space p → ℝ) (hf : Continuous f) (Y : Ω → Space p) (hY : Measurable Y)
    (x : Space p) (R : ℝ) (hR : ∀ ω, ‖Y ω - x‖ ≤ R) :
    Integrable (fun ω => f (Y ω)) P := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' (hf.measurable.comp hY).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  exact hC (Y ω) (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hR ω)

noncomputable def curvatureEndpoint (p : Params) (c : Config) (s : State p) (a : Aux p c) : Space p :=
  match s.phase with
  | .ncInit v => s.point + ((if a.2.1 then (1 : ℝ) else -1) * c.s) • v
  | _ => s.point

lemma curvatureJump_endpoint (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (a : Aux p c) :
    curvatureJump p c f s a = f (curvatureEndpoint p c s a) - f s.point := by
  cases hp : s.phase <;> simp [curvatureJump, curvatureEndpoint, hp, full_signedSegment]

lemma curvatureEndpoint_measurable (p : Params) (c : Config) :
    Measurable (fun z : State p × Aux p c => curvatureEndpoint p c z.1 z.2) := by
  have hm : Measurable (Function.uncurry (fun ph (z : State p × Aux p c) =>
      curvatureEndpoint p c {z.1 with phase := ph} z.2)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    all_goals simp only [curvatureEndpoint]
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · have hsign : Measurable (fun w : Space p × (State p × Aux p c) =>
          if w.2.2.2.1 then (1 : ℝ) else -1) :=
        (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp (by fun_prop)
      fun_prop
    · fun_prop
  have hc := hm.comp (((HeavyTailedSospMeasurable.measurable_phase p).comp measurable_fst).prodMk measurable_id)
  convert hc using 1
  funext z
  rfl

lemma curvatureEndpoint_displacement (p : Params) (c : Config) (hs : 0 ≤ c.s)
    (s : State p) (hbound : HeavyTailedSospGeometry.PhaseBound p c.h s.phase) (a : Aux p c) :
    ‖curvatureEndpoint p c s a - s.point‖ ≤ c.s := by
  cases hp : s.phase
  case ncInit v =>
    have hv : ‖v‖ = 1 := by simpa only [hp, HeavyTailedSospGeometry.PhaseBound] using hbound
    simp only [curvatureEndpoint, hp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hv, mul_one]
    split_ifs <;> simp [abs_of_nonneg hs]
  all_goals simpa [curvatureEndpoint, hp] using hs

lemma curvatureJump_integrable_of_bounded_points (p : Params) (c : Config) (hs : 0 ≤ c.s)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Space p → ℝ) (hf : Continuous f) (Y : Ω → State p) (hY : Measurable Y)
    (a : Ω → Aux p c) (ha : Measurable a) (x : Space p) (R : ℝ)
    (hR : ∀ ω, ‖(Y ω).point - x‖ ≤ R)
    (hbound : ∀ ω, HeavyTailedSospGeometry.PhaseBound p c.h (Y ω).phase) :
    Integrable (fun ω => curvatureJump p c f (Y ω) (a ω)) P := by
  have hpoint := (HeavyTailedSospMeasurable.measurable_point p).comp hY
  have hpointI := continuous_comp_integrable_of_bounded_range p P f hf _ hpoint x R hR
  have hend := (curvatureEndpoint_measurable p c).comp (hY.prodMk ha)
  have hendI := continuous_comp_integrable_of_bounded_range p P f hf _ hend x (R + c.s) (fun ω => ?_)
  · convert hendI.sub hpointI using 1
    funext ω
    exact curvatureJump_endpoint p c f (Y ω) (a ω)
  · calc
      ‖curvatureEndpoint p c (Y ω) (a ω) - x‖ ≤
          ‖curvatureEndpoint p c (Y ω) (a ω) - (Y ω).point‖ + ‖(Y ω).point - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c.s + R := add_le_add (curvatureEndpoint_displacement p c hs (Y ω) (hbound ω) (a ω)) (hR ω)
      _ = R + c.s := add_comm _ _

lemma ncCharge_eq_indicator (p : Params) (s : State p) :
    (HeavyTailedSospWork.ncCharge p s.phase : ℝ) =
      (HeavyTailedSospDetectionIntegration.ncSelectedEvent p Set.univ).indicator (fun _ => (1 : ℝ)) s := by
  classical
  cases hp : s.phase <;> simp [HeavyTailedSospWork.ncCharge,
    HeavyTailedSospDetectionIntegration.ncSelectedEvent, hp]

lemma ncSelectedEvent_integrable_comp (p : Params)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → State p) (hY : Measurable Y) (S : Set (Space p × Space p))
    (hS : MeasurableSet S) :
    Integrable (fun ω => (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
      (fun _ => (1 : ℝ)) (Y ω)) P := by
  classical
  convert (integrable_const (μ := P) (1 : ℝ)).indicator
    ((HeavyTailedSospDetectionIntegration.ncSelectedEvent_measurable p S hS).preimage hY) using 1
  funext ω
  rfl

lemma curvatureJump_product_bound (p : Params) (c : Config)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p) (A : Space p → Space p →L[ℝ] Space p)
    (hA : Measurable A) (L ρ : ℝ) (hs : 0 ≤ c.s) (hγ : 0 ≤ c.γ) (hρs : ρ * c.s ≤ c.γ)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGA : ∀ x, HasFDerivAt G (A x) x)
    (hALip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖)
    (Y : Ω → State p) (hY : Measurable Y) (x : Space p) (R : ℝ)
    (hR : ∀ ω, ‖(Y ω).point - x‖ ≤ R)
    (hbound : ∀ ω, HeavyTailedSospGeometry.PhaseBound p c.h (Y ω).phase) :
    let Q := (auxLaw p c : Measure (Aux p c)).prod P0
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    Integrable (fun z : Ω × (Aux p c × p.Ω) => curvatureJump p c f (Y z.1) z.2.1) (P.prod Q) ∧
    (∫ z : Ω × (Aux p c × p.Ω), curvatureJump p c f (Y z.1) z.2.1 ∂P.prod Q) ≤
      -(c.γ * c.s ^ 2 / 2) * (∫ ω, (HeavyTailedSospWork.ncCharge p (Y ω).phase : ℝ) ∂P) +
        ((L + c.γ) * c.s ^ 2 / 2) *
          (∫ ω, (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
            (fun _ => (1 : ℝ)) (Y ω) ∂P) := by
  classical
  intro Q S
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hi := curvatureJump_integrable_of_bounded_points p c hs (P.prod Q) f hf
    (fun z : Ω × (Aux p c × p.Ω) => Y z.1) (hY.comp measurable_fst)
    (fun z => z.2.1) (by fun_prop) x R (fun z => hR z.1) (fun z => hbound z.1)
  have hS : MeasurableSet S := by
    apply measurableSet_lt measurable_const
    have hAv : Measurable (fun z : Space p × Space p => A z.1 z.2) :=
      isBoundedBilinearMap_apply.continuous.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd)
    exact measurable_snd.inner hAv
  have hbI := ncSelectedEvent_integrable_comp p P Y hY S hS
  have hcI : Integrable (fun ω => (HeavyTailedSospWork.ncCharge p (Y ω).phase : ℝ)) P := by
    simpa only [ncCharge_eq_indicator] using ncSelectedEvent_integrable_comp p P Y hY Set.univ MeasurableSet.univ
  have hright := (hcI.const_mul (-(c.γ * c.s ^ 2 / 2))).add
    (hbI.const_mul ((L + c.γ) * c.s ^ 2 / 2))
  have hb := integral_mono hi.integral_prod_left hright (fun ω =>
    (curvatureJump_fiber_bound p c f G A L ρ hs hγ hρs hG hGLip hGA hALip (Y ω) (hbound ω) P0).2)
  rw [← integral_prod _ hi] at hb
  change (∫ z, curvatureJump p c f (Y z.1) z.2.1 ∂P.prod Q) ≤
    (∫ ω, -(c.γ * c.s ^ 2 / 2) * (HeavyTailedSospWork.ncCharge p (Y ω).phase : ℝ) +
      ((L + c.γ) * c.s ^ 2 / 2) *
        (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator (fun _ => (1 : ℝ)) (Y ω) ∂P) at hb
  rw [integral_add (hcI.const_mul _) (hbI.const_mul _), integral_const_mul, integral_const_mul] at hb
  exact ⟨hi, hb⟩

lemma finite_initial_displacement (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target n : ℕ) (η : Fin n → Aux p c × p.Ω) :
    ‖(OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) η).point - p.x0‖ ≤ n * c.h := by
  cases n with
  | zero => simp [OracleTemplate.ContinuizedSimilarQuasar.iterateSamples, initial]
  | succ n =>
    obtain ⟨ξ, he⟩ := HeavyTailedSospEpochIntegration.finite_iterate_stream
      (HeavyTailedSospExecution.sampleStep p c g H) (n + 1) (by omega) (initial p target) η
    rw [he]
    exact HeavyTailedSospGeometry.trajectory_displacement p c g H hd hh hs hseg
      (initial p target) (HeavyTailedSospGeometry.initial_bound p c target) (n + 1) ξ

lemma prefix_current_preserving {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ n))
      (Measure.infinitePi fun _ : ℕ => Q)
      ((Measure.pi fun _ : Fin n => Q).prod Q) := by
  have hcurrent := (MeasurePreserving.id (Measure.pi fun _ : Fin n => Q)).prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) 0)
  exact hcurrent.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving Q n)

lemma fresh_step_integral {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (advance : S → Ω → S)
    (ha : Measurable (Function.uncurry advance)) (n : ℕ) (s : S)
    (F : S × Ω → ℝ) (hF : Measurable F)
    (hi : Integrable (fun z : (Fin n → Ω) × Ω =>
      F (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s z.1, z.2))
        ((Measure.pi fun _ : Fin n => Q).prod Q)) :
    Integrable (fun ξ : ℕ → Ω => F (HeavyTailedProductProcess.trajectory advance n s ξ, ξ n))
      (Measure.infinitePi fun _ : ℕ => Q) ∧
    (∫ ξ : ℕ → Ω, F (HeavyTailedProductProcess.trajectory advance n s ξ, ξ n)
      ∂Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z : (Fin n → Ω) × Ω,
        F (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s z.1, z.2)
          ∂(Measure.pi fun _ : Fin n => Q).prod Q := by
  let J := fun z : (Fin n → Ω) × Ω =>
    F (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s z.1, z.2)
  have hpref : Measurable (fun η : Fin n → Ω =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id)
  have hJ : Measurable J := hF.comp ((hpref.comp measurable_fst).prodMk measurable_snd)
  have hp := prefix_current_preserving Q n
  have heq : (fun ξ : ℕ → Ω => F (HeavyTailedProductProcess.trajectory advance n s ξ, ξ n)) =
      J ∘ (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ n)) := by
    funext ξ
    simp only [J, Function.comp_apply, HeavyTailedSospEpochIntegration.trajectory_finite]
  rw [heq]
  refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
  have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Q)
    hp.measurable.aemeasurable hJ.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

lemma fresh_prefix_integral {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (advance : S → Ω → S)
    (ha : Measurable (Function.uncurry advance)) (n : ℕ) (s : S)
    (F : S → ℝ) (hF : Measurable F) :
    (∫ ξ : ℕ → Ω, F (HeavyTailedProductProcess.trajectory advance n s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ η : Fin n → Ω, F (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η)
        ∂Measure.pi (fun _ : Fin n => Q) := by
  have hpref : Measurable (fun η : Fin n → Ω =>
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n s η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id)
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving Q n
  have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Q)
    hp.measurable.aemeasurable (hF.comp hpref).aestronglyMeasurable
  rw [hp.map_eq] at he
  simpa only [HeavyTailedSospEpochIntegration.trajectory_finite, Function.comp_apply] using he.symm

lemma ncCharge_measurable (p : Params) :
    Measurable (fun s : State p => (HeavyTailedSospWork.ncCharge p s.phase : ℝ)) := by
  simpa only [ncCharge_eq_indicator] using
    (measurable_const (a := (1 : ℝ))).indicator
      (HeavyTailedSospDetectionIntegration.ncSelectedEvent_measurable p Set.univ MeasurableSet.univ)

lemma trajectory_curvatureJump_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p) (A : Space p → Space p →L[ℝ] Space p)
    (hA : Measurable A) (L ρ : ℝ)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hγ : 0 ≤ c.γ) (hρs : ρ * c.s ≤ c.γ)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGA : ∀ x, HasFDerivAt G (A x) x)
    (hALip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (target n : ℕ) :
    let Q := (auxLaw p c : Measure (Aux p c)).prod P0
    let P := Measure.infinitePi fun _ : ℕ => Q
    let X := fun ξ => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    Integrable (fun ξ => curvatureJump p c f (X ξ) (ξ n).1) P ∧
    (∫ ξ, curvatureJump p c f (X ξ) (ξ n).1 ∂P) ≤
      -(c.γ * c.s ^ 2 / 2) * (∫ ξ, (HeavyTailedSospWork.ncCharge p (X ξ).phase : ℝ) ∂P) +
        ((L + c.γ) * c.s ^ 2 / 2) *
          (∫ ξ, (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
            (fun _ => (1 : ℝ)) (X ξ) ∂P) := by
  classical
  intro Q P X S
  let advance := HeavyTailedSospExecution.sampleStep p c g H
  have ha := HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH
  let Y := fun η : Fin n → Aux p c × p.Ω =>
    OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance n (initial p target) η
  have hY : Measurable Y :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hb := curvatureJump_product_bound p c (Measure.pi fun _ : Fin n => Q) P0 f G A hA L ρ
    hs hγ hρs hG hGLip hGA hALip Y hY p.x0 (n * c.h)
    (finite_initial_displacement p c g H hd hh hs hseg target n)
    (fun η => (HeavyTailedSospEpochIntegration.finite_initial_invariants
      p c g H hd hh hs hseg target n η).2.1)
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)).measurable
  have hJ : Measurable (fun z : State p × (Aux p c × p.Ω) => curvatureJump p c f z.1 z.2.1) :=
    (curvatureJump_measurable p c f hf).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have ht := fresh_step_integral Q advance ha n (initial p target) _ hJ hb.1
  refine ⟨ht.1, ?_⟩
  have hAv : Measurable (fun z : Space p × Space p => A z.1 z.2) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_snd.inner hAv)
  have hbad : Measurable ((HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
      (fun _ => (1 : ℝ))) := (measurable_const (a := (1 : ℝ))).indicator
    (HeavyTailedSospDetectionIntegration.ncSelectedEvent_measurable p S hS)
  have hc := fresh_prefix_integral Q advance ha n (initial p target) _ (ncCharge_measurable p)
  have he := fresh_prefix_integral Q advance ha n (initial p target) _ hbad
  change (∫ ξ, curvatureJump p c f (X ξ) (ξ n).1 ∂P) ≤ _
  rw [ht.2, hc, he]
  exact hb.2

lemma trajectory_continuous_integrable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (f : Space p → ℝ) (hf : Continuous f) (target n : ℕ) :
    Integrable (fun ξ => f (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ).point) P := by
  have hX : Measurable (fun ξ : ℕ → Aux p c × p.Ω => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ) :=
    (HeavyTailedProductProcess.trajectory_measurable
    (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  exact continuous_comp_integrable_of_bounded_range p P f hf _
    ((HeavyTailedSospMeasurable.measurable_point p).comp hX) p.x0 (n * c.h)
    (HeavyTailedSospGeometry.trajectory_displacement p c g H hd hh hs hseg
      (initial p target) (HeavyTailedSospGeometry.initial_bound p c target) n)

noncomputable def markedGradientTotal (p : Params) (c : Config)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (target N : ℕ)
    (ξ : ℕ → Aux p c × p.Ω) : ℝ :=
  ∑ k ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p
      (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
        k (initial p target) ξ).phase = 1 then
    ‖G (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
      k (initial p target) ξ).point‖ else 0

lemma markedGradientTotal_integrable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (G : Space p → Space p) (hG : Continuous G) (target N : ℕ) :
    Integrable (markedGradientTotal p c G g H target N) P := by
  classical
  apply integrable_finsetSum
  intro k hk
  have hX : Measurable (fun ξ : ℕ → Aux p c × p.Ω => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ) :=
    (HeavyTailedProductProcess.trajectory_measurable
    (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hi := trajectory_continuous_integrable p c g hg H hH P hd hh hs hseg
    (fun x => ‖G x‖) hG.norm target k
  convert hi.indicator (measurableSet_eq_fun ((HeavyTailedSospStopped.measurable_markCharge p).comp
    ((HeavyTailedSospMeasurable.measurable_phase p).comp hX)) (measurable_const (a := (1 : ℕ)))) using 1
  funext ξ
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply]

lemma completed_gradient_sum (p : Params) (c : Config) (G : Space p → Space p) (L : ℝ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
      N (initial p target) ξ).phase = .done) :
    let X := fun k => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ
    (∑ k ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p (X k).phase = 1 then
      -c.h * ‖G (X k).point‖ + 2 * c.h * ‖(X k).estimate - G (X k).point‖ + L * c.h ^ 2 / 2
      else 0) =
      -c.h * markedGradientTotal p c G g H target N ξ +
        2 * c.h * HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ +
        L * c.h ^ 2 / 2 * c.cycles := by
  classical
  intro X
  have hc := HeavyTailedSospWork.completed_mark_count p c g H target N ξ hdone
  have hcr : (∑ k ∈ Finset.range N, (HeavyTailedSospInvariants.markCharge p (X k).phase : ℝ)) = c.cycles := by
    exact_mod_cast hc
  rw [← hcr]
  simp only [markedGradientTotal, HeavyTailedSospEpochIntegration.markedErrorTotal,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rcases HeavyTailedSospStopped.markCharge_zero_or_one p (X k).phase with hm | hm
  · simp [X] at hm ⊢
    simp [hm]
  · simp only [X] at hm ⊢
    simp [hm]

lemma trajectory_curvatureJump_total_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p) (A : Space p → Space p →L[ℝ] Space p)
    (hA : Measurable A) (L ρ : ℝ)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hγ : 0 ≤ c.γ) (hρs : ρ * c.s ≤ c.γ)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGA : ∀ x, HasFDerivAt G (A x) x)
    (hALip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (target N : ℕ) :
    let Q := (auxLaw p c : Measure (Aux p c)).prod P0
    let P := Measure.infinitePi fun _ : ℕ => Q
    let X := fun n ξ => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    Integrable (fun ξ => ∑ n ∈ Finset.range N, curvatureJump p c f (X n ξ) (ξ n).1) P ∧
    (∫ ξ, ∑ n ∈ Finset.range N, curvatureJump p c f (X n ξ) (ξ n).1 ∂P) ≤
      -(c.γ * c.s ^ 2 / 2) *
        (∫ ξ, ∑ n ∈ Finset.range N, (HeavyTailedSospWork.ncCharge p (X n ξ).phase : ℝ) ∂P) +
        ((L + c.γ) * c.s ^ 2 / 2) *
          (∫ ξ, ∑ n ∈ Finset.range N,
            (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
              (fun _ => (1 : ℝ)) (X n ξ) ∂P) := by
  classical
  intro Q P X S
  have ht (n : ℕ) := trajectory_curvatureJump_bound p c g hg H hH P0 f G A hA L ρ
    hd hh hs hseg hγ hρs hG hGLip hGA hALip target n
  have hX (n : ℕ) : Measurable (X n) :=
    (HeavyTailedProductProcess.trajectory_measurable
      (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
        ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hAv : Measurable (fun z : Space p × Space p => A z.1 z.2) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_snd.inner hAv)
  have hbi (n : ℕ) := ncSelectedEvent_integrable_comp p P (X n) (hX n) S hS
  have hci (n : ℕ) : Integrable (fun ξ => (HeavyTailedSospWork.ncCharge p (X n ξ).phase : ℝ)) P := by
    simpa only [ncCharge_eq_indicator] using
      ncSelectedEvent_integrable_comp p P (X n) (hX n) Set.univ MeasurableSet.univ
  refine ⟨integrable_finsetSum _ (fun n _ => (ht n).1), ?_⟩
  rw [integral_finsetSum _ (fun n _ => (ht n).1),
    integral_finsetSum _ (fun n _ => hci n), integral_finsetSum _ (fun n _ => hbi n)]
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (-(c.γ * c.s ^ 2 / 2) * (∫ ξ, (HeavyTailedSospWork.ncCharge p (X n ξ).phase : ℝ) ∂P) +
          ((L + c.γ) * c.s ^ 2 / 2) *
            (∫ ξ, (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
              (fun _ => (1 : ℝ)) (X n ξ) ∂P)) := Finset.sum_le_sum (fun n _ => (ht n).2)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma expected_completed_descent (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (f : Space p → ℝ) (G : Space p → Space p) (hGc : Continuous G)
    (L Δ : ℝ) (hL : 0 ≤ L) (hG : ∀ x, HasGradientAt f (G x) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ Δ) (target N : ℕ)
    (hdone : ∀ ξ, (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done)
    (herror : Integrable (HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N) P)
    (hcurv : Integrable (fun ξ => ∑ k ∈ Finset.range N, curvatureJump p c f
      (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
        k (initial p target) ξ) (ξ k).1) P) :
    c.h * (∫ ξ, markedGradientTotal p c G g H target N ξ ∂P) ≤
      Δ + 2 * c.h * (∫ ξ, HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ ∂P) +
        L * c.h ^ 2 / 2 * c.cycles +
        (∫ ξ, ∑ k ∈ Finset.range N, curvatureJump p c f
          (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
            k (initial p target) ξ) (ξ k).1 ∂P) := by
  have hgrad := markedGradientTotal_integrable p c g hg H hH P hd hh hs hseg G hGc target N
  have hi := (((integrable_const (μ := P) Δ).add (herror.const_mul (2 * c.h))).add
    (integrable_const (μ := P) (L * c.h ^ 2 / 2 * c.cycles))).add hcurv
  have hb := integral_mono (hgrad.const_mul c.h) hi (fun ξ => ?_)
  · change (∫ ξ, c.h * markedGradientTotal p c G g H target N ξ ∂P) ≤
      (∫ ξ, Δ + 2 * c.h * HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ +
        L * c.h ^ 2 / 2 * c.cycles +
        (∑ k ∈ Finset.range N, curvatureJump p c f
          (HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
            k (initial p target) ξ) (ξ k).1) ∂P) at hb
    have hi2 : Integrable (fun ξ => Δ + 2 * c.h *
        HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ) P :=
      (integrable_const _).add (herror.const_mul _)
    have hi3 : Integrable (fun ξ => Δ + 2 * c.h *
        HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ +
          L * c.h ^ 2 / 2 * c.cycles) P := hi2.add (integrable_const _)
    rw [integral_add hi3 hcurv,
      integral_add hi2 (integrable_const _),
      integral_add (integrable_const _) (herror.const_mul _),
      integral_const_mul, integral_const_mul, integral_const, integral_const] at hb
    simpa using hb
  · have hx := completed_descent_bound p c f G L hL hh hG hLip g H target ξ N (hdone ξ)
    dsimp only at hx
    rw [completed_gradient_sum p c G L g H target N ξ (hdone ξ)] at hx
    have hg := hgap (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).point
    change c.h * markedGradientTotal p c G g H target N ξ ≤ _
    simp only [Pi.add_apply]
    linarith

lemma trajectory_ncChargeTotal_integrable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P] (target N : ℕ) :
    Integrable (fun ξ => ∑ k ∈ Finset.range N,
      (HeavyTailedSospWork.ncCharge p (HeavyTailedProductProcess.trajectory
        (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ).phase : ℝ)) P := by
  apply integrable_finsetSum
  intro k hk
  have hX : Measurable (fun ξ : ℕ → Aux p c × p.Ω => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ) :=
    (HeavyTailedProductProcess.trajectory_measurable
      (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
        ((measurable_const (a := initial p target)).prodMk measurable_id)
  simpa only [ncCharge_eq_indicator] using
    ncSelectedEvent_integrable_comp p P _ hX Set.univ MeasurableSet.univ

lemma completed_virtualIndex_integral (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P] (target N : ℕ)
    (hdone : ∀ ξ, (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∫ ξ, ((HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
      N (initial p target) ξ).virtualIndex : ℝ) ∂P) = c.cycles +
        (max 1 c.ncSegments : ℕ) * (∫ ξ, ∑ k ∈ Finset.range N,
          (HeavyTailedSospWork.ncCharge p (HeavyTailedProductProcess.trajectory
            (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ).phase : ℝ) ∂P) := by
  have he : (fun ξ => ((HeavyTailedProductProcess.trajectory (HeavyTailedSospExecution.sampleStep p c g H)
      N (initial p target) ξ).virtualIndex : ℝ)) =
      (fun ξ => (c.cycles : ℝ) + (max 1 c.ncSegments : ℕ) * ∑ k ∈ Finset.range N,
        (HeavyTailedSospWork.ncCharge p (HeavyTailedProductProcess.trajectory
          (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ).phase : ℝ)) := by
    funext ξ
    rw [HeavyTailedSospWork.completed_virtualIndex p c g H target N ξ (hdone ξ)]
    push_cast
    rfl
  rw [he, integral_add (integrable_const _) ((trajectory_ncChargeTotal_integrable p c g hg H hH P target N).const_mul _),
    integral_const_mul, integral_const]
  simp

lemma combined_expected_descent (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p) (A : Space p → Space p →L[ℝ] Space p)
    (hA : Measurable A) (L ρ Δ e ν : ℝ) (hL : 0 ≤ L)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hγ : 0 ≤ c.γ) (hρs : ρ * c.s ≤ c.γ)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hGA : ∀ x, HasFDerivAt G (A x) x)
    (hALip : ∀ x y, ‖A x - A y‖ ≤ ρ * ‖x - y‖) (target N : ℕ)
    (hgap : ∀ x, f p.x0 - f x ≤ Δ)
    (hdone : ∀ ξ, (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let Q := (auxLaw p c : Measure (Aux p c)).prod P0
    let P := Measure.infinitePi fun _ : ℕ => Q
    let X := fun n ξ => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ
    let S := {z : Space p × Space p | -3 * c.γ / 2 < inner ℝ z.2 (A z.1 z.2)}
    Integrable (HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N) P →
    (∫ ξ, HeavyTailedSospEpochIntegration.markedErrorTotal p c G g H target N ξ ∂P) ≤
      e * ((∫ ξ, ((X N ξ).virtualIndex : ℝ) ∂P) + max 1 c.epoch) →
    (∫ ξ, ∑ n ∈ Finset.range N,
      (HeavyTailedSospDetectionIntegration.ncSelectedEvent p S).indicator
        (fun _ => (1 : ℝ)) (X n ξ) ∂P) ≤ ν * c.cycles →
    c.h * (∫ ξ, markedGradientTotal p c G g H target N ξ ∂P) +
      (c.γ * c.s ^ 2 / 2 - 2 * c.h * e * (max 1 c.ncSegments : ℕ)) *
        (∫ ξ, ∑ n ∈ Finset.range N, (HeavyTailedSospWork.ncCharge p (X n ξ).phase : ℝ) ∂P) ≤
      Δ + 2 * c.h * e * ((c.cycles : ℝ) + max 1 c.epoch) +
        L * c.h ^ 2 / 2 * c.cycles + ((L + c.γ) * c.s ^ 2 / 2) * ν * c.cycles := by
  intro Q P X S herror herr hbad
  have hcurv := trajectory_curvatureJump_total_bound p c g hg H hH P0 f G A hA L ρ
    hd hh hs hseg hγ hρs hG hGLip hGA hALip target N
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hGA x).continuousAt)
  have hdesc := expected_completed_descent p c g hg H hH P hd hh hs hseg f G hGc L Δ hL hG
    hGLip hgap target N hdone herror hcurv.1
  have hv := completed_virtualIndex_integral p c g hg H hH P target N hdone
  change (∫ ξ, ((X N ξ).virtualIndex : ℝ) ∂P) = _ at hv
  rw [hv] at herr
  have he := mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 2 * c.h)
  have hb := mul_le_mul_of_nonneg_left hbad
    (by positivity : 0 ≤ (L + c.γ) * c.s ^ 2 / 2)
  have hc := hcurv.2
  dsimp only at hc
  nlinarith

lemma primitive_combined_expected_descent (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p)
    (hG : ∀ x, HasGradientAt f (G x) x) (hDG : Differentiable ℝ G)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    (hALip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ p.ρ * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hd : 0 < p.d) (hL : 0 ≤ p.L) (hρ : 0 ≤ p.ρ) (hσh : 0 ≤ p.σh)
    (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s) (hγ : 0 < c.γ)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hρs : p.ρ * c.s ≤ c.γ)
    (hgi : ∀ x, Integrable (fun ω => g x ω - G x) P0)
    (hgm : ∀ x, (∫ ω, g x ω - G x ∂P0) = 0)
    (hgpi : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ p.p) P0)
    (hgb : ∀ x, (∫ ω, ‖g x ω - G x‖ ^ p.p ∂P0) ≤ p.σg ^ p.p)
    (hi : ∀ x v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ x v, (∫ ω, H x ω v ∂P0) = fderiv ℝ G x v)
    (hpi : ∀ x v, Integrable (fun ω => ‖H x ω v - fderiv ℝ G x v‖ ^ p.p) P0)
    (hb : ∀ x v, (∫ ω, ‖H x ω v - fderiv ℝ G x v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (htune : 6 * p.σh ^ p.p / ((max 1 c.meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤ (c.γ / 8) ^ p.p)
    (e ν : ℝ)
    (herrTune : (6 * p.σg ^ p.p / ((max 1 c.resetBatch : ℕ) : ℝ) ^ (p.p - 1)) ^ (1 / p.p) +
      (6 * ((max 1 c.epoch * max 1 c.transportBatch : ℕ) : ℝ) *
        (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ p.p *
          ((p.ρ * c.h ^ 2) ^ p.p + 6 * p.σh ^ p.p * c.h ^ p.p))) ^ (1 / p.p) ≤ e)
    (hνTune : ((max 1 c.repeats : ℕ) : ℝ) * Real.exp (-((max 1 c.groups : ℕ) : ℝ) / 8) ≤ ν)
    (target N : ℕ)
    (hdone : ∀ ξ, (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let P := Measure.infinitePi fun _ : ℕ => (auxLaw p c : Measure (Aux p c)).prod P0
    let X := fun n ξ => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) n (initial p target) ξ
    c.h * (∫ ξ, markedGradientTotal p c G g H target N ξ ∂P) +
      (c.γ * c.s ^ 2 / 2 - 2 * c.h * e * (max 1 c.ncSegments : ℕ)) *
        (∫ ξ, ∑ n ∈ Finset.range N, (HeavyTailedSospWork.ncCharge p (X n ξ).phase : ℝ) ∂P) ≤
      p.Δ + 2 * c.h * e * ((c.cycles : ℝ) + max 1 c.epoch) +
        p.L * c.h ^ 2 / 2 * c.cycles + ((p.L + c.γ) * c.s ^ 2 / 2) * ν * c.cycles := by
  intro P X
  have hD : Continuous (fderiv ℝ G) :=
    (show LipschitzWith ⟨p.ρ, hρ⟩ (fderiv ℝ G) from
      LipschitzWith.of_dist_le_mul (fun x y => by
        change dist (fderiv ℝ G x) (fderiv ℝ G y) ≤ p.ρ * dist x y
        simpa only [dist_eq_norm] using hALip x y)).continuous
  have he := HeavyTailedSospEpochIntegration.primitive_expected_marked_error_bound p c P0 G hDG hD
    hρ hσh hd hh hs hseg hp hp2 hALip g hg H hH hi hm hpi hb target N hgi hgm hgpi hgb
  have hbad := HeavyTailedSospDetectionIntegration.primitive_expected_bad_curvature_count p hd c
    g hg H hH (fderiv ℝ G) hD.measurable P0 hp.le hp2 hγ hi hm hpi hb htune target N hdone
  apply combined_expected_descent p c g hg H hH P0 f G (fderiv ℝ G) hD.measurable
    p.L p.ρ p.Δ e ν hL hd hh hs hseg hγ.le hρs hG hGLip
    (fun x => (hDG x).hasFDerivAt) hALip target N hgap hdone he.1
  · exact he.2.trans (mul_le_mul_of_nonneg_right herrTune (by
      apply add_nonneg
      · exact integral_nonneg (fun _ => Nat.cast_nonneg _)
      · positivity))
  · exact hbad.2.trans (mul_le_mul_of_nonneg_right hνTune (Nat.cast_nonneg _))

lemma outer_coefficient_bound {h e M s ε : ℝ}
    (he : 0 ≤ e) (hs : 0 ≤ s)
    (hM : h * M ≤ 2 * s) (heps : e ≤ ε / 10000) :
    ε * s / 4 ≤ ε * s / 2 - 2 * h * e * M := by
  have h1 := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 2 * e)
  have h2 := mul_le_mul_of_nonneg_right heps (by positivity : 0 ≤ 4 * s)
  nlinarith

lemma outer_remainder_bound {h e T q L Δ β ν ε : ℝ}
    (hh : 0 ≤ h) (he : 0 ≤ e) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hq : q ≤ T) (heps : e ≤ ε / 10000) (hLh : L * h ≤ ε / 100)
    (hgap : Δ ≤ T * h * ε / 100) (hrisk : β * ν ≤ h * ε / 400) :
    Δ + 2 * h * e * (T + q) + L * h ^ 2 / 2 * T + β * ν * T ≤ T * h * ε / 20 := by
  have h1 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * h * e)
  have h2 := mul_le_mul_of_nonneg_right heps (by positivity : 0 ≤ 4 * h * T)
  have h3 := mul_le_mul_of_nonneg_right hLh (by positivity : 0 ≤ h * T / 2)
  have h4 := mul_le_mul_of_nonneg_right hrisk hT
  have h0 : 0 ≤ T * h * ε := by positivity
  nlinarith

lemma outer_average_bounds {h s ε T C G A R : ℝ}
    (hh : 0 < h) (hs : 0 < s) (hε : 0 < ε) (hT : 0 < T)
    (hG : 0 ≤ G) (hA : 0 ≤ A)
    (hC : ε * s / 4 ≤ C) (hR : R ≤ T * h * ε / 20)
    (hmain : h * G + C * A ≤ R) :
    G / T ≤ ε / 20 ∧ A / T ≤ h / (5 * s) := by
  have hCA := mul_le_mul_of_nonneg_right hC hA
  have hCA0 : 0 ≤ C * A := le_trans (by positivity) hCA
  have hHG : 0 ≤ h * G := by positivity
  have hg : h * G ≤ T * h * ε / 20 := by linarith
  have ha : ε * s / 4 * A ≤ T * h * ε / 20 := by linarith
  constructor
  · apply (div_le_iff₀ hT).mpr
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith
  · apply (div_le_iff₀ hT).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 5 * s)).mpr
    apply (mul_le_mul_iff_left₀ hε).mp
    nlinarith

end LongTails.Proofs.HeavyTailedSospForecastIntegration
