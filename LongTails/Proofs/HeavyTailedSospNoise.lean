import LongTails.Proofs.HeavyTailedSospStopped
import LongTails.Proofs.HeavyTailedHessianTransport

open MeasureTheory Set
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp

namespace LongTails.Proofs.HeavyTailedSospNoise

abbrev Tail (p : Params) (c : Config) :=
  Bool × (Fin p.d → Bool) × Fin (max 1 c.probeSteps)

noncomputable def tailLaw (p : Params) (c : Config) : ProbabilityMeasure (Tail p c) := by
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  exact ⟨(PMF.uniformOfFintype Bool).toMeasure.prod
    ((PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
      (PMF.uniformOfFintype (Fin (max 1 c.probeSteps))).toMeasure), inferInstance⟩

lemma tail_path_oracle_projection (p : Params) (c : Config) (P : Measure p.Ω) [SFinite P] :
    MeasurePreserving (fun z : Aux p c × p.Ω => (z.1.2, (z.1.1, z.2)))
      ((auxLaw p c).toMeasure.prod P)
      ((tailLaw p c).toMeasure.prod ((volume.restrict (Ioc (0 : ℝ) 1)).prod P)) := by
  have hswap := (Measure.measurePreserving_swap
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (ν := (tailLaw p c).toMeasure)).prod (MeasurePreserving.id P)
  exact (measurePreserving_prodAssoc (tailLaw p c).toMeasure
    (volume.restrict (Ioc (0 : ℝ) 1)) P).comp hswap

lemma path_oracle_projection (p : Params) (c : Config) (P : Measure p.Ω) [SFinite P] :
    MeasurePreserving (fun z : Aux p c × p.Ω => (z.1.1, z.2))
      ((auxLaw p c).toMeasure.prod P) ((volume.restrict (Ioc (0 : ℝ) 1)).prod P) := by
  let : NeZero (max 1 c.probeSteps) := ⟨by omega⟩
  have haux : MeasurePreserving (fun a : Aux p c => a.1)
      (auxLaw p c).toMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    exact measurePreserving_fst
  exact haux.prod (MeasurePreserving.id P)

lemma paired_transport_moment (p : Params) (c : Config) (P : Measure p.Ω) [IsProbabilityMeasure P]
    (G : Space p → Space p) (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (x v : Space p) :
    let Q := (auxLaw p c).toMeasure.prod P
    let F := fun z : Aux p c × p.Ω => H (x + z.1.1 • v) z.2 v
    Integrable F Q ∧ (∫ z, F z ∂Q) = G (x + v) - G x ∧
      Integrable (fun z => ‖F z - (G (x + v) - G x)‖ ^ α) Q ∧
      (∫ z, ‖F z - (G (x + v) - G x)‖ ^ α ∂Q) ≤
        (ρ * ‖v‖ ^ 2) ^ α + 6 * σ ^ α * ‖v‖ ^ α := by
  intro Q F
  have hpj := path_oracle_projection p c P
  have hbase := HeavyTailedHessianTransport.random_path_transport hG hD hρ hσ hα hα2
    hLip H hH hi hm hpi hb x v
  have hF : Measurable (fun w : ℝ × p.Ω => H (x + w.1 • v) w.2 v) := by
    exact (hH.comp ((measurable_const.add (measurable_fst.smul_const v)).prodMk measurable_snd)).apply_continuousLinearMap v
  have heq : (∫ z, F z ∂Q) =
      (∫ w : ℝ × p.Ω, H (x + w.1 • v) w.2 v ∂(volume.restrict (Ioc (0 : ℝ) 1)).prod P) := by
    rw [← hpj.map_eq]
    exact (integral_map hpj.measurable.aemeasurable hF.aestronglyMeasurable).symm
  have heqp : (∫ z, ‖F z - (G (x + v) - G x)‖ ^ α ∂Q) =
      (∫ w : ℝ × p.Ω, ‖H (x + w.1 • v) w.2 v - (G (x + v) - G x)‖ ^ α
        ∂(volume.restrict (Ioc (0 : ℝ) 1)).prod P) := by
    rw [← hpj.map_eq]
    exact (integral_map hpj.measurable.aemeasurable
      ((hF.sub measurable_const).norm.pow_const α).aestronglyMeasurable).symm
  exact ⟨hpj.integrable_comp_of_integrable hbase.1, heq.trans hbase.2.1,
    hpj.integrable_comp_of_integrable hbase.2.2.1, heqp.trans_le hbase.2.2.2⟩

lemma centered_mixture {E Ω Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Ξ × Ω → E) (hF : Measurable F) {α κ : ℝ} (hα : 1 ≤ α)
    (hpi : ∀ t, Integrable (fun ω => ‖F (t, ω)‖ ^ α) P)
    (hb : ∀ t, (∫ ω, ‖F (t, ω)‖ ^ α ∂P) ≤ κ)
    (hm : ∀ t, (∫ ω, F (t, ω) ∂P) = 0) :
    Integrable F (Q.prod P) ∧ (∫ w, F w ∂Q.prod P) = 0 ∧
      Integrable (fun w => ‖F w‖ ^ α) (Q.prod P) ∧
      (∫ w, ‖F w‖ ^ α ∂Q.prod P) ≤ κ := by
  have hmoment := WeakGradientConvolution.nonnegative_fiber_integral_bound (P := Q) (Q := P)
    (hF.norm.pow_const α).stronglyMeasurable
    (fun w => Real.rpow_nonneg (norm_nonneg (F w)) α)
    (Filter.Eventually.of_forall hpi) (integrable_const κ) (Filter.Eventually.of_forall hb)
  have hmean := HeavyTailedHessianTransport.mixture_mean_of_centered_moment (P := P) (Q := Q) (0 : E) hα hF
    (by simpa using hmoment.1) (Filter.Eventually.of_forall hm)
  refine ⟨hmean.1, ?_, hmoment.1, ?_⟩
  · simpa using hmean.2
  · simpa using hmoment.2

lemma scaled_centered_moment {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → E) (δ : E) {a α κ : ℝ}
    (ha : 0 ≤ a) (hi : Integrable F P) (hm : (∫ ω, F ω ∂P) = δ)
    (hpi : Integrable (fun ω => ‖F ω - δ‖ ^ α) P)
    (hb : (∫ ω, ‖F ω - δ‖ ^ α ∂P) ≤ κ) :
    Integrable (fun ω => a • (F ω - δ)) P ∧
      (∫ ω, a • (F ω - δ) ∂P) = 0 ∧
      Integrable (fun ω => ‖a • (F ω - δ)‖ ^ α) P ∧
      (∫ ω, ‖a • (F ω - δ)‖ ^ α ∂P) ≤ a ^ α * κ := by
  have he : Integrable (fun ω => F ω - δ) P := hi.sub (integrable_const δ)
  have heq (ω : Ω) : ‖a • (F ω - δ)‖ ^ α = a ^ α * ‖F ω - δ‖ ^ α := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _)]
  refine ⟨Integrable.smul a he, ?_, ?_, ?_⟩
  · rw [integral_smul, integral_sub hi (integrable_const δ), hm, integral_const]
    simp
  · simp_rw [heq]
    exact hpi.const_mul _
  · simp_rw [heq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ha α)

lemma transport_bound_mono (p : Params) {ρ σ h α : ℝ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hα : 0 ≤ α)
    (v : Space p) (hv : ‖v‖ ≤ h) :
    (ρ * ‖v‖ ^ 2) ^ α + 6 * σ ^ α * ‖v‖ ^ α ≤
      (ρ * h ^ 2) ^ α + 6 * σ ^ α * h ^ α := by
  have hsquare : ‖v‖ ^ 2 ≤ h ^ 2 := sq_le_sq₀ (norm_nonneg v) hh |>.mpr hv
  have hfirst := Real.rpow_le_rpow (mul_nonneg hρ (sq_nonneg _))
    (mul_le_mul_of_nonneg_left hsquare hρ) hα
  have hsecond := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg v) hv hα)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hσ α))
  exact add_le_add hfirst hsecond

lemma tail_centered_transport_moment (p : Params) (c : Config) (P : Measure p.Ω)
    [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ h a α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (x : Space p) (v : Tail p c → Space p) (hv : ∀ t, ‖v t‖ ≤ h) :
    let Q := (auxLaw p c).toMeasure.prod P
    let F := fun z : Aux p c × p.Ω => a •
      (H (x + z.1.1 • v z.1.2) z.2 (v z.1.2) - (G (x + v z.1.2) - G x))
    Integrable F Q ∧ (∫ z, F z ∂Q) = 0 ∧
      Integrable (fun z => ‖F z‖ ^ α) Q ∧
      (∫ z, ‖F z‖ ^ α ∂Q) ≤ a ^ α * ((ρ * h ^ 2) ^ α + 6 * σ ^ α * h ^ α) := by
  intro Q F
  let U : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let F' : Tail p c × (ℝ × p.Ω) → Space p := fun w => a •
    (H (x + w.2.1 • v w.1) w.2.2 (v w.1) - (G (x + v w.1) - G x))
  have hpoint (t : Tail p c) := HeavyTailedHessianTransport.random_path_transport hG hD
    hρ hσ hα hα2 hLip H hH hi hm hpi hb x (v t)
  have hscaled (t : Tail p c) := scaled_centered_moment (U.prod P)
    (fun w : ℝ × p.Ω => H (x + w.1 • v t) w.2 (v t)) (G (x + v t) - G x)
    ha (hpoint t).1 (hpoint t).2.1 (hpoint t).2.2.1 (hpoint t).2.2.2
  have hFm : Measurable F' := by
    have hvmeas : Measurable v := measurable_of_countable v
    have hv' := hvmeas.comp (measurable_fst : Measurable (Prod.fst : Tail p c × (ℝ × p.Ω) → Tail p c))
    have hx : Measurable (fun w : Tail p c × (ℝ × p.Ω) => x + w.2.1 • v w.1) :=
      measurable_const.add (measurable_snd.fst.smul hv')
    have hHv := isBoundedBilinearMap_apply.continuous.measurable.comp
      ((hH.comp (hx.prodMk measurable_snd.snd)).prodMk hv')
    exact (measurable_const (a := a)).smul (hHv.sub
      ((hG.continuous.measurable.comp (measurable_const.add hv')).sub measurable_const))
  have hmix := centered_mixture (U.prod P) (tailLaw p c).toMeasure F' hFm hα
    (fun t => (hscaled t).2.2.1)
    (fun t => (hscaled t).2.2.2.trans (mul_le_mul_of_nonneg_left
      (transport_bound_mono p hρ hσ hh (by linarith) (v t) (hv t)) (Real.rpow_nonneg ha α)))
    (fun t => (hscaled t).2.1)
  have hpj := tail_path_oracle_projection p c P
  have heq : (∫ z, F z ∂Q) = (∫ w, F' w ∂(tailLaw p c).toMeasure.prod (U.prod P)) := by
    rw [← hpj.map_eq]
    exact (integral_map hpj.measurable.aemeasurable hFm.aestronglyMeasurable).symm
  have heqp : (∫ z, ‖F z‖ ^ α ∂Q) =
      (∫ w, ‖F' w‖ ^ α ∂(tailLaw p c).toMeasure.prod (U.prod P)) := by
    rw [← hpj.map_eq]
    exact (integral_map hpj.measurable.aemeasurable (hFm.norm.pow_const α).aestronglyMeasurable).symm
  exact ⟨hpj.integrable_comp_of_integrable hmix.1, heq.trans hmix.2.1,
    hpj.integrable_comp_of_integrable hmix.2.2.1, heqp.trans_le hmix.2.2.2⟩

lemma sampleNoise_moment (p : Params) (c : Config) (P : Measure p.Ω)
    [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (state : State p) (hbound : HeavyTailedSospGeometry.PhaseBound p c.h state.phase) :
    let Q := (auxLaw p c).toMeasure.prod P
    let F := HeavyTailedSospEstimator.sampleNoise p c G g H state
    Integrable F Q ∧ (∫ z, F z ∂Q) = 0 ∧
      Integrable (fun z => ‖F z‖ ^ α) Q ∧
      (∫ z, ‖F z‖ ^ α ∂Q) ≤ HeavyTailedSospInvariants.transportCharge p state.phase *
        (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
          ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α)) := by
  intro Q F
  have hα0 : α ≠ 0 := by linarith
  have ha : 0 ≤ ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ := by positivity
  cases hp : state.phase with
  | transport v i z r =>
    have hv : ‖v‖ ≤ c.h := by
      simp only [hp, HeavyTailedSospGeometry.PhaseBound] at hbound
      exact hbound.1
    have hresult := tail_centered_transport_moment p c P G hG hD hρ hσ hh ha hα hα2
      hLip H hH hi hm hpi hb state.point (fun _ => v) (fun _ => hv)
    have heq : F = fun z : Aux p c × p.Ω => ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
        (H (state.point + z.1.1 • v) z.2 v - (G (state.point + v) - G state.point)) := by
      funext z
      simp [F, HeavyTailedSospEstimator.sampleNoise, HeavyTailedSospEstimator.noise, query, hp]
    rw [heq]
    simpa [Q, hp, HeavyTailedSospInvariants.transportCharge] using hresult
  | ncInit v =>
    have hv : ‖v‖ = 1 := by simpa [hp, HeavyTailedSospGeometry.PhaseBound] using hbound
    let dir : Tail p c → Space p := fun t => signedSegment p c (0, t) v
    have hdir (t : Tail p c) : ‖dir t‖ ≤ c.h := by
      rw [show dir t = signedSegment p c (0, t) v from rfl,
        HeavyTailedSospGeometry.signedSegment_bound p c (0, t) v hs hv]
      exact hseg
    have hresult := tail_centered_transport_moment p c P G hG hD hρ hσ hh ha hα hα2
      hLip H hH hi hm hpi hb state.point dir hdir
    have heq : F = fun z : Aux p c × p.Ω => ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
        (H (state.point + z.1.1 • dir z.1.2) z.2 (dir z.1.2) -
          (G (state.point + dir z.1.2) - G state.point)) := by
      funext z
      simp [F, dir, signedSegment, HeavyTailedSospEstimator.sampleNoise,
        HeavyTailedSospEstimator.noise, query, hp]
    rw [heq]
    simpa [Q, hp, HeavyTailedSospInvariants.transportCharge] using hresult
  | _ =>
    have heq : F = fun _ => 0 := by
      funext z
      simp [F, HeavyTailedSospEstimator.sampleNoise, HeavyTailedSospEstimator.noise, hp]
    rw [heq]
    simp [HeavyTailedSospInvariants.transportCharge, Real.zero_rpow hα0]

lemma primitive_stopped_moment (p : Params) (c : Config) (base ordinal : ℕ)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hd : 0 < p.d)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (n : ℕ) (s : HeavyTailedSospStopped.Monitor p)
    (hv : HeavyTailedSospInvariants.PhaseValid p c s.1.phase)
    (hbound : HeavyTailedSospGeometry.PhaseBound p c.h s.1.phase) :
    let Q := (auxLaw p c).toMeasure.prod P
    let Z := fun ξ => HeavyTailedFreshProcess.noiseSum
      (HeavyTailedSospStopped.step p c base ordinal g H)
      (HeavyTailedSospStopped.stoppedNoise p c base ordinal G g H) n s 0 ξ
    Integrable (fun ξ => ‖Z ξ‖ ^ α) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖Z ξ‖ ^ α ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        6 * HeavyTailedSospStopped.remaining p c base s *
          (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
            ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α)) := by
  intro Q Z
  have hmoment (state : State p) (hbnd : HeavyTailedSospGeometry.PhaseBound p c.h state.phase) :=
    sampleNoise_moment p c P G hG hD hρ hσ hh hs hseg hα hα2 hLip g H hH hi hm hpi hb state hbnd
  exact HeavyTailedSospStopped.stopped_moment p c base ordinal G g H Q
    hG.continuous.measurable hg hH hd hh hs hseg hα hα2 (by positivity)
    (fun state _ hbnd => (hmoment state hbnd).1)
    (fun state _ hbnd => (hmoment state hbnd).2.1)
    (fun state _ hbnd => (hmoment state hbnd).2.2.1)
    (fun state _ hbnd => (hmoment state hbnd).2.2.2) n s hv hbound

lemma primitive_endpoint_integral_bound (p : Params) (c : Config) (ordinal : ℕ)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hd : 0 < p.d)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hα : 1 < α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (n : ℕ) (s : State p)
    (hv : HeavyTailedSospInvariants.PhaseValid p c s.phase)
    (hbound : HeavyTailedSospGeometry.PhaseBound p c.h s.phase)
    (hz : HeavyTailedSospEstimator.ZeroPartial p s.phase)
    (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hsr : ¬ HeavyTailedSospEpoch.IsReset p s.phase)
    (halign : s.virtualIndex % max 1 c.epoch = 0) :
    let Q := (auxLaw p c).toMeasure.prod P
    let E := fun ξ => HeavyTailedSospStopped.endpointError p c s.virtualIndex G
      (HeavyTailedProductProcess.trajectory
        (HeavyTailedSospStopped.step p c s.virtualIndex ordinal g H) n (s, 0) ξ).1
    Integrable (fun ξ => ‖E ξ‖) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖E ξ‖ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        ‖HeavyTailedSospEstimator.error p c G s‖ +
        (6 * HeavyTailedSospStopped.remaining p c s.virtualIndex (s, 0) *
          (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
            ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α))) ^ (1 / α) := by
  intro Q E
  have hmom := primitive_stopped_moment p c s.virtualIndex ordinal P G hG hD hρ hσ hd
    hh hs hseg hα.le hα2 hLip g hg H hH hi hm hpi hb n (s, 0) hv hbound
  exact HeavyTailedSospStopped.endpoint_integral_bound p c ordinal G g H Q
    hG.continuous.measurable hg hH s hv hz ha hsr halign n hα hmom.1 hmom.2

end LongTails.Proofs.HeavyTailedSospNoise
