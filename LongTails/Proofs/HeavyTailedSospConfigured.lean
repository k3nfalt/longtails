import LongTails.Proofs.HeavyTailedSospTuning

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedSospConfigured

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Algorithms.HeavyTailedSospTuned
open HeavyTailedSospTuning HeavyTailedProductProcess HeavyTailedSospExecution
open HeavyTailedSospForecastIntegration HeavyTailedSospWork

lemma configured_expected_bounds (p : Params) (hvalid : spec.valid p)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ) (G : Space p → Space p)
    (hG : ∀ x, HasGradientAt f (G x) x) (hDG : Differentiable ℝ G)
    (hGLip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖)
    (hALip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ p.ρ * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hgi : ∀ x, Integrable (g x) P0)
    (hgm : ∀ x, (∫ ω, g x ω ∂P0) = G x)
    (hgpi : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ p.p) P0)
    (hgb : ∀ x, (∫ ω, ‖g x ω - G x‖ ^ p.p ∂P0) ≤ p.σg ^ p.p)
    (hi : ∀ x v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ x v, (∫ ω, H x ω v ∂P0) = fderiv ℝ G x v)
    (hpi : ∀ x v, Integrable (fun ω => ‖H x ω v - fderiv ℝ G x v‖ ^ p.p) P0)
    (hb : ∀ x v, (∫ ω, ‖H x ω v - fderiv ℝ G x v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p (config p) g H) N (initial p target) ξ).phase = .done) :
    let P := Measure.infinitePi fun _ : ℕ => (auxLaw p (config p) : Measure (Aux p (config p))).prod P0
    let X := fun n ξ => trajectory (sampleStep p (config p) g H) n (initial p target) ξ
    (∫ ξ, markedGradientTotal p (config p) G g H target N ξ ∂P) / (cycleCount p : ℝ) ≤ p.ε / 500 ∧
      (∫ ξ, ∑ n ∈ Finset.range N, (ncCharge p (X n ξ).phase : ℝ) ∂P) / (cycleCount p : ℝ) ≤
        stepSize p / (5 * ncLength p) := by
  intro P X
  rcases hvalid with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  have hcenterI : ∀ x, Integrable (fun ω => g x ω - G x) P0 :=
    fun x => (hgi x).sub (integrable_const _)
  have hcenterM : ∀ x, (∫ ω, g x ω - G x ∂P0) = 0 := by
    intro x
    rw [integral_sub (hgi x) (integrable_const _), hgm x, integral_const]
    simp
  have hv := validationBatch_bound p hp hρ hσh hε
  have hvalidation : 6 * p.σh ^ p.p / ((max 1 (config p).meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤
      ((config p).γ / 8) ^ p.p := by
    simpa only [config, max_eq_right (show 1 ≤ validationBatch p from hv.1)] using hv.2
  have hh := primitive_combined_expected_descent p (config p) g hg H hH P0 f G hG hDG hGLip hALip hgap
    hd hL.le hρ.le hσh hp hp2 (stepSize_pos p hL hρ hε).le (ncLength_pos p hρ hε).le
    (curvature_pos p hρ hε) (ncSegments_bounds p hL hρ hε).1
    (le_of_eq (rho_length p hρ)) hcenterI hcenterM hgpi hgb hi hm hpi hb hvalidation
    (errorScale p) (missRisk p / 2) (estimator_tuning p hp hp2 hL hρ hσg hσh hε)
    (validation_failure_bound p hL hρ hε) target N hdone
  apply configured_average_bounds p hp hL hρ hσg hσh hε _ _
  · apply integral_nonneg
    intro ξ
    unfold markedGradientTotal
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  · exact integral_nonneg (fun ξ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  · exact hh

lemma configured_detector_none_probability (p : Params) (hvalid : spec.valid p)
    (x : Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (Hmean : Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (hsym : Hmean.toLinearMap.IsSymmetric) (hbound : ‖Hmean‖ ≤ p.L)
    (hi : ∀ v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ v, (∫ ω, H x ω v ∂P0) = Hmean v)
    (hpi : ∀ v, Integrable (fun ω => ‖H x ω v - Hmean v‖ ^ p.p) P0)
    (hb : ∀ v, (∫ ω, ‖H x ω v - Hmean v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (w : Space p) (hw : ‖w‖ = 1) (hbad : inner ℝ w (Hmean w) ≤ -4 * curvature p) :
    (Measure.infinitePi fun _ : ℕ => (auxLaw p (config p) : Measure (Aux p (config p))).prod P0).real
      {ξ | HeavyTailedSospDetection.detectorChoice p (config p) H x ξ
        (max 1 (config p).repeats) = none} ≤ missRisk p := by
  rcases hvalid with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  have ht := spectral_tuning_bounds p hd hp hL hρ hσh hε
  have hv := validationBatch_bound p hp hρ hσh hε
  have hvalidation : 6 * p.σh ^ p.p / ((max 1 (config p).meanBatch : ℕ) : ℝ) ^ (p.p - 1) ≤
      ((config p).γ / 8) ^ p.p := by
    simpa only [config, max_eq_right (show 1 ≤ validationBatch p from hv.1)] using hv.2
  have hh := HeavyTailedSospDetectionIntegration.primitive_detector_none_probability p hd (config p)
    x (conjugate p) H Hmean hH P0 ht.1 (conjugate_holder p hp) hp2 ht.2.1
    (curvature_pos p hρ hε) hσh rfl hsym hbound hi hm hpi hb w hw hbad
    ht.2.2.2.1 ht.2.2.2.2.2 ht.2.2.2.2.1 hvalidation
  have h1 := repetition_failure_bound p hL hρ hε
  have h2 := validation_failure_bound p hL hρ hε
  exact hh.trans (by simp only [config]; linarith)

lemma configured_success_probability (p : Params) (hvalid : spec.valid p)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P0 : Measure p.Ω) [IsProbabilityMeasure P0]
    (f : Space p → ℝ)
    (hG : ∀ x, HasGradientAt f ((gradient f) x) x) (hDG : Differentiable ℝ (gradient f))
    (hGLip : ∀ x y, ‖(gradient f) x - (gradient f) y‖ ≤ p.L * ‖x - y‖)
    (hALip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hgi : ∀ x, Integrable (g x) P0)
    (hgm : ∀ x, (∫ ω, g x ω ∂P0) = (gradient f) x)
    (hgpi : ∀ x, Integrable (fun ω => ‖g x ω - (gradient f) x‖ ^ p.p) P0)
    (hgb : ∀ x, (∫ ω, ‖g x ω - (gradient f) x‖ ^ p.p ∂P0) ≤ p.σg ^ p.p)
    (hi : ∀ x v, Integrable (fun ω => H x ω v) P0)
    (hm : ∀ x v, (∫ ω, H x ω v ∂P0) = fderiv ℝ (gradient f) x v)
    (hpi : ∀ x v, Integrable (fun ω => ‖H x ω v - fderiv ℝ (gradient f) x v‖ ^ p.p) P0)
    (hb : ∀ x v, (∫ ω, ‖H x ω v - fderiv ℝ (gradient f) x v‖ ^ p.p ∂P0) ≤ p.σh ^ p.p * ‖v‖ ^ p.p)
    (C : ℕ) (hC : 0 < C)
    (hWC : 10 * ((2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) *
      (max 1 (resetBatch p) : ℕ) + 2 * cycleCount p * (max 1 (transportBatch p) : ℕ) +
        cycleCount p * (detectorCalls (config p) : ℝ)) ≤ C) :
    letI : NeZero (max 1 (config p).cycles) := ⟨by omega⟩
    2 / 3 ≤ ((PMF.uniformOfFintype (Fin (max 1 (config p).cycles))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => (auxLaw p (config p) : Measure (Aux p (config p))).prod P0)).real
      {z | secondOrderAccurate p f
        (trajectory (sampleStep p (config p) g H) C (initial p z.1.val) z.2).selected} := by
  let : NeZero (max 1 (config p).cycles) := ⟨by omega⟩
  have hv := hvalid
  rcases hv with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  let N := max 1 (config p).resetBatch + (config p).cycles * HeavyTailedSospCompletion.cycleWork (config p)
  have hdone : ∀ ξ, (trajectory (sampleStep p (config p) g H) N (initial p 0) ξ).phase = .done :=
    HeavyTailedSospCompletion.uncapped_completion p (config p) g H 0
  have ha := configured_expected_bounds p hvalid g hg H hH P0 f (gradient f) hG hDG hGLip hALip hgap
    hgi hgm hgpi hgb hi hm hpi hb 0 N hdone
  have hA : Continuous (fun x => fderiv ℝ (gradient f) x) :=
    (show LipschitzWith ⟨p.ρ, hρ.le⟩ (fun x => fderiv ℝ (gradient f) x) from
      LipschitzWith.of_dist_le_mul (fun x y => by
        change dist (fderiv ℝ (gradient f) x) (fderiv ℝ (gradient f) y) ≤ p.ρ * dist x y
        simpa only [dist_eq_norm] using hALip x y)).continuous
  have hmiss : ∀ x ∈ HeavyTailedSospDetectionIntegration.strictBadCurvature p
      (fun x => fderiv ℝ (gradient f) x) (-4 * (config p).γ),
      (Measure.infinitePi fun _ : ℕ => (auxLaw p (config p) : Measure (Aux p (config p))).prod P0).real
        {ξ | HeavyTailedSospDetection.detectorChoice p (config p) H x ξ
          (max 1 (config p).repeats) = none} ≤ missRisk p := by
    intro x hx
    obtain ⟨w, hw, hbad⟩ := hx
    exact configured_detector_none_probability p hvalid x H (fderiv ℝ (gradient f) x) hH P0
      (OracleTemplate.SpectralGradient.hessian_symmetric (fun y => (hG y).differentiableAt) hDG x)
      (HeavyTailedCurvatureGeometry.hessian_norm_bound hL.le hGLip x)
      (hi x) (hm x) (hpi x) (hb x) w hw hbad.le
  exact HeavyTailedSospConvergence.capped_success_from_aggregate_bounds p (config p) f hDG.continuous hA
    g hg H hH ((auxLaw p (config p) : Measure (Aux p (config p))).prod P0)
    hd hρ.le hε hALip (stepSize_pos p hL hρ hε).le (ncLength_pos p hρ hε)
    (stepSize_le_length p hL hρ hε) (ncSegments_bounds p hL hρ hε).1
    (ncSegments_bounds p hL hρ hε).2 (rho_stepSize_le_curvature p hL hρ hε)
    (curvature_accuracy p hρ hε) N C (cycleCount_pos p) hC
    (missRisk_pos p hL hρ hε).le (missRisk_le p hL hρ hε) hmiss hdone ha.1 ha.2 hWC

lemma configured_execute_success (p : Params) (hvalid : spec.valid p)
    (f : Space p → ℝ) (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (hadm : spec.admissible p f O) (C : ℕ) (hC : 0 < C)
    (hWC : 10 * ((2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) *
      (max 1 (resetBatch p) : ℕ) + 2 * cycleCount p * (max 1 (transportBatch p) : ℕ) +
        cycleCount p * (detectorCalls (config p) : ℝ)) ≤ C) :
    letI : NeZero (max 1 (config p).cycles) := ⟨by omega⟩
    spec.successful p f
      (fun w : (algorithm p (config p)).Seed × ((i : ℕ) → O.Seed i) =>
        OracleTemplate.execute O (algorithm p (config p)) (fun _ => C) w.1 w.2)
      ⟨((algorithm p (config p)).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let : NeZero (max 1 (config p).cycles) := ⟨by omega⟩
  rcases hadm with ⟨g, H, P0, P, hiid, hO, hG, hGLip, hDG, hALip, hlower,
    hg, hH, hgi, hgm, hgpi, hgb, hi, hm, hpi, hb⟩
  subst O
  have hspace : WithLp.measurableSpace 2 (Fin p.d → ℝ) =
      LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector p.d := by
    let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
    exact BorelSpace.measurable_eq
  rw [hspace] at hg hH
  obtain ⟨m, hmf, hgap⟩ := hlower
  have hgap' : ∀ x, f p.x0 - f x ≤ p.Δ := by intro x; linarith [hmf x]
  have hp := configured_success_probability p hvalid g hg H hH (P0 : Measure _) f hG hDG hGLip hALip
    hgap' hgi hgm hgpi hgb hi hm hpi hb C hC hWC
  have hρ : 0 ≤ p.ρ := hvalid.2.2.1.le
  have hA : Continuous (fun x => fderiv ℝ (gradient f) x) :=
    (show LipschitzWith ⟨p.ρ, hρ⟩ (fun x => fderiv ℝ (gradient f) x) from
      LipschitzWith.of_dist_le_mul (fun x y => by
        change dist (fderiv ℝ (gradient f) x) (fderiv ℝ (gradient f) y) ≤ p.ρ * dist x y
        simpa only [dist_eq_norm] using hALip x y)).continuous
  exact HeavyTailedSospConvergence.execute_success_of_paired_probability p (config p) f hDG.continuous hA
    g hg H hH P0 P hiid C hp

end LongTails.Proofs.HeavyTailedSospConfigured
