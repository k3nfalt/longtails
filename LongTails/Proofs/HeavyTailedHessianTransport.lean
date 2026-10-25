import LongTails.Proofs.WeakGradientSegments
import LongTails.Proofs.HeavyTailedMomentBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory Set

namespace LongTails.Proofs.HeavyTailedHessianTransport

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma derivative_segment_integral {g : E → E} (hg : Differentiable ℝ g)
    (hD : Continuous (fderiv ℝ g)) (x v : E) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ g (x + t • v) v) = g (x + v) - g x := by
  have hc (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => g (x + s • v))
      (fderiv ℝ g (x + t • v) v) t :=
    (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hcont : Continuous (fun t : ℝ => fderiv ℝ g (x + t • v) v) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)
  simpa using hint

omit [CompleteSpace E] in
lemma segment_action_difference {D : E → E →L[ℝ] E} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hD : ∀ x y, ‖D x - D y‖ ≤ ρ * ‖x - y‖)
    (x v : E) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖D (x + t • v) v - D (x + s • v) v‖ ≤ ρ * ‖v‖ ^ 2 := by
  have heq : x + t • v - (x + s • v) = (t - s) • v := by rw [sub_smul]; abel
  have hdist : ‖x + t • v - (x + s • v)‖ ≤ ‖v‖ := by
    rw [heq, norm_smul, Real.norm_eq_abs]
    have hab : |t - s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
    simpa using mul_le_mul_of_nonneg_right hab (norm_nonneg v)
  have hnorm := (D (x + t • v) - D (x + s • v)).le_opNorm v
  simp only [sub_apply] at hnorm
  have hbound := (hD (x + t • v) (x + s • v)).trans
    (mul_le_mul_of_nonneg_left hdist hρ)
  have hmul := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
  nlinarith

lemma segment_centered_action_bound {g : E → E} (hg : Differentiable ℝ g)
    (hD : Continuous (fderiv ℝ g)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hLip : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ ρ * ‖x - y‖)
    (x v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ g (x + t • v) v - (g (x + v) - g x)‖ ≤ ρ * ‖v‖ ^ 2 := by
  have hcont : Continuous (fun s : ℝ => fderiv ℝ g (x + s • v) v) := by fun_prop
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun s => fderiv ℝ g (x + t • v) v - fderiv ℝ g (x + s • v) v)
    (C := ρ * ‖v‖ ^ 2) (fun s hs =>
      segment_action_difference hρ hLip x v
        (by simpa using Ioc_subset_Icc_self hs) ht)
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable 0 1),
    intervalIntegral.integral_const, derivative_segment_integral hg hD] at hbound
  simpa using hbound

end Calculus

section Mixture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
lemma mixture_centered_moment {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : Ξ × Ω → E} {m : Ξ → E} (z : E) {p R σ : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hF : Measurable F)
    (hpoint : ∀ᵐ t ∂Q, Integrable (fun ω => F (t, ω)) P ∧
      (∫ ω, F (t, ω) ∂P) = m t ∧
      Integrable (fun ω => ‖F (t, ω) - m t‖ ^ p) P ∧
      (∫ ω, ‖F (t, ω) - m t‖ ^ p ∂P) ≤ σ ^ p ∧ ‖m t - z‖ ≤ R) :
    Integrable (fun w => ‖F w - z‖ ^ p) (Q.prod P) ∧
      (∫ w, ‖F w - z‖ ^ p ∂Q.prod P) ≤ R ^ p + 6 * σ ^ p := by
  have hfiber : ∀ᵐ t ∂Q, Integrable (fun ω => ‖F (t, ω) - z‖ ^ p) P ∧
      (∫ ω, ‖F (t, ω) - z‖ ^ p ∂P) ≤ R ^ p + 6 * σ ^ p := by
    filter_upwards [hpoint] with t ht
    rcases ht with ⟨hi, hm, hpi, hpb, hnorm⟩
    have he : Integrable (fun ω => F (t, ω) - m t) P := hi.sub (integrable_const _)
    have hem : (∫ ω, F (t, ω) - m t ∂P) = 0 := by
      rw [integral_sub hi (integrable_const _), hm, integral_const]
      simp
    have hbound := HeavyTailedMomentBounds.integral_norm_add_rpow_le
      (w := m t - z) hp hp2 he hpi hem
    have hint := HeavyTailedMomentBounds.integrable_norm_add_rpow (m t - z)
      (by linarith : 0 < p) he.aestronglyMeasurable hpi
    have heq (ω : Ω) : m t - z + (F (t, ω) - m t) = F (t, ω) - z := by abel
    simp_rw [heq] at hbound hint
    refine ⟨hint, ?_⟩
    have hr := Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith : 0 ≤ p)
    linarith
  have hmeas : Measurable (fun w => ‖F w - z‖ ^ p) := (hF.sub_const z).norm.pow_const p
  have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hmeas.stronglyMeasurable (fun w => Real.rpow_nonneg (norm_nonneg _) _)
    (hfiber.mono fun _ ht => ht.1) (integrable_const (R ^ p + 6 * σ ^ p))
    (hfiber.mono fun _ ht => ht.2)
  simpa using hcontrol


omit [CompleteSpace E] in
lemma mixture_mean_of_centered_moment {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : Ξ × Ω → E} {m : Ξ → E} (z : E) {p : ℝ}
    (hp : 1 ≤ p) (hF : Measurable F)
    (hpi : Integrable (fun w => ‖F w - z‖ ^ p) (Q.prod P))
    (hm : ∀ᵐ t ∂Q, (∫ ω, F (t, ω) ∂P) = m t) :
    Integrable F (Q.prod P) ∧ (∫ w, F w ∂Q.prod P) = ∫ t, m t ∂Q := by
  have he : Integrable (fun w => F w - z) (Q.prod P) := by
    apply (integrable_norm_iff (hF.sub_const z).aestronglyMeasurable).mp
    have hh := integrable_norm_rpow_of_le (hF.sub_const z).aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ p) hp hpi
    simpa using hh
  have hi : Integrable F (Q.prod P) := by
    convert he.add (integrable_const z) using 1
    funext w
    exact (sub_add_cancel (F w) z).symm
  refine ⟨hi, ?_⟩
  rw [integral_prod F hi]
  exact integral_congr_ae hm


lemma random_path_transport {P : Measure Ω} [IsProbabilityMeasure P]
    {g : E → E} (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    {ρ σ p : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ ρ * ‖x - y‖)
    (H : E → Ω → E →L[ℝ] E) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ g y v‖ ^ p) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ g y v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (x v : E) :
    let Q := (volume.restrict (Ioc (0 : ℝ) 1)).prod P
    let F := fun w : ℝ × Ω => H (x + w.1 • v) w.2 v
    Integrable F Q ∧ (∫ w, F w ∂Q) = g (x + v) - g x ∧
      Integrable (fun w => ‖F w - (g (x + v) - g x)‖ ^ p) Q ∧
      (∫ w, ‖F w - (g (x + v) - g x)‖ ^ p ∂Q) ≤
        (ρ * ‖v‖ ^ 2) ^ p + 6 * σ ^ p * ‖v‖ ^ p := by
  intro Q F
  let U : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  have hF : Measurable F := by
    have hx : Measurable (fun w : ℝ × Ω => x + w.1 • v) :=
      measurable_const.add (measurable_fst.smul_const v)
    exact (hH.comp (hx.prodMk measurable_snd)).apply_continuousLinearMap v
  have hpoint : ∀ᵐ t ∂U, Integrable (fun ω => F (t, ω)) P ∧
      (∫ ω, F (t, ω) ∂P) = fderiv ℝ g (x + t • v) v ∧
      Integrable (fun ω => ‖F (t, ω) - fderiv ℝ g (x + t • v) v‖ ^ p) P ∧
      (∫ ω, ‖F (t, ω) - fderiv ℝ g (x + t • v) v‖ ^ p ∂P) ≤ (σ * ‖v‖) ^ p ∧
      ‖fderiv ℝ g (x + t • v) v - (g (x + v) - g x)‖ ≤ ρ * ‖v‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp only [F]
    refine ⟨hi (x + t • v) v, hm (x + t • v) v, hpi (x + t • v) v, ?_, ?_⟩
    · simpa only [Real.mul_rpow hσ (norm_nonneg v)] using hb (x + t • v) v
    · exact segment_centered_action_bound hg hD hρ hLip x v (Ioc_subset_Icc_self ht)
  have hmoment := mixture_centered_moment (g (x + v) - g x) hp hp2 hF hpoint
  have hmean := mixture_mean_of_centered_moment (g (x + v) - g x) hp hF hmoment.1
    (hpoint.mono fun _ ht => ht.2.1)
  refine ⟨hmean.1, ?_, hmoment.1, ?_⟩
  · rw [hmean.2]
    exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm.trans
      (derivative_segment_integral hg hD x v)
  · simpa only [Real.mul_rpow hσ (norm_nonneg v), mul_assoc] using hmoment.2

end Mixture

end LongTails.Proofs.HeavyTailedHessianTransport
