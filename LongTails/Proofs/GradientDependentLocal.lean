import LongTails.Proofs.GradientDependentCurvature
import LongTails.Proofs.GradientDependentEnergy
import LongTails.Proofs.CappedCubicModel
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Setups.GradientDependentHessian

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GradientDependentLocal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma local_models {f : E → ℝ} {g : E → E} {H : E → (E →L[ℝ] E)}
    {T : E → (E →L[ℝ] (E →L[ℝ] E))} {L₀ L₁ : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x, HasFDerivAt H (T x) x)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hT : ∀ x, ‖T x‖ ≤ L₀ + L₁ * ‖g x‖)
    (x s : E) (hcap : L₁ * ‖s‖ ^ 2 ≤ 4) :
    let A := L₀ + L₁ * (‖g x‖ + ‖g (x + s)‖)
    ‖H (x + s) - H x‖ ≤ 2 * A * ‖s‖ ∧
    ‖g (x + s) - g x - H x s‖ ≤ 2 * A * ‖s‖ ^ 2 ∧
    |f (x + s) - f x - ⟪g x, s⟫ - ⟪H x s, s⟫ / 2| ≤ 2 * A * ‖s‖ ^ 3 := by
  let G := ‖g x‖ + ‖g (x + s)‖
  let A := L₀ + L₁ * G
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => x + u • s) s t := by
    simpa using ((hasDerivAt_id t).smul_const s).const_add x
  have hvg (t : ℝ) : HasDerivAt (fun u : ℝ => g (x + u • s)) (H (x + t • s) s) t :=
    (hg _).comp_hasDerivAt t (hline t)
  have hvH (t : ℝ) : HasDerivAt (fun u : ℝ => H (x + u • s)) (T (x + t • s) s) t :=
    (hH _).comp_hasDerivAt t (hline t)
  have hvg' (t : ℝ) : HasDerivAt (fun u : ℝ => H (x + u • s) s)
      (T (x + t • s) s s) t := by
    simpa using (hvH t).clm_apply (hasDerivAt_const t s)
  have hTT (z : E) : ‖T z s s‖ ≤ ‖T z‖ * ‖s‖ ^ 2 := by
    calc
      _ ≤ ‖T z s‖ * ‖s‖ := (T z s).le_opNorm s
      _ ≤ (‖T z‖ * ‖s‖) * ‖s‖ :=
        mul_le_mul_of_nonneg_right ((T z).le_opNorm s) (norm_nonneg s)
      _ = _ := by ring
  have hgb := GradientDependentCurvature.gradient_dependent_segment_bound
    hvg hvg' hG hL₀ hL₁
    (by simp [G]) (by simp [G])
    (fun t _ => (hTT _).trans (by
      have h := mul_le_mul_of_nonneg_right (hT (x + t • s)) (sq_nonneg ‖s‖)
      nlinarith)) hcap
  have hcurv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖T (x + t • s)‖ ≤ 2 * A := by
    have hh := hT (x + t • s)
    have hb := mul_le_mul_of_nonneg_left (hgb t ht) hL₁
    have hc := mul_le_mul_of_nonneg_right hcap hL₀
    dsimp [A]
    nlinarith
  have hsecond (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖T (x + t • s) s s‖ ≤ 2 * A * ‖s‖ ^ 2 :=
    (hTT _).trans (mul_le_mul_of_nonneg_right (hcurv t ht) (sq_nonneg ‖s‖))
  have hhb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hvH t).hasDerivWithinAt)
    (fun t ht => ((T (x + t • s)).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right (hcurv t ⟨ht.1, ht.2.le⟩) (norm_nonneg s)))
  have hgr := GradientDependentCurvature.second_order_vector_remainder
    hvg hvg' (show 0 ≤ 2 * A * ‖s‖ ^ 2 by positivity) hsecond
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  have hff (t : ℝ) : HasDerivAt (fun u : ℝ => f (x + u • s)) ⟪g (x + t • s), s⟫ t :=
    (hf _).comp_hasDerivAt t (hline t)
  have hfr := GradientDependentCurvature.third_order_scalar_remainder s
    hff hvg hvg' (show 0 ≤ 2 * A * ‖s‖ ^ 2 by positivity) hsecond
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa [A, G] using hhb
  · simpa [A, G] using hgr
  · simpa [A, G, pow_succ, mul_assoc] using hfr

lemma step_estimates {f : E → ℝ} {g : E → E} {H : E → (E →L[ℝ] E)}
    {T : E → (E →L[ℝ] (E →L[ℝ] E))} {L₀ L₁ δ σ μ : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x, HasFDerivAt H (T x) x)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hT : ∀ x, ‖T x‖ ≤ L₀ + L₁ * ‖g x‖)
    (x s : E) (B : E →L[ℝ] E)
    (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hμ : 0 ≤ μ)
    (hcap : L₁ * ‖s‖ ^ 2 ≤ 1 / 10000)
    (htune : 100 * (L₀ + L₁ * ‖g x‖) ≤ σ)
    (herr : ‖H x - B‖ ≤ δ / 2)
    (hstat : g x + B s + (2 * δ + σ * ‖s‖ + μ) • s = 0)
    (hpsd : 0 ≤ ⟪s, B s + (2 * δ + σ * ‖s‖ + μ) • s⟫) :
    ‖g (x + s)‖ ≤ 4 * (σ * ‖s‖ ^ 2 + δ * ‖s‖ + μ * ‖s‖) ∧
    f (x + s) - f x ≤ -(σ * ‖s‖ ^ 3 + δ * ‖s‖ ^ 2 + μ * ‖s‖ ^ 2) / 3 := by
  obtain ⟨_, hgr, hfr⟩ := local_models hf hg hH hL₀ hL₁ hT x s
    (show L₁ * ‖s‖ ^ 2 ≤ 4 by linarith)
  have hlam : 0 ≤ 2 * δ + σ * ‖s‖ + μ := by positivity
  have he : ‖(H x - B) s‖ ≤ δ / 2 * ‖s‖ :=
    ((H x - B).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right herr (norm_nonneg s))
  have hgeq : g (x + s) = (g (x + s) - g x - H x s) + (H x - B) s -
      (2 * δ + σ * ‖s‖ + μ) • s := by
    calc
      _ = g (x + s) - (g x + B s + (2 * δ + σ * ‖s‖ + μ) • s) := by rw [hstat]; simp
      _ = _ := by simp only [sub_apply]; module
  have hgn := (norm_sub_le ((g (x + s) - g x - H x s) + (H x - B) s)
    ((2 * δ + σ * ‖s‖ + μ) • s)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [← hgeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hgn
  have hgrad : ‖g (x + s)‖ ≤ (5 * δ / 2 + μ) * ‖s‖ + σ * ‖s‖ ^ 2 +
      2 * (L₀ + L₁ * ‖g x‖ + L₁ * ‖g (x + s)‖) * ‖s‖ ^ 2 := by
    nlinarith
  have his := congrArg (fun v : E => ⟪v, s⟫) hstat
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at his
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hpsd
  have hbe : ⟪H x s, s⟫ - ⟪B s, s⟫ ≤ δ / 2 * ‖s‖ ^ 2 := by
    have hh := (real_inner_le_norm ((H x - B) s) s).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg s))
    simpa [sub_apply, inner_sub_left, pow_two, mul_assoc] using hh
  have hsym : ⟪s, B s⟫ = ⟪B s, s⟫ := real_inner_comm _ _
  have hchange : f (x + s) - f x ≤ -(3 * δ * ‖s‖ ^ 2 / 4) - σ * ‖s‖ ^ 3 / 2 -
      μ * ‖s‖ ^ 2 / 2 + 2 * (L₀ + L₁ * ‖g x‖ + L₁ * ‖g (x + s)‖) * ‖s‖ ^ 3 := by
    have hh := (abs_le.mp hfr).2
    nlinarith
  exact GradientDependentCurvature.capped_step_estimates (norm_nonneg s) hδ hσ hμ
    (norm_nonneg _) hcap htune hgrad hchange

lemma fresh_estimate {f : E → ℝ} {g : E → E} {H : E → (E →L[ℝ] E)}
    {T : E → (E →L[ℝ] (E →L[ℝ] E))} {L₀ L₁ σ μ : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x, HasFDerivAt H (T x) x)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hT : ∀ x, ‖T x‖ ≤ L₀ + L₁ * ‖g x‖)
    (x s : E) (hσ : 0 ≤ σ) (hμ : 0 ≤ μ)
    (hcap : L₁ * ‖s‖ ^ 2 ≤ 1 / 10000)
    (htune : 100 * (L₀ + L₁ * ‖g x‖) ≤ σ)
    (hstat : g x + H x s + (σ * ‖s‖ + μ) • s = 0) :
    ‖g (x + s)‖ ≤ 2 * σ * ‖s‖ ^ 2 + 2 * μ * ‖s‖ := by
  obtain ⟨_, hgr, _⟩ := local_models hf hg hH hL₀ hL₁ hT x s
    (show L₁ * ‖s‖ ^ 2 ≤ 4 by linarith)
  have hlam : 0 ≤ σ * ‖s‖ + μ := by positivity
  have hgeq : g (x + s) = (g (x + s) - g x - H x s) - (σ * ‖s‖ + μ) • s := by
    calc
      _ = g (x + s) - (g x + H x s + (σ * ‖s‖ + μ) • s) := by rw [hstat]; simp
      _ = _ := by module
  have hn := norm_sub_le (g (x + s) - g x - H x s) ((σ * ‖s‖ + μ) • s)
  rw [← hgeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hn
  apply GradientDependentEnergy.fresh_gradient_bound (norm_nonneg s) hσ hμ
    (norm_nonneg _) hcap htune
  nlinarith

lemma gradient_contDiff_two [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 (gradient f) := by
  have hh : ContDiff ℝ 2 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp hh

lemma derivative_chain [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
    (∀ x, HasFDerivAt f (innerSL ℝ (gradient f x)) x) ∧
    (∀ x, HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x) ∧
    (∀ x, HasFDerivAt (fderiv ℝ (gradient f))
      (fderiv ℝ (fderiv ℝ (gradient f)) x) x) := by
  have hg := gradient_contDiff_two hf
  have hH : ContDiff ℝ 1 (fderiv ℝ (gradient f)) :=
    (contDiff_succ_iff_fderiv.mp hg).2.2
  refine ⟨?_, fun x => (hg.differentiable (by norm_num) x).hasFDerivAt,
    fun x => (hH.differentiable (by norm_num) x).hasFDerivAt⟩
  intro x
  have hh := (hf.differentiable (by norm_num) x).hasFDerivAt
  rw [← toDual_gradient] at hh
  exact hh

end LongTails.Proofs.GradientDependentLocal
