import LongTails.Proofs.SymmetricThirdOrderGeometry

namespace LongTails.Proofs.SymmetricThirdOrderSmoothness

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderGeometry
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma kernel_hessian_identity (B : E →L[ℝ] E) (L δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    fderiv ℝ (gradient (kernel B L δ)) = kernelHessian B L δ := by
  rw [kernel_gradient B L δ hsym]
  funext s
  exact (kernelGradient_hasFDerivAt B L δ s).fderiv

lemma kernelHessian_derivative_apply (B : E →L[ℝ] E) (L δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (s u v : E) :
    fderiv ℝ (kernelHessian B L δ) s u v =
      (16 * L) • (⟪s, u⟫ • v + ⟪u, v⟫ • s + ⟪s, v⟫ • u) := by
  have hdiff := (GradientDependentLocal.derivative_chain (kernel_contDiff B L δ)).2.2 s
  rw [kernel_hessian_identity B L δ hsym] at hdiff
  have ha := hdiff.clm_apply (hasFDerivAt_const v s)
  have hn := ((hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul (8 * L)).add_const δ
  have hi := (hasFDerivAt_id s).inner ℝ (hasFDerivAt_const v s)
  have hp := ((hasFDerivAt_const (B v) s).add (hn.smul_const v)).add
    ((hi.smul (hasFDerivAt_id s)).const_smul (16 * L))
  have he : (fun x : E => B v + (8 * L * ‖x‖ ^ 2 + δ) • v +
      (16 * L) • (⟪x, v⟫ • x)) = (fun x => kernelHessian B L δ x v) := by
    funext x
    simp [kernelHessian]
  change HasFDerivAt (fun x : E => B v + (8 * L * ‖x‖ ^ 2 + δ) • v +
    (16 * L) • (⟪x, v⟫ • x)) _ s at hp
  rw [he] at hp
  have hh := congrArg (fun A : E →L[ℝ] E => A u) (ha.unique hp)
  simp only [add_apply, zero_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, innerSL_apply_apply, id_eq] at hh
  simp at hh
  rw [hh]
  module

lemma kernel_third_lipschitz (B : E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L) (δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (s t : E) :
    ‖fderiv ℝ (kernelHessian B L δ) s - fderiv ℝ (kernelHessian B L δ) t‖ ≤
      48 * L * ‖s - t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (fderiv ℝ (kernelHessian B L δ) s -
      fderiv ℝ (kernelHessian B L δ) t) u v =
      (16 * L) • (⟪s - t, u⟫ • v + ⟪u, v⟫ • (s - t) + ⟪s - t, v⟫ • u) := by
    simp only [sub_apply, kernelHessian_derivative_apply B L δ hsym,
      inner_sub_left, sub_smul, smul_sub]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 16 * L)]
  have h₁ : ‖⟪s - t, u⟫ • v‖ ≤ ‖s - t‖ * ‖u‖ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
  have h₂ : ‖⟪u, v⟫ • (s - t)‖ ≤ ‖s - t‖ * ‖u‖ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm u v) (norm_nonneg (s - t))
    nlinarith
  have h₃ : ‖⟪s - t, v⟫ • u‖ ≤ ‖s - t‖ * ‖u‖ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm (s - t) v) (norm_nonneg u)
    nlinarith
  have hn := (norm_add_le (⟪s - t, u⟫ • v + ⟪u, v⟫ • (s - t)) (⟪s - t, v⟫ • u)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  have hh : ‖⟪s - t, u⟫ • v + ⟪u, v⟫ • (s - t) + ⟪s - t, v⟫ • u‖ ≤
      3 * (‖s - t‖ * ‖u‖ * ‖v‖) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 16 * L)
  nlinarith

lemma model_hessian_identity {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    fderiv ℝ (gradient (model f c B L δ)) =
      modelHessian (fderiv ℝ (gradient f)) c B L δ := by
  rw [model_gradient (hf.differentiable (by norm_num)) c B L δ hsym]
  funext s
  exact (modelGradient_hasFDerivAt
    ((GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num))
    c B L δ s).fderiv

lemma model_third_identity {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (s : E) :
    fderiv ℝ (modelHessian (fderiv ℝ (gradient f)) c B L δ) s =
      (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ (gradient f)) (c + s) +
        fderiv ℝ (fderiv ℝ (gradient f)) (c - s)) +
        fderiv ℝ (kernelHessian B L δ) s := by
  have hd := (GradientDependentLocal.derivative_chain hf).2.2
  have hp := (hd (c + s)).comp s ((hasFDerivAt_id s).const_add c)
  have hm := (hd (c - s)).comp s ((hasFDerivAt_id s).const_sub c)
  have hk := (GradientDependentLocal.derivative_chain (kernel_contDiff B L δ)).2.2 s
  rw [kernel_hessian_identity B L δ hsym] at hk
  have hh := ((hp.sub hm).const_smul (1 / 2 : ℝ)).add hk
  have he : HasFDerivAt (modelHessian (fderiv ℝ (gradient f)) c B L δ)
      ((1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ (gradient f)) (c + s) +
        fderiv ℝ (fderiv ℝ (gradient f)) (c - s)) +
        fderiv ℝ (kernelHessian B L δ) s) s := by
    convert hh using 1
    · rfl
    · ext u v
      simp
  exact he.fderiv

lemma model_third_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E) (δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (s t : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (model f c B L δ))) s -
      fderiv ℝ (fderiv ℝ (gradient (model f c B L δ))) t‖ ≤ 49 * L * ‖s - t‖ := by
  rw [model_hessian_identity hf c B L δ hsym,
    model_third_identity hf c B L δ hsym, model_third_identity hf c B L δ hsym]
  let T := fderiv ℝ (fderiv ℝ (gradient f))
  have hp : ‖T (c + s) - T (c + t)‖ ≤ L * ‖s - t‖ := by
    have hh := hT (c + s) (c + t)
    have he : c + s - (c + t) = s - t := by abel
    simpa only [he] using hh
  have hm : ‖T (c - s) - T (c - t)‖ ≤ L * ‖s - t‖ := by
    have hh := hT (c - s) (c - t)
    have he : c - s - (c - t) = t - s := by abel
    simpa only [he, norm_sub_rev t s] using hh
  have hk := kernel_third_lipschitz B hL δ hsym s t
  change ‖(1 / 2 : ℝ) • (T (c + s) + T (c - s)) + fderiv ℝ (kernelHessian B L δ) s -
    ((1 / 2 : ℝ) • (T (c + t) + T (c - t)) + fderiv ℝ (kernelHessian B L δ) t)‖ ≤ _
  have he : (1 / 2 : ℝ) • (T (c + s) + T (c - s)) + fderiv ℝ (kernelHessian B L δ) s -
      ((1 / 2 : ℝ) • (T (c + t) + T (c - t)) + fderiv ℝ (kernelHessian B L δ) t) =
      (1 / 2 : ℝ) • ((T (c + s) - T (c + t)) + (T (c - s) - T (c - t))) +
        (fderiv ℝ (kernelHessian B L δ) s - fderiv ℝ (kernelHessian B L δ) t) := by module
  rw [he]
  calc
    _ ≤ ‖(1 / 2 : ℝ) • ((T (c + s) - T (c + t)) + (T (c - s) - T (c - t)))‖ +
      ‖fderiv ℝ (kernelHessian B L δ) s - fderiv ℝ (kernelHessian B L δ) t‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (1 / 2) * (L * ‖s - t‖ + L * ‖s - t‖) + 48 * L * ‖s - t‖ := by
      have hs := ContinuousLinearMap.opNorm_smul_le (1 / 2 : ℝ)
        ((T (c + s) - T (c + t)) + (T (c - s) - T (c - t)))
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hs
      exact add_le_add (hs.trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add hp hm)) (by norm_num))) hk
    _ = _ := by ring

end LongTails.Proofs.SymmetricThirdOrderSmoothness
