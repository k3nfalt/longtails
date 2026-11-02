import LongTails.Proofs.ComparisonTrustDirection
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.GdConvex
import LongTails.Proofs.HessianLipschitzModel

namespace LongTails.Proofs.ComparisonTrustTaylor

open OracleTemplate LongTails.Proofs.ComparisonTrustDirection
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Smooth (f : E → ℝ) (L ρ : ℝ) : Prop where
  hf : ∀ x, HasFDerivAt f (innerSL ℝ (gradient f x)) x
  hg : ∀ x, HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
  hess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖
  sym : ∀ x, (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric

lemma Smooth.of_contDiff {f : E → ℝ} {L ρ : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hρ : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖) :
    Smooth f L ρ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hgr : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp hd
  refine ⟨fun x => ?_, fun x => (hgr.differentiable (by norm_num) x).hasFDerivAt, hL, hρ,
    fun x => OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf x⟩
  have hh := (hf.differentiable (by norm_num) x).hasFDerivAt
  rw [← toDual_gradient] at hh
  exact hh

variable {f : E → ℝ} {L ρ : ℝ}

lemma Smooth.hasGradientAt (h : Smooth f L ρ) (x : E) : HasGradientAt f (gradient f x) x := by
  have he : InnerProductSpace.toDual ℝ E (gradient f x) = innerSL ℝ (gradient f x) :=
    ContinuousLinearMap.ext fun v => by
      simp
  rw [hasGradientAt_iff_hasFDerivAt, he]
  exact h.hf x

lemma Smooth.hess_norm (h : Smooth f L ρ) (hL : 0 ≤ L) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ ≤ L :=
  (h.hg x).le_of_lip' hL (Filter.Eventually.of_forall fun y => h.lip y x)

lemma Smooth.value_taylor (h : Smooth f L ρ) (x d : E) :
    |f (x + d) - f x - ⟪gradient f x, d⟫ - ⟪d, fderiv ℝ (gradient f) x d⟫ / 2| ≤
      ρ * ‖d‖ ^ 3 / 6 :=
  CubicRegularization.objective_taylor h.hf h.hg h.hess x d

lemma Smooth.grad_taylor (h : Smooth f L ρ) (x d : E) :
    ‖gradient f (x + d) - gradient f x - fderiv ℝ (gradient f) x d‖ ≤ ρ * ‖d‖ ^ 2 / 2 :=
  CubicRegularization.gradient_taylor h.hg h.hess x d

lemma Smooth.symmetric_taylor (h : Smooth f L ρ) (x d : E) :
    |f (x + d) + f (x - d) - 2 * f x - ⟪d, fderiv ℝ (gradient f) x d⟫| ≤ ρ * ‖d‖ ^ 3 / 3 :=
  CubicRegularization.symmetric_taylor h.hf h.hg h.hess x d

lemma Smooth.antisymmetric (h : Smooth f L ρ) (y d : E) :
    |f (y + d) - f (y - d) - 2 * ⟪gradient f y, d⟫| ≤ ρ * ‖d‖ ^ 3 / 3 := by
  have h₁ := h.value_taylor y d
  have h₂ := h.value_taylor y (-d)
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg, norm_neg,
    ← sub_eq_add_neg] at h₂
  have := abs_le.mp h₁
  have := abs_le.mp h₂
  apply abs_le.mpr
  constructor <;> linarith

lemma Smooth.test_spec (h : Smooth f L ρ) (hρ : 0 ≤ ρ) {τ : ℝ} (hτ : 0 < τ) (y : E) :
    TestSpec (fun w => decide (f (y - τ • w) ≤ f (y + τ • w))) (gradient f y)
      (9 * ρ * τ ^ 2 / 2) := by
  intro w hw
  have hb := h.antisymmetric y (τ • w)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, inner_smul_right] at hb
  have hcube : ρ * (τ * ‖w‖) ^ 3 / 3 ≤ τ * (9 * ρ * τ ^ 2) := by
    have h3 : ‖w‖ ^ 3 ≤ 27 := by
      calc ‖w‖ ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (norm_nonneg w) hw 3
        _ = 27 := by norm_num
    have : ρ * (τ * ‖w‖) ^ 3 / 3 = ρ * τ ^ 3 * ‖w‖ ^ 3 / 3 := by ring
    rw [this]
    have : 0 ≤ ρ * τ ^ 3 := by positivity
    nlinarith
  have hb' := abs_le.mp hb
  constructor
  · intro ht
    have hle : f (y - τ • w) ≤ f (y + τ • w) := of_decide_eq_true ht
    have : -(τ * (9 * ρ * τ ^ 2)) ≤ 2 * (τ * ⟪gradient f y, w⟫) := by linarith
    have h2 : -(9 * ρ * τ ^ 2 / 2) * (2 * τ) ≤ ⟪gradient f y, w⟫ * (2 * τ) := by nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  · intro ht
    have hle : ¬ f (y - τ • w) ≤ f (y + τ • w) := of_decide_eq_false ht
    push Not at hle
    have : 2 * (τ * ⟪gradient f y, w⟫) ≤ τ * (9 * ρ * τ ^ 2) := by linarith
    have h2 : ⟪gradient f y, w⟫ * (2 * τ) ≤ (9 * ρ * τ ^ 2 / 2) * (2 * τ) := by nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)

lemma Smooth.grad_sq_bound (h : Smooth f L ρ) (hL : 0 < L) {x0 x : E} {Δ : ℝ}
    (hgap : ∀ z, f x0 - f z ≤ Δ) (hx : f x ≤ f x0) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * Δ := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound (oracle := gradient f) h.hasGradientAt h.lip x
    (x - L⁻¹ • gradient f x)
  have hz := hgap (x - L⁻¹ • gradient f x)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL] at hup
  have : L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 = ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
  have : L⁻¹ * ‖gradient f x‖ ^ 2 = 2 * (‖gradient f x‖ ^ 2 / (2 * L)) := by
    field_simp
  have hq : ‖gradient f x‖ ^ 2 / (2 * L) ≤ Δ := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at hq

end LongTails.Proofs.ComparisonTrustTaylor
