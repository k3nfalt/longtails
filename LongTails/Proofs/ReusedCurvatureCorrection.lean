import LongTails.Proofs.CubicRegularization

namespace LongTails.Proofs.ReusedCurvatureCorrection

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma corrected_gradient {g : E → E} {A : E → E →L[ℝ] E} {H κ : ℝ}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (B : E →L[ℝ] E) (x s : E) (hs : B s = g x)
    (herror : ‖B - A x‖ ≤ κ) :
    ‖g (x - s)‖ ≤ κ * ‖s‖ + H * ‖s‖ ^ 2 / 2 := by
  have ht := CubicRegularization.gradient_taylor hg hLip x (-s)
  simp only [map_neg, norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at ht
  have he : g (x - s) = (B - A x) s + (g (x - s) - g x + A x s) := by
    rw [sub_apply, hs]
    abel
  calc
    _ ≤ ‖(B - A x) s‖ + ‖g (x - s) - g x + A x s‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ κ * ‖s‖ + H * ‖s‖ ^ 2 / 2 := add_le_add
      (((B - A x).le_opNorm s).trans (mul_le_mul_of_nonneg_right herror (norm_nonneg _))) ht

lemma correction_descent {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E} {H δ : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (B : E →L[ℝ] E) (x s : E) (hs : B s = g x)
    (hB : δ * ‖s‖ ^ 2 ≤ ⟪s, B s⟫)
    (hupper : ⟪s, A x s⟫ ≤ ⟪s, B s⟫ - δ * ‖s‖ ^ 2)
    (hδ : 0 ≤ δ) (hsmall : H * ‖s‖ ≤ δ) :
    f (x - s) ≤ f x - δ / 2 * ‖s‖ ^ 2 := by
  have ht := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip x (-s))).2
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg, norm_neg,
    ← sub_eq_add_neg, sub_neg_eq_add] at ht
  rw [← hs] at ht
  have he : ⟪B s, s⟫ = ⟪s, B s⟫ := real_inner_comm _ _
  rw [he] at ht
  have hr := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖s‖)
  have hn := mul_nonneg hδ (sq_nonneg ‖s‖)
  nlinarith

lemma negative_curvature_descent {f : E → ℝ} {g : E → E}
    {A : E → E →L[ℝ] E} {H γ t : ℝ}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (x v : E) (hv : ‖v‖ = 1) (ht : 0 ≤ t)
    (hsign : ⟪g x, v⟫ ≤ 0) (hcurvature : ⟪v, A x v⟫ ≤ -γ)
    (hstep : H * t ≤ γ) :
    f (x + t • v) ≤ f x - γ * t ^ 2 / 3 := by
  have h := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip x (t • v))).2
  simp only [map_smul, inner_smul_right, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hv, mul_one] at h
  have h₁ := mul_nonpos_of_nonneg_of_nonpos ht hsign
  have h₂ := mul_le_mul_of_nonneg_left hcurvature (sq_nonneg t)
  have h₃ := mul_le_mul_of_nonneg_right hstep (sq_nonneg t)
  nlinarith

lemma correction_scale_bound {H γ τ t s ε : ℝ}
    (hH : 0 ≤ H) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) (ht : 1 ≤ t) (hs : 0 ≤ s)
    (hstep : t ^ 2 * s ≤ 3 * τ) (hlocal : H * τ ≤ γ / 16)
    (haccuracy : γ * τ ≤ ε / 32) :
    6 * (t ^ 2 * γ) * s + H * s ^ 2 / 2 ≤ ε ∧ H * s ≤ t ^ 2 * γ := by
  have ht₂ : 1 ≤ t ^ 2 := by nlinarith
  have hs₁ : s ≤ 3 * τ := by nlinarith
  have hlin := mul_le_mul_of_nonneg_left hstep hγ
  have hs₂ := pow_le_pow_left₀ hs hs₁ 2
  have hquad := mul_le_mul_of_nonneg_left hs₂ hH
  have hlocal₂ := mul_le_mul_of_nonneg_right hlocal hτ
  have hHstep := mul_le_mul_of_nonneg_left hs₁ hH
  have hγt := mul_le_mul_of_nonneg_right ht₂ hγ
  constructor <;> nlinarith

end LongTails.Proofs.ReusedCurvatureCorrection
