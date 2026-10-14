import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.NearZeroSum

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma conjugate_bregman_lower {φ : E → F → ℝ} {r : E → ℝ} {ψ : F → ℝ}
    {x₁ x₂ z₁ z₂ : E} {y₁ y₂ w₁ : F} {a c : ℝ}
    (hx : φ x₂ y₂ + r x₂ + ⟪z₂, x₁ - x₂⟫ + a / 2 * ‖x₁ - x₂‖ ^ 2 ≤
      φ x₁ y₂ + r x₁)
    (hy : φ x₁ y₂ - ψ y₂ + ⟪w₁, y₂ - y₁⟫ + c / 2 * ‖y₂ - y₁‖ ^ 2 ≤
      φ x₁ y₁ - ψ y₁) :
    a / 2 * ‖x₂ - x₁‖ ^ 2 + c / 2 * ‖y₂ - y₁‖ ^ 2 ≤
      (⟪z₂, x₂⟫ - r x₂ - φ x₂ y₂ + ψ y₂) -
      (⟪z₁, x₁⟫ - r x₁ - φ x₁ y₁ + ψ y₁) -
      ⟪x₁, z₂ - z₁⟫ - ⟪w₁, y₂ - y₁⟫ := by
  rw [norm_sub_rev x₂ x₁]
  simp only [inner_sub_right] at hx hy ⊢
  have hz₂ : ⟪x₁, z₂⟫ = ⟪z₂, x₁⟫ := real_inner_comm _ _
  have hz₁ : ⟪x₁, z₁⟫ = ⟪z₁, x₁⟫ := real_inner_comm _ _
  rw [hz₂, hz₁]
  linarith

lemma shifted_lower_support {f : E → ℝ} {x y g : E} {M a : ℝ}
    (h : f x + ⟪g, y - x⟫ + M / 2 * ‖y - x‖ ^ 2 ≤ f y) :
    (f x - a / 2 * ‖x‖ ^ 2) + ⟪g - a • x, y - x⟫ +
      (M - a) / 2 * ‖y - x‖ ^ 2 ≤ f y - a / 2 * ‖y‖ ^ 2 := by
  have he : ‖y‖ ^ 2 - ‖x‖ ^ 2 - 2 * ⟪x, y - x⟫ = ‖y - x‖ ^ 2 := by
    simp only [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm y x]
    ring
  simp only [inner_sub_left, real_inner_smul_left]
  have he' := congrArg (fun t : ℝ => a * t) he
  nlinarith

lemma shifted_upper_support {f : E → ℝ} {x y g : E} {m b : ℝ}
    (h : f y ≤ f x + ⟪g, y - x⟫ - m / 2 * ‖y - x‖ ^ 2) :
    f y + b / 2 * ‖y‖ ^ 2 ≤ (f x + b / 2 * ‖x‖ ^ 2) +
      ⟪g + b • x, y - x⟫ - (m - b) / 2 * ‖y - x‖ ^ 2 := by
  have he : ‖y‖ ^ 2 - ‖x‖ ^ 2 - 2 * ⟪x, y - x⟫ = ‖y - x‖ ^ 2 := by
    simp only [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm y x]
    ring
  have he' := congrArg (fun t : ℝ => b * t) he
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith

noncomputable def fastValue (φ : E → F → ℝ) (q : F → ℝ) (a b : ℝ)
    (x z : E) (y : F) : ℝ :=
  ‖z‖ ^ 2 / (2 * a) + b / 2 * ‖y‖ ^ 2 + ⟪z, x⟫ - φ x y + 2 * q y

lemma fast_value_support {φ : E → F → ℝ} {q : F → ℝ}
    {x₁ x₂ z₁ z₂ : E} {y₁ y₂ w₁ dq : F} {a b c : ℝ} (ha : 0 < a)
    (hx : φ x₂ y₂ + ⟪z₂, x₁ - x₂⟫ + a / 2 * ‖x₁ - x₂‖ ^ 2 ≤ φ x₁ y₂)
    (hy : φ x₁ y₂ + ⟪w₁, y₂ - y₁⟫ + c / 2 * ‖y₂ - y₁‖ ^ 2 ≤ φ x₁ y₁)
    (hq : q y₁ + ⟪dq, y₂ - y₁⟫ ≤ q y₂) :
    fastValue φ q a b x₁ z₁ y₁ + ⟪x₁ + (1 / a) • z₁, z₂ - z₁⟫ +
      ⟪w₁ + b • y₁ + (2 : ℝ) • dq, y₂ - y₁⟫ +
      ‖z₂ - z₁‖ ^ 2 / (2 * a) + (b + c) / 2 * ‖y₂ - y₁‖ ^ 2 +
      a / 2 * ‖x₂ - x₁‖ ^ 2 ≤ fastValue φ q a b x₂ z₂ y₂ := by
  have hg := conjugate_bregman_lower (z₁ := z₁) (r := fun _ => 0) (ψ := fun _ => 0)
    (by simpa using hx) (by simpa using hy)
  have hz : ‖z₂‖ ^ 2 / (2 * a) - ‖z₁‖ ^ 2 / (2 * a) -
      ⟪(1 / a) • z₁, z₂ - z₁⟫ = ‖z₂ - z₁‖ ^ 2 / (2 * a) := by
    simp only [norm_sub_sq_real, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm z₂ z₁]
    field_simp
    ring
  have hyq : b / 2 * ‖y₂‖ ^ 2 - b / 2 * ‖y₁‖ ^ 2 -
      ⟪b • y₁, y₂ - y₁⟫ = b / 2 * ‖y₂ - y₁‖ ^ 2 := by
    simp only [norm_sub_sq_real, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm y₂ y₁]
    ring
  simp only [sub_zero] at hg
  dsimp [fastValue]
  simp only [inner_add_left, real_inner_smul_left] at hz hyq ⊢
  linarith

lemma fast_value_support_of_normal {φ : E → F → ℝ} {q : F → ℝ}
    {x₁ x₂ z₁ z₂ gx nx : E} {y₁ y₂ gy ny dq : F} {a b c : ℝ} (ha : 0 < a)
    (hx : φ x₂ y₂ + ⟪gx, x₁ - x₂⟫ + a / 2 * ‖x₁ - x₂‖ ^ 2 ≤ φ x₁ y₂)
    (hy : φ x₁ y₂ ≤ φ x₁ y₁ + ⟪gy, y₂ - y₁⟫ - c / 2 * ‖y₂ - y₁‖ ^ 2)
    (hnx : ⟪nx, x₁ - x₂⟫ ≤ 0) (hny : ⟪ny, y₂ - y₁⟫ ≤ 0)
    (hz : z₂ = gx + nx) (hq : q y₁ + ⟪dq, y₂ - y₁⟫ ≤ q y₂) :
    fastValue φ q a b x₁ z₁ y₁ + ⟪x₁ + (1 / a) • z₁, z₂ - z₁⟫ +
      ⟪-gy + ny + b • y₁ + (2 : ℝ) • dq, y₂ - y₁⟫ +
      ‖z₂ - z₁‖ ^ 2 / (2 * a) + (b + c) / 2 * ‖y₂ - y₁‖ ^ 2 +
      a / 2 * ‖x₂ - x₁‖ ^ 2 ≤ fastValue φ q a b x₂ z₂ y₂ := by
  apply fast_value_support ha (w₁ := -gy + ny) ?_ ?_ hq
  · rw [hz, inner_add_left]
    linarith
  · simp only [inner_add_left, inner_neg_left]
    linarith

lemma weighted_cross_bound {δ c X Y : ℝ} (hc : 0 < c) :
    4 * δ * X * Y ≤ c / 2 * Y ^ 2 + 8 * δ ^ 2 / c * X ^ 2 := by
  have heq : c / 2 * Y ^ 2 + 8 * δ ^ 2 / c * X ^ 2 - 4 * δ * X * Y =
      (c * Y - 4 * δ * X) ^ 2 / (2 * c) := by field_simp; ring
  have h : 0 ≤ (c * Y - 4 * δ * X) ^ 2 / (2 * c) := by positivity
  linarith

lemma coupling_error_absorption {a c α δ X Y V : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hsmall : 8 * δ ^ 2 ≤ a * α * c) :
    4 * δ * X * Y + 4 * δ * ((1 - α) / α) * X * V ≤
      a * X ^ 2 + c / 2 * Y ^ 2 + c / 2 * ((1 - α) / α) * V ^ 2 := by
  have ht : 0 ≤ (1 - α) / α := div_nonneg (by linarith) hα.le
  have h₁ := weighted_cross_bound (δ := δ) (X := X) (Y := Y) hc
  have h₂ := mul_le_mul_of_nonneg_left
    (weighted_cross_bound (δ := δ) (X := X) (Y := V) hc) ht
  have heq : 8 * δ ^ 2 / c + (1 - α) / α * (8 * δ ^ 2 / c) =
      8 * δ ^ 2 / (α * c) := by field_simp; ring
  have hcoef : 8 * δ ^ 2 / (α * c) ≤ a := by
    rw [div_le_iff₀ (mul_pos hα hc)]
    nlinarith [hsmall]
  have h₃ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg X)
  rw [← heq] at h₃
  nlinarith

lemma coupling_pairings_absorbed {a c α δ X : ℝ} {e u v : F}
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hsmall : 8 * δ ^ 2 ≤ a * α * c) (herr : ‖e‖ ≤ 2 * δ * X) :
    2 * ⟪e, u⟫ + 2 * ((1 - α) / α) * ⟪e, v⟫ ≤
      a * X ^ 2 + c / 2 * ‖u‖ ^ 2 + c / 2 * ((1 - α) / α) * ‖v‖ ^ 2 := by
  have ht : 0 ≤ (1 - α) / α := div_nonneg (sub_nonneg.mpr hα₁) hα.le
  have hu := (real_inner_le_norm e u).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg u))
  have hv := (real_inner_le_norm e v).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg v))
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * ((1 - α) / α) by positivity)
  have h := coupling_error_absorption (X := X) (Y := ‖u‖) (V := ‖v‖) hc hα hα₁ hsmall
  nlinarith

end OracleTemplate.NearZeroSum
