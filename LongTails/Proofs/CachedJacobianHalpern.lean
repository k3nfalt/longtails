import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CachedJacobianHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affine_vi_error {X : Set E} {A : E →L[ℝ] E} {b u y e : E} {μ : ℝ}
    (hu : u ∈ X) (hy : y ∈ X)
    (hA : ∀ x z, x ∈ X → z ∈ X → 0 ≤ ⟪A (x - z), x - z⟫)
    (huvi : ∀ z ∈ X, 0 ≤ ⟪b + A u + μ • u, z - u⟫)
    (hyvi : ∀ z ∈ X, 0 ≤ ⟪b + A y + μ • y + e, z - y⟫) :
    μ * ‖u - y‖ ≤ ‖e‖ := by
  have h₁ := huvi y hy
  have h₂ := hyvi u hu
  have h₃ := hA u y hu hy
  have hcs := real_inner_le_norm e (u - y)
  have hid : ⟪b + A u + μ • u, y - u⟫ +
      ⟪b + A y + μ • y + e, u - y⟫ =
      -⟪A (u - y), u - y⟫ - μ * ‖u - y‖ ^ 2 + ⟪e, u - y⟫ := by
    simp only [map_sub, inner_add_left, inner_sub_left, inner_sub_right,
      real_inner_smul_left, norm_sub_sq_real, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y u]
    ring
  have hquad : μ * ‖u - y‖ ^ 2 ≤ ‖e‖ * ‖u - y‖ := by linarith
  by_cases hzero : ‖u - y‖ = 0
  · simp [hzero]
  · have hp : 0 < ‖u - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

lemma potential_identity {a t : ℝ} (hden : t + 2 ≠ 0)
    {u up v vp anchor e : E}
    (he : u - up = -(2 / (t + 2)) • (up - anchor) -
      (a * (t + 3) / 3) • v + e) :
    2 * ((t + 1) * (t + 2) / 2) * ⟪v, u - anchor⟫ +
        (a * (t + 1) * (t + 2) * (t + 3) * (t + 4) / 12) * ‖v‖ ^ 2 -
      (2 * (t * (t + 1) / 2) * ⟪vp, up - anchor⟫ +
        (a * t * (t + 1) * (t + 2) * (t + 3) / 12) * ‖vp‖ ^ 2) =
      -(a * t * (t + 1) * (t + 2) * (t + 3) / 12) * ‖v - vp‖ ^ 2 -
      (t * (t + 1) * (t + 2) / 2) * ⟪v - vp, u - up⟫ +
      (t * (t + 1) * (t + 2) / 2) * ⟪v - vp, e⟫ +
      ((t + 1) * (t + 2)) * ⟪v, e⟫ := by
  have he' : e = u - up + (2 / (t + 2)) • (up - anchor) +
      (a * (t + 3) / 3) • v := by
    rw [he]
    module
  rw [he']
  simp only [inner_add_right, inner_sub_right, inner_sub_left, real_inner_smul_right,
    norm_sub_sq_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm vp v]
  field_simp
  ring

lemma energy_cross_bound {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) (w e : E) :
    -C * ‖w‖ ^ 2 + (2 * C / η) * ⟪w, e⟫ ≤ (2 * C / η ^ 2) * ‖e‖ ^ 2 := by
  have hcs := mul_le_mul_of_nonneg_left (real_inner_le_norm w e)
    (show 0 ≤ 2 * C / η by positivity)
  have hs := mul_nonneg hC (sq_nonneg (‖w‖ - (2 / η) * ‖e‖))
  have heq : C * (‖w‖ - (2 / η) * ‖e‖) ^ 2 =
      C * ‖w‖ ^ 2 - (4 * C / η) * ‖w‖ * ‖e‖ +
        (4 * C / η ^ 2) * ‖e‖ ^ 2 := by ring
  rw [heq] at hs
  have hw := mul_nonneg hC (sq_nonneg ‖w‖)
  ring_nf at hcs hs ⊢
  linarith

lemma energy_step_bound {P Pprev C K B η : ℝ} {v vp u up e : E}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hB : 0 ≤ B) (hη : 0 < η)
    (hmono : 0 ≤ ⟪v - vp, u - up⟫)
    (hid : P - Pprev = -C * ‖v - vp‖ ^ 2 - K * ⟪v - vp, u - up⟫ +
      (2 * C / η) * ⟪v - vp, e⟫ + 2 * B * ⟪v, e⟫) :
    P ≤ Pprev + (2 * C / η ^ 2) * ‖e‖ ^ 2 + 2 * B * ‖v‖ * ‖e‖ := by
  have hcross := energy_cross_bound hC hη (v - vp) e
  have hm := mul_nonneg hK hmono
  have he := mul_le_mul_of_nonneg_left (real_inner_le_norm v e)
    (show 0 ≤ 2 * B by positivity)
  linarith

lemma potential_lower_bound {a B C D : ℝ} {v z : E}
    (ha : 0 < a) (hB : 0 ≤ B) (hz : ‖z‖ ≤ D) (hC : a * B ^ 2 ≤ 3 * C) :
    (a * B * ‖v‖) ^ 2 - 6 * D * (a * B * ‖v‖) ≤
      3 * a * (2 * B * ⟪v, z⟫ + C * ‖v‖ ^ 2) := by
  have hcs : -‖v‖ * D ≤ ⟪v, z⟫ := by
    have h := real_inner_le_norm v (-z)
    rw [inner_neg_right, norm_neg] at h
    have hh := mul_le_mul_of_nonneg_left hz (norm_nonneg v)
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 6 * a * B by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hC (show 0 ≤ a * ‖v‖ ^ 2 by positivity)
  nlinarith

lemma prefix_quadratic_bound {D W : ℝ} (hD : 0 ≤ D) (hW : 0 ≤ W)
    (h : W ^ 2 ≤ 12 * D * W + 18 * D ^ 2) : W ≤ 20 * D := by
  nlinarith [sq_nonneg (W - 20 * D)]

end LongTails.Proofs.CachedJacobianHalpern
