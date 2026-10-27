import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdaptiveCubicEnergy

lemma residual_absorption {κ Λ r δ : ℝ} (hκ : 0 < κ) (hΛ : κ ≤ Λ)
    (hr : 0 ≤ r) (hsq : Λ ^ 2 = κ ^ 2 + r ^ 2)
    (hquad : δ * κ ≤ r ^ 2) (hlin : δ ≤ r) :
    δ ≤ 3 * (Λ - κ) := by
  by_cases hsmall : Λ ≤ 2 * κ
  · have hprod : 0 ≤ (2 * κ - Λ) * (Λ - κ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hrΛ : r ≤ Λ := by nlinarith
    linarith

lemma scaled_residual_absorption {κ Λ r δ D : ℝ} (hκ : 0 < κ) (hΛ : κ ≤ Λ)
    (hr : 0 ≤ r) (hD : 0 < D) (hsq : Λ ^ 2 = κ ^ 2 + r ^ 2)
    (hquad : δ * κ ≤ D ^ 2 * r ^ 2) (hlin : δ ≤ D ^ 2 * r) :
    δ ≤ 3 * D ^ 2 * (Λ - κ) := by
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  have hq : (δ / D ^ 2) * κ ≤ r ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hDsq).mp
    field_simp
    exact hquad
  have hl : δ / D ^ 2 ≤ r := (div_le_iff₀ hDsq).2 (by nlinarith)
  have h := residual_absorption hκ hΛ hr hsq hq hl
  have hm := (div_le_iff₀ hDsq).mp h
  nlinarith

lemma quadratic_linear_absorption {κ Λ a c D r : ℝ} (hκ : 0 < κ) (hΛ : κ ≤ Λ)
    (hc : 0 < c) (hcκ : c ≤ κ) (hD : 0 < D)
    (hsq : (Λ ^ 2 - κ ^ 2) * (c * D ^ 2) = κ * a ^ 2 * r ^ 2) :
    min (a ^ 2 / c * r ^ 2) (a * D * r) ≤ 3 * D ^ 2 * (Λ - κ) := by
  let δ := min (a ^ 2 / c * r ^ 2) (a * D * r)
  have hq : δ * c ≤ a ^ 2 * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (a ^ 2 / c * r ^ 2) (a * D * r)) hc.le
    have he : a ^ 2 / c * r ^ 2 * c = a ^ 2 * r ^ 2 := by field_simp
    simpa only [he] using h
  have hl : δ ≤ a * D * r := min_le_right _ _
  by_cases hsmall : Λ ≤ 2 * κ
  · have hprod := mul_nonneg (show 0 ≤ 2 * κ - Λ by linarith) (sub_nonneg.mpr hΛ)
    have hqκ := mul_le_mul_of_nonneg_right hq hκ.le
    have hprod' := mul_nonneg (show 0 ≤ c * D ^ 2 by positivity) hprod
    have hh : c * κ * (δ - 3 * D ^ 2 * (Λ - κ)) ≤ 0 := by nlinarith
    have hpos : 0 < c * κ := mul_pos hc hκ
    dsimp only [δ] at hh
    nlinarith
  · have hneg := mul_nonneg (show 0 ≤ κ - c by linarith)
      (show 0 ≤ a ^ 2 * r ^ 2 by positivity)
    have hsqbound : (a * r) ^ 2 ≤ D ^ 2 * Λ ^ 2 := by
      have hp : 0 ≤ c * D ^ 2 * κ ^ 2 := by positivity
      nlinarith
    have har : a * r ≤ D * Λ := by
      have hDL : 0 ≤ D * Λ := mul_nonneg hD.le (hκ.le.trans hΛ)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left har hD.le
    have hlarge := mul_nonneg (sq_nonneg D) (show 0 ≤ 2 * Λ - 3 * κ by linarith)
    change δ ≤ _
    nlinarith

lemma adaptive_scale_energy {κ R Λ a c D r Enew Eprev V znoise vdist : ℝ}
    (hκ : 0 < κ) (hR : κ ≤ R) (hΛ : R ≤ Λ)
    (hc : 0 < c) (hcκ : c ≤ κ) (hD : 0 < D) (hdist : vdist ≤ D ^ 2)
    (hsq : (R ^ 2 - κ ^ 2) * (c * D ^ 2) = κ * a ^ 2 * r ^ 2)
    (henergy : Enew + V ≤ Eprev +
      min (a ^ 2 / c * r ^ 2) (a * D * r) + znoise) :
    Enew + (Λ - κ) / 2 * vdist + V ≤
      Eprev + (7 / 2) * D ^ 2 * (Λ - κ) + znoise := by
  have habs := quadratic_linear_absorption hκ hR hc hcκ hD hsq
  have hdiff : 0 ≤ Λ - κ := by linarith
  have hdist' := mul_le_mul_of_nonneg_left hdist (show 0 ≤ (Λ - κ) / 2 by positivity)
  have hmono := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 3 * D ^ 2 by positivity)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma optimistic_square {a c κ : ℝ} (hc : 0 < c) (hκ : c ≤ κ)
    (r h d : E) :
    2 * c * (a * ⟪r, h - d⟫ - c * ⟪h, h - d⟫ - κ / 2 * ‖d‖ ^ 2) ≤
      a ^ 2 * ‖r‖ ^ 2 - c ^ 2 * ‖h‖ ^ 2 := by
  have hs := sq_nonneg ‖a • r - c • (h - d)‖
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
    sq_abs, sq_abs, norm_sub_sq_real, inner_sub_right] at hs
  rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
  have hp := mul_nonneg (show 0 ≤ c * (κ - c) by positivity) (sq_nonneg ‖d‖)
  nlinarith

lemma optimistic_linear {a c κ D : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hκ : c ≤ κ)
    (r h d : E) (hD : ‖h - d‖ ≤ D) :
    a * ⟪r, h - d⟫ - c * ⟪h, h - d⟫ - κ / 2 * ‖d‖ ^ 2 ≤
      a * D * ‖r‖ - c / 2 * ‖h‖ ^ 2 := by
  have hi := real_inner_le_norm r (h - d)
  have hr := norm_nonneg r
  have hiD : a * ⟪r, h - d⟫ ≤ a * D * ‖r‖ := by
    calc
      a * ⟪r, h - d⟫ ≤ a * (‖r‖ * ‖h - d‖) := mul_le_mul_of_nonneg_left hi ha
      _ ≤ a * (‖r‖ * D) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hD hr) ha
      _ = a * D * ‖r‖ := by ring
  have hs := mul_nonneg hc.le (sq_nonneg ‖h - d‖)
  rw [norm_sub_sq_real] at hs
  rw [inner_sub_right h h d, real_inner_self_eq_norm_sq]
  have hp := mul_nonneg (show 0 ≤ κ - c by linarith) (sq_nonneg ‖d‖)
  nlinarith

end LongTails.Proofs.AdaptiveCubicEnergy
