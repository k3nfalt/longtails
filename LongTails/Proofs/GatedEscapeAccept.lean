import LongTails.Proofs.GatedEscapeDescent

namespace LongTails.Proofs.GatedEscapeAccept

open LongTails.Algorithms.GatedPerturbedEscape LongTails.Proofs.ComparisonTrustTaylor
  LongTails.Proofs.GatedEscapeDescent
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma onesided_bias {f : E → ℝ} {L ρ : ℝ} (hsm : Smooth f L ρ) (hρ : 0 ≤ ρ) (x w g0 : E)
    (hw : ‖w‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    |⟪w, gradient f (x + r • w) - g0⟫ / r - ⟪w, fderiv ℝ (gradient f) x w⟫| ≤
      ρ * r / 2 + ‖g0 - gradient f x‖ / r := by
  set H := fderiv ℝ (gradient f) x
  have ht := hsm.grad_taylor x (r • w)
  have hnw : ‖r • w‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]; nlinarith [norm_nonneg w]
  have hR : ‖gradient f (x + r • w) - gradient f x - H (r • w)‖ ≤ ρ * r ^ 2 / 2 :=
    ht.trans (by have := pow_le_pow_left₀ (norm_nonneg _) hnw 2; nlinarith)
  have hsplit : ⟪w, gradient f (x + r • w) - g0⟫ =
      ⟪w, gradient f (x + r • w) - gradient f x - H (r • w)⟫ + r * ⟪w, H w⟫ +
        ⟪w, gradient f x - g0⟫ := by
    rw [map_smul, inner_sub_right, inner_sub_right, inner_sub_right, inner_smul_right,
      inner_sub_right]
    ring
  have h1 : |⟪w, gradient f (x + r • w) - gradient f x - H (r • w)⟫| ≤ ρ * r ^ 2 / 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖w‖ * ‖gradient f (x + r • w) - gradient f x - H (r • w)‖
        ≤ 1 * (ρ * r ^ 2 / 2) := mul_le_mul hw hR (norm_nonneg _) zero_le_one
      _ = ρ * r ^ 2 / 2 := one_mul _
  have h2 : |⟪w, gradient f x - g0⟫| ≤ ‖g0 - gradient f x‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (g0 - gradient f x)]
  have heq : ⟪w, gradient f (x + r • w) - g0⟫ / r - ⟪w, H w⟫ =
      (⟪w, gradient f (x + r • w) - gradient f x - H (r • w)⟫ + ⟪w, gradient f x - g0⟫) / r := by
    rw [hsplit]; field_simp; ring
  rw [heq, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have := abs_add_le (⟪w, gradient f (x + r • w) - gradient f x - H (r • w)⟫) (⟪w, gradient f x - g0⟫)
  have e : (ρ * r / 2 + ‖g0 - gradient f x‖ / r) * r = ρ * r ^ 2 / 2 + ‖g0 - gradient f x‖ := by
    field_simp
    try ring
  rw [e]
  linarith

omit [FiniteDimensional ℝ E] in
lemma unit_of_ge {v : E} {r : ℝ} (hr : 0 < r) (hv : r / 2 ≤ ‖v‖) : ‖(1 / ‖v‖) • v‖ = 1 := by
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le (by linarith) hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_cancel₀ hv0.ne']

omit [FiniteDimensional ℝ E] in
lemma unit_le (v : E) : ‖(1 / ‖v‖) • v‖ ≤ 1 := by
  by_cases h : v = 0
  · simp [h]
  · have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_cancel₀ hv0.ne']

theorem accept_safe {f : E → ℝ} {L ρ : ℝ} (hsm : Smooth f L ρ) (hρ : 0 ≤ ρ) (x g0 v : E)
    {r θ τ0 τq qh : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) (hρr : ρ * r ≤ θ) (h3τ0 : 3 * τ0 ≤ r * θ / 8)
    (h3τq : 3 * τq ≤ 3 * θ / 8)
    (hA0 : ‖g0 - gradient f x‖ ≤ 3 * τ0)
    (hAq : |qh - ⟪(1 / ‖v‖) • v, gradient f (x + r • ((1 / ‖v‖) • v)) - g0⟫ / r| ≤ 3 * τq)
    (hv : r / 2 ≤ ‖v‖) (hqh : qh ≤ -2 * θ) :
    f (x + -(((if 0 ≤ ⟪g0, (1 / ‖v‖) • v⟫ then (1 : ℝ) else -1) * r) • ((1 / ‖v‖) • v))) ≤
      f x - r ^ 2 * θ / 5 := by
  set w := (1 / ‖v‖) • v with hwdef
  have hw : ‖w‖ = 1 := unit_of_ge hr hv
  have hb := onesided_bias hsm hρ x w g0 hw.le hr
  have hcurv : ⟪w, fderiv ℝ (gradient f) x w⟫ ≤ -θ := by
    have k1 := (abs_le.mp hb).1
    have k2 := (abs_le.mp hAq).1
    have k3 : ‖g0 - gradient f x‖ / r ≤ θ / 8 := by
      rw [div_le_iff₀ hr]; nlinarith
    nlinarith
  have hg0 : |⟪g0 - gradient f x, w⟫| ≤ r * θ / 8 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hw, mul_one]; linarith
  have hd := escape_decrease hsm x w g0 hw hr hθ hρr hcurv hg0
  have hx : x + -(((if 0 ≤ ⟪g0, w⟫ then (1 : ℝ) else -1) * r) • w) =
      x - ((if 0 ≤ ⟪g0, w⟫ then (1 : ℝ) else -1) * r) • w := by abel
  rw [hx]
  exact hd

theorem accept_ok {f : E → ℝ} {L ρ : ℝ} (hsm : Smooth f L ρ) (hρ : 0 ≤ ρ) (x g0 v : E)
    {r θ τ0 τq qh : ℝ} (hr : 0 < r) (hρr : ρ * r ≤ θ) (h3τ0 : 3 * τ0 ≤ r * θ / 8)
    (h3τq : 3 * τq ≤ 3 * θ / 8)
    (hA0 : ‖g0 - gradient f x‖ ≤ 3 * τ0)
    (hAq : |qh - ⟪(1 / ‖v‖) • v, gradient f (x + r • ((1 / ‖v‖) • v)) - g0⟫ / r| ≤ 3 * τq)
    (hv : r / 2 ≤ ‖v‖) (hneg : ⟪v, fderiv ℝ (gradient f) x v⟫ ≤ -3 * θ * ‖v‖ ^ 2) :
    qh ≤ -2 * θ := by
  set w := (1 / ‖v‖) • v with hwdef
  have hw : ‖w‖ = 1 := unit_of_ge hr hv
  have hb := onesided_bias hsm hρ x w g0 hw.le hr
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le (by linarith) hv
  have hRay : ⟪w, fderiv ℝ (gradient f) x w⟫ ≤ -3 * θ := by
    have e : ⟪w, fderiv ℝ (gradient f) x w⟫ = ⟪v, fderiv ℝ (gradient f) x v⟫ / ‖v‖ ^ 2 := by
      rw [hwdef, map_smul, inner_smul_left, inner_smul_right]
      simp only [RCLike.conj_to_real]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have k1 := (abs_le.mp hb).2
  have k2 := (abs_le.mp hAq).2
  have k3 : ‖g0 - gradient f x‖ / r ≤ θ / 8 := by
    rw [div_le_iff₀ hr]; nlinarith
  nlinarith

end LongTails.Proofs.GatedEscapeAccept
