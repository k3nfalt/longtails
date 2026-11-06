import LongTails.Proofs.PLMinimaxGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma regularized_monotonicity {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F}
    {L μ : ℝ}
    (hx : ∀ x x' y, f x y + ⟪gx x y, x' - x⟫ - L / 2 * ‖x' - x‖ ^ 2 ≤ f x' y)
    (hy : ∀ x y y', f x y' ≤ f x y + ⟪gy x y, y' - y⟫ - μ / 2 * ‖y' - y‖ ^ 2)
    (u u' z : E) (v v' : F) :
    L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
      ⟪(gx u v + (2 * L) • (u - z)) - (gx u' v' + (2 * L) • (u' - z)), u - u'⟫ -
        ⟪gy u v - gy u' v', v - v'⟫ := by
  have h1 := hx u u' v
  have h2 := hx u' u v'
  have h3 := hy u v v'
  have h4 := hy u' v' v
  have heu : u' - u = -(u - u') := by abel
  have hev : v' - v = -(v - v') := by abel
  rw [heu, inner_neg_right, norm_neg] at h1
  rw [hev, inner_neg_right, norm_neg] at h3
  have he : (gx u v + (2 * L) • (u - z)) - (gx u' v' + (2 * L) • (u' - z)) =
      (gx u v - gx u' v') + (2 * L) • (u - u') := by module
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_left]
  linarith

lemma weighted_center_stability {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    {u u' z z' : E} {v v' : F} {a a' : E} {b b' : F}
    (hmono : L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
      ⟪a - a', u - u'⟫ - ⟪b - b', v - v'⟫)
    (ha : a = (2 * L) • z) (ha' : a' = (2 * L) • z')
    (hb : ⟪b, v' - v⟫ ≤ 0) (hb' : ⟪b', v - v'⟫ ≤ 0) :
    ‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2 ≤ (4 + L / μ) * ‖z - z'‖ ^ 2 := by
  apply OracleTemplate.PLMinimax.lift_energy hL hμ (z - z') (u - u') (v - v')
  have hb0 : 0 ≤ ⟪b, v - v'⟫ := by
    have he : v' - v = -(v - v') := by abel
    rw [he, inner_neg_right] at hb
    linarith
  rw [ha, ha', ← smul_sub, real_inner_smul_left] at hmono
  simp only [inner_sub_left] at hmono ⊢
  linarith

lemma weighted_residual_stability {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    {u a : E} {v b : F}
    (henergy : L * ‖u‖ ^ 2 + μ * ‖v‖ ^ 2 ≤ ⟪a, u⟫ + ⟪b, v⟫) :
    L ^ 2 * ‖u‖ ^ 2 ≤ ‖a‖ ^ 2 + L / μ * ‖b‖ ^ 2 := by
  have ha := real_inner_le_norm a u
  have hb := real_inner_le_norm b v
  have hya : 2 * ‖a‖ * ‖u‖ ≤ L * ‖u‖ ^ 2 + ‖a‖ ^ 2 / L := by
    have hh : (2 * ‖a‖ * ‖u‖ - L * ‖u‖ ^ 2) * L ≤ ‖a‖ ^ 2 := by
      nlinarith [sq_nonneg (L * ‖u‖ - ‖a‖)]
    have hd := (le_div_iff₀ hL).mpr hh
    linarith
  have hyb : 2 * ‖b‖ * ‖v‖ ≤ μ * ‖v‖ ^ 2 + ‖b‖ ^ 2 / μ := by
    have hh : (2 * ‖b‖ * ‖v‖ - μ * ‖v‖ ^ 2) * μ ≤ ‖b‖ ^ 2 := by
      nlinarith [sq_nonneg (μ * ‖v‖ - ‖b‖)]
    have hd := (le_div_iff₀ hμ).mpr hh
    linarith
  have he : L * ‖u‖ ^ 2 ≤ ‖a‖ ^ 2 / L + ‖b‖ ^ 2 / μ := by
    nlinarith [mul_nonneg hμ.le (sq_nonneg ‖v‖)]
  have hm := mul_le_mul_of_nonneg_left he hL.le
  field_simp at hm ⊢
  nlinarith

end LongTails.Proofs.ConstrainedSaddleGeometry
