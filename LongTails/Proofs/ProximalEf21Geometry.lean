import Mathlib

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def modelDecrease (ψ : E → ℝ) (τ : ℝ) (x m z : E) : ℝ :=
  ψ x - ψ z - ⟪m, z - x⟫_ℝ - ‖z - x‖ ^ 2 / (2 * τ)

noncomputable def functionalEnergy (F ψ : E → ℝ)
    (μ τ : ℝ) (xstar x m z : E) : ℝ :=
  F x + ψ x - (F xstar + ψ xstar) -
    (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8 +
    modelDecrease ψ τ x m z / (μ * τ)

lemma inner_self_eq (u : E) : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq u

lemma square_add (u v : E) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
  rw [← inner_self_eq, inner_add_left, inner_add_right, inner_add_right]
  rw [inner_self_eq, inner_self_eq, real_inner_comm v u]
  ring

lemma square_sub (u v : E) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := by
  rw [← inner_self_eq, inner_sub_left, inner_sub_right, inner_sub_right]
  rw [inner_self_eq, inner_self_eq, real_inner_comm v u]
  ring

lemma square_smul (a : ℝ) (u : E) :
    ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

lemma square_add_smul (u v : E) (a : ℝ) :
    ‖u + a • v‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * a * ⟪u, v⟫_ℝ + a ^ 2 * ‖v‖ ^ 2 := by
  rw [square_add, square_smul, real_inner_smul_right]
  ring

lemma square_sub_smul (u v : E) (a : ℝ) :
    ‖u - a • v‖ ^ 2 =
      ‖u‖ ^ 2 - 2 * a * ⟪u, v⟫_ℝ + a ^ 2 * ‖v‖ ^ 2 := by
  rw [square_sub, square_smul, real_inner_smul_right]
  ring

lemma twice_inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    2 * ⟪u, v⟫_ℝ ≤ a * ‖u‖ ^ 2 + a⁻¹ * ‖v‖ ^ 2 := by
  have h := sq_nonneg ‖a • u - v‖
  rw [square_sub, square_smul, real_inner_smul_left] at h
  simp at h
  apply (mul_le_mul_left ha).mp
  rw [mul_add, ← mul_assoc a a⁻¹, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  nlinarith [h]

lemma inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    ⟪u, v⟫_ℝ ≤ a / 2 * ‖u‖ ^ 2 + 1 / (2 * a) * ‖v‖ ^ 2 := by
  have h := twice_inner_young a ha u v
  have heq : (1 : ℝ) / (2 * a) = a⁻¹ / 2 := by ring
  rw [heq]
  linarith

lemma neg_inner_young (a : ℝ) (ha : 0 < a) (u v : E) :
    -⟪u, v⟫_ℝ ≤ a / 2 * ‖u‖ ^ 2 + 1 / (2 * a) * ‖v‖ ^ 2 := by
  simpa only [inner_neg_right, norm_neg] using inner_young a ha u (-v)

lemma square_two (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := twice_inner_young 1 (by norm_num) u v
  norm_num at h
  rw [square_add]
  linarith

lemma square_three (u v w : E) :
    ‖u + v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have huv := twice_inner_young 1 (by norm_num) u v
  have huw := twice_inner_young 1 (by norm_num) u w
  have hvw := twice_inner_young 1 (by norm_num) v w
  norm_num at huv huw hvw
  rw [square_add, square_add, inner_add_left]
  linarith

lemma square_convex_combination (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (u v : E) :
    ‖(1 - a) • u + a • v‖ ^ 2 ≤ (1 - a) * ‖u‖ ^ 2 + a * ‖v‖ ^ 2 := by
  have h := sq_nonneg ‖u - v‖
  rw [square_sub] at h
  have hc : 0 ≤ a * (1 - a) := mul_nonneg ha (sub_nonneg.mpr ha1)
  have hmul := mul_nonneg hc h
  rw [square_add, square_smul, square_smul, real_inner_smul_left, real_inner_smul_right]
  simp
  nlinarith [hmul]

lemma complete_model_square (ψ : E → ℝ) {τ : ℝ} (hτ : τ ≠ 0)
    (x m z : E) :
    ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) =
      ψ z + ‖z - (x - τ • m)‖ ^ 2 / (2 * τ) - τ / 2 * ‖m‖ ^ 2 := by
  have hz : z - (x - τ • m) = (z - x) + τ • m := by abel
  rw [hz, square_add_smul, real_inner_comm (z - x) m]
  field_simp [hτ]
  <;> ring

lemma modelDecrease_completed_square (ψ : E → ℝ) {τ : ℝ}
    (hτ : τ ≠ 0) (x m z : E) :
    modelDecrease ψ τ x m z =
      ψ x + τ / 2 * ‖m‖ ^ 2 - ψ z -
        ‖z - (x - τ • m)‖ ^ 2 / (2 * τ) := by
  have h := complete_model_square ψ hτ x m z
  unfold modelDecrease
  linarith

lemma quadratic_lower_bound {τ : ℝ} (hτ : 0 < τ) (a u : E) :
    -τ / 2 * ‖a‖ ^ 2 ≤ ⟪a, u⟫_ℝ + ‖u‖ ^ 2 / (2 * τ) := by
  have h := sq_nonneg ‖u + τ • a‖
  rw [square_add_smul, real_inner_comm u a] at h
  apply (mul_le_mul_left (show 0 < 2 * τ by positivity)).mp
  have heq : (2 * τ) * (⟪a, u⟫_ℝ + ‖u‖ ^ 2 / (2 * τ)) =
      2 * τ * ⟪a, u⟫_ℝ + ‖u‖ ^ 2 := by
    field_simp [ne_of_gt hτ]
    <;> ring
  rw [heq]
  nlinarith

lemma next_model_lower_bound (ψ : E → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (x y m mnext z znext : E)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    ψ z + ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ -
        τ / 2 * ‖mnext - m + τ⁻¹ • (x - z)‖ ^ 2 ≤
      ψ znext + ⟪mnext, znext - y⟫_ℝ + ‖znext - y‖ ^ 2 / (2 * τ) := by
  have hquad := quadratic_lower_bound hτ
    (mnext - m + τ⁻¹ • (x - z)) (znext - y)
  have hsplit :
      ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ + ⟪mnext, znext - y⟫_ℝ =
        ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ +
          ⟪mnext - m + τ⁻¹ • (x - z), znext - y⟫_ℝ := by
    have hv : znext - z = (znext - y) + (y - z) := by abel
    rw [hv]
    simp only [inner_add_right, inner_add_left, inner_sub_left]
    ring
  linarith [hsplit]

lemma proximal_model_change (ψ : E → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (x y m mnext z znext : E)
    (hsupport : ψ z + ⟪τ⁻¹ • (x - z) - m, znext - z⟫_ℝ ≤ ψ znext) :
    modelDecrease ψ τ y mnext znext - modelDecrease ψ τ x m z ≤
      ψ y - ψ x - ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
        ⟪x - z, mnext - m⟫_ℝ + τ / 2 * ‖mnext - m‖ ^ 2 := by
  have hmin := next_model_lower_bound ψ hτ x y m mnext z znext hsupport
  have hquad :
      τ / 2 * ‖mnext - m + τ⁻¹ • (x - z)‖ ^ 2 =
        τ / 2 * ‖mnext - m‖ ^ 2 +
          ⟪x - z, mnext - m⟫_ℝ + ‖x - z‖ ^ 2 / (2 * τ) := by
    rw [square_add_smul, real_inner_comm (mnext - m) (x - z)]
    field_simp [ne_of_gt hτ]
    <;> ring
  have hv : y - z = (y - x) + (x - z) := by abel
  have hinner :
      ⟪τ⁻¹ • (x - z) - m, y - z⟫_ℝ =
        ⟪τ⁻¹ • (x - z) - m, y - x⟫_ℝ +
          τ⁻¹ * ‖x - z‖ ^ 2 - ⟪m, x - z⟫_ℝ := by
    simp only [hv, inner_add_right, inner_sub_left, real_inner_smul_left, inner_self_eq]
    simp
    <;> ring
  have hneg : ⟪m, z - x⟫_ℝ = -⟪m, x - z⟫_ℝ := by
    rw [show z - x = -(x - z) by abel, inner_neg_right]
  have hnorm : ‖z - x‖ ^ 2 = ‖x - z‖ ^ 2 := by rw [norm_sub_rev]
  have hinv : τ⁻¹ * ‖x - z‖ ^ 2 = 2 * (‖x - z‖ ^ 2 / (2 * τ)) := by ring
  rw [hquad, hinner] at hmin
  unfold modelDecrease
  rw [hneg, hnorm]
  linarith [hinv]

lemma modelDecrease_nonnegative (ψ : E → ℝ) (τ : ℝ) (x m z : E)
    (hmin : ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) ≤ ψ x) :
    0 ≤ modelDecrease ψ τ x m z := by
  unfold modelDecrease
  linarith

lemma modelDecrease_upper_from_support (ψ : E → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (x y m z η : E)
    (hsupport : ψ y + ⟪η, z - y⟫_ℝ ≤ ψ z) :
    modelDecrease ψ τ x m z ≤
      ψ x - ψ y - ⟪η, x - y⟫_ℝ + τ / 2 * ‖m + η‖ ^ 2 := by
  have hq := quadratic_lower_bound hτ (m + η) (z - x)
  have hv : z - y = (z - x) + (x - y) := by abel
  rw [hv, inner_add_right] at hsupport
  rw [inner_add_left] at hq
  unfold modelDecrease
  linarith

lemma subgradient_monotonicity (ψ : E → ℝ) (x y ηx ηy : E)
    (hxy : ψ x + ⟪ηx, y - x⟫_ℝ ≤ ψ y)
    (hyx : ψ y + ⟪ηy, x - y⟫_ℝ ≤ ψ x) :
    0 ≤ ⟪ηx - ηy, x - y⟫_ℝ := by
  have hv : y - x = -(x - y) := by abel
  rw [hv, inner_neg_right] at hxy
  rw [inner_sub_left]
  linarith

lemma proximal_displacement_identity {γ τ : ℝ} (hγ : γ ≠ 0) (hτ : τ ≠ 0)
    (x y z : E) :
    y - z = (τ - γ) • (γ⁻¹ • (x - y)) -
      τ • (γ⁻¹ • (x - y) - τ⁻¹ • (x - z)) := by
  simp only [smul_sub, smul_smul, sub_smul]
  simp [hγ, hτ]
  <;> abel

lemma proximal_displacement_comparison {γ τ : ℝ}
    (hγ : 0 < γ) (hτγ : γ < τ) (x y z m v : E)
    (hmono : 0 ≤
      ⟪γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m), y - z⟫_ℝ) :
    τ / (τ - γ) *
        (‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 -
          ⟪v - m, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ) ≤
      ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
        γ⁻¹ • (x - y)⟫_ℝ := by
  have hτ : 0 < τ := lt_trans hγ hτγ
  have hden : 0 < τ - γ := sub_pos.mpr hτγ
  have hv : γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m) =
      γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m) := by abel
  rw [hv, proximal_displacement_identity (ne_of_gt hγ) (ne_of_gt hτ),
    inner_sub_right, real_inner_smul_right, real_inner_smul_right] at hmono
  have hi :
      ⟪γ⁻¹ • (x - y) - τ⁻¹ • (x - z) - (v - m),
        γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ =
      ‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 -
        ⟪v - m, γ⁻¹ • (x - y) - τ⁻¹ • (x - z)⟫_ℝ := by
    rw [inner_sub_left, inner_self_eq]
  rw [hi] at hmono
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith

lemma mixed_proximal_products {γ μ τ : ℝ}
    (hγ : 0 < γ) (hμ : 0 < μ) (hτγ : γ < τ)
    (a r rτ c : E)
    (hmono : τ / (τ - γ) * (‖r - rτ‖ ^ 2 - ⟪c, r - rτ⟫_ℝ) ≤
      ⟪r - rτ - c, r⟫_ℝ) :
    -γ * ⟪a, r - rτ⟫_ℝ - γ / (μ * τ) * ⟪r - rτ - c, r⟫_ℝ ≤
      -γ / (2 * μ * (τ - γ)) * ‖r - rτ‖ ^ 2 +
        γ * μ * (τ - γ) * ‖a‖ ^ 2 +
        γ / (μ * (τ - γ)) * ‖c‖ ^ 2 := by
  have hτ : 0 < τ := lt_trans hγ hτγ
  have hd : 0 < τ - γ := sub_pos.mpr hτγ
  have hscaled := mul_le_mul_of_nonneg_left hmono
    (show 0 ≤ γ / (μ * τ) by positivity)
  have hcancel : γ / (μ * τ) * (τ / (τ - γ)) = γ / (μ * (τ - γ)) := by
    field_simp [ne_of_gt hμ, ne_of_gt hτ, ne_of_gt hd]
    <;> ring
  have hmono' :
      γ / (μ * (τ - γ)) * (‖r - rτ‖ ^ 2 - ⟪c, r - rτ⟫_ℝ) ≤
        γ / (μ * τ) * ⟪r - rτ - c, r⟫_ℝ := by
    simpa only [← mul_assoc, hcancel] using hscaled
  have hy₁ := neg_inner_young (1 / (2 * μ * (τ - γ)))
    (by positivity) (r - rτ) a
  rw [real_inner_comm (r - rτ) a] at hy₁
  have hc₁ : (1 / (2 * μ * (τ - γ)) : ℝ) / 2 =
      1 / (4 * μ * (τ - γ)) := by ring
  have hc₂ : (1 : ℝ) / (2 * (1 / (2 * μ * (τ - γ)))) =
      μ * (τ - γ) := by
    field_simp [ne_of_gt hμ, ne_of_gt hd]
    <;> ring
  rw [hc₁, hc₂] at hy₁
  have hy₁' := mul_le_mul_of_nonneg_left hy₁ (le_of_lt hγ)
  have hy₂ := inner_young (1 / 2 : ℝ) (by norm_num) (r - rτ) c
  norm_num at hy₂
  rw [real_inner_comm (r - rτ) c] at hy₂
  have hy₂' := mul_le_mul_of_nonneg_left hy₂
    (show 0 ≤ γ / (μ * (τ - γ)) by positivity)
  have hquarter : γ * (1 / (4 * μ * (τ - γ))) =
      γ / (μ * (τ - γ)) / 4 := by ring
  have hhalf : -γ / (2 * μ * (τ - γ)) =
      -(γ / (μ * (τ - γ))) / 2 := by ring
  rw [hhalf]
  nlinarith [hmono', hy₁', hy₂', hquarter]

lemma objective_cross_lower_bound (F ψ : E → ℝ) (μ γ : ℝ)
    (x y xstar g m v b : E)
    (hstrong : F y + ⟪g, xstar - y⟫_ℝ + μ / 2 * ‖xstar - y‖ ^ 2 ≤ F xstar) :
    F y + ψ y - (F xstar + ψ xstar) + μ / 2 * ‖y - xstar‖ ^ 2 +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
      ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ + ⟪y - xstar, v - m + b⟫_ℝ ≤
        ⟪y - xstar, g - m + b⟫_ℝ := by
  have hv : xstar - y = -(y - xstar) := by abel
  rw [hv, inner_neg_right, norm_neg, real_inner_comm g (y - xstar)] at hstrong
  simp only [inner_sub_left, inner_sub_right, inner_add_right]
  rw [real_inner_comm (γ⁻¹ • (x - y)) (y - xstar),
    real_inner_comm v (y - xstar)]
  linarith

lemma subgradient_remainders_nonnegative (ψ : E → ℝ) (x y xstar η : E)
    (hx : ψ y + ⟪η, x - y⟫_ℝ ≤ ψ x)
    (hstar : ψ y + ⟪η, xstar - y⟫_ℝ ≤ ψ xstar) :
    0 ≤ ψ x - ψ y - ⟪η, x - y⟫_ℝ ∧
      0 ≤ ⟪η, y - xstar⟫_ℝ - ψ y + ψ xstar := by
  have hv : xstar - y = -(y - xstar) := by abel
  rw [hv, inner_neg_right] at hstar
  constructor <;> linarith

lemma model_lower_from_segment (ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (x xstar m z : E)
    (hconvex : ψ ((1 - μ * τ) • x + (μ * τ) • xstar) ≤
      (1 - μ * τ) * ψ x + μ * τ * ψ xstar)
    (hmin : ψ z + ⟪m, z - x⟫_ℝ + ‖z - x‖ ^ 2 / (2 * τ) ≤
      ψ ((1 - μ * τ) • x + (μ * τ) • xstar) +
        ⟪m, (1 - μ * τ) • x + (μ * τ) • xstar - x⟫_ℝ +
        ‖(1 - μ * τ) • x + (μ * τ) • xstar - x‖ ^ 2 / (2 * τ)) :
    ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ - μ / 2 * ‖x - xstar‖ ^ 2 ≤
      modelDecrease ψ τ x m z / (μ * τ) := by
  have hv : (1 - μ * τ) • x + (μ * τ) • xstar - x =
      -(μ * τ) • (x - xstar) := by
    simp only [sub_smul, one_smul, smul_sub, neg_smul]
    abel
  rw [hv, real_inner_smul_right, square_smul] at hmin
  have hq : (-(μ * τ)) ^ 2 * ‖x - xstar‖ ^ 2 / (2 * τ) =
      μ * τ * (μ / 2 * ‖x - xstar‖ ^ 2) := by
    field_simp [ne_of_gt hτ]
    <;> ring
  rw [hq] at hmin
  apply (le_div_iff₀ (mul_pos hμ hτ)).2
  unfold modelDecrease
  nlinarith [hconvex, hmin]

lemma functionalEnergy_nonnegative (F ψ : E → ℝ) {μ τ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (xstar x m z : E)
    (hgap : 0 ≤ F x + ψ x - (F xstar + ψ xstar))
    (hstronggap : μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x + ψ x - (F xstar + ψ xstar))
    (hmodel : 0 ≤ modelDecrease ψ τ x m z)
    (hlower : ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ -
      μ / 2 * ‖x - xstar‖ ^ 2 ≤ modelDecrease ψ τ x m z / (μ * τ)) :
    (7 / 8 : ℝ) * (F x + ψ x - (F xstar + ψ xstar) +
      modelDecrease ψ τ x m z / (μ * τ)) ≤
        functionalEnergy F ψ μ τ xstar x m z ∧
      0 ≤ functionalEnergy F ψ μ τ xstar x m z := by
  have hscaledmodel : 0 ≤ modelDecrease ψ τ x m z / (μ * τ) := by positivity
  have hbound : ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ ≤
      F x + ψ x - (F xstar + ψ xstar) + modelDecrease ψ τ x m z / (μ * τ) := by
    linarith
  constructor
  · unfold functionalEnergy
    linarith
  · unfold functionalEnergy
    linarith

end LongTails.Proofs.ProximalEf21Geometry
