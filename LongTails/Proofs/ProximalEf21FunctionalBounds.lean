import LongTails.Proofs.ProximalEf21FunctionalCalculus

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21FunctionalBounds

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21FunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma remaining_young_bounds {μ γ α : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hα : α = μ * γ)
    (x y xstar c b : E) :
    α / 8 * ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ ≤
        α * μ / 32 * ‖y - xstar‖ ^ 2 + ‖y - x‖ ^ 2 / (8 * γ) ∧
    -α / 8 * ⟪y - xstar, c⟫_ℝ ≤
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖c‖ ^ 2 ∧
    -α / 8 * ⟪y - xstar, b⟫_ℝ ≤
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖b‖ ^ 2 ∧
    7 / 8 * ⟪c, x - y⟫_ℝ ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 ∧
    ⟪b, x - y⟫_ℝ ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖b‖ ^ 2 := by
  have hαpos : 0 < α := by rw [hα]; positivity
  have hnorm : ‖x - y‖ ^ 2 = ‖y - x‖ ^ 2 := by rw [norm_sub_rev]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := inner_young (μ / 2) (by positivity)
      (y - xstar) (γ⁻¹ • (x - y))
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    rw [square_smul, hnorm] at hh
    have hid : α / 8 * ((μ / 2) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 2)) * (γ⁻¹ ^ 2 * ‖y - x‖ ^ 2)) =
        α * μ / 32 * ‖y - xstar‖ ^ 2 + ‖y - x‖ ^ 2 / (8 * γ) := by
      rw [hα]
      field_simp [ne_of_gt hμ, ne_of_gt hγ]
      <;> ring
    simpa only [hid] using hh
  · have h := neg_inner_young (μ / 8) (by positivity) (y - xstar) c
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    have hid : α / 8 * ((μ / 8) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 8)) * ‖c‖ ^ 2) =
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖c‖ ^ 2 := by
      rw [hα]
      field_simp [ne_of_gt hμ]
      <;> ring
    rw [hid] at hh
    linarith
  · have h := neg_inner_young (μ / 8) (by positivity) (y - xstar) b
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 8 by positivity)
    have hid : α / 8 * ((μ / 8) / 2 * ‖y - xstar‖ ^ 2 +
        1 / (2 * (μ / 8)) * ‖b‖ ^ 2) =
        α * μ / 128 * ‖y - xstar‖ ^ 2 + γ / 2 * ‖b‖ ^ 2 := by
      rw [hα]
      field_simp [ne_of_gt hμ]
      <;> ring
    rw [hid] at hh
    linarith
  · have h := inner_young (1 / (8 * γ)) (by positivity) (x - y) c
    rw [real_inner_comm (x - y) c, hnorm] at h
    have hc₁ : (1 / (8 * γ) : ℝ) / 2 = 1 / (16 * γ) := by ring
    have hc₂ : (1 : ℝ) / (2 * (1 / (8 * γ))) = 4 * γ := by
      field_simp [ne_of_gt hγ]
      <;> ring
    rw [hc₁, hc₂] at h
    have hn : 0 ≤ ‖y - x‖ ^ 2 / (16 * γ) + 4 * γ * ‖c‖ ^ 2 := by positivity
    linarith
  · have h := inner_young (1 / (8 * γ)) (by positivity) (x - y) b
    rw [real_inner_comm (x - y) b, hnorm] at h
    have hc₁ : (1 / (8 * γ) : ℝ) / 2 = 1 / (16 * γ) := by ring
    have hc₂ : (1 : ℝ) / (2 * (1 / (8 * γ))) = 4 * γ := by
      field_simp [ne_of_gt hγ]
      <;> ring
    simpa only [hc₁, hc₂, div_eq_mul_inv] using h

lemma pointwise_functional_progress (F ψ : E → ℝ) {μ M τ γ α W V : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096)
    (hα : α = μ * γ) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (xstar x y m v z g gstar b : E)
    (hD : 0 ≤ ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
    (hstrong : F y + ⟪g, xstar - y⟫_ℝ + μ / 2 * ‖xstar - y‖ ^ 2 ≤ F xstar)
    (hmono : 0 ≤
      ⟪γ⁻¹ • (x - y) - v - (τ⁻¹ • (x - z) - m), y - z⟫_ℝ)
    (hgrad : ‖g - gstar‖ ^ 2 ≤ 2 * M * (F y + ψ y - (F xstar + ψ xstar)))
    (hmemory : ‖m - gstar‖ ^ 2 ≤ 2 * W)
    (hcompression : ‖v - m‖ ^ 2 ≤ 2 * V) :
    componentBound F ψ μ τ γ α xstar x y m z g b ≤
      -α * (1 / 8 - 15 * M * τ / 2) * (F y + ψ y - (F xstar + ψ xstar)) -
      5 / (8 * γ) * ‖y - x‖ ^ 2 -
      α / 8 * (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) -
      1 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
      15 * α * τ / 2 * W + 5 * γ / (μ * τ) * V + 5 * γ * ‖b‖ ^ 2 := by
  have hτγ : γ < τ := by linarith
  have hden : 0 < τ - γ := by linarith
  have hαpos : 0 < α := by rw [hα]; positivity
  have hmcomp := proximal_displacement_comparison hγ hτγ x y z m v hmono
  have hmix := mixed_proximal_products hγ hμ hτγ (g - m + b)
    (γ⁻¹ • (x - y)) (τ⁻¹ • (x - z)) (v - m) hmcomp
  have hcross := objective_cross_lower_bound F ψ μ γ x y xstar g m v b hstrong
  have hcross' := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ α / 8 by positivity)
  obtain ⟨hy₁, hy₂, hy₃, hy₄, hy₅⟩ :=
    remaining_young_bounds hμ hγ hα x y xstar (v - m) b
  have hq := square_three (g - gstar) (-(m - gstar)) b
  have hqvec : g - gstar + -(m - gstar) + b = g - m + b := by abel
  rw [hqvec, norm_neg] at hq
  have hqbound : ‖g - m + b‖ ^ 2 ≤
      3 * (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) := by
    nlinarith [hgrad, hmemory, hq]
  have hqcoef0 : 0 ≤ μ * γ ^ 2 / 2 + γ * μ * (τ - γ) := by positivity
  have hqcoef : μ * γ ^ 2 / 2 + γ * μ * (τ - γ) ≤ 5 * α * τ / 4 := by
    rw [hα]
    nlinarith [mul_nonneg (le_of_lt (mul_pos hμ hγ)) (le_of_lt hτ)]
  have hq₁ := mul_le_mul_of_nonneg_right hqcoef (sq_nonneg ‖g - m + b‖)
  have hq₂ := mul_le_mul_of_nonneg_left hqbound
    (show 0 ≤ 5 * α * τ / 4 by positivity)
  have hqfinal :
      (μ * γ ^ 2 / 2 + γ * μ * (τ - γ)) * ‖g - m + b‖ ^ 2 ≤
      15 * α * τ / 4 *
        (2 * M * (F y + ψ y - (F xstar + ψ xstar)) + 2 * W + ‖b‖ ^ 2) := by
    nlinarith only [hq₁, hq₂]
  have hcden : γ / (μ * (τ - γ)) ≤ 2 * γ / (μ * τ) := by
    apply (div_le_div_iff₀ (mul_pos hμ hden) (mul_pos hμ hτ)).2
    nlinarith [mul_nonneg (le_of_lt (mul_pos hμ hγ)) (show 0 ≤ τ - 2 * γ by linarith)]
  have hc₁ := mul_le_mul_of_nonneg_right hcden (sq_nonneg ‖v - m‖)
  have hc₂ := mul_le_mul_of_nonneg_left hcompression
    (show 0 ≤ 2 * γ / (μ * τ) + 9 * γ / 2 by positivity)
  have hcsmall : (2 * γ / (μ * τ) + 9 * γ / 2) * 2 ≤ 5 * γ / (μ * τ) := by
    apply (mul_le_mul_right (mul_pos hμ hτ)).mp
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    nlinarith [mul_le_mul_of_nonneg_left hμτ (show 0 ≤ 9 * γ by positivity)]
  have hc₃ := mul_le_mul_of_nonneg_right hcsmall hV
  have hcfinal : (γ / (μ * (τ - γ)) + 9 * γ / 2) * ‖v - m‖ ^ 2 ≤
      5 * γ / (μ * τ) * V := by
    nlinarith only [hc₁, hc₂, hc₃]
  have hbcoef : 9 * γ / 2 + 15 * α * τ / 4 ≤ 5 * γ := by
    rw [hα]
    nlinarith [mul_le_mul_of_nonneg_left hμτ (show 0 ≤ 15 * γ by positivity)]
  have hb := mul_le_mul_of_nonneg_right hbcoef (sq_nonneg ‖b‖)
  have hdist : 0 ≤ α * μ * ‖y - xstar‖ ^ 2 := by positivity
  have hdisp : 0 ≤ μ * ‖y - x‖ ^ 2 := by positivity
  have hprox : 0 ≤ γ / (2 * μ * (τ - γ)) *
      ‖γ⁻¹ • (x - y) - τ⁻¹ • (x - z)‖ ^ 2 := by positivity
  rw [componentBound_assembled F ψ (ne_of_gt hμ) (ne_of_gt hγ) (ne_of_gt hτ) xstar x y m v z g b]
  simp only [inner_add_right] at hcross'
  have hcancel : -7 / (8 * γ) + 1 / (8 * γ) + 1 / (16 * γ) + 1 / (16 * γ) =
      -5 / (8 * γ) := by ring
  nlinarith only [hmix, hcross', hy₁, hy₂, hy₃, hy₄, hy₅, hqfinal,
    hcfinal, hb, hdist, hdisp, hprox, hD, hcancel]

end LongTails.Proofs.ProximalEf21FunctionalBounds
