import LongTails.Proofs.ProximalEf21Geometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21EnergyComparison

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma functional_upper_raw (F ψ : E → ℝ) {μ τ γ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hγ : 0 < γ)
    (xstar x y m v z : E)
    (hsupport : ψ y + ⟪γ⁻¹ • (x - y) - v, z - y⟫_ℝ ≤ ψ z) :
    functionalEnergy F ψ μ τ xstar x m z ≤
      (F x + ψ x - (F xstar + ψ xstar)) +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) / 8 +
      (1 / (μ * τ) - 1 / 8) *
        (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
      (1 / (2 * μ * γ ^ 2) - 1 / (8 * γ)) * ‖y - x‖ ^ 2 -
      ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ / 8 +
      ⟪y - xstar, v - m⟫_ℝ / 8 +
      (γ / 8 - 1 / μ) * ⟪v - m, γ⁻¹ • (x - y)⟫_ℝ +
      ‖v - m‖ ^ 2 / (2 * μ) := by
  have hmodel := modelDecrease_upper_from_support ψ hτ x y m z
    (γ⁻¹ • (x - y) - v) hsupport
  have hscaled := div_le_div_of_nonneg_right hmodel (show 0 ≤ μ * τ by positivity)
  have hvec : m + (γ⁻¹ • (x - y) - v) = γ⁻¹ • (x - y) - (v - m) := by abel
  rw [hvec, square_sub, square_smul] at hscaled
  have hdist : ‖x - y‖ ^ 2 = ‖y - x‖ ^ 2 := by rw [norm_sub_rev]
  rw [hdist] at hscaled
  have hsplit : x - xstar = (x - y) + (y - xstar) := by abel
  have hid :
      F x + ψ x - (F xstar + ψ xstar) -
          (ψ x - ψ xstar + ⟪m, x - xstar⟫_ℝ) / 8 +
        (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ +
          τ / 2 * (γ⁻¹ ^ 2 * ‖y - x‖ ^ 2 -
            2 * ⟪γ⁻¹ • (x - y), v - m⟫_ℝ + ‖v - m‖ ^ 2)) / (μ * τ) =
      (F x + ψ x - (F xstar + ψ xstar)) +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) / 8 +
      (1 / (μ * τ) - 1 / 8) *
        (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
      (1 / (2 * μ * γ ^ 2) - 1 / (8 * γ)) * ‖y - x‖ ^ 2 -
      ⟪y - xstar, γ⁻¹ • (x - y)⟫_ℝ / 8 +
      ⟪y - xstar, v - m⟫_ℝ / 8 +
      (γ / 8 - 1 / μ) * ⟪v - m, γ⁻¹ • (x - y)⟫_ℝ +
      ‖v - m‖ ^ 2 / (2 * μ) := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
      inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      inner_neg_right, inner_neg_left, real_inner_comm]
    field_simp [ne_of_gt hμ, ne_of_gt hτ, ne_of_gt hγ]
    <;> ring
  unfold functionalEnergy
  linarith [hscaled, hid]

lemma functional_upper_intermediate (F ψ : E → ℝ) {μ τ γ : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hγ : 0 < γ) (hμγ : μ * γ ≤ 1)
    (xstar x y m v z : E)
    (hsupport : ψ y + ⟪γ⁻¹ • (x - y) - v, z - y⟫_ℝ ≤ ψ z)
    (hD : 0 ≤ ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
    (hgap : μ / 2 * ‖y - xstar‖ ^ 2 ≤ F y + ψ y - (F xstar + ψ xstar)) :
    functionalEnergy F ψ μ τ xstar x m z ≤
      (F x + ψ x - (F xstar + ψ xstar)) +
      (F y + ψ y - (F xstar + ψ xstar)) / 8 +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) / 8 +
      (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) / (μ * τ) +
      9 / (8 * μ * γ ^ 2) * ‖y - x‖ ^ 2 + 9 / (8 * μ) * ‖v - m‖ ^ 2 := by
  have hraw := functional_upper_raw F ψ hμ hτ hγ xstar x y m v z hsupport
  have hy₁ := neg_inner_young (μ / 2) (by positivity)
    (y - xstar) (γ⁻¹ • (x - y))
  have hy₂ := inner_young (μ / 2) (by positivity) (y - xstar) (v - m)
  have hy₃ := neg_inner_young 1 (by norm_num) (v - m) (γ⁻¹ • (x - y))
  have hrnorm : ‖γ⁻¹ • (x - y)‖ ^ 2 = ‖y - x‖ ^ 2 / γ ^ 2 := by
    rw [square_smul, norm_sub_rev x y]
    ring
  rw [hrnorm] at hy₁ hy₃
  have hcoef0 : 0 ≤ 1 / μ - γ / 8 := by
    apply (mul_le_mul_left hμ).mp
    field_simp [ne_of_gt hμ]
    nlinarith
  have hcoef1 : 1 / μ - γ / 8 ≤ 1 / μ := by linarith
  have hy₃' := mul_le_mul_of_nonneg_left hy₃ hcoef0
  have hright0 : 0 ≤ ‖v - m‖ ^ 2 / 2 + (‖y - x‖ ^ 2 / γ ^ 2) / 2 := by positivity
  have hy₃'' := mul_le_mul_of_nonneg_right hcoef1 hright0
  have hDdrop : -(1 / 8 : ℝ) *
      (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) ≤ 0 := by nlinarith
  have hdisdrop : 0 ≤ ‖y - x‖ ^ 2 / (8 * γ) := by positivity
  have hμid : (1 : ℝ) / (2 * (μ / 2)) = 1 / μ := by ring
  rw [hμid] at hy₁ hy₂
  norm_num at hy₃ hy₃'
  have hcoeffid : 1 / (2 * μ * γ ^ 2) + 1 / (8 * μ * γ ^ 2) +
      1 / (2 * μ * γ ^ 2) = 9 / (8 * μ * γ ^ 2) := by ring
  nlinarith only [hraw, hy₁, hy₂, hy₃', hy₃'', hgap, hDdrop, hdisdrop, hcoeffid]

lemma objective_reverse_bound (F ψ : E → ℝ) {μ M γ W : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hγ : 0 < γ) (hμM : μ ≤ M)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3)
    (xstar x y m v g gstar : E)
    (hsmooth : F x ≤ F y + ⟪g, x - y⟫_ℝ + M / 2 * ‖x - y‖ ^ 2)
    (hgrad : ‖g - gstar‖ ^ 2 ≤ 2 * M * (F y + ψ y - (F xstar + ψ xstar)))
    (hmemory : ‖m - gstar‖ ^ 2 ≤ 2 * W) :
    F x + ψ x - (F xstar + ψ xstar) ≤
      2 * (F y + ψ y - (F xstar + ψ xstar)) +
      3 / (μ * γ ^ 2) * ‖y - x‖ ^ 2 + W / M + ‖v - m‖ ^ 2 / (2 * μ) +
      (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) := by
  have hy₁ := inner_young (1 / M) (by positivity) (g - gstar) (x - y)
  have hy₂ := neg_inner_young (1 / M) (by positivity) (m - gstar) (x - y)
  have hy₃ := neg_inner_young (1 / μ) (by positivity) (v - m) (x - y)
  have hcM : (1 : ℝ) / (2 * (1 / M)) = M / 2 := by
    field_simp [ne_of_gt hM]
  have hcμ : (1 : ℝ) / (2 * (1 / μ)) = μ / 2 := by
    field_simp [ne_of_gt hμ]
  rw [hcM] at hy₁ hy₂
  rw [hcμ] at hy₃
  have hgn := div_le_div_of_nonneg_right hgrad (show 0 ≤ 2 * M by positivity)
  have hmn := div_le_div_of_nonneg_right hmemory (show 0 ≤ 2 * M by positivity)
  have hgp : (2 * M * (F y + ψ y - (F xstar + ψ xstar))) / (2 * M) =
      F y + ψ y - (F xstar + ψ xstar) := by field_simp [ne_of_gt hM]
  have hmp : 2 * W / (2 * M) = W / M := by ring
  rw [hgp] at hgn
  rw [hmp] at hmn
  have hcoef : 1 / γ + 3 * M / 2 + μ / 2 ≤ 3 / (μ * γ ^ 2) := by
    apply (le_div_iff₀ (show 0 < μ * γ ^ 2 by positivity)).2
    have hid : (1 / γ + 3 * M / 2 + μ / 2) * (μ * γ ^ 2) =
        μ * γ + (3 * M / 2 + μ / 2) * μ * γ ^ 2 := by
      field_simp [ne_of_gt hγ]
      <;> ring
    rw [hid]
    nlinarith [mul_nonneg (show 0 ≤ M - μ by linarith)
      (show 0 ≤ μ * γ ^ 2 by positivity)]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖x - y‖)
  have hid : ⟪g, x - y⟫_ℝ =
      ⟪g - gstar, x - y⟫_ℝ - ⟪m - gstar, x - y⟫_ℝ -
      ⟪v - m, x - y⟫_ℝ + ⟪v, x - y⟫_ℝ := by
    simp only [inner_sub_left]
    ring
  have hη : ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ =
      ‖x - y‖ ^ 2 / γ - ⟪v, x - y⟫_ℝ := by
    rw [inner_sub_left, real_inner_smul_left, inner_self_eq]
    ring
  rw [hid] at hsmooth
  rw [hη, norm_sub_rev y x]
  nlinarith only [hsmooth, hy₁, hy₂, hy₃, hgn, hmn, hcoef']

lemma functional_upper_comparison (F ψ : E → ℝ) {μ M τ γ W V : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hμM : μ ≤ M) (hμγ : μ * γ ≤ 1) (hμτ : μ * τ ≤ 1)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3)
    (xstar x y m v z g gstar : E)
    (hsupport : ψ y + ⟪γ⁻¹ • (x - y) - v, z - y⟫_ℝ ≤ ψ z)
    (hD : 0 ≤ ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ)
    (hgap : μ / 2 * ‖y - xstar‖ ^ 2 ≤ F y + ψ y - (F xstar + ψ xstar))
    (hsmooth : F x ≤ F y + ⟪g, x - y⟫_ℝ + M / 2 * ‖x - y‖ ^ 2)
    (hgrad : ‖g - gstar‖ ^ 2 ≤ 2 * M * (F y + ψ y - (F xstar + ψ xstar)))
    (hmemory : ‖m - gstar‖ ^ 2 ≤ 2 * W)
    (hcompression : ‖v - m‖ ^ 2 ≤ 2 * V) :
    functionalEnergy F ψ μ τ xstar x m z ≤
      3 * (F y + ψ y - (F xstar + ψ xstar)) +
      5 / (μ * γ ^ 2) * ‖y - x‖ ^ 2 +
      (⟪γ⁻¹ • (x - y) - v, y - xstar⟫_ℝ - ψ y + ψ xstar) / 8 +
      2 / (μ * τ) * (ψ x - ψ y - ⟪γ⁻¹ • (x - y) - v, x - y⟫_ℝ) +
      W / M + 4 / μ * V := by
  have hE := functional_upper_intermediate F ψ hμ hτ hγ hμγ
    xstar x y m v z hsupport hD hgap
  have hΔ := objective_reverse_bound F ψ hμ hM hγ hμM hsmall
    xstar x y m v g gstar hsmooth hgrad hmemory
  have hΔpos : 0 ≤ F y + ψ y - (F xstar + ψ xstar) :=
    (show 0 ≤ μ / 2 * ‖y - xstar‖ ^ 2 by positivity).trans hgap
  have hVpos : 0 ≤ V := by nlinarith [sq_nonneg ‖v - m‖]
  have hcoefD : 1 + 1 / (μ * τ) ≤ 2 / (μ * τ) := by
    apply (mul_le_mul_right (mul_pos hμ hτ)).mp
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    linarith
  have hDscaled := mul_le_mul_of_nonneg_right hcoefD hD
  have hcscaled := mul_le_mul_of_nonneg_left hcompression
    (show 0 ≤ 13 / (8 * μ) by positivity)
  have hdisp : 0 ≤ ‖y - x‖ ^ 2 / (μ * γ ^ 2) := by positivity
  have hV : 0 ≤ V / μ := by positivity
  nlinarith only [hE, hΔ, hΔpos, hDscaled, hcscaled, hdisp, hV]

end LongTails.Proofs.ProximalEf21EnergyComparison
