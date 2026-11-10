import LongTails.Proofs.ProximalEf21Geometry
import LongTails.Proofs.ProximalEf21WeightedErrors

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21ConvexAnalysis

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nonpositive_of_segment_bounds {a c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ t * c) : a ≤ 0 := by
  by_contra hnot
  have ha : 0 < a := lt_of_not_ge hnot
  have hden : 0 < 2 * (c + a) := by positivity
  have ht : 0 < a / (2 * (c + a)) := div_pos ha hden
  have ht1 : a / (2 * (c + a)) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have h := hbound (a / (2 * (c + a))) ht ht1
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt hden)
  have heq : a / (2 * (c + a)) * c * (2 * (c + a)) = a * c := by
    field_simp [ne_of_gt hden]
    <;> ring
  rw [heq] at hm
  nlinarith [mul_nonneg hc (le_of_lt ha), sq_pos_of_pos ha]

lemma proximal_supporting_affine (D : Set E) (ψ : E → ℝ)
    (hψ : ConvexOn ℝ D ψ) {τ : ℝ} (hτ : 0 < τ) (u p : E)
    (hp : p ∈ D)
    (hmin : ∀ z ∈ D,
      ψ p + ‖p - u‖ ^ 2 / (2 * τ) ≤ ψ z + ‖z - u‖ ^ 2 / (2 * τ)) :
    ∀ z ∈ D, ψ p + ⟪τ⁻¹ • (u - p), z - p⟫_ℝ ≤ ψ z := by
  intro z hz
  have hmain : ψ p + ⟪τ⁻¹ • (u - p), z - p⟫_ℝ - ψ z ≤ 0 := by
    apply nonpositive_of_segment_bounds
      (c := ‖z - p‖ ^ 2 / (2 * τ)) (by positivity)
    intro t ht ht1
    have ht0 : 0 ≤ t := le_of_lt ht
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : (1 - t) + t = 1 := by ring
    have hmem := hψ.1 hp hz h1t ht0 hsum
    have hconv := hψ.2 hp hz h1t ht0 hsum
    simp only [smul_eq_mul] at hconv
    have hprox := hmin ((1 - t) • p + t • z) hmem
    have hv : (1 - t) • p + t • z - u = (p - u) + t • (z - p) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [hv, square_add_smul] at hprox
    have hnormterm :
        (‖p - u‖ ^ 2 + 2 * t * ⟪p - u, z - p⟫_ℝ +
          t ^ 2 * ‖z - p‖ ^ 2) / (2 * τ) =
        ‖p - u‖ ^ 2 / (2 * τ) +
          t / τ * ⟪p - u, z - p⟫_ℝ + t ^ 2 * ‖z - p‖ ^ 2 / (2 * τ) := by
      ring
    rw [hnormterm] at hprox
    have hip : ⟪τ⁻¹ • (u - p), z - p⟫_ℝ =
        -τ⁻¹ * ⟪p - u, z - p⟫_ℝ := by
      rw [show u - p = -(p - u) by abel]
      simp [real_inner_smul_left, inner_neg_left]
    rw [hip]
    apply (mul_le_mul_left ht).mp
    nlinarith [hconv, hprox]
  linarith

lemma smooth_convex_interpolation (f : E → ℝ) (g : E → E)
    {L : ℝ} (hL : 0 < L)
    (hconvex : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y)
    (hsmooth : ∀ x y,
      f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (x y : E) :
    ‖g x - g y‖ ^ 2 ≤
      2 * L * (f x - f y - ⟪g y, x - y⟫_ℝ) := by
  let z := x - L⁻¹ • (g x - g y)
  have hlow := hconvex y z
  have hupp := hsmooth x z
  have hzx : z - x = -(L⁻¹) • (g x - g y) := by dsimp [z]; module
  have hzy : z - y = (x - y) - L⁻¹ • (g x - g y) := by dsimp [z]; abel
  rw [hzy, inner_sub_right, real_inner_smul_right] at hlow
  rw [hzx, real_inner_smul_right, square_smul] at hupp
  have hdiff : ⟪g x, g x - g y⟫_ℝ - ⟪g y, g x - g y⟫_ℝ =
      ‖g x - g y‖ ^ 2 := by rw [← inner_sub_left, inner_self_eq]
  have hcoef : L / 2 * (-(L⁻¹)) ^ 2 = L⁻¹ / 2 := by
    field_simp [ne_of_gt hL]
    <;> ring
  have htw : 2 * L * L⁻¹ = 2 := by field_simp [ne_of_gt hL]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * L by positivity)
  have hupp' := mul_le_mul_of_nonneg_left hupp (show 0 ≤ 2 * L by positivity)
  have hclean :
      (2 * L) * (L / 2 * ((-(L⁻¹)) ^ 2 * ‖g x - g y‖ ^ 2)) =
        ‖g x - g y‖ ^ 2 := by
    field_simp [ne_of_gt hL]
    <;> ring
  have hmul₁ : 2 * L * (L⁻¹ * ⟪g y, g x - g y⟫_ℝ) =
      2 * ⟪g y, g x - g y⟫_ℝ := by field_simp [ne_of_gt hL]
  have hmul₂ : 2 * L * (-(L⁻¹) * ⟪g x, g x - g y⟫_ℝ) =
      -2 * ⟪g x, g x - g y⟫_ℝ := by field_simp [ne_of_gt hL]
  nlinarith [hlow', hupp', hclean, hmul₁, hmul₂, hdiff]

lemma composite_gradient_interpolation (F ψ : E → ℝ) (g : E → E)
    {M : ℝ} (hM : 0 ≤ M) (x xstar : E)
    (hinterp : ‖g x - g xstar‖ ^ 2 ≤
      2 * M * (F x - F xstar - ⟪g xstar, x - xstar⟫_ℝ))
    (hstar : ψ xstar + ⟪-g xstar, x - xstar⟫_ℝ ≤ ψ x) :
    ‖g x - g xstar‖ ^ 2 ≤
      2 * M * (F x + ψ x - (F xstar + ψ xstar)) := by
  rw [inner_neg_left] at hstar
  have hgap : F x - F xstar - ⟪g xstar, x - xstar⟫_ℝ ≤
      F x + ψ x - (F xstar + ψ xstar) := by linarith
  exact hinterp.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

lemma composite_strong_gap (F ψ : E → ℝ) (μ : ℝ) (x xstar gstar : E)
    (hstrong : F xstar + ⟪gstar, x - xstar⟫_ℝ +
      μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x)
    (hstar : ψ xstar + ⟪-gstar, x - xstar⟫_ℝ ≤ ψ x) :
    μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x + ψ x - (F xstar + ψ xstar) := by
  rw [inner_neg_left] at hstar
  linarith

lemma regularization_center_offset (μ : ℝ) (x x0 xstar g : E) :
    g + μ • (x - x0) = (g + μ • (x - xstar)) + μ • (xstar - x0) := by
  simp only [smul_sub]
  abel

lemma regularization_offset_norm {μ R : ℝ} (hμ : 0 ≤ μ)
    (x0 xstar : E) (hdistance : ‖x0 - xstar‖ ≤ R) :
    ‖μ • (xstar - x0)‖ ≤ μ * R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ, norm_sub_rev xstar x0]
  exact mul_le_mul_of_nonneg_left hdistance hμ

lemma weighted_initial_momentum_bound {n : ℕ} (hn : 0 < n)
    (w l : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hl : ∀ i, 0 ≤ l i) (m g0 gstar : Fin n → E)
    {L R : ℝ} (hR : 0 ≤ R)
    (hsmooth : ∀ i, ‖g0 i - gstar i‖ ≤ l i * R)
    (hrms : (n : ℝ)⁻¹ * ∑ i, l i ^ 2 ≤ L ^ 2) :
    (n : ℝ)⁻¹ * ∑ i, w i * ‖m i - gstar i‖ ^ 2 ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - g0 i‖ ^ 2) + 2 * L ^ 2 * R ^ 2 := by
  have hpoint : ∀ i, w i * ‖m i - gstar i‖ ^ 2 ≤
      2 * ‖m i - g0 i‖ ^ 2 + 2 * l i ^ 2 * R ^ 2 := by
    intro i
    have hv : m i - gstar i = (m i - g0 i) + (g0 i - gstar i) := by abel
    have htwo := square_two (m i - g0 i) (g0 i - gstar i)
    rw [← hv] at htwo
    have hg : ‖g0 i - gstar i‖ ^ 2 ≤ l i ^ 2 * R ^ 2 := by
      have hnn : 0 ≤ l i * R := mul_nonneg (hl i) hR
      nlinarith [hsmooth i, norm_nonneg (g0 i - gstar i)]
    have hwbound := mul_le_mul_of_nonneg_right (hw1 i) (sq_nonneg ‖m i - gstar i‖)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hmean := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hsumid :
      (n : ℝ)⁻¹ * ∑ i, (2 * ‖m i - g0 i‖ ^ 2 + 2 * l i ^ 2 * R ^ 2) =
        2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - g0 i‖ ^ 2) +
          2 * ((n : ℝ)⁻¹ * ∑ i, l i ^ 2) * R ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hsumid] at hmean
  have hscaled := mul_le_mul_of_nonneg_right hrms (sq_nonneg R)
  nlinarith

end LongTails.Proofs.ProximalEf21ConvexAnalysis
