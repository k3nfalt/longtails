import LongTails.Proofs.ProximalEf21Moments
import LongTails.Proofs.ProximalEf21Step
import LongTails.Proofs.ProximalEf21Tuning
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

section EnergyComparison

open scoped BigOperators InnerProductSpace RealInnerProductSpace

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
    apply (mul_le_mul_iff_of_pos_left hμ).mp
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
  ring_nf at hraw hy₁ hy₂ hy₃' hy₃'' hgap hDdrop hdisdrop ⊢
  linarith only [hraw, hy₁, hy₂, hy₃', hy₃'', hgap, hDdrop, hdisdrop]

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
  ring_nf at hsmooth hy₁ hy₂ hy₃ hgn hmn hcoef' ⊢
  linarith only [hsmooth, hy₁, hy₂, hy₃, hgn, hmn, hcoef']

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
    apply (mul_le_mul_iff_of_pos_right (mul_pos hμ hτ)).mp
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    linarith
  have hDscaled := mul_le_mul_of_nonneg_right hcoefD hD
  have hcscaled := mul_le_mul_of_nonneg_left hcompression
    (show 0 ≤ 13 / (8 * μ) by positivity)
  have hdisp : 0 ≤ ‖y - x‖ ^ 2 / (μ * γ ^ 2) := by positivity
  have hV : 0 ≤ V / μ := by positivity
  ring_nf at hE hΔ hΔpos hDscaled hcscaled hdisp hV ⊢
  linarith only [hE, hΔ, hΔpos, hDscaled, hcscaled, hdisp, hV]

end LongTails.Proofs.ProximalEf21EnergyComparison


end EnergyComparison


section Initialization

open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21Initialization

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} {L R : ℝ} (G : ConvexCompositeGeometry (E := E) n L)

lemma unweighted_mean_square (hn : 0 < n) (u : Fin n → E) :
    ‖workerMean u‖ ^ 2 ≤ (n : ℝ)⁻¹ * ∑ i, ‖u i‖ ^ 2 := by
  have h := weighted_cauchy_schwarz_mean hn (fun _ => (1 : ℝ))
    (fun _ => by norm_num) u
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simpa [workerMean, Finset.sum_const, Fintype.card_fin, hnR] using h

lemma initial_reference_bounds (x0 : E) (hx0 : x0 ∈ G.domain)
    (hR : 0 ≤ R) (hdistance : ‖x0 - G.xstar‖ ≤ R) (m v : Fin n → E) :
    (G.regularized (2 * L) (by linarith [G.hL]) (by rfl)).W m ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - G.grad i x0‖ ^ 2) + 2 * L ^ 2 * R ^ 2 ∧
    (G.regularized (2 * L) (by linarith [G.hL]) (by rfl)).V m v ≤
      (n : ℝ)⁻¹ * ∑ i, ‖v i - m i‖ ^ 2 ∧
    ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, ‖m i - G.grad i x0‖ ^ 2) + 2 * L ^ 2 * R ^ 2 := by
  have hL : 0 < L := G.hL
  let Q := G.regularized (2 * L) (by linarith [G.hL]) (by rfl)
  have hs : ∀ i, ‖G.grad i x0 - G.grad i G.xstar‖ ≤ G.localL i * R := by
    intro i
    exact (G.local_lipschitz i x0 G.xstar).trans
      (mul_le_mul_of_nonneg_left hdistance (G.localL_nonnegative i))
  have hw := weighted_initial_momentum_bound G.hn Q.weights G.localL
    (fun i => (Q.weights_positive i).le) Q.weights_le_one
    G.localL_nonnegative m (fun i => G.grad i x0) (fun i => G.grad i G.xstar)
    hR hs G.rms_bound
  have hwu := weighted_initial_momentum_bound G.hn (fun _ => (1 : ℝ)) G.localL
    (fun _ => by norm_num) (fun _ => by norm_num)
    G.localL_nonnegative m (fun i => G.grad i x0) (fun i => G.grad i G.xstar)
    hR hs G.rms_bound
  have hW : Q.W m = weightedSquare Q.weights (fun i => m i - G.grad i G.xstar) := by
    unfold InnerGeometry.W Q ConvexCompositeGeometry.regularized
    simp only [sub_self, smul_zero, add_zero]
  have hV : Q.V m v ≤ (n : ℝ)⁻¹ * ∑ i, ‖v i - m i‖ ^ 2 := by
    unfold InnerGeometry.V weightedSquare
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    apply Finset.sum_le_sum
    intro i hi
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Q.weights_le_one i) (sq_nonneg ‖v i - m i‖)
  have hm := unweighted_mean_square G.hn (fun i => m i - G.grad i G.xstar)
  rw [workerMean_sub] at hm
  change ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤ _ at hm
  refine ⟨?_, hV, hm.trans ?_⟩
  · change Q.W m ≤ _
    rw [hW]
    exact hw
  · simpa only [one_mul] using hwu

lemma regularizer_reference_bounds (x : E) (hx : x ∈ G.domain) :
    0 ≤ G.ψ x - G.ψ G.xstar + ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ∧
    G.ψ x - G.ψ G.xstar + ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.gap x := by
  have hL : 0 < L := G.hL
  have hp := G.optimum_support x hx
  change G.ψ G.xstar + ⟪-G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.ψ x at hp
  rw [inner_neg_left] at hp
  have hf := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_lower i G.xstar x))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hid : (n : ℝ)⁻¹ * ∑ i, (G.f i G.xstar + ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) =
      G.smoothValue G.xstar + ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ := by
    simp only [ConvexCompositeGeometry.smoothValue,
      ConvexCompositeGeometry.smoothGradient, workerMean, Finset.sum_add_distrib,
      mul_add, real_inner_smul_left, sum_inner]
  rw [hid] at hf
  change _ ≤ G.smoothValue x at hf
  unfold ConvexCompositeGeometry.gap
  constructor <;> linarith

lemma initial_potential_bound (x0 : E) (hx0 : x0 ∈ G.domain)
    (hR : 0 < R) (hdistance : ‖x0 - G.xstar‖ ≤ R) (m v : Fin n → E) :
    (G.regularized (2 * L) (by linarith [G.hL]) (by rfl)).potential (1 / (12288 * L)) x0 m v ≤
      8192 * (G.gap x0 + L * R ^ 2 +
        ((n : ℝ)⁻¹ * ∑ i, ‖v i - m i‖ ^ 2 +
          (n : ℝ)⁻¹ * ∑ i, ‖m i - G.grad i x0‖ ^ 2) / L) := by
  have hL : 0 < L := G.hL
  let τ : ℝ := 1 / (12288 * L)
  let Q := G.regularized (2 * L) (by linarith [G.hL]) (by rfl)
  let W : ℝ := (n : ℝ)⁻¹ * ∑ i, ‖m i - G.grad i x0‖ ^ 2
  let V : ℝ := (n : ℝ)⁻¹ * ∑ i, ‖v i - m i‖ ^ 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hW0 : 0 ≤ W := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hV0 : 0 ≤ V := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  obtain ⟨hW, hV, hm⟩ := initial_reference_bounds G x0 hx0 hR.le hdistance m v
  change Q.W m ≤ 2 * W + 2 * L ^ 2 * R ^ 2 at hW
  change Q.V m v ≤ V at hV
  change ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤
    2 * W + 2 * L ^ 2 * R ^ 2 at hm
  obtain ⟨hψ0, hψΔ⟩ := regularizer_reference_bounds G x0 hx0
  have hz : Q.auxiliary τ x0 m ∈ G.domain := G.prox_mem τ hτ _
  have hs := G.optimum_support (Q.auxiliary τ x0 m) hz
  have hmodel := modelDecrease_upper_from_support G.ψ hτ x0 G.xstar
    (workerMean m) (Q.auxiliary τ x0 m) (-G.smoothGradient G.xstar) hs
  simp only [inner_neg_left, ← sub_eq_add_neg] at hmodel
  have hmodel' : modelDecrease G.ψ τ x0 (workerMean m) (Q.auxiliary τ x0 m) ≤
      G.gap x0 + τ * (W + L ^ 2 * R ^ 2) := by
    have hms := mul_le_mul_of_nonneg_left hm (show 0 ≤ τ / 2 by positivity)
    ring_nf at hmodel hms hψΔ ⊢
    linarith only [hmodel, hms, hψΔ]
  have hsq : ‖x0 - G.xstar‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (x0 - G.xstar)]
  have hcross := neg_inner_young (2 * L) (by positivity)
    (x0 - G.xstar) (workerMean m - G.smoothGradient G.xstar)
  have hcross' : -(G.ψ x0 - G.ψ G.xstar + ⟪workerMean m, x0 - G.xstar⟫_ℝ) / 8 ≤
      3 * L * R ^ 2 / 16 + W / (16 * L) := by
    have hid : G.ψ x0 - G.ψ G.xstar + ⟪workerMean m, x0 - G.xstar⟫_ℝ =
        (G.ψ x0 - G.ψ G.xstar + ⟪G.smoothGradient G.xstar, x0 - G.xstar⟫_ℝ) +
          ⟪x0 - G.xstar, workerMean m - G.smoothGradient G.xstar⟫_ℝ := by
      have hsplit :
          ⟪x0 - G.xstar, workerMean m - G.smoothGradient G.xstar⟫_ℝ =
            ⟪workerMean m, x0 - G.xstar⟫_ℝ -
              ⟪G.smoothGradient G.xstar, x0 - G.xstar⟫_ℝ := by
        rw [inner_sub_right,
          real_inner_comm (workerMean m) (x0 - G.xstar),
          real_inner_comm (G.smoothGradient G.xstar) (x0 - G.xstar)]
      rw [hsplit]
      ring
    rw [hid]
    have hms : ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 / (32 * L) ≤
        W / (16 * L) + L * R ^ 2 / 16 := by
      apply (div_le_iff₀ (show 0 < 32 * L by positivity)).2
      have hid : (W / (16 * L) + L * R ^ 2 / 16) * (32 * L) =
          2 * W + 2 * L ^ 2 * R ^ 2 := by
        field_simp [ne_of_gt hL]
        <;> ring
      rw [hid]
      exact hm
    have hrs := mul_le_mul_of_nonneg_left hsq (show 0 ≤ L / 8 by positivity)
    have hc : -⟪x0 - G.xstar, workerMean m - G.smoothGradient G.xstar⟫_ℝ / 8 ≤
        L / 8 * ‖x0 - G.xstar‖ ^ 2 +
          ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 / (32 * L) := by
      convert div_le_div_of_nonneg_right hcross (by norm_num : (0 : ℝ) ≤ 8) using 1 <;> ring
    ring_nf at hc hms hrs hψ0 ⊢
    linarith only [hc, hms, hrs, hψ0]
  have hgap := G.regularized_gap (show 0 < 2 * L by positivity) (le_refl _) x0
  have hgap' : Q.gap x0 ≤ G.gap x0 + L * R ^ 2 := by
    change (G.regularized (2 * L) (by linarith [G.hL]) (by rfl)).gap x0 ≤ _
    rw [hgap]
    have hrs := mul_le_mul_of_nonneg_left hsq G.hL.le
    nlinarith only [hrs]
  have hmodelScaled := div_le_div_of_nonneg_right hmodel' (show 0 ≤ (2 * L) * τ by positivity)
  have hWScaled := div_le_div_of_nonneg_right hW (show 0 ≤ 64 * (3 * L) by positivity)
  have hVScaled := div_le_div_of_nonneg_right hV (show 0 ≤ 2 * L by positivity)
  have hexp : Q.potential τ x0 m v ≤
      G.gap x0 + L * R ^ 2 + (3 * L * R ^ 2 / 16 + W / (16 * L)) +
      (G.gap x0 + τ * (W + L ^ 2 * R ^ 2)) / ((2 * L) * τ) +
      V / (2 * L) + (2 * W + 2 * L ^ 2 * R ^ 2) / (64 * (3 * L)) := by
    change Q.gap x0 -
      (G.ψ x0 - G.ψ G.xstar + ⟪workerMean m, x0 - G.xstar⟫_ℝ) / 8 +
      modelDecrease G.ψ τ x0 (workerMean m) (Q.auxiliary τ x0 m) / ((2 * L) * τ) +
      Q.V m v / (2 * L) + Q.W m / (64 * (3 * L)) ≤ _
    linarith only [hgap', hcross', hmodelScaled, hWScaled, hVScaled]
  have hid : G.gap x0 + L * R ^ 2 + (3 * L * R ^ 2 / 16 + W / (16 * L)) +
      (G.gap x0 + τ * (W + L ^ 2 * R ^ 2)) / ((2 * L) * τ) +
      V / (2 * L) + (2 * W + 2 * L ^ 2 * R ^ 2) / (64 * (3 * L)) =
      6145 * G.gap x0 + (163 / 96 : ℝ) * L * R ^ 2 +
        (55 / 96 : ℝ) * W / L + V / (2 * L) := by
    dsimp [τ]
    field_simp [ne_of_gt G.hL]
    <;> ring
  rw [hid] at hexp
  have hΔ0 := G.base_gap_nonnegative x0 hx0
  have hLR : 0 ≤ L * R ^ 2 := by positivity
  have hWL : 0 ≤ W / L := by positivity
  have hVL : 0 ≤ V / L := by positivity
  change Q.potential τ x0 m v ≤ 8192 * (G.gap x0 + L * R ^ 2 + (V + W) / L)
  rw [add_div]
  have hidV : V / (2 * L) = (V / L) / 2 := by ring
  rw [hidV] at hexp
  ring_nf at hexp hΔ0 hLR hWL hVL ⊢
  linarith only [hexp, hΔ0, hLR, hWL, hVL]

end LongTails.Proofs.ProximalEf21Initialization

end

end Initialization


section StochasticContraction

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21StochasticContraction

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21FunctionalCalculus
open LongTails.Proofs.ProximalEf21FunctionalBounds
open LongTails.Proofs.ProximalEf21EnergyComparison
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21MomentCalculus

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [mΩ : MeasurableSpace Ω]

section ConditionalStep

lemma expected_functional_change (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (F ψ : E → ℝ) {μ τ γ α variance : ℝ}
    (hμ : 0 < μ) (hτ : 0 < τ) (hα : α = μ * γ)
    (xstar x y m z g b : E) (mnext znext ζ : Ω → E)
    (hζ : Integrable ζ P)
    (hζsq : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hζzero : (∫ ω, ζ ω ∂P) = 0)
    (hζvariance : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance)
    (hE : Integrable (fun ω => functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω)) P)
    (hupdate : ∀ᵐ ω ∂P, mnext ω = m + α • (g - m + b + ζ ω))
    (hsmooth : F y - F x ≤ -⟪g, x - y⟫_ℝ - μ / 2 * ‖y - x‖ ^ 2)
    (hsupport : ∀ᵐ ω ∂P,
      ψ z + ⟪τ⁻¹ • (x - z) - m, znext ω - z⟫_ℝ ≤ ψ (znext ω)) :
    (∫ ω, functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω) ∂P) -
        functionalEnergy F ψ μ τ xstar x m z ≤
      componentBound F ψ μ τ γ α xstar x y m z g b +
        μ * γ ^ 2 / 2 * variance := by
  have hi₁ : Integrable (fun ω => ⟪x - z, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (x - z) hζ
  have hi₂ : Integrable (fun ω => ⟪y - xstar, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (y - xstar) hζ
  have hi₃ : Integrable (fun ω => ⟪g - m + b, ζ ω⟫_ℝ) P :=
    Integrable.const_inner (g - m + b) hζ
  have hz₁ : (∫ ω, ⟪x - z, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hz₂ : (∫ ω, ⟪y - xstar, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hz₃ : (∫ ω, ⟪g - m + b, ζ ω⟫_ℝ ∂P) = 0 := by
    rw [integral_inner hζ, hζzero, inner_zero_right]
  have hpoint : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar y (mnext ω) (znext ω) -
          functionalEnergy F ψ μ τ xstar x m z ≤
        componentBound F ψ μ τ γ α xstar x y m z g b +
          γ / τ * ⟪x - z, ζ ω⟫_ℝ - α / 8 * ⟪y - xstar, ζ ω⟫_ℝ +
          μ * γ ^ 2 * ⟪g - m + b, ζ ω⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ ω‖ ^ 2 := by
    filter_upwards [hupdate, hsupport] with ω hu hs
    exact functional_change_with_noise F ψ hμ hτ hα
      xstar x y m (mnext ω) z (znext ω) g b (ζ ω) hu hsmooth hs
  have hleft := hE.sub (integrable_const (functionalEnergy F ψ μ τ xstar x m z))
  have hconstant : Integrable
      (fun _ : Ω => componentBound F ψ μ τ γ α xstar x y m z g b) P :=
    integrable_const _
  have hprefix := hconstant.add (hi₁.const_mul (γ / τ))
  have hprefixSub := hprefix.sub (hi₂.const_mul (α / 8))
  have hright := hprefixSub.add (hi₃.const_mul (μ * γ ^ 2))
  have hright' := hright.add (hζsq.const_mul (μ * γ ^ 2 / 2))
  have h := integral_mono_ae hleft hright' hpoint
  rw [integral_sub' hE (integrable_const _)] at h
  rw [integral_add' hright (hζsq.const_mul (μ * γ ^ 2 / 2)),
    integral_add' hprefixSub (hi₃.const_mul (μ * γ ^ 2)),
    integral_sub' hprefix (hi₂.const_mul (α / 8)),
    integral_add' hconstant (hi₁.const_mul (γ / τ))] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, hz₁, hz₂, hz₃, mul_zero, add_zero, sub_zero] at h
  have hv := mul_le_mul_of_nonneg_left hζvariance
    (show 0 ≤ μ * γ ^ 2 / 2 by positivity)
  linarith

end ConditionalStep

lemma weighted_momentum_recurrence {n : ℕ} (hn : 0 < n)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (filtration : MeasurableSpace Ω) (hfiltration : filtration ≤ mΩ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (m g ζ mnext : Fin n → Ω → E) (gstar : Fin n → E) (b : E)
    {α M variance gap : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hvariance : 0 ≤ variance)
    (hm : ∀ i, MemLp (m i) 2 P) (hg : ∀ i, MemLp (g i) 2 P)
    (hζ : ∀ i, MemLp (ζ i) 2 P) (hmnext : ∀ i, MemLp (mnext i) 2 P)
    (hpm : ∀ i, AEStronglyMeasurable[filtration] (m i) P)
    (hpg : ∀ i, AEStronglyMeasurable[filtration] (g i) P)
    (hcentered : ∀ i, condExp filtration P (ζ i) =ᵐ[P] (fun _ => 0))
    (hvar : ∀ i, ∀ᵐ ω ∂P,
      condExp filtration P (fun ω' => ‖ζ i ω'‖ ^ 2) ω ≤ variance)
    (hupdate : ∀ i, ∀ᵐ ω ∂P,
      mnext i ω = (1 - α) • m i ω + α • (g i ω + b + ζ i ω))
    (hinterpolation : (n : ℝ)⁻¹ * ∑ i,
      w i * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) ≤ 2 * M * gap) :
    (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖mnext i ω - gstar i‖ ^ 2 ∂P) ≤
      (1 - α) * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P)) +
      4 * α * M * gap + 2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
  have hi (i : Fin n) :
      (∫ ω, ‖mnext i ω - gstar i‖ ^ 2 ∂P) ≤
        (1 - α) * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P) +
        2 * α * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) +
        2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
    let u : Ω → E := fun ω =>
      (1 - α) • m i ω + α • (g i ω + b) - gstar i
    have hu : MemLp u 2 P :=
      (((hm i).const_smul (1 - α)).add
        (((hg i).add (memLp_const b)).const_smul α)).sub (memLp_const (gstar i))
    have hpu : AEStronglyMeasurable[filtration] u P :=
      (((hpm i).const_smul (1 - α)).add
        (((hpg i).add aestronglyMeasurable_const).const_smul α)).sub
          aestronglyMeasurable_const
    have hnoise := square_integral_add_fresh_noise (mΩ := mΩ) P filtration hfiltration
      u (ζ i) α variance hu (hζ i) hpu (hcentered i) (hvar i)
    have hid : (fun ω => ‖mnext i ω - gstar i‖ ^ 2) =ᵐ[P]
        (fun ω => ‖u ω + α • ζ i ω‖ ^ 2) := by
      filter_upwards [hupdate i] with ω hω
      rw [hω]
      congr 1
      dsimp [u]
      simp only [smul_add]
      abel
    have hmi : Integrable (fun ω => ‖m i ω - gstar i‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm
        ((hm i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
        ((hm i).sub (memLp_const (gstar i)))
    have hgi : Integrable (fun ω => ‖g i ω - gstar i‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm
        ((hg i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
        ((hg i).sub (memLp_const (gstar i)))
    have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
    have hr := ((hmi.const_mul (1 - α)).add (hgi.const_mul (2 * α))).add
      (integrable_const (2 * α * ‖b‖ ^ 2))
    have hdet := integral_mono hui hr (fun ω =>
      momentum_square_bound α hα hα1 (m i ω) (g i ω) (gstar i) b)
    rw [integral_add' ((hmi.const_mul (1 - α)).add (hgi.const_mul (2 * α)))
      (integrable_const (2 * α * ‖b‖ ^ 2)),
      integral_add' (hmi.const_mul (1 - α)) (hgi.const_mul (2 * α)),
      integral_const_mul, integral_const_mul] at hdet
    simp only [integral_const, probReal_univ, smul_eq_mul] at hdet
    rw [integral_congr_ae hid]
    linarith
  have hsum := weighted_sum_le w hw _ _ hi
  have hconst := weighted_constant_le hn w hw1
    (show 0 ≤ 2 * α * ‖b‖ ^ 2 + α ^ 2 * variance by positivity)
  have hq := mul_le_mul_of_nonneg_left hinterpolation
    (show 0 ≤ 2 * α by positivity)
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have hrew (a : ℝ) (u : Fin n → ℝ) :
      (n : ℝ)⁻¹ * ∑ i, w i * (a * u i) =
      a * ((n : ℝ)⁻¹ * ∑ i, w i * u i) := by
    simp only [show ∀ i, w i * (a * u i) = a * (w i * u i) by intro i; ring,
      ← Finset.mul_sum]
    ring
  simp only [hrew] at hsum
  have hc : (n : ℝ)⁻¹ * ∑ i, w i * (2 * α * ‖b‖ ^ 2) +
      (n : ℝ)⁻¹ * ∑ i, w i * (α ^ 2 * variance) ≤
      2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
    simpa only [mul_add, Finset.sum_add_distrib] using hconst
  simp only [hrew] at hc
  apply sub_nonneg.mp
  calc
    (0 : ℝ) ≤ _ := sub_nonneg.mpr (add_le_add (add_le_add hsum hq) hc)
    _ = _ := by ring

lemma weighted_compression_recurrence {n : ℕ} (hn : 0 < n)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (filtration : MeasurableSpace Ω) (hfiltration : filtration ≤ mΩ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (m v g ζ mnext vnext : Fin n → Ω → E) (gstar : Fin n → E) (b : E)
    {α δ M variance gap : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvariance : 0 ≤ variance)
    (hm : ∀ i, MemLp (m i) 2 P) (hv : ∀ i, MemLp (v i) 2 P)
    (hg : ∀ i, MemLp (g i) 2 P) (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hpm : ∀ i, AEStronglyMeasurable[filtration] (m i) P)
    (hpv : ∀ i, AEStronglyMeasurable[filtration] (v i) P)
    (hpg : ∀ i, AEStronglyMeasurable[filtration] (g i) P)
    (hcentered : ∀ i, condExp filtration P (ζ i) =ᵐ[P] (fun _ => 0))
    (hvar : ∀ i, ∀ᵐ ω ∂P,
      condExp filtration P (fun ω' => ‖ζ i ω'‖ ^ 2) ω ≤ variance)
    (hupdate : ∀ i, ∀ᵐ ω ∂P,
      mnext i ω = (1 - α) • m i ω + α • (g i ω + b + ζ i ω))
    (hcontractive : ∀ i,
      (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
        (1 - δ) * (∫ ω, ‖mnext i ω - v i ω‖ ^ 2 ∂P))
    (hinterpolation : (n : ℝ)⁻¹ * ∑ i,
      w i * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) ≤ 2 * M * gap) :
    (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
      (1 - δ / 2) * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖v i ω - m i ω‖ ^ 2 ∂P)) +
      6 * α ^ 2 / δ * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P)) +
      12 * α ^ 2 * M / δ * gap + 6 * α ^ 2 / δ * ‖b‖ ^ 2 +
      α ^ 2 * variance := by
  have hi (i : Fin n) :
      (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
        (1 - δ / 2) * (∫ ω, ‖v i ω - m i ω‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance := by
    let u : Ω → E := fun ω => m i ω - v i ω + α • (g i ω - m i ω + b)
    have hu : MemLp u 2 P := ((hm i).sub (hv i)).add
      ((((hg i).sub (hm i)).add (memLp_const b)).const_smul α)
    have hpu : AEStronglyMeasurable[filtration] u P := ((hpm i).sub (hpv i)).add
      ((((hpg i).sub (hpm i)).add aestronglyMeasurable_const).const_smul α)
    have hnoise := square_integral_add_fresh_noise (mΩ := mΩ) P filtration hfiltration
      u (ζ i) α variance hu (hζ i) hpu (hcentered i) (hvar i)
    have hid : (fun ω => ‖mnext i ω - v i ω‖ ^ 2) =ᵐ[P]
        (fun ω => ‖u ω + α • ζ i ω‖ ^ 2) := by
      filter_upwards [hupdate i] with ω hω
      rw [hω]
      congr 1
      dsimp [u]
      simp only [smul_add, smul_sub, sub_smul, one_smul]
      abel
    have hmi : Integrable (fun ω => ‖m i ω - gstar i‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm
        ((hm i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
        ((hm i).sub (memLp_const (gstar i)))
    have hgi : Integrable (fun ω => ‖g i ω - gstar i‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm
        ((hg i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
        ((hg i).sub (memLp_const (gstar i)))
    have hvi : Integrable (fun ω => ‖v i ω - m i ω‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm
        ((hv i).sub (hm i)).aestronglyMeasurable).mp ((hv i).sub (hm i))
    have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
    have hr := (hvi.const_mul (1 - δ / 2)).add
      (((hmi.add hgi).add (integrable_const (‖b‖ ^ 2))).const_mul (6 * α ^ 2 / δ))
    have hdet := integral_mono (hui.const_mul (1 - δ)) hr (fun ω =>
      compression_square_bound δ α hδ hδ1 (m i ω) (v i ω)
        (g i ω) (gstar i) b)
    rw [integral_const_mul,
      integral_add' (hvi.const_mul (1 - δ / 2))
        (((hmi.add hgi).add (integrable_const (‖b‖ ^ 2))).const_mul (6 * α ^ 2 / δ)),
      integral_const_mul, integral_const_mul,
      integral_add' (hmi.add hgi) (integrable_const (‖b‖ ^ 2)),
      integral_add' hmi hgi] at hdet
    simp only [integral_const, probReal_univ, smul_eq_mul] at hdet
    have hscale := mul_le_mul_of_nonneg_left hnoise (sub_nonneg.mpr hδ1)
    have hnoiseDrop : (1 - δ) * (α ^ 2 * variance) ≤ α ^ 2 * variance := by
      nlinarith [mul_nonneg (le_of_lt hδ) (mul_nonneg (sq_nonneg α) hvariance)]
    have hc := hcontractive i
    rw [integral_congr_ae hid] at hc
    ring_nf at hc hscale hdet hnoiseDrop ⊢
    linarith only [hc, hscale, hdet, hnoiseDrop]
  have hsum := weighted_sum_le w hw _ _ hi
  have hconst := weighted_constant_le hn w hw1
    (show 0 ≤ 6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance by positivity)
  have hq := mul_le_mul_of_nonneg_left hinterpolation
    (show 0 ≤ 6 * α ^ 2 / δ by positivity)
  have hrew (a : ℝ) (u : Fin n → ℝ) :
      (n : ℝ)⁻¹ * ∑ i, w i * (a * u i) =
      a * ((n : ℝ)⁻¹ * ∑ i, w i * u i) := by
    simp only [show ∀ i, w i * (a * u i) = a * (w i * u i) by intro i; ring,
      ← Finset.mul_sum]
    ring
  simp only [mul_add, Finset.sum_add_distrib, hrew] at hsum
  have hc : (n : ℝ)⁻¹ * ∑ i, w i * (6 * α ^ 2 / δ * ‖b‖ ^ 2) +
      (n : ℝ)⁻¹ * ∑ i, w i * (α ^ 2 * variance) ≤
      6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance := by
    simpa only [mul_add, Finset.sum_add_distrib] using hconst
  simp only [hrew] at hc
  apply sub_nonneg.mp
  calc
    (0 : ℝ) ≤ _ := sub_nonneg.mpr (add_le_add (add_le_add hsum hq) hc)
    _ = _ := by ring

lemma integrated_functional_progress
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (F ψ : E → ℝ) {μ M τ γ α variance : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096) (hα : α = μ * γ)
    (xstar gstar b : E) (x y m v z g mnext znext ζ : Ω → E)
    (W V : Ω → ℝ)
    (hW0 : ∀ᵐ ω ∂P, 0 ≤ W ω) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hW : Integrable W P) (hV : Integrable V P)
    (hE0 : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω)) P)
    (hE1 : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω)) P)
    (hgap : Integrable (fun ω => F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) P)
    (hdisp : Integrable (fun ω => ‖y ω - x ω‖ ^ 2) P)
    (hrem1 : Integrable (fun ω =>
      ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) P)
    (hrem2 : Integrable (fun ω =>
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) P)
    (hi1 : Integrable (fun ω => ⟪x ω - z ω, ζ ω⟫_ℝ) P)
    (hi2 : Integrable (fun ω => ⟪y ω - xstar, ζ ω⟫_ℝ) P)
    (hi3 : Integrable (fun ω => ⟪g ω - m ω + b, ζ ω⟫_ℝ) P)
    (hζsq : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hz1 : (∫ ω, ⟪x ω - z ω, ζ ω⟫_ℝ ∂P) = 0)
    (hz2 : (∫ ω, ⟪y ω - xstar, ζ ω⟫_ℝ ∂P) = 0)
    (hz3 : (∫ ω, ⟪g ω - m ω + b, ζ ω⟫_ℝ ∂P) = 0)
    (hvariance : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance)
    (hupdate : ∀ᵐ ω ∂P,
      mnext ω = m ω + α • (g ω - m ω + b + ζ ω))
    (hsmooth : ∀ᵐ ω ∂P,
      F (y ω) - F (x ω) ≤ -⟪g ω, x ω - y ω⟫_ℝ - μ / 2 * ‖y ω - x ω‖ ^ 2)
    (hsupport : ∀ᵐ ω ∂P,
      ψ (z ω) + ⟪τ⁻¹ • (x ω - z ω) - m ω, znext ω - z ω⟫_ℝ ≤ ψ (znext ω))
    (hD : ∀ᵐ ω ∂P, 0 ≤
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ)
    (hstrong : ∀ᵐ ω ∂P,
      F (y ω) + ⟪g ω, xstar - y ω⟫_ℝ + μ / 2 * ‖xstar - y ω‖ ^ 2 ≤ F xstar)
    (hmono : ∀ᵐ ω ∂P, 0 ≤
      ⟪γ⁻¹ • (x ω - y ω) - v ω - (τ⁻¹ • (x ω - z ω) - m ω), y ω - z ω⟫_ℝ)
    (hgrad : ∀ᵐ ω ∂P, ‖g ω - gstar‖ ^ 2 ≤
      2 * M * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)))
    (hmemory : ∀ᵐ ω ∂P, ‖m ω - gstar‖ ^ 2 ≤ 2 * W ω)
    (hcompression : ∀ᵐ ω ∂P, ‖v ω - m ω‖ ^ 2 ≤ 2 * V ω) :
    (∫ ω, functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω) ∂P) ≤
      (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) -
      α * (1 / 8 - 15 * M * τ / 2) *
        (∫ ω, F (y ω) + ψ (y ω) - (F xstar + ψ xstar) ∂P) -
      5 / (8 * γ) * (∫ ω, ‖y ω - x ω‖ ^ 2 ∂P) -
      α / 8 * (∫ ω,
        ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar ∂P) -
      1 / (μ * τ) * (∫ ω,
        ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ ∂P) +
      15 * α * τ / 2 * (∫ ω, W ω ∂P) + 5 * γ / (μ * τ) * (∫ ω, V ω ∂P) +
      5 * γ * ‖b‖ ^ 2 + μ * γ ^ 2 / 2 * variance := by
  let rhs : Ω → ℝ := fun ω =>
    -α * (1 / 8 - 15 * M * τ / 2) * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) -
    5 / (8 * γ) * ‖y ω - x ω‖ ^ 2 -
    α / 8 * (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) -
    1 / (μ * τ) * (ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) +
    15 * α * τ / 2 * W ω + 5 * γ / (μ * τ) * V ω + 5 * γ * ‖b‖ ^ 2 +
    γ / τ * ⟪x ω - z ω, ζ ω⟫_ℝ - α / 8 * ⟪y ω - xstar, ζ ω⟫_ℝ +
    μ * γ ^ 2 * ⟪g ω - m ω + b, ζ ω⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ ω‖ ^ 2
  have hpart1 := (hgap.const_mul (-α * (1 / 8 - 15 * M * τ / 2))).sub
    (hdisp.const_mul (5 / (8 * γ)))
  have hpart2 := hpart1.sub (hrem1.const_mul (α / 8))
  have hpart3 := hpart2.sub (hrem2.const_mul (1 / (μ * τ)))
  have hpart4 := hpart3.add (hW.const_mul (15 * α * τ / 2))
  have hpart5 := hpart4.add (hV.const_mul (5 * γ / (μ * τ)))
  have hpart6 := hpart5.add (integrable_const (5 * γ * ‖b‖ ^ 2))
  have hpart7 := hpart6.add (hi1.const_mul (γ / τ))
  have hpart8 := hpart7.sub (hi2.const_mul (α / 8))
  have hpart9 := hpart8.add (hi3.const_mul (μ * γ ^ 2))
  have hrhs : Integrable rhs P := hpart9.add (hζsq.const_mul (μ * γ ^ 2 / 2))
  have hp : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω) -
        functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ≤ rhs ω := by
    filter_upwards [hupdate, hsmooth, hsupport, hD, hstrong, hmono,
      hgrad, hmemory, hcompression, hW0, hV0] with ω hu hs hsu hd hst hmo hg hm hc hw hv
    have h1 := functional_change_with_noise F ψ hμ hτ hα
      xstar (x ω) (y ω) (m ω) (mnext ω) (z ω) (znext ω) (g ω) b (ζ ω) hu hs hsu
    have h2 := pointwise_functional_progress F ψ hμ hM hτ hγ hγτ hμτ hα hw hv
      xstar (x ω) (y ω) (m ω) (v ω) (z ω) (g ω) gstar b hd hst hmo hg hm hc
    dsimp [rhs]
    linarith only [h1, h2]
  have h := integral_mono_ae (hE1.sub hE0) hrhs hp
  rw [integral_sub' hE1 hE0] at h
  change
    (∫ ω, functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω) ∂P) -
        (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) ≤
      ∫ ω,
        (((((((((((fun ω : Ω =>
            -α * (1 / 8 - 15 * M * τ / 2) *
              (F (y ω) + ψ (y ω) - (F xstar + ψ xstar))) -
            (fun ω : Ω => 5 / (8 * γ) * ‖y ω - x ω‖ ^ 2)) -
            (fun ω : Ω => α / 8 *
              (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar))) -
            (fun ω : Ω => 1 / (μ * τ) *
              (ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ))) +
            (fun ω : Ω => 15 * α * τ / 2 * W ω)) +
            (fun ω : Ω => 5 * γ / (μ * τ) * V ω)) +
            (fun _ : Ω => 5 * γ * ‖b‖ ^ 2)) +
            (fun ω : Ω => γ / τ * ⟪x ω - z ω, ζ ω⟫_ℝ)) -
            (fun ω : Ω => α / 8 * ⟪y ω - xstar, ζ ω⟫_ℝ)) +
            (fun ω : Ω => μ * γ ^ 2 * ⟪g ω - m ω + b, ζ ω⟫_ℝ)) +
            (fun ω : Ω => μ * γ ^ 2 / 2 * ‖ζ ω‖ ^ 2) : Ω → ℝ) ω ∂P at h
  rw [integral_add' hpart9 (hζsq.const_mul (μ * γ ^ 2 / 2)),
    integral_add' hpart8 (hi3.const_mul (μ * γ ^ 2)),
    integral_sub' hpart7 (hi2.const_mul (α / 8)),
    integral_add' hpart6 (hi1.const_mul (γ / τ)),
    integral_add' hpart5 (integrable_const (5 * γ * ‖b‖ ^ 2)),
    integral_add' hpart4 (hV.const_mul (5 * γ / (μ * τ))),
    integral_add' hpart3 (hW.const_mul (15 * α * τ / 2)),
    integral_sub' hpart2 (hrem2.const_mul (1 / (μ * τ))),
    integral_sub' hpart1 (hrem1.const_mul (α / 8)),
    integral_sub' (hgap.const_mul (-α * (1 / 8 - 15 * M * τ / 2)))
      (hdisp.const_mul (5 / (8 * γ)))] at h
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul,
    one_mul, hz1, hz2, hz3, mul_zero, add_zero, sub_zero] at h
  have hv := mul_le_mul_of_nonneg_left hvariance
    (show 0 ≤ μ * γ ^ 2 / 2 by positivity)
  linarith

lemma integrated_upper_comparison
    (P : @Measure Ω mΩ) (F ψ : E → ℝ) {μ M τ γ : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hμM : μ ≤ M) (hμγ : μ * γ ≤ 1) (hμτ : μ * τ ≤ 1)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3)
    (xstar gstar : E) (x y m v z g : Ω → E) (W V : Ω → ℝ)
    (hE : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω)) P)
    (hgap : Integrable (fun ω => F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) P)
    (hdisp : Integrable (fun ω => ‖y ω - x ω‖ ^ 2) P)
    (hrem1 : Integrable (fun ω =>
      ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) P)
    (hrem2 : Integrable (fun ω =>
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) P)
    (hW : Integrable W P) (hV : Integrable V P)
    (hsupport : ∀ᵐ ω ∂P, ψ (y ω) +
      ⟪γ⁻¹ • (x ω - y ω) - v ω, z ω - y ω⟫_ℝ ≤ ψ (z ω))
    (hD : ∀ᵐ ω ∂P, 0 ≤ ψ (x ω) - ψ (y ω) -
      ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ)
    (hdistance : ∀ᵐ ω ∂P, μ / 2 * ‖y ω - xstar‖ ^ 2 ≤
      F (y ω) + ψ (y ω) - (F xstar + ψ xstar))
    (hsmooth : ∀ᵐ ω ∂P,
      F (x ω) ≤ F (y ω) + ⟪g ω, x ω - y ω⟫_ℝ + M / 2 * ‖x ω - y ω‖ ^ 2)
    (hgrad : ∀ᵐ ω ∂P, ‖g ω - gstar‖ ^ 2 ≤
      2 * M * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)))
    (hmemory : ∀ᵐ ω ∂P, ‖m ω - gstar‖ ^ 2 ≤ 2 * W ω)
    (hcompression : ∀ᵐ ω ∂P, ‖v ω - m ω‖ ^ 2 ≤ 2 * V ω) :
    (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) ≤
      3 * (∫ ω, F (y ω) + ψ (y ω) - (F xstar + ψ xstar) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖y ω - x ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ ∂P) +
      (∫ ω, W ω ∂P) / M + 4 / μ * (∫ ω, V ω ∂P) := by
  have hpart1 := (hgap.const_mul 3).add (hdisp.const_mul (5 / (μ * γ ^ 2)))
  have hpart2 := hpart1.add (hrem1.div_const 8)
  have hpart3 := hpart2.add (hrem2.const_mul (2 / (μ * τ)))
  have hpart4 := hpart3.add (hW.div_const M)
  have hr : Integrable (fun ω =>
      3 * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) +
      5 / (μ * γ ^ 2) * ‖y ω - x ω‖ ^ 2 +
      (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) / 8 +
      2 / (μ * τ) * (ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) + W ω / M + 4 / μ * V ω) P :=
    hpart4.add (hV.const_mul (4 / μ))
  have hp : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ≤
      3 * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) +
      5 / (μ * γ ^ 2) * ‖y ω - x ω‖ ^ 2 +
      (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) / 8 +
      2 / (μ * τ) * (ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) + W ω / M + 4 / μ * V ω := by
    filter_upwards [hsupport, hD, hdistance, hsmooth, hgrad, hmemory,
      hcompression] with ω hs hd hdi hsm hg hm hc
    exact functional_upper_comparison F ψ hμ hM hτ hγ hμM hμγ hμτ hsmall
      xstar (x ω) (y ω) (m ω) (v ω) (z ω) (g ω) gstar hs hd hdi hsm hg hm hc
  have h := integral_mono_ae hE hr hp
  change
    (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) ≤
      ∫ ω,
        ((((((fun ω : Ω => 3 * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar))) +
            (fun ω : Ω => 5 / (μ * γ ^ 2) * ‖y ω - x ω‖ ^ 2)) +
            (fun ω : Ω =>
              (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) / 8)) +
            (fun ω : Ω => 2 / (μ * τ) *
              (ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ))) +
            (fun ω : Ω => W ω / M)) +
            (fun ω : Ω => 4 / μ * V ω) : Ω → ℝ) ω ∂P at h
  rw [integral_add' hpart4 (hV.const_mul (4 / μ)),
    integral_add' hpart3 (hW.div_const M),
    integral_add' hpart2 (hrem2.const_mul (2 / (μ * τ))),
    integral_add' hpart1 (hrem1.div_const 8),
    integral_add' (hgap.const_mul 3) (hdisp.const_mul (5 / (μ * γ ^ 2)))] at h
  simpa only [integral_const_mul, integral_div] using h

end LongTails.Proofs.ProximalEf21StochasticContraction

end

end StochasticContraction


section InnerTrajectory

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21InnerTrajectory

open LongTails.Proofs.ProximalEf21AverageMoments

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21StochasticContraction
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21ScalarCore
open LongTails.Proofs.ProximalEf21Schedule

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} {μ M τ γ δ variance : ℝ}

structure Trajectory (P : @Measure Ω mΩ) (G : InnerGeometry (E := E) n μ M)
    (τ γ δ variance : ℝ) (b : E) where
  x : ℕ → Ω → E
  m : ℕ → Fin n → Ω → E
  v : ℕ → Fin n → Ω → E
  noise : ℕ → Fin n → Ω → E
  correction : ℕ → Fin n → Ω → E
  beforeSample : ℕ → MeasurableSpace Ω
  beforeCompress : ℕ → MeasurableSpace Ω
  beforeSample_le : ∀ t, beforeSample t ≤ mΩ
  beforeCompress_le : ∀ t, beforeCompress t ≤ mΩ
  sample_before_compress : ∀ t, beforeSample t ≤ beforeCompress t
  feasible : ∀ t, ∀ᵐ ω ∂P, x t ω ∈ G.domain
  proximal_update : ∀ t, ∀ᵐ ω ∂P,
    x (t + 1) ω = G.prox γ (x t ω - γ • workerMean (fun i => v t i ω))
  momentum_update : ∀ t i, ∀ᵐ ω ∂P,
    m (t + 1) i ω = (1 - μ * γ) • m t i ω +
      (μ * γ) • (G.grad i (x (t + 1) ω) + b + noise t i ω)
  compression_update : ∀ t i, ∀ᵐ ω ∂P,
    v (t + 1) i ω = v t i ω + correction t i ω
  centered_noise : ∀ t i,
    condExp (beforeSample t) P (noise t i) =ᵐ[P] (fun _ => 0)
  variance_bound : ∀ t i, ∀ᵐ ω ∂P,
    condExp (beforeSample t) P (fun ω' => ‖noise t i ω'‖ ^ 2) ω ≤ variance
  contractive_compression : ∀ t i, ∀ᵐ ω ∂P,
    condExp (beforeCompress t) P (fun ω' =>
      ‖correction t i ω' - (m (t + 1) i ω' - v t i ω')‖ ^ 2) ω ≤
      (1 - δ) * ‖m (t + 1) i ω - v t i ω‖ ^ 2
  x_lp : ∀ t, MemLp (x t) 2 P
  m_lp : ∀ t i, MemLp (m t i) 2 P
  v_lp : ∀ t i, MemLp (v t i) 2 P
  noise_lp : ∀ t i, MemLp (noise t i) 2 P
  gradient_lp : ∀ t i, MemLp (fun ω => G.grad i (x (t + 1) ω)) 2 P
  auxiliary_lp : ∀ t, MemLp
    (fun ω => G.auxiliary τ (x t ω) (fun i => m t i ω)) 2 P
  gap_integrable : ∀ t, Integrable (fun ω => G.gap (x t ω)) P
  regularizer_integrable : ∀ t, Integrable (fun ω => G.ψ (x t ω)) P
  auxiliary_regularizer_integrable : ∀ t, Integrable
    (fun ω => G.ψ (G.auxiliary τ (x t ω) (fun i => m t i ω))) P
  x_predictable : ∀ t, AEStronglyMeasurable[beforeSample t] (x t) P
  next_x_predictable : ∀ t, AEStronglyMeasurable[beforeSample t] (x (t + 1)) P
  m_predictable : ∀ t i, AEStronglyMeasurable[beforeSample t] (m t i) P
  v_predictable : ∀ t i, AEStronglyMeasurable[beforeSample t] (v t i) P
  gradient_predictable : ∀ t i,
    AEStronglyMeasurable[beforeSample t] (fun ω => G.grad i (x (t + 1) ω)) P
  auxiliary_predictable : ∀ t, AEStronglyMeasurable[beforeSample t]
    (fun ω => G.auxiliary τ (x t ω) (fun i => m t i ω)) P

namespace Trajectory

variable (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
variable (G : InnerGeometry (E := E) n μ M) (b : E)
variable (r : Trajectory P G τ γ δ variance b)

lemma m_mean_lp (t : ℕ) :
    MemLp (fun ω => workerMean (fun i => r.m t i ω)) 2 P :=
  workerMean_memLp (mΩ := mΩ) P (r.m t) (r.m_lp t)

lemma v_mean_lp (t : ℕ) :
    MemLp (fun ω => workerMean (fun i => r.v t i ω)) 2 P :=
  workerMean_memLp (mΩ := mΩ) P (r.v t) (r.v_lp t)

lemma gradient_mean_lp (t : ℕ) :
    MemLp (fun ω => G.smoothGradient (r.x (t + 1) ω)) 2 P :=
  workerMean_memLp (mΩ := mΩ) P _ (r.gradient_lp t)

lemma W_integrable (t : ℕ) :
    Integrable (fun ω => G.W (fun i => r.m t i ω)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.m_lp t i).sub (memLp_const (G.grad i G.xstar))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma V_integrable (t : ℕ) :
    Integrable (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.v_lp t i).sub (r.m_lp t i)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma model_integrable (t : ℕ) :
    Integrable (fun ω => modelDecrease G.ψ τ (r.x t ω)
      (workerMean (fun i => r.m t i ω))
      (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))) P := by
  have hdiff := (r.auxiliary_lp t).sub (r.x_lp t)
  have hi := integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (r.m_mean_lp P G b t) hdiff
  have hs := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  exact (((r.regularizer_integrable t).sub (r.auxiliary_regularizer_integrable t)).sub hi).sub
    (hs.div_const (2 * τ))

lemma energy_integrable (t : ℕ) :
    Integrable (fun ω => G.energy τ (r.x t ω) (fun i => r.m t i ω)) P := by
  have hi := integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (r.m_mean_lp P G b t)
    ((r.x_lp t).sub (memLp_const G.xstar))
  exact ((r.gap_integrable t).sub
    ((((r.regularizer_integrable t).sub (integrable_const _)).add hi).div_const 8)).add
      ((r.model_integrable P G b t).div_const (μ * τ))

lemma potential_integrable (t : ℕ) :
    Integrable (fun ω => G.potential τ (r.x t ω)
      (fun i => r.m t i ω) (fun i => r.v t i ω)) P := by
  exact ((r.energy_integrable P G b t).add ((r.V_integrable P G b t).div_const μ)).add
    ((r.W_integrable P G b t).div_const (64 * M))

lemma integral_potential (t : ℕ) :
    (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) =
      (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) +
      (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) / μ +
      (∫ ω, G.W (fun i => r.m t i ω) ∂P) / (64 * M) := by
  unfold InnerGeometry.potential
  rw [integral_add
    (f := fun ω => G.energy τ (r.x t ω) (fun i => r.m t i ω) +
      G.V (fun i => r.m t i ω) (fun i => r.v t i ω) / μ)
    (g := fun ω => G.W (fun i => r.m t i ω) / (64 * M))
    ((r.energy_integrable P G b t).add ((r.V_integrable P G b t).div_const μ))
    ((r.W_integrable P G b t).div_const (64 * M))]
  rw [integral_add
    (f := fun ω => G.energy τ (r.x t ω) (fun i => r.m t i ω))
    (g := fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω) / μ)
    (r.energy_integrable P G b t) ((r.V_integrable P G b t).div_const μ),
    integral_div, integral_div]

lemma displacement_integrable (t : ℕ) :
    Integrable (fun ω => ‖r.x (t + 1) ω - r.x t ω‖ ^ 2) P := by
  have h := (r.x_lp (t + 1)).sub (r.x_lp t)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma proximal_subgradient_lp (t : ℕ) :
    MemLp (fun ω => γ⁻¹ • (r.x t ω - r.x (t + 1) ω) -
      workerMean (fun i => r.v t i ω)) 2 P :=
  ((((r.x_lp t).sub (r.x_lp (t + 1))).const_smul γ⁻¹).sub
    (r.v_mean_lp P G b t))

lemma first_remainder_integrable (t : ℕ) :
    Integrable (fun ω =>
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar) P := by
  have hi := integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (r.proximal_subgradient_lp P G b t)
    ((r.x_lp (t + 1)).sub (memLp_const G.xstar))
  exact (hi.sub (r.regularizer_integrable (t + 1))).add (integrable_const _)

lemma second_remainder_integrable (t : ℕ) :
    Integrable (fun ω => G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x t ω - r.x (t + 1) ω⟫_ℝ) P := by
  have hi := integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (r.proximal_subgradient_lp P G b t)
    ((r.x_lp t).sub (r.x_lp (t + 1)))
  exact ((r.regularizer_integrable t).sub (r.regularizer_integrable (t + 1))).sub hi

lemma aggregate_momentum_update (t : ℕ) :
    ∀ᵐ ω ∂P,
      workerMean (fun i => r.m (t + 1) i ω) = workerMean (fun i => r.m t i ω) +
        (μ * γ) • (G.smoothGradient (r.x (t + 1) ω) -
          workerMean (fun i => r.m t i ω) + b + workerMean (fun i => r.noise t i ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, r.m (t + 1) i ω =
      (1 - μ * γ) • r.m t i ω +
        (μ * γ) • (G.grad i (r.x (t + 1) ω) + b + r.noise t i ω) :=
    ae_all_iff.mpr (r.momentum_update t)
  filter_upwards [hall] with ω hω
  simp_rw [hω]
  exact workerMean_momentum G.hn (μ * γ) _ _ _ b

lemma aggregate_gradient_integrable (t : ℕ) :
    Integrable (fun ω => weightedSquare G.weights
      (fun i => G.grad i (r.x (t + 1) ω) - G.grad i G.xstar)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma integral_gradient_interpolation (t : ℕ) :
    (n : ℝ)⁻¹ * ∑ i, G.weights i *
      (∫ ω, ‖G.grad i (r.x (t + 1) ω) - G.grad i G.xstar‖ ^ 2 ∂P) ≤
      2 * M * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) := by
  have hp : ∀ᵐ ω ∂P, weightedSquare G.weights
      (fun i => G.grad i (r.x (t + 1) ω) - G.grad i G.xstar) ≤
      2 * M * G.gap (r.x (t + 1) ω) := by
    filter_upwards [r.feasible (t + 1)] with ω hω
    exact G.weighted_gradient_interpolation (r.x (t + 1) ω) hω
  have h := integral_mono_ae (r.aggregate_gradient_integrable P G b t)
    ((r.gap_integrable (t + 1)).const_mul (2 * M)) hp
  rw [integral_const_mul] at h
  rw [integral_weightedSquare (mΩ := mΩ) P G.weights
    (fun i ω => G.grad i (r.x (t + 1) ω) - G.grad i G.xstar) (fun i =>
    (memLp_two_iff_integrable_sq_norm
      ((r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
      ((r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))))] at h
  exact h

lemma integral_compression_contractiveness (t : ℕ) (i : Fin n) :
    (∫ ω, ‖r.v (t + 1) i ω - r.m (t + 1) i ω‖ ^ 2 ∂P) ≤
      (1 - δ) * (∫ ω, ‖r.m (t + 1) i ω - r.v t i ω‖ ^ 2 ∂P) := by
  have hi := ((r.m_lp (t + 1) i).sub (r.v_lp t i))
  have hisq := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have heq : (fun ω => ‖r.v (t + 1) i ω - r.m (t + 1) i ω‖ ^ 2) =ᵐ[P]
      (fun ω => ‖r.correction t i ω - (r.m (t + 1) i ω - r.v t i ω)‖ ^ 2) := by
    filter_upwards [r.compression_update t i] with ω hω
    rw [hω]
    congr 1
    abel
  rw [integral_congr_ae heq]
  calc
    (∫ ω, ‖r.correction t i ω - (r.m (t + 1) i ω - r.v t i ω)‖ ^ 2 ∂P) =
        ∫ ω, condExp (r.beforeCompress t) P (fun ω' =>
          ‖r.correction t i ω' - (r.m (t + 1) i ω' - r.v t i ω')‖ ^ 2) ω ∂P :=
      (integral_condExp (μ := P) (f := fun ω =>
        ‖r.correction t i ω - (r.m (t + 1) i ω - r.v t i ω)‖ ^ 2)
        (r.beforeCompress_le t)).symm
    _ ≤ ∫ ω, (1 - δ) * ‖r.m (t + 1) i ω - r.v t i ω‖ ^ 2 ∂P :=
      integral_mono_ae integrable_condExp (hisq.const_mul _) (r.contractive_compression t i)
    _ = _ := integral_const_mul _ _

lemma momentum_recurrence (hα0 : 0 ≤ μ * γ) (hα1 : μ * γ ≤ 1)
    (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.W (fun i => r.m (t + 1) i ω) ∂P) ≤
      (1 - μ * γ) * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      4 * (μ * γ) * M * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      2 * (μ * γ) * ‖b‖ ^ 2 + (μ * γ) ^ 2 * variance := by
  have hw := weighted_momentum_recurrence (mΩ := mΩ) G.hn P (r.beforeSample t) (r.beforeSample_le t)
    G.weights (fun i => (G.weights_positive i).le) G.weights_le_one
    (r.m t) (fun i ω => G.grad i (r.x (t + 1) ω)) (r.noise t) (r.m (t + 1))
    (fun i => G.grad i G.xstar) b hα0 hα1 hvar
    (r.m_lp t) (r.gradient_lp t) (r.noise_lp t) (r.m_lp (t + 1))
    (r.m_predictable t) (r.gradient_predictable t) (r.centered_noise t)
    (r.variance_bound t) (r.momentum_update t) (r.integral_gradient_interpolation P G b t)
  have hW (k : ℕ) : (∫ ω, G.W (fun i => r.m k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.m k i ω - G.grad i G.xstar‖ ^ 2 ∂P) :=
    integral_weightedSquare (mΩ := mΩ) P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))))
  simpa only [hW] using hw

lemma compression_recurrence (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.V (fun i => r.m (t + 1) i ω) (fun i => r.v (t + 1) i ω) ∂P) ≤
      (1 - δ / 2) * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      6 * (μ * γ) ^ 2 / δ * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      12 * (μ * γ) ^ 2 * M / δ * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      6 * (μ * γ) ^ 2 / δ * ‖b‖ ^ 2 + (μ * γ) ^ 2 * variance := by
  have hv := weighted_compression_recurrence (mΩ := mΩ) G.hn P (r.beforeSample t) (r.beforeSample_le t)
    G.weights (fun i => (G.weights_positive i).le) G.weights_le_one
    (r.m t) (r.v t) (fun i ω => G.grad i (r.x (t + 1) ω))
    (r.noise t) (r.m (t + 1)) (r.v (t + 1)) (fun i => G.grad i G.xstar) b
    hδ hδ1 hvar (r.m_lp t) (r.v_lp t) (r.gradient_lp t) (r.noise_lp t)
    (r.m_predictable t) (r.v_predictable t) (r.gradient_predictable t)
    (r.centered_noise t) (r.variance_bound t) (r.momentum_update t)
    (r.integral_compression_contractiveness P G b t)
    (r.integral_gradient_interpolation P G b t)
  have hV (k : ℕ) : (∫ ω, G.V (fun i => r.m k i ω) (fun i => r.v k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.v k i ω - r.m k i ω‖ ^ 2 ∂P) :=
    integral_weightedSquare (mΩ := mΩ) P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.v_lp k i).sub (r.m_lp k i)).aestronglyMeasurable).mp
        ((r.v_lp k i).sub (r.m_lp k i)))
  have hW (k : ℕ) : (∫ ω, G.W (fun i => r.m k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.m k i ω - G.grad i G.xstar‖ ^ 2 ∂P) :=
    integral_weightedSquare (mΩ := mΩ) P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))))
  simpa only [hV, hW] using hv

lemma functional_progress (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096) (t : ℕ) :
    (∫ ω, G.energy τ (r.x (t + 1) ω) (fun i => r.m (t + 1) i ω) ∂P) ≤
      (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) -
      (μ * γ) * (1 / 8 - 15 * M * τ / 2) *
        (∫ ω, G.gap (r.x (t + 1) ω) ∂P) -
      5 / (8 * γ) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) -
      (μ * γ) / 8 * (∫ ω,
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) -
      1 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      15 * (μ * γ) * τ / 2 * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      5 * γ / (μ * τ) * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      5 * γ * ‖b‖ ^ 2 + μ * γ ^ 2 / 2 * variance := by
  let ζ : Ω → E := fun ω => workerMean (fun i => r.noise t i ω)
  have hζ := workerMean_memLp (mΩ := mΩ) P (r.noise t) (r.noise_lp t)
  have hζsq := (memLp_two_iff_integrable_sq_norm hζ.aestronglyMeasurable).mp hζ
  have hu1 : MemLp (fun ω => r.x t ω -
      G.auxiliary τ (r.x t ω) (fun i => r.m t i ω)) 2 P :=
    (r.x_lp t).sub (r.auxiliary_lp t)
  have hu2 : MemLp (fun ω => r.x (t + 1) ω - G.xstar) 2 P :=
    (r.x_lp (t + 1)).sub (memLp_const G.xstar)
  have hu3 : MemLp (fun ω => G.smoothGradient (r.x (t + 1) ω) -
      workerMean (fun i => r.m t i ω) + b) 2 P :=
    ((r.gradient_mean_lp P G b t).sub (r.m_mean_lp P G b t)).add (memLp_const b)
  have hp1 : AEStronglyMeasurable[r.beforeSample t] (fun ω => r.x t ω -
      G.auxiliary τ (r.x t ω) (fun i => r.m t i ω)) P :=
    (r.x_predictable t).fun_sub (r.auxiliary_predictable t)
  have hp2 : AEStronglyMeasurable[r.beforeSample t]
      (fun ω => r.x (t + 1) ω - G.xstar) P :=
    (r.next_x_predictable t).fun_sub
      (aestronglyMeasurable_const : AEStronglyMeasurable[r.beforeSample t]
        (fun _ : Ω => G.xstar) P)
  have hp3 : AEStronglyMeasurable[r.beforeSample t]
      (fun ω => G.smoothGradient (r.x (t + 1) ω) -
        workerMean (fun i => r.m t i ω) + b) P :=
    ((workerMean_predictable (mΩ := mΩ) P (r.beforeSample t)
      (fun i ω => G.grad i (r.x (t + 1) ω)) (r.gradient_predictable t)).fun_sub
      (workerMean_predictable (mΩ := mΩ) P (r.beforeSample t)
        (r.m t) (r.m_predictable t))).fun_add
      (aestronglyMeasurable_const : AEStronglyMeasurable[r.beforeSample t]
        (fun _ : Ω => b) P)
  have hz1 := mean_noise_orthogonal (mΩ := mΩ) P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu1 hp1
  have hz2 := mean_noise_orthogonal (mΩ := mΩ) P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu2 hp2
  have hz3 := mean_noise_orthogonal (mΩ := mΩ) P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu3 hp3
  have hvariance := mean_noise_second_moment (mΩ := mΩ) G.hn P (r.noise t) variance
    (r.noise_lp t) (fun i => conditional_variance_to_integral (mΩ := mΩ) P (r.beforeSample t)
      (r.beforeSample_le t) (r.noise t i) variance (r.variance_bound t i))
  apply integrated_functional_progress (mΩ := mΩ) P G.smoothValue G.ψ G.hμ G.M_pos hτ hγ
    hγτ hμτ rfl G.xstar (G.smoothGradient G.xstar) b
    (r.x t) (r.x (t + 1))
    (fun ω => workerMean (fun i => r.m t i ω))
    (fun ω => workerMean (fun i => r.v t i ω))
    (fun ω => G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
    (fun ω => G.smoothGradient (r.x (t + 1) ω))
    (fun ω => workerMean (fun i => r.m (t + 1) i ω))
    (fun ω => G.auxiliary τ (r.x (t + 1) ω) (fun i => r.m (t + 1) i ω)) ζ
    (fun ω => G.W (fun i => r.m t i ω))
    (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω))
  · exact Filter.Eventually.of_forall (fun ω => G.W_nonnegative _)
  · exact Filter.Eventually.of_forall (fun ω => G.V_nonnegative _ _)
  · exact r.W_integrable P G b t
  · exact r.V_integrable P G b t
  · exact r.energy_integrable P G b t
  · exact r.energy_integrable P G b (t + 1)
  · exact r.gap_integrable (t + 1)
  · exact r.displacement_integrable P G b t
  · exact r.first_remainder_integrable P G b t
  · exact r.second_remainder_integrable P G b t
  · exact integrable_inner_of_memLp_two (mΩ := mΩ) P _ ζ hu1 hζ
  · exact integrable_inner_of_memLp_two (mΩ := mΩ) P _ ζ hu2 hζ
  · exact integrable_inner_of_memLp_two (mΩ := mΩ) P _ ζ hu3 hζ
  · exact hζsq
  · exact hz1
  · exact hz2
  · exact hz3
  · exact hvariance
  · exact r.aggregate_momentum_update P G b t
  · exact Filter.Eventually.of_forall (fun ω => by
      have hs := G.average_strong (r.x (t + 1) ω) (r.x t ω)
      change G.smoothValue (r.x (t + 1) ω) +
        ⟪G.smoothGradient (r.x (t + 1) ω), r.x t ω - r.x (t + 1) ω⟫_ℝ +
        μ / 2 * ‖r.x t ω - r.x (t + 1) ω‖ ^ 2 ≤ G.smoothValue (r.x t ω) at hs
      rw [norm_sub_rev (r.x t ω) (r.x (t + 1) ω)] at hs
      linarith)
  · exact Filter.Eventually.of_forall (fun ω => G.prox_support_step hτ
      (r.x t ω) (workerMean (fun i => r.m t i ω))
      (G.auxiliary τ (r.x (t + 1) ω) (fun i => r.m (t + 1) i ω))
      (G.prox_mem τ hτ
        (r.x (t + 1) ω - τ • workerMean (fun i => r.m (t + 1) i ω))))
  · filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω) (workerMean (fun i => r.v t i ω)) _ hx
    rw [← hu] at hs
    linarith
  · exact Filter.Eventually.of_forall (fun ω => G.average_strong (r.x (t + 1) ω) G.xstar)
  · filter_upwards [r.proximal_update t, r.feasible (t + 1)] with ω hu hy
    have hxy := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω))
      (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
      (G.prox_mem τ hτ (r.x t ω - τ • workerMean (fun i => r.m t i ω)))
    rw [← hu] at hxy
    have hyx := G.prox_support_step hτ (r.x t ω)
      (workerMean (fun i => r.m t i ω)) (r.x (t + 1) ω) hy
    exact subgradient_monotonicity G.ψ _ _ _ _ hxy hyx
  · filter_upwards [r.feasible (t + 1)] with ω hω
    exact G.global_gradient_interpolation _ hω
  · exact Filter.Eventually.of_forall (fun ω => G.average_momentum_control _)
  · exact Filter.Eventually.of_forall (fun ω => G.average_compression_control _ _)

lemma upper_comparison (hτ : 0 < τ) (hγ : 0 < γ)
    (hμγ : μ * γ ≤ 1) (hμτ : μ * τ ≤ 1)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3) (t : ℕ) :
    (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) ≤
      3 * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      (∫ ω, G.W (fun i => r.m t i ω) ∂P) / M +
      4 / μ * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
  apply integrated_upper_comparison (mΩ := mΩ) P G.smoothValue G.ψ G.hμ G.M_pos hτ hγ
    G.hμM hμγ hμτ hsmall G.xstar (G.smoothGradient G.xstar)
    (r.x t) (r.x (t + 1))
    (fun ω => workerMean (fun i => r.m t i ω))
    (fun ω => workerMean (fun i => r.v t i ω))
    (fun ω => G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
    (fun ω => G.smoothGradient (r.x (t + 1) ω))
    (fun ω => G.W (fun i => r.m t i ω))
    (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω))
  · exact r.energy_integrable P G b t
  · exact r.gap_integrable (t + 1)
  · exact r.displacement_integrable P G b t
  · exact r.first_remainder_integrable P G b t
  · exact r.second_remainder_integrable P G b t
  · exact r.W_integrable P G b t
  · exact r.V_integrable P G b t
  · filter_upwards [r.proximal_update t] with ω hu
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω))
      (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
      (G.prox_mem τ hτ (r.x t ω - τ • workerMean (fun i => r.m t i ω)))
    simpa only [← hu] using hs
  · filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) _ hx
    rw [← hu] at hs
    linarith
  · filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.strong_gap _ hx
  · exact Filter.Eventually.of_forall (fun ω => G.smooth_upper (r.x (t + 1) ω) (r.x t ω))
  · filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.global_gradient_interpolation _ hx
  · exact Filter.Eventually.of_forall (fun ω => G.average_momentum_control _)
  · exact Filter.Eventually.of_forall (fun ω => G.average_compression_control _ _)

lemma objective_control (hτ : 0 < τ) (hμτ : μ * τ ≤ 1) (t : ℕ) :
    (∫ ω, G.gap (r.x t ω) ∂P) ≤
      (8 / 7 : ℝ) * (∫ ω, G.potential τ (r.x t ω)
        (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
  have hp : ∀ᵐ ω ∂P, G.gap (r.x t ω) ≤
      (8 / 7 : ℝ) * G.potential τ (r.x t ω)
        (fun i => r.m t i ω) (fun i => r.v t i ω) := by
    filter_upwards [r.feasible t] with ω hx
    have h := G.potential_lower hτ hμτ (r.x t ω) hx
      (fun i => r.m t i ω) (fun i => r.v t i ω)
    have hμpos : 0 < μ := G.hμ
    have hMpos : 0 < M := G.M_pos
    have hm := G.model_nonnegative hτ (r.x t ω) hx (fun i => r.m t i ω)
    have hv := G.V_nonnegative (fun i => r.m t i ω) (fun i => r.v t i ω)
    have hw := G.W_nonnegative (fun i => r.m t i ω)
    have ht : 0 ≤ modelDecrease G.ψ τ (r.x t ω)
        (workerMean (fun i => r.m t i ω))
        (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω)) / (μ * τ) := by positivity
    have hvt : 0 ≤ G.V (fun i => r.m t i ω) (fun i => r.v t i ω) / μ := by positivity
    have hwt : 0 ≤ G.W (fun i => r.m t i ω) / (64 * M) := by positivity
    ring_nf at h ht hvt hwt ⊢
    linarith only [h, ht, hvt, hwt]
  have h := integral_mono_ae (r.gap_integrable t)
    ((r.potential_integrable P G b t).const_mul (8 / 7)) hp
  simpa only [integral_const_mul] using h

lemma contraction (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.potential τ (r.x (t + 1) ω)
      (fun i => r.m (t + 1) i ω) (fun i => r.v (t + 1) i ω) ∂P) ≤
      (1 - μ * γ / 512) *
        (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      6 * γ * ‖b‖ ^ 2 + 2 * μ * γ ^ 2 * variance := by
  obtain ⟨hM, hτpos, hMτ, hMγδ, hγτ, hαpos, hαδ, hα1⟩ :=
    tuning_bounds G.hμ G.hμM hδ hδ1 hτ hγ hγbound (α := μ * γ) rfl
  have hhalf : γ ≤ τ / 2 := by
    have hg : γ ≤ τ / 128 :=
      hγbound.trans (div_le_div_of_nonneg_right
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hδ1 hτpos.le) (by norm_num))
    linarith
  have hμτ : μ * τ ≤ 1 / 4096 := by
    have h := mul_le_mul_of_nonneg_right G.hμM hτpos.le
    linarith
  have hμτ1 : μ * τ ≤ 1 := by linarith
  have hMg : M * γ ≤ 1 := by
    have h := (div_le_iff₀ hδ).mp hMγδ
    nlinarith
  have hμg : μ * γ ≤ 1 := hα1
  have hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3 := by
    have hprod : (μ * γ) * (M * γ) ≤ 1 :=
      (by simpa only [one_mul] using
        mul_le_mul hμg hMg (mul_nonneg hM.le hγ.le) (by norm_num : (0 : ℝ) ≤ 1))
    nlinarith only [hprod, hμg]
  have hE := r.functional_progress P G b hτpos hγ hhalf hμτ t
  have hW := r.momentum_recurrence P G b hαpos.le hα1 hvar t
  have hV := r.compression_recurrence P G b hδ hδ1 hvar t
  have hg : 0 ≤ ∫ ω, G.gap (r.x (t + 1) ω) ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.gap_nonnegative _ hx
  have hdn : 0 ≤ ∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hwn : 0 ≤ ∫ ω, G.W (fun i => r.m t i ω) ∂P :=
    integral_nonneg (fun _ => G.W_nonnegative _)
  have hvn : 0 ≤ ∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P :=
    integral_nonneg (fun _ => G.V_nonnegative _ _)
  have hrem1 : 0 ≤ ∫ ω,
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.proximal_update t] with ω hu
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) G.xstar G.optimum_mem
    rw [← hu, show G.xstar - r.x (t + 1) ω = -(r.x (t + 1) ω - G.xstar) by abel,
      inner_neg_right] at hs
    change (0 : ℝ) ≤
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar
    linarith only [hs]
  have hrem2 : 0 ≤ ∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) (r.x t ω) hx
    rw [← hu] at hs
    change (0 : ℝ) ≤ G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x t ω - r.x (t + 1) ω⟫_ℝ
    linarith only [hs]
  have hdescent := assembled_descent G.hμ G.hμM hδ hτ hγ hγbound
    (α := μ * γ) rfl hg hdn hwn hvn (sq_nonneg ‖b‖) hvar hE hW hV
  have hu := r.upper_comparison P G b hτpos hγ hμg hμτ1 hsmall t
  have hupper :
      (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) ≤
      3 * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      2 / M * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      5 / μ * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
    rw [r.integral_potential P G b t]
    have hwc : (1 / M + 1 / (64 * M) : ℝ) ≤ 2 / M := by
      apply (mul_le_mul_iff_of_pos_right hM).mp
      field_simp [ne_of_gt hM]
      norm_num
    have hwterm := mul_le_mul_of_nonneg_right hwc hwn
    apply sub_nonneg.mp
    calc
      (0 : ℝ) ≤ _ := sub_nonneg.mpr (add_le_add hu hwterm)
      _ = _ := by ring
  rw [← r.integral_potential P G b t, ← r.integral_potential P G b (t + 1)] at hdescent
  have hαδ' : 5 * (μ * γ) ≤ 128 * δ := by nlinarith only [hαδ, hδ.le]
  have hcontract := contraction_from_dissipation
    (noise := 6 * γ * ‖b‖ ^ 2 + 2 * μ * γ ^ 2 * variance)
    G.hμ hM hγ hτpos rfl hα1 hαδ'
    hg hdn hrem1 hrem2 hwn hvn hupper (by
      simpa only [add_assoc] using hdescent)
  simpa only [add_assoc] using hcontract

lemma inner_contraction_unrolled (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hvar : 0 ≤ variance) (K : ℕ) :
    (∫ ω, G.potential τ (r.x K ω) (fun i => r.m K i ω) (fun i => r.v K i ω) ∂P) ≤
      Real.exp (-μ * γ * K / 512) *
        (∫ ω, G.potential τ (r.x 0 ω) (fun i => r.m 0 i ω) (fun i => r.v 0 i ω) ∂P) +
      3072 * ‖b‖ ^ 2 / μ + 1024 * γ * variance := by
  obtain ⟨hM, hτpos, hMτ, _, _, _, _, hα1⟩ :=
    tuning_bounds G.hμ G.hμM hδ hδ1 hτ hγ hγbound (α := μ * γ) rfl
  have hμτ : μ * τ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right G.hμM hτpos.le
    linarith
  have hΛ0 : 0 ≤ ∫ ω, G.potential τ (r.x 0 ω)
      (fun i => r.m 0 i ω) (fun i => r.v 0 i ω) ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.feasible 0] with ω hx
    exact G.potential_nonnegative hτpos hμτ _ hx _ _
  have h := inner_polynomial_bound_to_exponential
    (fun t => ∫ ω, G.potential τ (r.x t ω)
      (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P)
    G.hμ hγ (B := 1) (by norm_num) (by linarith)
    hΛ0 hvar (sq_nonneg ‖b‖)
    (by intro t; simpa only [div_one] using r.contraction P G b hδ hδ1 hτ hγ hγbound hvar t) K
  simpa only [div_one] using h

end Trajectory

end LongTails.Proofs.ProximalEf21InnerTrajectory

end

end InnerTrajectory


section HomotopyTrajectory_definitions

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21HomotopyTrajectory

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21StochasticContraction
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21InnerTrajectory
open LongTails.Proofs.ProximalEf21Regularization
open LongTails.Proofs.ProximalEf21Initialization
open LongTails.Proofs.ProximalEf21ScalarCore
open LongTails.Proofs.ProximalEf21Schedule
open LongTails.Proofs.ProximalEf21CountedBudget

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} {L : ℝ}

noncomputable def stageGeometry (G : ConvexCompositeGeometry (E := E) n L) (s : ℕ) :
    InnerGeometry (E := E) n (mu L s) (3 * L) :=
  G.regularized (mu L s) (mu_positive G.hL s) (mu_le_initial G.hL s)

structure HomotopyTrajectory (P : @Measure Ω mΩ) (G : ConvexCompositeGeometry (E := E) n L)
    (x0 : E) (R σ δ H : ℝ) where
  run : ∀ s, Trajectory P (stageGeometry G s) (1 / (12288 * L)) (gamma L δ) δ
    (σ ^ 2 / (batches L R σ δ s : ℝ)) ((mu L s) • (G.xstar - x0))
  initial_point : ∀ᵐ ω ∂P, (run 0).x 0 ω = x0
  transfer_x : ∀ s, ∀ᵐ ω ∂P,
    (run (s + 1)).x 0 ω = (run s).x (ProximalEf21CountedBudget.length L R δ H s) ω
  transfer_m : ∀ s i, ∀ᵐ ω ∂P,
    (run (s + 1)).m 0 i ω = (run s).m (ProximalEf21CountedBudget.length L R δ H s) i ω
  transfer_v : ∀ s i, ∀ᵐ ω ∂P,
    (run (s + 1)).v 0 i ω = (run s).v (ProximalEf21CountedBudget.length L R δ H s) i ω

namespace HomotopyTrajectory

variable (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
variable (G : ConvexCompositeGeometry (E := E) n L)
variable (x0 : E) {R σ δ H ε : ℝ}
variable (r : HomotopyTrajectory P G x0 R σ δ H)

noncomputable def output (ε : ℝ) (ω : Ω) : E :=
  (r.run (lastStage L R ε)).x
    (ProximalEf21CountedBudget.length L R δ H (lastStage L R ε)) ω

end HomotopyTrajectory

end LongTails.Proofs.ProximalEf21HomotopyTrajectory

end

end HomotopyTrajectory_definitions
