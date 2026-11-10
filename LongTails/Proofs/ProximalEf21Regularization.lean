import LongTails.Proofs.ProximalEf21InnerTrajectory

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21Regularization

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21StochasticContraction
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21ScalarCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ConvexCompositeGeometry (n : ℕ) (L : ℝ) where
  domain : Set E
  ψ : E → ℝ
  f : Fin n → E → ℝ
  grad : Fin n → E → E
  localL : Fin n → ℝ
  prox : ℝ → E → E
  xstar : E
  hn : 0 < n
  hL : 0 < L
  localL_nonnegative : ∀ i, 0 ≤ localL i
  rms_bound : (n : ℝ)⁻¹ * ∑ i, (localL i) ^ 2 ≤ L ^ 2
  local_lower : ∀ i x y, f i x + ⟪grad i x, y - x⟫_ℝ ≤ f i y
  local_upper : ∀ i x y,
    f i y ≤ f i x + ⟪grad i x, y - x⟫_ℝ + localL i / 2 * ‖y - x‖ ^ 2
  local_lipschitz : ∀ i x y, ‖grad i x - grad i y‖ ≤ localL i * ‖x - y‖
  regularizer_convex : ConvexOn ℝ domain ψ
  optimum_mem : xstar ∈ domain
  optimum_support : ∀ x ∈ domain,
    ψ xstar + ⟪-workerMean (fun i => grad i xstar), x - xstar⟫_ℝ ≤ ψ x
  prox_mem : ∀ τ, 0 < τ → ∀ u, prox τ u ∈ domain
  prox_min : ∀ τ, 0 < τ → ∀ u z, z ∈ domain →
    ψ (prox τ u) + ‖prox τ u - u‖ ^ 2 / (2 * τ) ≤
      ψ z + ‖z - u‖ ^ 2 / (2 * τ)

namespace ConvexCompositeGeometry

variable {n : ℕ} {L : ℝ} (G : ConvexCompositeGeometry (E := E) n L)

noncomputable def smoothValue (x : E) : ℝ := (n : ℝ)⁻¹ * ∑ i, G.f i x
noncomputable def smoothGradient (x : E) : E := workerMean (fun i => G.grad i x)
noncomputable def gap (x : E) : ℝ := G.smoothValue x + G.ψ x - (G.smoothValue G.xstar + G.ψ G.xstar)

lemma mean_localL : (n : ℝ)⁻¹ * ∑ i, G.localL i ≤ L := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast G.hn
  let a : ℝ := (n : ℝ)⁻¹ * ∑ i, G.localL i
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : 0 ≤ ∑ i, (G.localL i - a) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hid : (n : ℝ)⁻¹ * ∑ i, (G.localL i - a) ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, (G.localL i) ^ 2 - a ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [a]
    field_simp [hnz]
    <;> ring
  have h := mul_nonneg (inv_nonneg.mpr hnR.le) hsum
  rw [hid] at h
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (inv_nonneg.mpr hnR.le)
      (Finset.sum_nonneg (fun i _ => G.localL_nonnegative i))
  change a ≤ L
  nlinarith [G.rms_bound, G.hL]

lemma quadratic_expansion (x y : E) :
    ‖y - G.xstar‖ ^ 2 = ‖x - G.xstar‖ ^ 2 +
      2 * ⟪x - G.xstar, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
  rw [show y - G.xstar = (x - G.xstar) + (y - x) by abel, square_add]

noncomputable def regularized (μ : ℝ) (hμ : 0 < μ) (hμL : μ ≤ 2 * L) :
    InnerGeometry (E := E) n μ (3 * L) where
  domain := G.domain
  ψ := G.ψ
  f i x := G.f i x + μ / 2 * ‖x - G.xstar‖ ^ 2
  grad i x := G.grad i x + μ • (x - G.xstar)
  localL i := G.localL i + 2 * L
  prox := G.prox
  xstar := G.xstar
  hn := G.hn
  hμ := hμ
  hμM := by linarith [G.hL]
  localL_nonnegative i := by linarith [G.localL_nonnegative i, G.hL]
  localL_average := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_add]
    have hc : (n : ℝ)⁻¹ * ((n : ℝ) * (2 * L)) = 2 * L := by
      field_simp [hnR]
    rw [hc]
    linarith [G.mean_localL]
  local_lower i x y := by
    have h := G.local_lower i x y
    rw [G.quadratic_expansion x y]
    simp only [inner_add_left, real_inner_smul_left]
    have hsq : 0 ≤ μ * ‖y - x‖ ^ 2 := by positivity
    nlinarith
  local_upper i x y := by
    have h := G.local_upper i x y
    rw [G.quadratic_expansion x y]
    simp only [inner_add_left, real_inner_smul_left]
    have hh := mul_le_mul_of_nonneg_right hμL (sq_nonneg ‖y - x‖)
    nlinarith
  average_strong x y := by
    have hs := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_lower i x y))
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
    have hf (z : E) : (n : ℝ)⁻¹ * ∑ i,
        (G.f i z + μ / 2 * ‖z - G.xstar‖ ^ 2) =
        G.smoothValue z + μ / 2 * ‖z - G.xstar‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_add, smoothValue]
      field_simp [hnR]
      <;> ring
    rw [hf, hf, workerMean_add, workerMean_const G.hn,
      inner_add_left, real_inner_smul_left, G.quadratic_expansion x y]
    have hi : (n : ℝ)⁻¹ * ∑ i, (G.f i x + ⟪G.grad i x, y - x⟫_ℝ) =
        G.smoothValue x + ⟪workerMean (fun i => G.grad i x), y - x⟫_ℝ := by
      simp only [Finset.sum_add_distrib, mul_add, workerMean,
        real_inner_smul_left, sum_inner, smoothValue]
    rw [hi] at hs
    change _ ≤ G.smoothValue y at hs
    linarith
  regularizer_convex := G.regularizer_convex
  optimum_mem := G.optimum_mem
  optimum_support x hx := by
    simpa only [sub_self, smul_zero, add_zero] using G.optimum_support x hx
  prox_mem := G.prox_mem
  prox_min := G.prox_min

lemma regularized_gradient {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).smoothGradient x =
      G.smoothGradient x + μ • (x - G.xstar) := by
  exact (workerMean_add _ _).trans (by rw [workerMean_const G.hn]; rfl)

lemma regularized_value {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).smoothValue x = G.smoothValue x + μ / 2 * ‖x - G.xstar‖ ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt G.hn
  simp only [InnerGeometry.smoothValue, regularized, smoothValue,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_add]
  field_simp [hnR]
  <;> ring

lemma regularized_gap {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * L) (x : E) :
    (G.regularized μ hμ hμL).gap x = G.gap x + μ / 2 * ‖x - G.xstar‖ ^ 2 := by
  unfold InnerGeometry.gap
  rw [G.regularized_value hμ hμL, G.regularized_value hμ hμL]
  simp only [sub_self, norm_zero, zero_pow, mul_zero, add_zero]
  unfold gap
  ring

lemma base_gap_nonnegative (x : E) (hx : x ∈ G.domain) : 0 ≤ G.gap x := by
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_lower i G.xstar x))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hi : (n : ℝ)⁻¹ * ∑ i, (G.f i G.xstar + ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) =
      G.smoothValue G.xstar + ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ := by
    simp only [smoothValue, smoothGradient, workerMean, Finset.sum_add_distrib,
      mul_add, real_inner_smul_left, sum_inner]
  rw [hi] at hs
  have hp := G.optimum_support x hx
  change G.ψ G.xstar + ⟪-G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.ψ x at hp
  rw [inner_neg_left] at hp
  unfold gap
  change _ ≤ G.smoothValue x at hs
  linarith

lemma regularized_potential_transfer {μ τ : ℝ}
    (hμ : 0 < μ) (h2μ : 2 * μ ≤ 2 * L)
    (hτ : 0 < τ) (hscale : (2 * μ) * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) :
    (G.regularized μ hμ (by linarith)).potential τ x m v ≤
      (15 / 7 : ℝ) * (G.regularized (2 * μ) (by positivity) h2μ).potential τ x m v := by
  let oldG := G.regularized (2 * μ) (by positivity) h2μ
  let newG := G.regularized μ hμ (by linarith)
  have hV : newG.V m v = oldG.V m v := rfl
  have hW : newG.W m = oldG.W m := by
    unfold InnerGeometry.W InnerGeometry.weights newG oldG regularized
    simp only [sub_self, smul_zero, add_zero]
  have hz : newG.auxiliary τ x m = oldG.auxiliary τ x m := rfl
  have hgapnew := G.regularized_gap hμ (show μ ≤ 2 * L by linarith) x
  have hgapold := G.regularized_gap (show 0 < 2 * μ by positivity) h2μ x
  have hidentity : newG.potential τ x m v = oldG.potential τ x m v -
      μ / 2 * ‖x - G.xstar‖ ^ 2 +
      modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ) +
      oldG.V m v / (2 * μ) := by
    unfold InnerGeometry.potential InnerGeometry.energy functionalEnergy
    change newG.gap x - _ + _ + _ + _ = oldG.gap x - _ + _ + _ + _ - _ + _ + _
    rw [hV, hW, hz, hgapnew, hgapold]
    field_simp [ne_of_gt hμ, ne_of_gt hτ]
    <;> ring
  have hlo := oldG.potential_lower hτ hscale x hx m v
  have hgap := oldG.gap_nonnegative x hx
  have hwn := oldG.W_nonnegative m
  have hvn := oldG.V_nonnegative m v
  have hWt : 0 ≤ oldG.W m / (64 * (3 * L)) := by positivity
  have hcontrol : (7 / 8 : ℝ) *
      (modelDecrease G.ψ τ x (workerMean m) (oldG.auxiliary τ x m) / ((2 * μ) * τ)) +
      oldG.V m v / (2 * μ) ≤ oldG.potential τ x m v := by
    linarith
  exact stage_transfer_from_model_control
    (show 0 ≤ μ / 2 * ‖x - G.xstar‖ ^ 2 by positivity)
    (show 0 ≤ oldG.V m v / (2 * μ) by positivity) hcontrol hidentity

end ConvexCompositeGeometry

end LongTails.Proofs.ProximalEf21Regularization
