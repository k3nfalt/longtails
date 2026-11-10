import LongTails.Proofs.ProximalEf21ConvexAnalysis
import LongTails.Proofs.ProximalEf21StochasticContraction

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21TrajectoryGeometry

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21StochasticContraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure InnerGeometry (n : ℕ) (μ M : ℝ) where
  domain : Set E
  ψ : E → ℝ
  f : Fin n → E → ℝ
  grad : Fin n → E → E
  localL : Fin n → ℝ
  prox : ℝ → E → E
  xstar : E
  hn : 0 < n
  hμ : 0 < μ
  hμM : μ ≤ M
  localL_nonnegative : ∀ i, 0 ≤ localL i
  localL_average : (n : ℝ)⁻¹ * ∑ i, localL i ≤ M
  local_lower : ∀ i x y, f i x + ⟪grad i x, y - x⟫_ℝ ≤ f i y
  local_upper : ∀ i x y,
    f i y ≤ f i x + ⟪grad i x, y - x⟫_ℝ + localL i / 2 * ‖y - x‖ ^ 2
  average_strong : ∀ x y,
    (n : ℝ)⁻¹ * ∑ i, f i x +
      ⟪workerMean (fun i => grad i x), y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, f i y
  regularizer_convex : ConvexOn ℝ domain ψ
  optimum_mem : xstar ∈ domain
  optimum_support : ∀ x ∈ domain,
    ψ xstar + ⟪-workerMean (fun i => grad i xstar), x - xstar⟫_ℝ ≤ ψ x
  prox_mem : ∀ τ, 0 < τ → ∀ u, prox τ u ∈ domain
  prox_min : ∀ τ, 0 < τ → ∀ u z, z ∈ domain →
    ψ (prox τ u) + ‖prox τ u - u‖ ^ 2 / (2 * τ) ≤
      ψ z + ‖z - u‖ ^ 2 / (2 * τ)

namespace InnerGeometry

variable {n : ℕ} {μ M : ℝ} (G : InnerGeometry (E := E) n μ M)

noncomputable def smoothValue (x : E) : ℝ := (n : ℝ)⁻¹ * ∑ i, G.f i x
noncomputable def smoothGradient (x : E) : E := workerMean (fun i => G.grad i x)
noncomputable def gap (x : E) : ℝ := G.smoothValue x + G.ψ x - (G.smoothValue G.xstar + G.ψ G.xstar)
noncomputable def weights (i : Fin n) : ℝ := M / (M + G.localL i)
noncomputable def W (m : Fin n → E) : ℝ := weightedSquare G.weights (fun i => m i - G.grad i G.xstar)
noncomputable def V (m v : Fin n → E) : ℝ := weightedSquare G.weights (fun i => v i - m i)
noncomputable def auxiliary (τ : ℝ) (x : E) (m : Fin n → E) : E :=
  G.prox τ (x - τ • workerMean m)
noncomputable def energy (τ : ℝ) (x : E) (m : Fin n → E) : ℝ :=
  functionalEnergy G.smoothValue G.ψ μ τ G.xstar x (workerMean m) (G.auxiliary τ x m)
noncomputable def potential (τ : ℝ) (x : E) (m v : Fin n → E) : ℝ :=
  G.energy τ x m + G.V m v / μ + G.W m / (64 * M)

lemma M_pos : 0 < M := lt_of_lt_of_le G.hμ G.hμM

lemma weights_positive (i : Fin n) : 0 < G.weights i :=
  (weight_properties G.M_pos (G.localL_nonnegative i)).1

lemma weights_le_one (i : Fin n) : G.weights i ≤ 1 :=
  (weight_properties G.M_pos (G.localL_nonnegative i)).2.1

lemma W_nonnegative (m : Fin n → E) : 0 ≤ G.W m :=
  weightedSquare_nonnegative _ (fun i => (G.weights_positive i).le) _

lemma V_nonnegative (m v : Fin n → E) : 0 ≤ G.V m v :=
  weightedSquare_nonnegative _ (fun i => (G.weights_positive i).le) _

lemma average_inner (x u : E) :
    (n : ℝ)⁻¹ * ∑ i, ⟪G.grad i x, u⟫_ℝ = ⟪G.smoothGradient x, u⟫_ℝ := by
  simp only [smoothGradient, workerMean, real_inner_smul_left, sum_inner]

lemma smooth_upper (x y : E) :
    G.smoothValue y ≤ G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
      M / 2 * ‖y - x‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => G.local_upper i x y))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hid : (n : ℝ)⁻¹ * ∑ i,
      (G.f i x + ⟪G.grad i x, y - x⟫_ℝ + G.localL i / 2 * ‖y - x‖ ^ 2) =
      G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
      ((n : ℝ)⁻¹ * ∑ i, G.localL i) / 2 * ‖y - x‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
      mul_add, G.average_inner, smoothValue]
    ring
  rw [hid] at h
  have hM := mul_le_mul_of_nonneg_right G.localL_average (sq_nonneg ‖y - x‖)
  exact h.trans (by nlinarith only [hM])

lemma smooth_lower (x y : E) :
    G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ ≤ G.smoothValue y := by
  have h := G.average_strong x y
  change G.smoothValue x + ⟪G.smoothGradient x, y - x⟫_ℝ +
    μ / 2 * ‖y - x‖ ^ 2 ≤ G.smoothValue y at h
  have hn : 0 ≤ μ / 2 * ‖y - x‖ ^ 2 := by positivity
  linarith

lemma strong_gap (x : E) (hx : x ∈ G.domain) : μ / 2 * ‖x - G.xstar‖ ^ 2 ≤ G.gap x := by
  apply composite_strong_gap G.smoothValue G.ψ μ x G.xstar (G.smoothGradient G.xstar)
  · exact G.average_strong G.xstar x
  · exact G.optimum_support x hx

lemma gap_nonnegative (x : E) (hx : x ∈ G.domain) : 0 ≤ G.gap x := by
  exact (show 0 ≤ μ / 2 * ‖x - G.xstar‖ ^ 2 by positivity).trans (G.strong_gap x hx)

lemma global_gradient_interpolation (x : E) (hx : x ∈ G.domain) :
    ‖G.smoothGradient x - G.smoothGradient G.xstar‖ ^ 2 ≤ 2 * M * G.gap x := by
  apply composite_gradient_interpolation G.smoothValue G.ψ G.smoothGradient
    G.M_pos.le x G.xstar
  · exact smooth_convex_interpolation G.smoothValue G.smoothGradient G.M_pos
      G.smooth_lower G.smooth_upper x G.xstar
  · exact G.optimum_support x hx

lemma weighted_gradient_interpolation (x : E) (hx : x ∈ G.domain) :
    weightedSquare G.weights (fun i => G.grad i x - G.grad i G.xstar) ≤ 2 * M * G.gap x := by
  have hp (i : Fin n) :
      G.weights i * ‖G.grad i x - G.grad i G.xstar‖ ^ 2 ≤
        2 * M * (G.f i x - G.f i G.xstar - ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) := by
    have hlocalPos : 0 < M + G.localL i := add_pos_of_pos_of_nonneg G.M_pos (G.localL_nonnegative i)
    have hu : ∀ y z,
        G.f i z ≤ G.f i y + ⟪G.grad i y, z - y⟫_ℝ +
          (M + G.localL i) / 2 * ‖z - y‖ ^ 2 := by
      intro y z
      have hs := G.local_upper i y z
      have hh : 0 ≤ M * ‖z - y‖ ^ 2 := by positivity
      linarith
    have h := smooth_convex_interpolation (G.f i) (G.grad i) hlocalPos
      (G.local_lower i) hu x G.xstar
    have hscaled := mul_le_mul_of_nonneg_left h (G.weights_positive i).le
    have hid (a : ℝ) : G.weights i * (2 * (M + G.localL i) * a) = 2 * M * a := by
      unfold weights
      field_simp [ne_of_gt hlocalPos]
      <;> ring
    simpa only [hid] using hscaled
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i))
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hid : (n : ℝ)⁻¹ * ∑ i,
      2 * M * (G.f i x - G.f i G.xstar - ⟪G.grad i G.xstar, x - G.xstar⟫_ℝ) =
      2 * M * (G.smoothValue x - G.smoothValue G.xstar -
        ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ) := by
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub,
      G.average_inner, smoothValue]
    ring
  rw [hid] at hs
  have hstar := G.optimum_support x hx
  change G.ψ G.xstar + ⟪-G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.ψ x at hstar
  rw [inner_neg_left] at hstar
  have hgap : G.smoothValue x - G.smoothValue G.xstar -
      ⟪G.smoothGradient G.xstar, x - G.xstar⟫_ℝ ≤ G.gap x := by
    unfold gap
    linarith
  exact hs.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

lemma average_momentum_control (m : Fin n → E) :
    ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤ 2 * G.W m := by
  have h := aggregate_error_bound G.hn G.M_pos G.localL G.localL_nonnegative
    G.localL_average (fun i => m i - G.grad i G.xstar)
  simpa only [← workerMean_sub, smoothGradient, W, weightedSquare, weights,
    workerMean] using h

lemma average_compression_control (m v : Fin n → E) :
    ‖workerMean v - workerMean m‖ ^ 2 ≤ 2 * G.V m v := by
  have h := aggregate_error_bound G.hn G.M_pos G.localL G.localL_nonnegative
    G.localL_average (fun i => v i - m i)
  simpa only [← workerMean_sub, V, weightedSquare, weights, workerMean] using h

lemma prox_support {a : ℝ} (ha : 0 < a) (u z : E) (hz : z ∈ G.domain) :
    G.ψ (G.prox a u) + ⟪a⁻¹ • (u - G.prox a u), z - G.prox a u⟫_ℝ ≤ G.ψ z :=
  proximal_supporting_affine G.domain G.ψ G.regularizer_convex ha u
    (G.prox a u) (G.prox_mem a ha u) (G.prox_min a ha u) z hz

lemma prox_support_step {a : ℝ} (ha : 0 < a) (x v z : E) (hz : z ∈ G.domain) :
    G.ψ (G.prox a (x - a • v)) +
      ⟪a⁻¹ • (x - G.prox a (x - a • v)) - v,
        z - G.prox a (x - a • v)⟫_ℝ ≤ G.ψ z := by
  have h := G.prox_support ha (x - a • v) z hz
  have hv : a⁻¹ • ((x - a • v) - G.prox a (x - a • v)) =
      a⁻¹ • (x - G.prox a (x - a • v)) - v := by
    have he : (x - a • v) - G.prox a (x - a • v) =
        (x - G.prox a (x - a • v)) - a • v := by abel
    rw [he, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  simpa only [hv] using h

lemma model_nonnegative {τ : ℝ} (hτ : 0 < τ) (x : E) (hx : x ∈ G.domain)
    (m : Fin n → E) : 0 ≤ modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) := by
  apply modelDecrease_nonnegative
  have hmin := G.prox_min τ hτ (x - τ • workerMean m) x hx
  have hz := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m) (G.auxiliary τ x m)
  have hxid := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m) x
  simp only [sub_self, inner_zero_right, norm_zero, zero_pow, zero_div, add_zero] at hxid
  change G.ψ (G.auxiliary τ x m) +
    ‖G.auxiliary τ x m - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) ≤
      G.ψ x + ‖x - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) at hmin
  linarith

lemma model_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m : Fin n → E) :
    G.ψ x - G.ψ G.xstar + ⟪workerMean m, x - G.xstar⟫_ℝ -
      μ / 2 * ‖x - G.xstar‖ ^ 2 ≤
      modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) := by
  have ht : 0 ≤ μ * τ := by positivity
  have hconv := G.regularizer_convex.2 hx G.optimum_mem
    (sub_nonneg.mpr hμτ) ht (by ring)
  have hmem := G.regularizer_convex.1 hx G.optimum_mem
    (sub_nonneg.mpr hμτ) ht (by ring)
  apply model_lower_from_segment G.ψ G.hμ hτ x G.xstar (workerMean m)
    (G.auxiliary τ x m)
  · simpa only [smul_eq_mul] using hconv
  · have hmin := G.prox_min τ hτ (x - τ • workerMean m)
      ((1 - μ * τ) • x + (μ * τ) • G.xstar) hmem
    have h1 := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m)
      (G.auxiliary τ x m)
    have h2 := complete_model_square G.ψ (ne_of_gt hτ) x (workerMean m)
      ((1 - μ * τ) • x + (μ * τ) • G.xstar)
    change G.ψ (G.auxiliary τ x m) +
      ‖G.auxiliary τ x m - (x - τ • workerMean m)‖ ^ 2 / (2 * τ) ≤ _ at hmin
    linarith

lemma energy_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m : Fin n → E) :
    (7 / 8 : ℝ) * (G.gap x +
      modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ)) ≤
      G.energy τ x m := by
  exact (functionalEnergy_nonnegative G.smoothValue G.ψ G.hμ hτ G.xstar x
    (workerMean m) (G.auxiliary τ x m) (G.gap_nonnegative x hx)
    (G.strong_gap x hx) (G.model_nonnegative hτ x hx m)
    (G.model_lower hτ hμτ x hx m)).1

lemma potential_lower {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) :
    (7 / 8 : ℝ) * G.gap x +
      (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) +
      G.V m v / μ + G.W m / (64 * M) ≤ G.potential τ x m v := by
  have h := G.energy_lower hτ hμτ x hx m
  unfold potential
  linarith

lemma potential_nonnegative {τ : ℝ} (hτ : 0 < τ) (hμτ : μ * τ ≤ 1)
    (x : E) (hx : x ∈ G.domain) (m v : Fin n → E) : 0 ≤ G.potential τ x m v := by
  have h := G.potential_lower hτ hμτ x hx m v
  have hg := G.gap_nonnegative x hx
  have ha := G.model_nonnegative hτ x hx m
  have hv := G.V_nonnegative m v
  have hw := G.W_nonnegative m
  have hnon : 0 ≤ (7 / 8 : ℝ) * G.gap x +
      (7 / 8 : ℝ) * modelDecrease G.ψ τ x (workerMean m) (G.auxiliary τ x m) / (μ * τ) +
      G.V m v / μ + G.W m / (64 * M) := by positivity
  exact hnon.trans h

end InnerGeometry

end LongTails.Proofs.ProximalEf21TrajectoryGeometry
