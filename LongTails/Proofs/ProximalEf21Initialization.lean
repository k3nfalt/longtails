import LongTails.Proofs.ProximalEf21Regularization

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21Initialization

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21ConvexAnalysis
open LongTails.Proofs.ProximalEf21StochasticContraction
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
  obtain ⟨hW, hV, hm⟩ := G.initial_reference_bounds x0 hx0 hR.le hdistance m v
  change Q.W m ≤ 2 * W + 2 * L ^ 2 * R ^ 2 at hW
  change Q.V m v ≤ V at hV
  change ‖workerMean m - G.smoothGradient G.xstar‖ ^ 2 ≤
    2 * W + 2 * L ^ 2 * R ^ 2 at hm
  obtain ⟨hψ0, hψΔ⟩ := G.regularizer_reference_bounds x0 hx0
  have hz : Q.auxiliary τ x0 m ∈ G.domain := G.prox_mem τ hτ _
  have hs := G.optimum_support (Q.auxiliary τ x0 m) hz
  have hmodel := modelDecrease_upper_from_support G.ψ hτ x0 G.xstar
    (workerMean m) (Q.auxiliary τ x0 m) (-G.smoothGradient G.xstar) hs
  simp only [inner_neg_left, ← sub_eq_add_neg] at hmodel
  have hmodel' : modelDecrease G.ψ τ x0 (workerMean m) (Q.auxiliary τ x0 m) ≤
      G.gap x0 + τ * (W + L ^ 2 * R ^ 2) := by
    have hms := mul_le_mul_of_nonneg_left hm (show 0 ≤ τ / 2 by positivity)
    linarith
  have hsq : ‖x0 - G.xstar‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (x0 - G.xstar)]
  have hcross := neg_inner_young (2 * L) (by positivity)
    (x0 - G.xstar) (workerMean m - G.smoothGradient G.xstar)
  have hcross' : -(G.ψ x0 - G.ψ G.xstar + ⟪workerMean m, x0 - G.xstar⟫_ℝ) / 8 ≤
      3 * L * R ^ 2 / 16 + W / (16 * L) := by
    have hid : G.ψ x0 - G.ψ G.xstar + ⟪workerMean m, x0 - G.xstar⟫_ℝ =
        (G.ψ x0 - G.ψ G.xstar + ⟪G.smoothGradient G.xstar, x0 - G.xstar⟫_ℝ) +
          ⟪x0 - G.xstar, workerMean m - G.smoothGradient G.xstar⟫_ℝ := by
      rw [inner_sub_right, real_inner_comm (workerMean m) (x0 - G.xstar),
        real_inner_comm (G.smoothGradient G.xstar) (x0 - G.xstar)]
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
    nlinarith only [hc, hms, hrs, hψ0]
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
    unfold InnerGeometry.potential InnerGeometry.energy functionalEnergy
    change Q.gap x0 - _ / 8 + _ + _ + _ ≤ _
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
  nlinarith only [hexp, hΔ0, hLR, hWL, hVL]

end LongTails.Proofs.ProximalEf21Initialization
