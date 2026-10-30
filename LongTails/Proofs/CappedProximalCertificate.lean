import LongTails.Proofs.CappedProximalOracle
import LongTails.Proofs.CappedProximalSampling

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalCertificate

open LongTails.Setups.CappedHessianSimilarConvex
open CappedProximalOracle CappedProximalSampling

lemma estimator_error {p : Params} {inst : Instance p}
    (x w : p.E) {s : ℕ} (hs : 0 < s) (ξ : Fin s → Fin p.m) :
    (s : ℝ)⁻¹ • (∑ j, (gradient (inst.components (ξ j)) x -
      gradient (inst.components (ξ j)) w)) + gradient (objective inst) w -
      gradient (objective inst) x =
    (s : ℝ)⁻¹ • ∑ j, (centeredGradient inst (ξ j) x - centeredGradient inst (ξ j) w) := by
  have hc := OracleTemplate.RobustGradient.finite_mean_centered
    (X := fun i => gradient (inst.components i) x - gradient (inst.components i) w)
    (gradient (objective inst) x - gradient (objective inst) w) s hs ξ
  simp only [one_div] at hc
  rw [show (s : ℝ)⁻¹ • (∑ j, (gradient (inst.components (ξ j)) x -
      gradient (inst.components (ξ j)) w)) + gradient (objective inst) w -
      gradient (objective inst) x =
    (s : ℝ)⁻¹ • (∑ j, (gradient (inst.components (ξ j)) x -
      gradient (inst.components (ξ j)) w)) -
      (gradient (objective inst) x - gradient (objective inst) w) by abel, hc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp [centeredGradient]
  abel

lemma estimator_variance {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x w : p.E) {s : ℕ} (hs : 0 < s) :
    (𝔼 ξ : Fin s → Fin p.m,
      ‖(s : ℝ)⁻¹ • ∑ j, (centeredGradient inst (ξ j) x -
        centeredGradient inst (ξ j) w)‖ ^ 2) ≤ p.δ ^ 2 * ‖x - w‖ ^ 2 / s := by
  rw [OracleTemplate.VarianceReducedWeakMinty.batch_mean_second_moment _
    (centered_difference_sum h x w) hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, one_div_mul_eq_div]
    using h.2.2.2.1 x w

lemma estimator_unbiased_inner {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (x w v : p.E) (s : ℕ) :
    (𝔼 ξ : Fin s → Fin p.m,
      ⟪(s : ℝ)⁻¹ • ∑ j, (centeredGradient inst (ξ j) x -
        centeredGradient inst (ξ j) w), v⟫) = 0 := by
  rw [Fintype.expect_eq_sum_div_card, ← sum_inner, ← Finset.smul_sum,
    OracleTemplate.VarianceReducedWeakMinty.batch_sum_zero _
      (centered_difference_sum h x w) s, smul_zero, inner_zero_left, zero_div]

lemma sampled_objective_gap {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E) (k : ℕ) :
    let U := (p.m : ℝ)⁻¹ • ∑ i, u i
    (𝔼 ξ : Fin (k + 1) → Fin p.m,
      (objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst U)) ≤
      (𝔼 i, (inst.components i (u i) - inst.components i U -
        ⟪gradient (inst.components i) U, u i - U⟫)) +
      ((p.δ * Real.sqrt k + 3 * (Real.sqrt p.m * p.δ) / 2) / ((k : ℝ) + 1)) *
        (𝔼 i, ‖u i - U‖ ^ 2) := by
  dsimp only
  let U := (p.m : ℝ)⁻¹ • ∑ i, u i
  let v := fun i => u i - U
  let z := fun ξ : Fin (k + 1) → Fin p.m => ((k : ℝ) + 1)⁻¹ • ∑ j, v (ξ j)
  have hv : ∑ i, v i = 0 :=
    OracleTemplate.VarianceReducedWeakMinty.component_centered_sum (NeZero.pos p.m) u
  have hz (ξ : Fin (k + 1) → Fin p.m) :
      ((k : ℝ) + 1)⁻¹ • (∑ j, u (ξ j)) = U + z ξ := by
    simpa only [Nat.cast_succ] using sample_mean_translation (Nat.succ_pos k) u U ξ
  have hpoint (ξ : Fin (k + 1) → Fin p.m) :=
    sampled_primal_upper h hd (Nat.succ_pos k) ξ u U (U + z ξ) (by
      rw [← Finset.smul_sum]
      simpa only [one_div, Nat.cast_succ] using hz ξ)
  have hnorm (ξ : Fin (k + 1) → Fin p.m) : ‖U - (U + z ξ)‖ = ‖z ξ‖ := by
    rw [show U - (U + z ξ) = -(z ξ) by abel, norm_neg]
  have ht := expected_primal_from_certificate v hv
    (fun i t => centeredGradient inst i U - centeredGradient inst i (U + t))
    (fun t => objective inst (U + t))
    (fun i => inst.components i (u i) - inst.components i U -
      ⟪gradient (inst.components i) U, v i⟫)
    (gradient (objective inst) U) z (fun _ => rfl) hd
    (translated_centered_second_moment h U)
    (translated_centered_lipschitz h hd U) (by
      intro ξ
      have hp := hpoint ξ
      simp only [add_zero, add_sub_cancel_left, hnorm] at hp ⊢
      simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, one_div_mul_eq_div,
        Nat.cast_succ, v] using hp)
  simp only [add_zero] at ht
  simpa only [hz, U, v] using ht

lemma sampled_comparison {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (x g v : p.E) (lam : ℝ) (k : ℕ)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    let U := (p.m : ℝ)⁻¹ • ∑ i, u i
    let V := (1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2
    (𝔼 ξ : Fin (k + 1) → Fin p.m,
      (objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst v)) ≤
      ⟪gradient (objective inst) x - g + lam • (x - U), U - v⟫ +
      2 * p.δ * ‖x - U‖ * Real.sqrt V +
      (-2 * lam + (p.δ * Real.sqrt k + 3 * (Real.sqrt p.m * p.δ) / 2) /
        ((k : ℝ) + 1)) * V := by
  dsimp only
  let U := (p.m : ℝ)⁻¹ • ∑ i, u i
  have hU : ∑ i, (1 / (p.m : ℝ)) • u i = U := by
    rw [← Finset.smul_sum, one_div]
  have hg := sampled_objective_gap h hd u k
  dsimp only at hg
  have hb := common_point_bregman h hd u U x g lam hU hs
  have hc := common_point_comparison h hd u U x g v lam hU hs
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    div_eq_mul_inv, mul_comm] at hg
  have he :
      (𝔼 ξ : Fin (k + 1) → Fin p.m,
        (objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst v)) =
      (𝔼 ξ : Fin (k + 1) → Fin p.m,
        (objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst U)) +
        (objective inst U - objective inst v) := by
    have hp (ξ : Fin (k + 1) → Fin p.m) :
        objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst v =
        (objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)) - objective inst U) +
          (objective inst U - objective inst v) := by ring
    simp_rw [hp]
    rw [Finset.expect_add_distrib, Fintype.expect_const]
  rw [he]
  dsimp [U]
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, one_mul]
  dsimp [U] at hb hc
  simp only [one_div] at hb hc
  nlinarith only [hg, hb, hc]

lemma sampled_residual_comparison {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (x g v : p.E) (lam : ℝ) (k : ℕ)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    let U := (p.m : ℝ)⁻¹ • ∑ i, u i
    let V := (1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2
    let z := fun ξ : Fin (k + 1) → Fin p.m => ((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)
    (𝔼 ξ, (objective inst (z ξ) - objective inst v)) ≤
      (𝔼 ξ, ⟪lam • (x - z ξ), z ξ - v⟫) -
      ⟪g - gradient (objective inst) x, U - v⟫ +
      2 * p.δ * ‖x - U‖ * Real.sqrt V +
      (-2 * lam + lam / ((k : ℝ) + 1) +
        (p.δ * Real.sqrt k + 3 * (Real.sqrt p.m * p.δ) / 2) / ((k : ℝ) + 1)) * V := by
  dsimp only
  have hh := sampled_comparison h hd u x g v lam k hs
  have hc := sampled_residual_covariance (Nat.succ_pos k) u x v lam
  dsimp only at hh hc
  simp only [Nat.cast_succ] at hc
  have he (U : p.E) :
      ⟪gradient (objective inst) x - g + lam • (x - U), U - v⟫ =
      ⟪lam • (x - U), U - v⟫ - ⟪g - gradient (objective inst) x, U - v⟫ := by
    simp only [inner_add_left, inner_sub_left]
    ring
  simp_rw [he] at hh
  nlinarith only [hh, hc]

lemma sampled_proximal_certificate {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (u : Fin p.m → p.E)
    (x g v : p.E) {lam : ℝ} (hl : 0 < lam) (k : ℕ)
    (ht : 16 * p.δ + 6 * (Real.sqrt p.m * p.δ) / ((k : ℝ) + 1) ≤ lam)
    (hs : ∀ i, gradient (inst.components i) (u i) + lam • (u i - x) =
      gradient (inst.components i) x - g) :
    let z := fun ξ : Fin (k + 1) → Fin p.m => ((k : ℝ) + 1)⁻¹ • ∑ j, u (ξ j)
    (𝔼 ξ, (objective inst (z ξ) - objective inst v)) ≤
      (𝔼 ξ, ⟪lam • (x - z ξ), z ξ - v⟫) +
      lam / 8 * (𝔼 ξ, ‖x - z ξ‖ ^ 2) +
      4 / lam * ‖g - gradient (objective inst) x‖ ^ 2 -
      ⟪g - gradient (objective inst) x, x - v⟫ := by
  dsimp only
  let U := (p.m : ℝ)⁻¹ • ∑ i, u i
  let V := (1 / (p.m : ℝ)) * ∑ i, ‖u i - U‖ ^ 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hdelta : 16 * p.δ ≤ lam := by
    have hn : 0 ≤ 6 * (Real.sqrt p.m * p.δ) / ((k : ℝ) + 1) := by positivity
    linarith
  have hcoef := CappedProximalGeometry.sampled_variance_coefficient k hl.le hd ht
  have ha := CappedProximalGeometry.proximal_error_absorption
    (g - gradient (objective inst) x) U x v hl hV hdelta hcoef
  have hi := sampled_residual_comparison h hd u x g v lam k hs
  dsimp only at hi
  have hdist := congrArg (fun t : ℝ => lam / 8 * t)
    (sampled_squared_distance (Nat.succ_pos k) u x)
  dsimp only at hdist
  simp only [Nat.cast_succ] at hdist
  have hn : 0 ≤ lam / 8 * (V / ((k : ℝ) + 1)) := by positivity
  dsimp [U, V] at ha hn
  nlinarith only [hi, ha, hdist, hn]

set_option maxHeartbeats 800000 in
lemma independent_cohort_certificate {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (x w v : p.E)
    {lam : ℝ} (hl : 0 < lam) (k : ℕ)
    (ht : 16 * p.δ + 6 * (Real.sqrt p.m * p.δ) / ((k : ℝ) + 1) ≤ lam)
    (g : (Fin (k + 1) → Fin p.m) → p.E)
    (u : (Fin (k + 1) → Fin p.m) → Fin p.m → p.E)
    (hg : ∀ η, g η - gradient (objective inst) x =
      ((k : ℝ) + 1)⁻¹ • ∑ j, (centeredGradient inst (η j) x - centeredGradient inst (η j) w))
    (hu : ∀ η i, gradient (inst.components i) (u η i) + lam • (u η i - x) =
      gradient (inst.components i) x - g η) :
    let z := fun η ξ : Fin (k + 1) → Fin p.m => ((k : ℝ) + 1)⁻¹ • ∑ j, u η (ξ j)
    (𝔼 η, 𝔼 ξ, (objective inst (z η ξ) - objective inst v)) ≤
      (𝔼 η, 𝔼 ξ, ⟪lam • (x - z η ξ), z η ξ - v⟫) +
      lam / 8 * (𝔼 η, 𝔼 ξ, ‖x - z η ξ‖ ^ 2) +
      4 / lam * (p.δ ^ 2 * ‖x - w‖ ^ 2 / ((k : ℝ) + 1)) := by
  dsimp only
  apply average_stochastic_certificate
    (gap := fun η ξ : Fin (k + 1) → Fin p.m =>
      objective inst (((k : ℝ) + 1)⁻¹ • ∑ j, u η (ξ j)) - objective inst v)
    (pairing := fun η ξ : Fin (k + 1) → Fin p.m =>
      ⟪lam • (x - ((k : ℝ) + 1)⁻¹ • ∑ j, u η (ξ j)),
        ((k : ℝ) + 1)⁻¹ • (∑ j, u η (ξ j)) - v⟫)
    (movement := fun η ξ : Fin (k + 1) → Fin p.m =>
      ‖x - ((k : ℝ) + 1)⁻¹ • ∑ j, u η (ξ j)‖ ^ 2)
    (error := fun η => ‖g η - gradient (objective inst) x‖ ^ 2)
    (noise := fun η => ⟪g η - gradient (objective inst) x, x - v⟫) hl
  · intro η
    exact sampled_proximal_certificate h hd (u η) x (g η) v hl k ht (hu η)
  · simp_rw [hg]
    simpa only [Nat.cast_succ] using estimator_variance h x w (Nat.succ_pos k)
  · simp_rw [hg]
    simpa only [Nat.cast_succ] using estimator_unbiased_inner h x w (x - v) (k + 1)

set_option maxHeartbeats 800000 in
lemma regularized_cohort_certificate {p : Params} {inst : Instance p}
    (h : Assumptions p inst) (hd : 0 ≤ p.δ) (center x w v : p.E)
    {lam rho : ℝ} (hl : 0 < lam) (hr : 0 < rho) (s : ℕ) (hsize : 0 < s)
    (ht : 16 * p.δ + 6 * (Real.sqrt p.m * p.δ) / (s : ℝ) ≤ lam) :
    let g := fun η : Fin s → Fin p.m =>
      gradient (objective inst) w + (s : ℝ)⁻¹ •
        (∑ j, (gradient (inst.components (η j)) x - gradient (inst.components (η j)) w)) +
        rho • (x - center)
    let u := fun η i => inst.prox i (lam + rho)
      (x + (lam + rho)⁻¹ • (gradient (inst.components i) x - g η))
    let z := fun η ξ : Fin s → Fin p.m => (s : ℝ)⁻¹ • ∑ j, u η (ξ j)
    let H := fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2
    (𝔼 η, 𝔼 ξ, (H (z η ξ) - H v)) ≤
      (𝔼 η, 𝔼 ξ, ⟪lam • (x - z η ξ), z η ξ - v⟫) +
      lam / 8 * (𝔼 η, 𝔼 ξ, ‖x - z η ξ‖ ^ 2) +
      4 / lam * (p.δ ^ 2 * ‖x - w‖ ^ 2 / (s : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsize)
  simp only [Nat.cast_succ] at ht ⊢
  let g := fun η : Fin (k + 1) → Fin p.m =>
    gradient (objective inst) w + ((k : ℝ) + 1)⁻¹ •
      (∑ j, (gradient (inst.components (η j)) x - gradient (inst.components (η j)) w)) +
      rho • (x - center)
  let u := fun η i => inst.prox i (lam + rho)
    (x + (lam + rho)⁻¹ • (gradient (inst.components i) x - g η))
  have ho : objective (regularizedInstance inst rho center) =
      fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2 :=
    funext (regularized_objective inst rho center)
  have hg (η : Fin (k + 1) → Fin p.m) :
      g η - gradient (objective (regularizedInstance inst rho center)) x =
        ((k : ℝ) + 1)⁻¹ • ∑ j,
          (centeredGradient (regularizedInstance inst rho center) (η j) x -
            centeredGradient (regularizedInstance inst rho center) (η j) w) := by
    rw [ho, (regularized_hasGradient (objective_hasGradient h x) rho center).gradient]
    simp only [regularized_centering h]
    have he := estimator_error (inst := inst) x w (Nat.succ_pos k) η
    simp only [Nat.cast_succ] at he
    dsimp [g]
    rw [← he]
    abel
  have hu (η : Fin (k + 1) → Fin p.m) (i : Fin p.m) :
      gradient ((regularizedInstance inst rho center).components i) (u η i) +
        lam • (u η i - x) =
      gradient ((regularizedInstance inst rho center).components i) x - g η := by
    change gradient (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2) (u η i) +
        lam • (u η i - x) =
      gradient (fun y => inst.components i y + rho / 2 * ‖y - center‖ ^ 2) x - g η
    rw [(regularized_hasGradient (h.2.1 i (u η i)) rho center).gradient,
      (regularized_hasGradient (h.2.1 i x) rho center).gradient]
    exact regularized_corrected_stationary h i (by linarith) center x (g η)
  have hc := independent_cohort_certificate (regularized_assumptions h hr center)
    hd x w v hl k ht g u hg hu
  simpa only [regularized_objective, g, u] using hc

end LongTails.Proofs.CappedProximalCertificate
