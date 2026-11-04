import LongTails.Proofs.TensorFreeModelTermination

namespace LongTails.Proofs.TensorFreeModelTuning

lemma contraction_log_bound {Q : ℝ} (hQ : 0 < Q) (K m : ℕ)
    (hK : 24 * (m : ℝ) * Real.log Q ≤ K) :
    (23 / 24 : ℝ) ^ K ≤ 1 / Q ^ m := by
  have hbase : (23 / 24 : ℝ) ≤ Real.exp (-1 / 24) := by
    have hh := Real.add_one_le_exp (-1 / 24)
    linarith
  calc
    (23 / 24 : ℝ) ^ K ≤ (Real.exp (-1 / 24)) ^ K := pow_le_pow_left₀ (by norm_num) hbase K
    _ = Real.exp ((K : ℝ) * (-1 / 24)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-((m : ℝ) * Real.log Q)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Q ^ m := by rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hQ, one_div]

lemma model_iterations_log_bound {Q : ℝ} (hQ : 1 ≤ Q) :
    (23 / 24 : ℝ) ^ (5000 * (1 + ⌈Real.log Q⌉₊)) ≤ 1 / Q ^ 208 := by
  apply contraction_log_bound (lt_of_lt_of_le zero_lt_one hQ)
  have hc := Nat.le_ceil (Real.log Q)
  have hl := Real.log_nonneg hQ
  push_cast
  nlinarith

lemma polynomial_power_mono {Q : ℝ} (hQ : 1 ≤ Q) {a b : ℕ} (hab : a ≤ b) : Q ^ a ≤ Q ^ b :=
  pow_le_pow_right₀ hQ hab

lemma model_probe_error {ε R Q L : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hLlo : ε / R ^ 4 ≤ L) (hLhi : L ≤ ε / R ^ 4 * Q ^ 3) :
    (1 / Q ^ 142) * L * (R * Q ^ 18) ^ 3 / 6 ≤ ε / (R * Q ^ 84) ∧
      ε / (R * Q ^ 84) ≤ L * (R / Q ^ 28) ^ 3 := by
  have hQpos : 0 < Q := by linarith
  constructor
  · have hh := mul_le_mul_of_nonneg_left hLhi (show 0 ≤ (1 / Q ^ 142) * (R * Q ^ 18) ^ 3 / 6 by positivity)
    have he : ((1 / Q ^ 142) * (R * Q ^ 18) ^ 3 / 6) * (ε / R ^ 4 * Q ^ 3) = ε / (6 * R * Q ^ 85) := by
      field_simp
    have he' : (1 / Q ^ 142) * L * (R * Q ^ 18) ^ 3 / 6 ≤ ε / (6 * R * Q ^ 85) := by
      rw [he] at hh
      convert hh using 1; ring
    apply he'.trans
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    have hp : Q ^ 84 ≤ Q ^ 85 := polynomial_power_mono (by linarith) (by decide)
    nlinarith [pow_pos hQpos 85]
  · have hh := mul_le_mul_of_nonneg_right hLlo (show 0 ≤ (R / Q ^ 28) ^ 3 by positivity)
    have he : (ε / R ^ 4) * (R / Q ^ 28) ^ 3 = ε / (R * Q ^ 84) := by
      field_simp
    rwa [he] at hh


lemma model_gradient_polynomial {Q : ℝ} (hQ : 3 ≤ Q) :
    Q ^ 46 + Q ^ 31 * Q ^ 18 + Q ^ 20 * (Q ^ 18) ^ 2 / 2 + Q ^ 3 * (Q ^ 18) ^ 3 ≤ Q ^ 61 := by
  have h1 : 1 ≤ Q := by linarith
  have h46 := polynomial_power_mono h1 (by decide : 46 ≤ 57)
  have h49 := polynomial_power_mono h1 (by decide : 49 ≤ 57)
  have h56 := polynomial_power_mono h1 (by decide : 56 ≤ 57)
  have h4 : (3 : ℝ) ^ 4 ≤ Q ^ 4 := pow_le_pow_left₀ (by norm_num) hQ 4
  have he : Q ^ 61 = Q ^ 4 * Q ^ 57 := by ring
  have hmul := mul_le_mul_of_nonneg_right h4 (show 0 ≤ Q ^ 57 by positivity)
  rw [← he] at hmul
  have hx : Q ^ 46 + Q ^ 31 * Q ^ 18 + Q ^ 20 * (Q ^ 18) ^ 2 / 2 + Q ^ 3 * (Q ^ 18) ^ 3 =
      Q ^ 46 + Q ^ 49 + Q ^ 56 / 2 + Q ^ 57 := by ring
  rw [hx]
  nlinarith [show 0 ≤ Q ^ 57 by positivity]

lemma model_hessian_polynomial {Q : ℝ} (hQ : 3 ≤ Q) :
    Q ^ 31 + Q ^ 20 * (Q ^ 18 + 1) + 3 * Q ^ 3 * (Q ^ 18 + 1) ^ 2 ≤ Q ^ 45 := by
  have h1 : 1 ≤ Q := by linarith
  have h31 := polynomial_power_mono h1 (by decide : 31 ≤ 39)
  have h38 := polynomial_power_mono h1 (by decide : 38 ≤ 39)
  have h20 := polynomial_power_mono h1 (by decide : 20 ≤ 39)
  have h21 := polynomial_power_mono h1 (by decide : 21 ≤ 39)
  have h3 := polynomial_power_mono h1 (by decide : 3 ≤ 39)
  have h6 : (3 : ℝ) ^ 6 ≤ Q ^ 6 := pow_le_pow_left₀ (by norm_num) hQ 6
  have he : Q ^ 45 = Q ^ 6 * Q ^ 39 := by ring
  have hmul := mul_le_mul_of_nonneg_right h6 (show 0 ≤ Q ^ 39 by positivity)
  rw [← he] at hmul
  have hx : Q ^ 31 + Q ^ 20 * (Q ^ 18 + 1) + 3 * Q ^ 3 * (Q ^ 18 + 1) ^ 2 =
      Q ^ 31 + Q ^ 38 + Q ^ 20 + 3 * Q ^ 39 + 6 * Q ^ 21 + 3 * Q ^ 3 := by ring
  rw [hx]
  nlinarith [show 0 ≤ Q ^ 39 by positivity]

lemma model_tolerance_margin {ε R Q : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) :
    ε / (R * Q ^ 84) ≤ (ε / (R * Q ^ 12)) / 24 := by
  have hQpos : 0 < Q := by linarith
  have h72 : (3 : ℝ) ^ 72 ≤ Q ^ 72 := pow_le_pow_left₀ (by norm_num) hQ 72
  have hlarge : 24 ≤ Q ^ 72 := by norm_num at h72 ⊢; linarith
  have he : Q ^ 84 = Q ^ 12 * Q ^ 72 := by ring
  rw [div_div]
  apply div_le_div_of_nonneg_left hε.le (by positivity)
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hlarge (show 0 ≤ R * Q ^ 12 by positivity)]


lemma model_budget_polynomial {ε R Q : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) :
    4 * (1 / Q ^ 208) * (ε * Q ^ 76) +
      288 * (ε / R ^ 4 * Q ^ 3) * (R / Q ^ 28) ^ 4 ≤
        (ε / (R * Q ^ 12)) ^ 2 / (288 * (ε / R ^ 2 * Q ^ 62)) := by
  have hQpos : 0 < Q := by linarith
  have h1 : 1 ≤ Q := by linarith
  have h6 : 288 ≤ Q ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 6
    norm_num at hh
    linarith
  have h2 : 4 ≤ Q ^ 2 := by nlinarith
  have he₁ : 4 * (1 / Q ^ 208) * (ε * Q ^ 76) = 4 * ε / Q ^ 132 := by field_simp
  have he₂ : 288 * (ε / R ^ 4 * Q ^ 3) * (R / Q ^ 28) ^ 4 = 288 * ε / Q ^ 109 := by field_simp
  have he₃ : (ε / (R * Q ^ 12)) ^ 2 / (288 * (ε / R ^ 2 * Q ^ 62)) = ε / (288 * Q ^ 86) := by field_simp
  rw [he₁, he₂, he₃]
  have ha : 4 * ε / Q ^ 132 ≤ ε / Q ^ 130 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : Q ^ 132 = Q ^ 2 * Q ^ 130 := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ ε * Q ^ 130 by positivity)]
  have hb : 288 * ε / Q ^ 109 ≤ ε / Q ^ 103 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : Q ^ 109 = Q ^ 6 * Q ^ 103 := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right h6 (show 0 ≤ ε * Q ^ 103 by positivity)]
  have hc : ε / Q ^ 130 ≤ ε / Q ^ 103 :=
    div_le_div_of_nonneg_left hε.le (by positivity) (polynomial_power_mono h1 (by decide))
  have hd : 2 * (ε / Q ^ 103) ≤ ε / Q ^ 102 := by
    have he : Q ^ 103 = Q * Q ^ 102 := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp
    nlinarith
  have he : ε / Q ^ 102 ≤ ε / (288 * Q ^ 86) := by
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    have h16 := h6.trans (polynomial_power_mono h1 (by decide : 6 ≤ 16))
    have hp : Q ^ 102 = Q ^ 16 * Q ^ 86 := by ring
    rw [hp]
    exact mul_le_mul_of_nonneg_right h16 (by positivity)
  linarith


lemma model_physical_caps {ε R Q G H T L : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hG : G ≤ ε / R * Q ^ 46) (hH : H ≤ ε / R ^ 2 * Q ^ 31)
    (hT : T ≤ ε / R ^ 3 * Q ^ 20) (hL : L ≤ ε / R ^ 4 * Q ^ 3) :
    G + H * (R * Q ^ 18) + T * (R * Q ^ 18) ^ 2 / 2 + L * (R * Q ^ 18) ^ 3 ≤
      (ε / R ^ 2 * Q ^ 62) * R ∧
    H + T * (R * Q ^ 18 + R) + 3 * L * (R * Q ^ 18 + R) ^ 2 ≤ ε / R ^ 2 * Q ^ 62 := by
  have hQpos : 0 < Q := by linarith
  have h1 : 1 ≤ Q := by linarith
  constructor
  · calc
      _ ≤ ε / R * Q ^ 46 + (ε / R ^ 2 * Q ^ 31) * (R * Q ^ 18) +
          (ε / R ^ 3 * Q ^ 20) * (R * Q ^ 18) ^ 2 / 2 +
          (ε / R ^ 4 * Q ^ 3) * (R * Q ^ 18) ^ 3 := by gcongr
      _ = ε / R * (Q ^ 46 + Q ^ 31 * Q ^ 18 + Q ^ 20 * (Q ^ 18) ^ 2 / 2 + Q ^ 3 * (Q ^ 18) ^ 3) := by
        field_simp
      _ ≤ ε / R * Q ^ 61 := mul_le_mul_of_nonneg_left (model_gradient_polynomial hQ) (by positivity)
      _ ≤ ε / R * Q ^ 62 := mul_le_mul_of_nonneg_left (polynomial_power_mono h1 (by decide)) (by positivity)
      _ = _ := by field_simp
  · calc
      _ ≤ ε / R ^ 2 * Q ^ 31 + (ε / R ^ 3 * Q ^ 20) * (R * Q ^ 18 + R) +
          3 * (ε / R ^ 4 * Q ^ 3) * (R * Q ^ 18 + R) ^ 2 := by gcongr
      _ = ε / R ^ 2 * (Q ^ 31 + Q ^ 20 * (Q ^ 18 + 1) + 3 * Q ^ 3 * (Q ^ 18 + 1) ^ 2) := by
        field_simp
      _ ≤ ε / R ^ 2 * Q ^ 45 := mul_le_mul_of_nonneg_left (model_hessian_polynomial hQ) (by positivity)
      _ ≤ ε / R ^ 2 * Q ^ 62 := mul_le_mul_of_nonneg_left (polynomial_power_mono h1 (by decide)) (by positivity)

lemma model_radius_cap {ε R Q G L : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hG : G ≤ ε / R * Q ^ 46) (hL : ε / R ^ 4 ≤ L) :
    16 * G ≤ L * (R * Q ^ 18) ^ 3 := by
  have hQpos : 0 < Q := by linarith
  have h8 : 16 ≤ Q ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 8
    norm_num at hh
    linarith
  calc
    16 * G ≤ 16 * (ε / R * Q ^ 46) := by gcongr
    _ ≤ (ε / R) * Q ^ 54 := by
      have he : Q ^ 54 = Q ^ 8 * Q ^ 46 := by ring
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_right h8 (show 0 ≤ ε / R * Q ^ 46 by positivity)]
    _ = (ε / R ^ 4) * (R * Q ^ 18) ^ 3 := by field_simp
    _ ≤ L * (R * Q ^ 18) ^ 3 := by gcongr


open LongTails.Algorithms.TensorFreeModel
open scoped RealInnerProductSpace

lemma kernel_initial_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) {L ρ : ℝ} (hL : 0 ≤ L) (u : E) (hu : ‖u‖ ≤ ρ) :
    kernelBregman H L 0 u ≤ ‖H‖ * ρ ^ 2 / 2 + L * ρ ^ 4 / 4 := by
  have hi : ⟪u, H u⟫ ≤ ‖H‖ * ‖u‖ ^ 2 := by
    calc
      ⟪u, H u⟫ ≤ ‖u‖ * ‖H u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖H‖ * ‖u‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  simp only [kernelBregman, kernelValue, kernelGradient, map_zero, inner_zero_left,
    inner_zero_right, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    mul_zero, zero_div, add_zero, sub_zero, smul_zero, inner_zero_left]
  have hh : ⟪u, H u⟫ / 2 + L * ‖u‖ ^ 4 / 4 ≤ ‖H‖ * ‖u‖ ^ 2 / 2 + L * ‖u‖ ^ 4 / 4 := by linarith
  exact hh.trans (by gcongr)

lemma model_energy_cap {ε R Q H L : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hH : H ≤ ε / R ^ 2 * Q ^ 31) (hL : L ≤ ε / R ^ 4 * Q ^ 3) :
    H * (R * Q ^ 18) ^ 2 / 2 + L * (R * Q ^ 18) ^ 4 / 4 ≤ ε * Q ^ 76 := by
  have hQpos : 0 < Q := by linarith
  calc
    _ ≤ (ε / R ^ 2 * Q ^ 31) * (R * Q ^ 18) ^ 2 / 2 +
        (ε / R ^ 4 * Q ^ 3) * (R * Q ^ 18) ^ 4 / 4 := by gcongr
    _ = ε * (Q ^ 67 / 2 + Q ^ 75 / 4) := by field_simp
    _ ≤ ε * Q ^ 76 := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      have h67 := polynomial_power_mono (by linarith : 1 ≤ Q) (by decide : 67 ≤ 76)
      have h75 := polynomial_power_mono (by linarith : 1 ≤ Q) (by decide : 75 ≤ 76)
      linarith [show 0 ≤ Q ^ 76 by positivity]


open LongTails.Proofs.TensorFreeModel LongTails.Proofs.TensorFreeModelConvergence
open LongTails.Proofs.TensorFreeModelExecution LongTails.Proofs.TensorFreeModelTermination
open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate.QueryPlan

lemma solveModel_concrete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {ε R Q L : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hLlo : ε / R ^ 4 ≤ L) (hLhi : L ≤ ε / R ^ 4 * Q ^ 3)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖) (z : E)
    (hG : ‖gradient (objective f) z‖ ≤ ε / R * Q ^ 46)
    (hH : ‖fderiv ℝ (gradient (objective f)) z‖ ≤ ε / R ^ 2 * Q ^ 31)
    (hthird : ‖fderiv ℝ (fderiv ℝ (gradient (objective f))) z‖ ≤ ε / R ^ 3 * Q ^ 20) :
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (solveModel L (1 / Q ^ 142) (R * Q ^ 18) (ε / (R * Q ^ 84)) (ε / (R * Q ^ 12)) z
        (5000 * (1 + ⌈Real.log Q⌉₊)))
    next.accepted = true ∧ Certificate (objective f) L (ε / (R * Q ^ 12)) z next := by
  have hQpos : 0 < Q := by linarith
  have hL : 0 < L := (by positivity : 0 < ε / R ^ 4).trans_le hLlo
  have hτ : 0 < 1 / Q ^ 142 := by positivity
  have hρ : 0 ≤ R * Q ^ 18 := by positivity
  have hδ := model_probe_error hε hR hQ hLlo hLhi
  have hsmall := model_tolerance_margin hε hR hQ
  obtain ⟨u, hu, hmin⟩ := global_model_min (FiniteSumThirdSmoothGeometry.objective_contDiff f hf)
    (OracleTemplate.FiniteSum.objective_convex hc) hL hρ
    (FiniteSumThirdSmoothGeometry.objective_third_lipschitz f hf hT) z
    (model_radius_cap hε hR hQ hG hLlo)
  have hcaps := model_physical_caps hε hR hQ hG hH hthird hLhi
  have henergy := (kernel_initial_upper _ hL.le u
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu)).trans
    (model_energy_cap hε hR hQ hH hLhi)
  have henergy0 := objective_kernel_nonneg f hf hc hL.le z 0 u
  have hcoeff : 2 * (1 + 1 / Real.sqrt 2) ≤ (4 : ℝ) := by linarith [kernel_constants.1]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 5000 * (1 + ⌈Real.log Q⌉₊) = k + 1 := by
    exact ⟨5000 * (1 + ⌈Real.log Q⌉₊) - 1, by omega⟩
  have hcontract := model_iterations_log_bound (by linarith : 1 ≤ Q)
  rw [hk] at hcontract
  have hbudget : (2 * (1 + 1 / Real.sqrt 2)) * (23 / 24 : ℝ) ^ (k + 1) *
      kernelBregman (fderiv ℝ (gradient (objective f)) z) L 0 u +
      24 * (2 * (1 + 1 / Real.sqrt 2)) * (3 * L * (R / Q ^ 28) ^ 4) ≤
        (ε / (R * Q ^ 12)) ^ 2 / (288 * (ε / R ^ 2 * Q ^ 62)) := by
    apply le_trans _ (model_budget_polynomial hε hR hQ)
    have ha : (2 * (1 + 1 / Real.sqrt 2)) * (23 / 24 : ℝ) ^ (k + 1) *
        kernelBregman (fderiv ℝ (gradient (objective f)) z) L 0 u ≤
        4 * (1 / Q ^ 208) * (ε * Q ^ 76) := by gcongr
    have hb : 24 * (2 * (1 + 1 / Real.sqrt 2)) * (3 * L * (R / Q ^ 28) ^ 4) ≤
        288 * (ε / R ^ 4 * Q ^ 3) * (R / Q ^ 28) ^ 4 := by
      calc
        _ ≤ 24 * 4 * (3 * (ε / R ^ 4 * Q ^ 3) * (R / Q ^ 28) ^ 4) := by gcongr
        _ = _ := by ring
    exact add_le_add ha hb
  have haccept := solveModel_terminates f hf hc hL.le hτ hρ (by positivity : 0 ≤ R / Q ^ 28)
    (by positivity : 0 < ε / R ^ 2 * Q ^ 62) hR.le (by positivity : 0 ≤ ε / (R * Q ^ 12))
    hT hδ.1 hδ.2 hsmall z u hu k hcaps.1 hcaps.2 hmin hbudget
  rw [← hk] at haccept
  exact ⟨haccept, solveModel_certificate f hf hL.le hτ hρ hT hδ.1 z _ haccept⟩

end LongTails.Proofs.TensorFreeModelTuning
