import LongTails.Proofs.ThirdSmoothLocalBounds
import LongTails.Algorithms.QuarticProximalTrial
import LongTails.Proofs.TensorFreeModelTuning

namespace LongTails.Proofs.QuarticLocalTuning

open LongTails.Proofs.TensorFreeModelTuning

lemma initial_third_cap {ε R Q L H : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hLhi : L ≤ ε / R ^ 4 * Q) (hHhi : H ≤ ε / R ^ 2 * Q) :
    6 * Real.sqrt (2 * L * H) ≤ ε / R ^ 3 * Q ^ 4 := by
  have hQpos : 0 < Q := by linarith
  have hprod : 2 * L * H ≤ 2 * (ε / R ^ 4 * Q) * (ε / R ^ 2 * Q) := by gcongr
  have he : 2 * (ε / R ^ 4 * Q) * (ε / R ^ 2 * Q) = 2 * (ε / R ^ 3) ^ 2 * Q ^ 2 := by field_simp
  rw [he] at hprod
  have h6 : 72 ≤ Q ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 6
    norm_num at hh
    linarith
  have hh := mul_le_mul_of_nonneg_right h6 (show 0 ≤ (ε / R ^ 3) ^ 2 * Q ^ 2 by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have he' : (ε / R ^ 3 * Q ^ 4) ^ 2 = Q ^ 6 * ((ε / R ^ 3) ^ 2 * Q ^ 2) := by ring
  rw [he']
  nlinarith

lemma local_gradient_polynomial {Q : ℝ} (hQ : 3 ≤ Q) :
    Q + Q * Q ^ 14 + Q ^ 4 * (Q ^ 14) ^ 2 / 2 + Q * (Q ^ 14) ^ 3 / 6 + Q * (Q ^ 14) ^ 3 ≤ Q ^ 46 := by
  have h1 : 1 ≤ Q := by linarith
  have h01 : Q ≤ Q ^ 43 := by simpa using polynomial_power_mono h1 (by decide : 1 ≤ 43)
  have h15 := polynomial_power_mono h1 (by decide : 15 ≤ 43)
  have h32 := polynomial_power_mono h1 (by decide : 32 ≤ 43)
  have h3 : (3 : ℝ) ^ 3 ≤ Q ^ 3 := pow_le_pow_left₀ (by norm_num) hQ 3
  have hm := mul_le_mul_of_nonneg_right h3 (show 0 ≤ Q ^ 43 by positivity)
  have he : Q ^ 46 = Q ^ 3 * Q ^ 43 := by ring
  rw [← he] at hm
  have hx : Q + Q * Q ^ 14 + Q ^ 4 * (Q ^ 14) ^ 2 / 2 + Q * (Q ^ 14) ^ 3 / 6 + Q * (Q ^ 14) ^ 3 =
      Q + Q ^ 15 + Q ^ 32 / 2 + Q ^ 43 / 6 + Q ^ 43 := by ring
  rw [hx]
  nlinarith [show 0 ≤ Q ^ 43 by positivity]

lemma local_hessian_polynomial {Q : ℝ} (hQ : 3 ≤ Q) :
    Q + Q ^ 4 * Q ^ 14 + Q * (Q ^ 14) ^ 2 / 2 + 3 * Q * (Q ^ 14) ^ 2 ≤ Q ^ 31 := by
  have h1 : 1 ≤ Q := by linarith
  have h01 : Q ≤ Q ^ 29 := by simpa using polynomial_power_mono h1 (by decide : 1 ≤ 29)
  have h18 := polynomial_power_mono h1 (by decide : 18 ≤ 29)
  have h2 : (3 : ℝ) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by norm_num) hQ 2
  have hm := mul_le_mul_of_nonneg_right h2 (show 0 ≤ Q ^ 29 by positivity)
  have he : Q ^ 31 = Q ^ 2 * Q ^ 29 := by ring
  rw [← he] at hm
  have hx : Q + Q ^ 4 * Q ^ 14 + Q * (Q ^ 14) ^ 2 / 2 + 3 * Q * (Q ^ 14) ^ 2 =
      Q + Q ^ 18 + Q ^ 29 / 2 + 3 * Q ^ 29 := by ring
  rw [hx]
  nlinarith [show 0 ≤ Q ^ 29 by positivity]

lemma local_third_polynomial {Q : ℝ} (hQ : 3 ≤ Q) :
    Q ^ 4 + Q * Q ^ 14 + 6 * Q * Q ^ 14 ≤ Q ^ 20 := by
  have h1 : 1 ≤ Q := by linarith
  have h4 := polynomial_power_mono h1 (by decide : 4 ≤ 15)
  have h5 : (3 : ℝ) ^ 5 ≤ Q ^ 5 := pow_le_pow_left₀ (by norm_num) hQ 5
  have hm := mul_le_mul_of_nonneg_right h5 (show 0 ≤ Q ^ 15 by positivity)
  have he : Q ^ 20 = Q ^ 5 * Q ^ 15 := by ring
  rw [← he] at hm
  have hx : Q ^ 4 + Q * Q ^ 14 + 6 * Q * Q ^ 14 = Q ^ 4 + 7 * Q ^ 15 := by ring
  rw [hx]
  nlinarith [show 0 ≤ Q ^ 15 by positivity]


open LongTails.Algorithms.QuarticProximal
open LongTails.Proofs.ThirdSmoothLocalBounds

lemma augmented_model_caps {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    {ε R Q L γ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hLhi : L ≤ ε / R ^ 4 * Q) (hγhi : γ ≤ ε / R ^ 4 * Q)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x0 c z : E) (hG0 : ‖gradient f x0‖ ≤ ε / R * Q)
    (hH0 : ‖fderiv ℝ (gradient f) x0‖ ≤ ε / R ^ 2 * Q)
    (hz0 : ‖z - x0‖ ≤ R * Q ^ 14) (hzc : ‖z - c‖ ≤ R * Q ^ 14) :
    let F := fun x => f x + penalty γ 0 c c x
    ‖gradient F z‖ ≤ ε / R * Q ^ 46 ∧
    ‖fderiv ℝ (gradient F) z‖ ≤ ε / R ^ 2 * Q ^ 31 ∧
    ‖fderiv ℝ (fderiv ℝ (gradient F)) z‖ ≤ ε / R ^ 3 * Q ^ 20 := by
  have hQpos : 0 < Q := by linarith
  have hT0 : ‖fderiv ℝ (fderiv ℝ (gradient f)) x0‖ ≤ ε / R ^ 3 * Q ^ 4 :=
    (third_initial_bound hf hc hL (norm_nonneg _) hT x0 le_rfl).trans
      (initial_third_cap hε hR hQ hL (norm_nonneg _) hLhi hH0)
  have hGz := gradient_local_bound hf hT x0 z hG0 hH0 hT0
  have hHz := hessian_local_bound hf hT x0 z hH0 hT0
  have hTz := third_local_bound hT x0 z hT0
  have haug := augmented_local_norms hf hγ c z
  dsimp only at haug ⊢
  constructor
  · calc
      _ ≤ ‖gradient f z‖ + γ * ‖z - c‖ ^ 3 := haug.1
      _ ≤ ε / R * Q + (ε / R ^ 2 * Q) * ‖z - x0‖ +
          (ε / R ^ 3 * Q ^ 4) * ‖z - x0‖ ^ 2 / 2 + L * ‖z - x0‖ ^ 3 / 6 + γ * ‖z - c‖ ^ 3 := by linarith
      _ ≤ ε / R * Q + (ε / R ^ 2 * Q) * (R * Q ^ 14) +
          (ε / R ^ 3 * Q ^ 4) * (R * Q ^ 14) ^ 2 / 2 +
          (ε / R ^ 4 * Q) * (R * Q ^ 14) ^ 3 / 6 + (ε / R ^ 4 * Q) * (R * Q ^ 14) ^ 3 := by gcongr
      _ = ε / R * (Q + Q * Q ^ 14 + Q ^ 4 * (Q ^ 14) ^ 2 / 2 + Q * (Q ^ 14) ^ 3 / 6 + Q * (Q ^ 14) ^ 3) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (local_gradient_polynomial hQ) (by positivity)
  constructor
  · calc
      _ ≤ ‖fderiv ℝ (gradient f) z‖ + 3 * γ * ‖z - c‖ ^ 2 := haug.2.1
      _ ≤ ε / R ^ 2 * Q + (ε / R ^ 3 * Q ^ 4) * ‖z - x0‖ + L * ‖z - x0‖ ^ 2 / 2 +
          3 * γ * ‖z - c‖ ^ 2 := by linarith
      _ ≤ ε / R ^ 2 * Q + (ε / R ^ 3 * Q ^ 4) * (R * Q ^ 14) +
          (ε / R ^ 4 * Q) * (R * Q ^ 14) ^ 2 / 2 + 3 * (ε / R ^ 4 * Q) * (R * Q ^ 14) ^ 2 := by gcongr
      _ = ε / R ^ 2 * (Q + Q ^ 4 * Q ^ 14 + Q * (Q ^ 14) ^ 2 / 2 + 3 * Q * (Q ^ 14) ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (local_hessian_polynomial hQ) (by positivity)
  · calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ + 6 * γ * ‖z - c‖ := haug.2.2
      _ ≤ ε / R ^ 3 * Q ^ 4 + L * ‖z - x0‖ + 6 * γ * ‖z - c‖ := by linarith
      _ ≤ ε / R ^ 3 * Q ^ 4 + (ε / R ^ 4 * Q) * (R * Q ^ 14) +
          6 * (ε / R ^ 4 * Q) * (R * Q ^ 14) := by gcongr
      _ = ε / R ^ 3 * (Q ^ 4 + Q * Q ^ 14 + 6 * Q * Q ^ 14) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (local_third_polynomial hQ) (by positivity)


open LongTails.Setups.FiniteSumSmoothAndConvex
open LongTails.Algorithms.TaylorCorrectedNewton LongTails.Algorithms.QuarticProximalTrial
open LongTails.Proofs.TensorFreeModelExecution
open OracleTemplate.QueryPlan

lemma modelSolve_certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {ε R Q L M γ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hLhi : L ≤ ε / R ^ 4 * Q) (hγhi : γ ≤ ε / R ^ 4 * Q)
    (hMlo : ε / R ^ 4 ≤ M) (hMhi : M ≤ ε / R ^ 4 * Q ^ 3) (hLM : L + 6 * γ ≤ M)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (x0 c z : E) (hG0 : ‖gradient (objective f) x0‖ ≤ ε / R * Q)
    (hH0 : ‖fderiv ℝ (gradient (objective f)) x0‖ ≤ ε / R ^ 2 * Q)
    (hz0 : ‖z - x0‖ ≤ R * Q ^ 14) (hzc : ‖z - c‖ ≤ R * Q ^ 14) :
    let F := fun x => objective f x + penalty γ 0 c c x
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelSolve ε R Q M γ c z)
    next.accepted = true ∧ Certificate F M (ε / (R * Q ^ 12)) z next := by
  let aug := fun i x => f i x + penalty γ 0 c c x
  have hfaug : ∀ i, ContDiff ℝ 3 (aug i) := QuarticFiniteSum.component_contDiff f hf γ 0 c c
  have hcaug : ∀ i, ConvexOn ℝ Set.univ (aug i) :=
    QuarticFiniteSum.component_convex f hf hc hγ le_rfl c c
  have hTaug (i : Fin n) (x y : E) :
      ‖fderiv ℝ (fderiv ℝ (gradient (aug i))) x - fderiv ℝ (fderiv ℝ (gradient (aug i))) y‖ ≤ M * ‖x - y‖ :=
    (QuarticFiniteSum.component_third_lipschitz f hf hγ hT c c x y i).trans
      (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))
  have he : objective aug = fun x => objective f x + penalty γ 0 c c x :=
    funext (QuarticFiniteSum.objective_penalty f γ 0 c c)
  have hcaps := augmented_model_caps (FiniteSumThirdSmoothGeometry.objective_contDiff f hf)
    (OracleTemplate.FiniteSum.objective_convex hc) hε hR hQ hL hγ hLhi hγhi
    (FiniteSumThirdSmoothGeometry.objective_third_lipschitz f hf hT) x0 c z hG0 hH0 hz0 hzc
  rw [← he] at hcaps
  have hh := solveModel_concrete aug hfaug hcaug hε hR hQ hMlo hMhi hTaug z hcaps.1 hcaps.2.1 hcaps.2.2
  rw [he] at hh
  simpa only [modelSolve, TaylorCorrectedStep.eval_augmentPlan, QuarticFiniteSum.augment_answer f hf] using hh

end LongTails.Proofs.QuarticLocalTuning
