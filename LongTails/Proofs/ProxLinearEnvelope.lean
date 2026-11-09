import LongTails.Proofs.WeaklyConvexMoreau
import LongTails.Proofs.AdamLogGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ProxLinearEnvelope

variable {E : Type*} [NormedAddCommGroup E]

lemma model_prox_distance {F model : E → ℝ} {x y z : E} {γ : ℝ}
    (hγ : 0 < γ)
    (hy : F y ≤ model y + γ / 2 * ‖y - x‖ ^ 2)
    (hz : model z ≤ F z + γ / 2 * ‖z - x‖ ^ 2)
    (hmodel : model y + 2 * γ * ‖y - x‖ ^ 2 + 2 * γ * ‖y - z‖ ^ 2 ≤
      model z + 2 * γ * ‖z - x‖ ^ 2)
    (hprox : F z + γ * ‖z - x‖ ^ 2 + γ / 2 * ‖y - z‖ ^ 2 ≤
      F y + γ * ‖y - x‖ ^ 2) :
    ‖y - z‖ ^ 2 ≤ 3 / 5 * ‖z - x‖ ^ 2 - 1 / 5 * ‖y - x‖ ^ 2 := by
  have h : γ * (5 * ‖y - z‖ ^ 2 + ‖y - x‖ ^ 2) ≤
      γ * (3 * ‖z - x‖ ^ 2) := by linarith
  have := (mul_le_mul_iff_right₀ hγ).mp h
  linarith

lemma norm_add_sq_weighted (u v : E) :
    ‖u + v‖ ^ 2 ≤ 4 / 3 * ‖u‖ ^ 2 + 4 * ‖v‖ ^ 2 := by
  have ht := norm_add_le u v
  have hs : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 ht
  nlinarith [sq_nonneg (‖u‖ - 3 * ‖v‖)]

lemma perturbed_envelope_step {x y z yhat : E} {γ φold φnew Fz : ℝ}
    (hγ : 0 ≤ γ)
    (hmodel : ‖y - z‖ ^ 2 ≤ 3 / 5 * ‖z - x‖ ^ 2 - 1 / 5 * ‖y - x‖ ^ 2)
    (hold : φold = Fz + γ * ‖z - x‖ ^ 2)
    (hnew : φnew ≤ Fz + γ * ‖yhat - z‖ ^ 2) :
    φnew ≤ φold - γ / 5 * (‖z - x‖ ^ 2 + ‖y - x‖ ^ 2) +
      4 * γ * ‖yhat - y‖ ^ 2 := by
  have heq : y - z + (yhat - y) = yhat - z := by abel
  have hn := norm_add_sq_weighted (y - z) (yhat - y)
  rw [heq] at hn
  have hnγ := mul_le_mul_of_nonneg_left hn hγ
  have hmγ := mul_le_mul_of_nonneg_left hmodel hγ
  nlinarith [mul_nonneg hγ (sq_nonneg ‖y - x‖)]

section Inner

variable [InnerProductSpace ℝ E]

lemma model_step_inner {x y z : E}
    (hmodel : ‖y - z‖ ^ 2 ≤ 3 / 5 * ‖z - x‖ ^ 2 - 1 / 5 * ‖y - x‖ ^ 2) :
    2 * ⟪x - z, y - x⟫ ≤ -2 / 5 * ‖x - z‖ ^ 2 - 6 / 5 * ‖y - x‖ ^ 2 := by
  have heq : x - z + (y - x) = y - z := by abel
  have hn := norm_add_sq_real (x - z) (y - x)
  rw [heq] at hn
  rw [norm_sub_rev z x] at hmodel
  nlinarith

lemma inner_error_bound (u v : E) :
    2 * ⟪u, v⟫ ≤ 1 / 5 * ‖u‖ ^ 2 + 5 * ‖v‖ ^ 2 := by
  have hi := real_inner_le_norm u v
  nlinarith [sq_nonneg (‖u‖ - 5 * ‖v‖)]

lemma norm_add_sq_two (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real]
  have hi := real_inner_le_norm u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

lemma relaxed_perturbed_norm {x y z yhat : E} {θ : ℝ}
    (hθ : 0 ≤ θ) (hθmax : θ ≤ 1 / 10)
    (hmodel : ‖y - z‖ ^ 2 ≤ 3 / 5 * ‖z - x‖ ^ 2 - 1 / 5 * ‖y - x‖ ^ 2) :
    ‖x + θ • (yhat - x) - z‖ ^ 2 ≤
      ‖x - z‖ ^ 2 - θ * ‖y - x‖ ^ 2 + 6 * θ * ‖yhat - y‖ ^ 2 := by
  have hi := model_step_inner hmodel
  have he := inner_error_bound (x - z) (yhat - y)
  have hs := norm_add_sq_two (y - x) (yhat - y)
  have hadd : y - x + (yhat - y) = yhat - x := by abel
  rw [hadd] at hs
  have hip : ⟪x - z, yhat - x⟫ = ⟪x - z, y - x⟫ + ⟪x - z, yhat - y⟫ := by
    rw [← inner_add_right, hadd]
  have hexp : ‖x + θ • (yhat - x) - z‖ ^ 2 =
      ‖x - z‖ ^ 2 + 2 * θ * ⟪x - z, yhat - x⟫ + θ ^ 2 * ‖yhat - x‖ ^ 2 := by
    have h : x + θ • (yhat - x) - z = (x - z) + θ • (yhat - x) := by abel
    rw [h, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]
    ring
  rw [hexp, hip]
  have hiθ := mul_le_mul_of_nonneg_left hi hθ
  have heθ := mul_le_mul_of_nonneg_left he hθ
  have hsθ := mul_le_mul_of_nonneg_left hs (sq_nonneg θ)
  have hb := mul_nonneg (show 0 ≤ θ / 5 - 2 * θ ^ 2 by nlinarith)
    (sq_nonneg ‖y - x‖)
  have hd := mul_nonneg (show 0 ≤ θ - 2 * θ ^ 2 by nlinarith)
    (sq_nonneg ‖yhat - y‖)
  nlinarith [mul_nonneg hθ (sq_nonneg ‖x - z‖)]

lemma relaxed_envelope_step {x y z yhat : E} {γ θ φold φnew Fz : ℝ}
    (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hθmax : θ ≤ 1 / 10)
    (hmodel : ‖y - z‖ ^ 2 ≤ 3 / 5 * ‖z - x‖ ^ 2 - 1 / 5 * ‖y - x‖ ^ 2)
    (hold : φold = Fz + γ * ‖z - x‖ ^ 2)
    (hnew : φnew ≤ Fz + γ * ‖x + θ • (yhat - x) - z‖ ^ 2) :
    φnew ≤ φold - γ * θ * ‖y - x‖ ^ 2 + 6 * γ * θ * ‖yhat - y‖ ^ 2 := by
  have hn := relaxed_perturbed_norm (yhat := yhat) hθ hθmax hmodel
  have hnγ := mul_le_mul_of_nonneg_left hn hγ
  rw [norm_sub_rev z x] at hold
  nlinarith

lemma smooth_model_abs_error [CompleteSpace E] {f : E → ℝ} {g : E → E} {L : ℝ}
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    |f y - f x - ⟪g x, y - x⟫| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have hs : ∀ u v, (0 : ℝ) * ‖v - u‖ ≤ 1 →
      ‖g v - g u‖ ≤ (L + 0 * ‖g u‖) * ‖v - u‖ := by
    intro u v _
    simpa only [zero_mul, add_zero] using hlip v u
  simpa only [zero_mul, add_zero] using
    LongTails.Proofs.AdamLogGeometry.local_remainder (L0 := L) (L1 := 0)
      (by norm_num) hgrad hs x y (by norm_num)

end Inner

end LongTails.Proofs.ProxLinearEnvelope
