import LongTails.Proofs.RelativeHessianSimulation
import LongTails.Setups.PointwiseHessianStationarity

namespace LongTails.Proofs.RelativeHessianScaling

open scoped RealInnerProductSpace
open RelativeHessianSimulation RelativeHessianOracle

variable {d m : ℕ}

noncomputable def scaled (a β : ℝ) (π : Fin (m + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  a * RelativeHessianLocalized.value (axes π) (β • x)

noncomputable def scaleReply (a β : ℝ) (v : Reply (EuclideanSpace ℝ (Fin d))) :
    Reply (EuclideanSpace ℝ (Fin d)) := (a * v.1, (a * β) • v.2.1, (a * β ^ 2) • v.2.2)

lemma scaled_smooth (a β : ℝ) (π : Fin (m + 1) ↪ Fin d) : ContDiff ℝ 3 (scaled a β π) := by
  apply contDiff_const.mul
  exact (RelativeHessianLocalized.smooth _).comp (by fun_prop)

lemma jet_scale (a β : ℝ) (π : Fin (m + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    jet (scaled a β π) x = scaleReply a β (jet (RelativeHessianLocalized.value (axes π)) (β • x)) := by
  unfold jet scaled scaleReply
  rw [ThirdOrderAffineCalculus.scale_gradient (RelativeHessianLocalized.smooth _),
    ThirdOrderAffineCalculus.scale_hessian (RelativeHessianLocalized.smooth _)]

lemma gradient_norm {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (scaled a β π) x‖ = (a * β) * ‖gradient (RelativeHessianLocalized.value (axes π)) (β • x)‖ := by
  unfold scaled
  rw [ThirdOrderAffineCalculus.scale_gradient (RelativeHessianLocalized.smooth _), norm_smul,
    Real.norm_of_nonneg (mul_nonneg ha hβ)]

lemma absolute_third {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ (gradient (scaled a β π))) x‖ ≤ 2 ^ 56 * a * β ^ 3 := by
  unfold scaled
  rw [ThirdOrderAffineCalculus.scale_third (RelativeHessianLocalized.smooth _)]
  have h := ThirdOrderAffineCalculus.norm_smul_tensor_le (a * β ^ 3)
    (fderiv ℝ (fderiv ℝ (gradient (RelativeHessianLocalized.value (axes π)))) (β • x))
  rw [abs_of_nonneg (mul_nonneg ha (pow_nonneg hβ 3))] at h
  exact h.trans (by
    have ht := mul_le_mul_of_nonneg_left (RelativeHessianLocalized.absolute_third (axes_orthonormal π) (β • x))
      (mul_nonneg ha (pow_nonneg hβ 3))
    nlinarith)

lemma relative_third {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ (gradient (scaled a β π))) x‖ ≤ 2 ^ 56 * β ^ 2 * ‖gradient (scaled a β π) x‖ := by
  rw [gradient_norm ha hβ]
  unfold scaled
  rw [ThirdOrderAffineCalculus.scale_third (RelativeHessianLocalized.smooth _)]
  have h := ThirdOrderAffineCalculus.norm_smul_tensor_le (a * β ^ 3)
    (fderiv ℝ (fderiv ℝ (gradient (RelativeHessianLocalized.value (axes π)))) (β • x))
  rw [abs_of_nonneg (mul_nonneg ha (pow_nonneg hβ 3))] at h
  exact h.trans (by
    have ht := mul_le_mul_of_nonneg_left (RelativeHessianLocalized.relative_third (axes_orthonormal π) (β • x))
      (mul_nonneg ha (pow_nonneg hβ 3))
    convert ht using 1
    ring)

lemma growth {a β L₀ L₁ ε : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (h₀ : 0 ≤ L₀) (h₁ : 0 ≤ L₁)
    (hε : 0 < ε) (habs : 2 ^ 56 * a * β ^ 3 ≤ L₀ + L₁ * ε)
    (hrel : 2 ^ 56 * β ^ 2 * ε ≤ L₀ + L₁ * ε) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ (gradient (scaled a β π))) x‖ ≤ L₀ + L₁ * ‖gradient (scaled a β π) x‖ := by
  by_cases hg : ε ≤ ‖gradient (scaled a β π) x‖
  · exact (absolute_third ha hβ π x).trans (habs.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg h₁)))
  · have hr := mul_le_mul_of_nonneg_right (relative_third ha hβ π x) hε.le
    have hs := mul_le_mul_of_nonneg_right hrel (norm_nonneg (gradient (scaled a β π) x))
    have hL := mul_le_mul_of_nonneg_left (le_of_not_ge hg) h₀
    nlinarith

lemma initial_gradient {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (π : Fin (m + 1) ↪ Fin d) :
    ‖gradient (scaled a β π) 0‖ = a * β := by
  rw [gradient_norm ha hβ]
  simp [RelativeHessianLocalized.initial_gradient, (axes_orthonormal π).norm_eq_one]

lemma gap {a β : ℝ} (ha : 0 ≤ a) (π : Fin (m + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    scaled a β π 0 - scaled a β π x ≤ a * (4 * (m + 1 : ℕ)) := by
  have h := mul_le_mul_of_nonneg_left (RelativeHessianLocalized.gap (axes π) (β • x)) ha
  simpa [scaled, mul_sub] using h

end LongTails.Proofs.RelativeHessianScaling
