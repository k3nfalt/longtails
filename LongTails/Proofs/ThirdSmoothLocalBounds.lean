import LongTails.Proofs.TensorFreeModelTermination
import LongTails.Proofs.QuarticFiniteSum
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace LongTails.Proofs.ThirdSmoothLocalBounds

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma third_initial_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hx : ‖fderiv ℝ (gradient f) x‖ ≤ H) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ 6 * Real.sqrt (2 * L * H) := by
  have hbound : ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ Real.sqrt (2 * L * H) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro s
    have hsym : (fderiv ℝ (fderiv ℝ (gradient f)) x s).IsSymmetric := by
      intro v w
      change ⟪fderiv ℝ (fderiv ℝ (gradient f)) x s v, w⟫ =
        ⟪v, fderiv ℝ (fderiv ℝ (gradient f)) x s w⟫
      exact (ThirdOrderObjectiveGeometry.third_swap_last hf x s v w).trans (real_inner_comm _ _)
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
    apply ciSup_le
    intro v
    by_cases hv : v = 0
    · subst v
      simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
      positivity
    have hvpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
    have hh : ⟪fderiv ℝ (gradient f) x v, v⟫ ≤ H * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖fderiv ℝ (gradient f) x v‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ (H * ‖v‖) * ‖v‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
        _ = _ := by ring
    have ht := TensorFreeModel.third_mixed_bound hf hc hT x s v
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * L * ‖s‖ ^ 2 * ‖v‖ ^ 2 by positivity)
    have hquad : |⟪fderiv ℝ (fderiv ℝ (gradient f)) x s v, v⟫| ≤
        (Real.sqrt (2 * L * H) * ‖s‖) * ‖v‖ ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    change |⟪fderiv ℝ (fderiv ℝ (gradient f)) x s v, v⟫ / ‖v‖ ^ 2| ≤ _
    rw [abs_div, abs_of_pos hvpos]
    exact (div_le_iff₀ hvpos).mpr hquad
  linarith [Real.sqrt_nonneg (2 * L * H)]

lemma hessian_local_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L H T : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x y : E) (hH : ‖fderiv ℝ (gradient f) x‖ ≤ H)
    (hthird : ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ T) :
    ‖fderiv ℝ (gradient f) y‖ ≤ H + T * ‖y - x‖ + L * ‖y - x‖ ^ 2 / 2 := by
  have hr := TensorFreeModel.hessian_remainder hf hT x (y - x)
  rw [add_sub_cancel] at hr
  have ht := (ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ (gradient f)) x) (y - x)).trans
    (mul_le_mul_of_nonneg_right hthird (norm_nonneg _))
  have he : fderiv ℝ (gradient f) y =
      (fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x - fderiv ℝ (fderiv ℝ (gradient f)) x (y - x)) +
        fderiv ℝ (fderiv ℝ (gradient f)) x (y - x) + fderiv ℝ (gradient f) x := by abel
  have hn₁ := norm_add_le
    (fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x - fderiv ℝ (fderiv ℝ (gradient f)) x (y - x))
    (fderiv ℝ (fderiv ℝ (gradient f)) x (y - x))
  have hn₂ := norm_add_le
    ((fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) x - fderiv ℝ (fderiv ℝ (gradient f)) x (y - x)) +
      fderiv ℝ (fderiv ℝ (gradient f)) x (y - x)) (fderiv ℝ (gradient f) x)
  rw [← he] at hn₂
  linarith


lemma gradient_local_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L G H T : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x y : E) (hG : ‖gradient f x‖ ≤ G) (hH : ‖fderiv ℝ (gradient f) x‖ ≤ H)
    (hthird : ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ T) :
    ‖gradient f y‖ ≤ G + H * ‖y - x‖ + T * ‖y - x‖ ^ 2 / 2 + L * ‖y - x‖ ^ 3 / 6 := by
  let d := y - x
  let a := fderiv ℝ (gradient f) x d
  let b := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) x d d
  let e := gradient f y - gradient f x - a - b
  have hr : ‖e‖ ≤ L * ‖d‖ ^ 3 / 6 := by
    simpa only [d, a, b, e, add_sub_cancel] using TensorFreeModel.gradient_remainder hf hT x (y - x)
  have ha : ‖a‖ ≤ H * ‖d‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hb : ‖b‖ ≤ T * ‖d‖ ^ 2 / 2 := by
    have hh : ‖fderiv ℝ (fderiv ℝ (gradient f)) x d d‖ ≤ T * ‖d‖ ^ 2 := by
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ (gradient f)) x d‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (T * ‖d‖) * ‖d‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hthird (norm_nonneg _))
        _ = _ := by ring
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have he : gradient f y = gradient f x + a + b + e := by dsimp [e]; module
  have h₁ := norm_add_le (gradient f x) a
  have h₂ := norm_add_le (gradient f x + a) b
  have h₃ := norm_add_le (gradient f x + a + b) e
  rw [← he] at h₃
  change ‖gradient f y‖ ≤ G + H * ‖d‖ + T * ‖d‖ ^ 2 / 2 + L * ‖d‖ ^ 3 / 6
  linarith

lemma third_local_bound {f : E → ℝ} {L T : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x y : E) (hthird : ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ T) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ T + L * ‖y - x‖ := by
  have hh := norm_sub_norm_le (fderiv ℝ (fderiv ℝ (gradient f)) y)
    (fderiv ℝ (fderiv ℝ (gradient f)) x)
  linarith [hT y x]


open LongTails.Algorithms.QuarticProximal

omit [FiniteDimensional ℝ E] in
lemma quartic_third_norm (x : E) : ‖fderiv ℝ (hess : E → E →L[ℝ] E) x‖ ≤ 6 * ‖x‖ := by
  have hz : fderiv ℝ (hess : E → E →L[ℝ] E) 0 = 0 := by
    ext u v
    simp only [QuarticProximalGeometry.hess_derivative_apply, inner_zero_left, mul_zero,
      zero_smul, smul_zero, add_zero, zero_apply]
  simpa only [hz, sub_zero] using QuarticProximalGeometry.hess_derivative_lipschitz x 0

lemma penalty_third_norm {γ μ : ℝ} (hγ : 0 ≤ γ) (c y0 x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x‖ ≤ 6 * γ * ‖x - c‖ := by
  have hg : gradient (penalty γ μ c y0) = penaltyGrad γ μ c y0 :=
    gradient_eq (QuarticProximalGeometry.penalty_hasGradientAt γ μ c y0)
  have hh : fderiv ℝ (penaltyGrad γ μ c y0) = penaltyHess γ μ c :=
    funext (fun z => (QuarticProximalGeometry.penaltyGrad_hasFDerivAt γ μ c y0 z).fderiv)
  rw [hg, hh, QuarticProximalGeometry.penaltyHess_derivative]
  have hs := ContinuousLinearMap.opNorm_smul_le γ (fderiv ℝ (hess : E → E →L[ℝ] E) (x - c))
  rw [Real.norm_eq_abs, abs_of_nonneg hγ] at hs
  have ht := mul_le_mul_of_nonneg_left (quartic_third_norm (x - c)) hγ
  exact hs.trans (by nlinarith)

lemma augmented_local_norms {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {γ : ℝ} (hγ : 0 ≤ γ) (c x : E) :
    let F := fun y => f y + penalty γ 0 c c y
    ‖gradient F x‖ ≤ ‖gradient f x‖ + γ * ‖x - c‖ ^ 3 ∧
    ‖fderiv ℝ (gradient F) x‖ ≤ ‖fderiv ℝ (gradient f) x‖ + 3 * γ * ‖x - c‖ ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ (gradient F)) x‖ ≤ ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ + 6 * γ * ‖x - c‖ := by
  dsimp only
  have hg := QuarticFiniteSum.component_gradient (fun _ : Fin 1 => f) (fun _ => hf) γ 0 c c x 0
  have hH := QuarticFiniteSum.component_hessian (fun _ : Fin 1 => f) (fun _ => hf) γ 0 c c x 0
  have hT := QuarticFiniteSum.component_third (fun _ : Fin 1 => f) (fun _ => hf) γ 0 c c x 0
  constructor
  · rw [hg]
    have hn : ‖penaltyGrad γ 0 c c x‖ = γ * ‖x - c‖ ^ 3 := by
      simp only [penaltyGrad, zero_smul, add_zero, grad, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hγ, abs_of_nonneg (sq_nonneg ‖x - c‖)]
      ring
    exact (norm_add_le _ _).trans_eq (by rw [hn])
  constructor
  · rw [hH]
    have hn : ‖penaltyHess γ 0 c x‖ ≤ 3 * γ * ‖x - c‖ ^ 2 := by
      simp only [penaltyHess, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
      have hh := mul_le_mul_of_nonneg_left (TensorFreeModelTermination.quartic_hessian_norm (x - c)) hγ
      nlinarith
    exact (norm_add_le _ _).trans (by linarith)
  · rw [hT]
    have hh := ContinuousLinearMap.opNorm_add_le (fderiv ℝ (fderiv ℝ (gradient f)) x)
      (fderiv ℝ (fderiv ℝ (gradient (penalty γ 0 c c))) x)
    have hp := penalty_third_norm (μ := 0) hγ c c x
    linarith

end LongTails.Proofs.ThirdSmoothLocalBounds
