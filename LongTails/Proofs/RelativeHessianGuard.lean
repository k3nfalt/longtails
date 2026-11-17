import LongTails.Proofs.RelativeHessianJetBounds
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery

namespace LongTails.Proofs.RelativeHessianGuard

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def value {m : ℕ} (v : Fin (m + 1) → E) (x : E) : ℝ :=
  chain v x + FullGeneralizedSmoothZeroQuery.quadratic coefficient 0 x

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma quadratic_smooth (a : ℝ) :
    ContDiff ℝ 3 (FullGeneralizedSmoothZeroQuery.quadratic a (0 : E)) := by
  unfold FullGeneralizedSmoothZeroQuery.quadratic
  exact contDiff_const.mul ((show ContDiff ℝ 3 (fun x : E => x - (0 : E)) from
    contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))

omit [FiniteDimensional ℝ E] in
lemma quadratic_gradient (a : ℝ) (x : E) :
    gradient (FullGeneralizedSmoothZeroQuery.quadratic a 0) x = a • x := by
  simpa [FullGeneralizedSmoothZeroQuery.field] using
    (FullGeneralizedSmoothZeroQuery.quadratic_gradient a (0 : E) x).gradient

omit [FiniteDimensional ℝ E] in
lemma quadratic_third (a : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (FullGeneralizedSmoothZeroQuery.quadratic a (0 : E)))) x = 0 := by
  have hg : gradient (FullGeneralizedSmoothZeroQuery.quadratic a (0 : E)) = fun y => a • y :=
    funext (quadratic_gradient a)
  have hH : fderiv ℝ (fun y : E => a • y) = fun _ => a • ContinuousLinearMap.id ℝ E := by
    funext y
    exact ((hasFDerivAt_id y).const_smul a).fderiv
  rw [hg, hH]
  exact (hasFDerivAt_const (𝕜 := ℝ) (a • ContinuousLinearMap.id ℝ E) x).fderiv

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smooth {m : ℕ} (v : Fin (m + 1) → E) : ContDiff ℝ 3 (value v) :=
  (chain_smooth v).add (quadratic_smooth coefficient)

lemma gradient_eq {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    gradient (value v) x = gradient (chain v) x + coefficient • x := by
  unfold value
  have h := ThirdOrderAffineCalculus.combination_gradient (chain_smooth v)
    (quadratic_smooth coefficient) 1 1 x
  simpa only [one_mul, one_smul, quadratic_gradient] using h

lemma third_eq {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (value v))) x =
      fderiv ℝ (fderiv ℝ (gradient (chain v))) x := by
  unfold value
  have h := ThirdOrderAffineCalculus.combination_third (chain_smooth v)
    (quadratic_smooth coefficient) 1 1 x
  simpa only [one_mul, one_smul, quadratic_third, add_zero] using h

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma bessel {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (u : E) :
    ∑ i, ⟪v i, u⟫ ^ 2 ≤ ‖u‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    hv.sum_inner_products_le (s := Finset.univ) u

lemma gradient_coordinate_plateau {m : ℕ} {v : Fin (m + 1) → E}
    (hv : Orthonormal ℝ v) (x : E) (hx : ∀ i, 1 / 5 ≤ |⟪v i, x⟫|) (j : Fin (m + 1)) :
    ⟪gradient (value v) x, v j⟫ = slope coefficient ⟪v j, x⟫ := by
  classical
  rw [gradient_eq, chain_gradient_plateau v x hx]
  simp [inner_add_left, sum_inner, inner_neg_left, real_inner_smul_left,
    orthonormal_iff_ite.mp hv, RelativeHessianArctan.slope]
  rw [real_inner_comm x (v j)]
  ring

lemma relative_plateau {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (hx : ∀ i, 1 / 5 ≤ |⟪v i, x⟫|) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x‖ ≤ 12 * ‖gradient (value v) x‖ := by
  have hc (i : Fin (m + 1)) : |densityCurvature ⟪v i, x⟫| ≤ 12 * ‖gradient (value v) x‖ := by
    have hb := abs_real_inner_le_norm (gradient (value v) x) (v i)
    rw [hv.norm_eq_one, mul_one, gradient_coordinate_plateau hv x hx i] at hb
    exact (balanced_relative _).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [third_eq, chain_third_plateau v x u w hx, norm_neg]
  have hsum : ∑ i, |⟪v i, u⟫| * |⟪v i, w⟫| ≤ ‖u‖ * ‖w‖ := by
    have h := SparseTensorBounds.sum_product_bound (fun i => |⟪v i, u⟫|)
      (fun i => |⟪v i, w⟫|) (norm_nonneg u) (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [sq_abs, one_mul] using bessel hv u)
      (by simpa only [sq_abs, one_mul] using bessel hv w)
    simpa only [one_mul] using h
  calc
    _ ≤ ∑ i, ‖(densityCurvature ⟪v i, x⟫ * ⟪v i, u⟫ * ⟪v i, w⟫) • v i‖ := norm_sum_le _ _
    _ = ∑ i, |densityCurvature ⟪v i, x⟫| * |⟪v i, u⟫| * |⟪v i, w⟫| := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, hv.norm_eq_one, mul_one]
    _ ≤ ∑ i, (12 * ‖gradient (value v) x‖) * |⟪v i, u⟫| * |⟪v i, w⟫| :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)) (abs_nonneg _))
    _ = (12 * ‖gradient (value v) x‖) * ∑ i, |⟪v i, u⟫| * |⟪v i, w⟫| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (12 * ‖gradient (value v) x‖) * (‖u‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end LongTails.Proofs.RelativeHessianGuard
