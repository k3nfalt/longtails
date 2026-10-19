import LongTails.Proofs.SymmetricReverseFisherRidge
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology
namespace LongTails.Proofs.SymmetricReverseFisherGradient
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherCoefficients
lemma hasFDerivAt_euclidean_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {θ : E} (hθ : θ ≠ 0) :
    HasFDerivAt (fun x : E => ‖x‖) (‖θ‖⁻¹ • innerSL ℝ θ) θ := by
  have hr : 0 < ‖θ‖ := norm_pos_iff.mpr hθ
  have h := (Real.hasDerivAt_sqrt (pow_ne_zero 2 hr.ne')).comp_hasFDerivAt θ
    (hasStrictFDerivAt_norm_sq θ).hasFDerivAt
  convert h using 1
  · ext x
    simp
  · ext x
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
      Real.sqrt_sq (norm_nonneg θ)]
    field_simp
    simp only [two_smul]
    ring

lemma hasGradientAt_radial_nonzero {p : Params} {θ : Space p} (hθ : θ ≠ 0) :
    HasGradientAt (fun x : Space p => radialSelf ‖x‖) (alpha ‖θ‖ • θ) θ := by
  have hr : ‖θ‖ ≠ 0 := norm_ne_zero_iff.mpr hθ
  have h := (hasDerivAt_radialSelf ‖θ‖).comp_hasFDerivAt θ (hasFDerivAt_euclidean_norm hθ)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext x
    simp only [InnerProductSpace.toDual_apply_apply, inner_smul_left, conj_trivial,
      smul_apply, smul_eq_mul, innerSL_apply_apply, radialFirst_eq_alpha]
    field_simp

lemma hasGradientAt_radial_zero {p : Params} :
    HasGradientAt (fun x : Space p => radialSelf ‖x‖) 0 0 := by
  rw [hasGradientAt_iff_tendsto]
  have hf0 : radialSelf 0 = 0 := by simp [radialSelf]
  simp only [norm_zero, hf0, inner_zero_left, sub_zero]
  have hb (x : Space p) : ‖x‖⁻¹ * ‖radialSelf ‖x‖‖ ≤ ‖x‖ ^ 3 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialSelf_nonneg _)]
    have h := mul_le_mul_of_nonneg_left (radialSelf_le_fourth ‖x‖)
      (inv_nonneg.mpr (norm_nonneg x))
    calc
      _ ≤ ‖x‖⁻¹ * ‖x‖ ^ 4 := h
      _ = _ := by
        by_cases hx : x = 0
        · simp [hx]
        · field_simp [norm_ne_zero_iff.mpr hx]
  have ht : Tendsto (fun x : Space p => ‖x‖ ^ 3) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : Space p)).pow 3
  exact squeeze_zero (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hb ht
lemma hasGradientAt_radial {p : Params} (θ : Space p) :
    HasGradientAt (fun x : Space p => radialSelf ‖x‖) (alpha ‖θ‖ • θ) θ := by
  by_cases hθ : θ = 0
  · subst θ
    simpa using (hasGradientAt_radial_zero (p := p))
  · exact hasGradientAt_radial_nonzero hθ
lemma hasGradientAt_loss {p : Params} (μ θ : Space p) :
    HasGradientAt (loss μ) (alpha ‖θ‖ • θ - ridgeForce ‖μ‖ ⟪θ, μ⟫ • μ) θ := by
  have hr := (hasGradientAt_radial θ).hasFDerivAt
  have ht := (LongTails.Proofs.SymmetricReverseFisherScalar.hasDerivAt_scalarPotential ‖μ‖ ⟪μ, θ⟫).comp_hasFDerivAt θ
    ((innerSL ℝ μ).hasFDerivAt)
  have he : ⟪μ, θ⟫ = ⟪θ, μ⟫ := real_inner_comm _ _
  have h := hr.add ht
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · ext x
    change loss μ x = radialSelf ‖x‖ + scalarPotential ‖μ‖ ⟪μ, x⟫
    rw [loss_scalar_decomposition, real_inner_comm x μ]
  · ext x
    simp [InnerProductSpace.toDual_apply_apply, he, sub_eq_add_neg]
lemma gradient_loss {p : Params} (μ θ : Space p) :
    gradient (loss μ) θ = alpha ‖θ‖ • θ - ridgeForce ‖μ‖ ⟪θ, μ⟫ • μ :=
  (hasGradientAt_loss μ θ).gradient
lemma radialFirst_lipschitz {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |radialFirst r - radialFirst s| ≤ 48 * |r - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ici (0 : ℝ)) (f := radialFirst) (f' := radialSecond)
    (fun x _ => (hasDerivAt_radialFirst x).hasDerivWithinAt)
    (fun x hx => radialSecond_bound_nonneg hx) (convex_Ici 0) hs hr
  exact h
lemma radial_gradient_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : ‖alpha ‖x‖ • x - alpha ‖y‖ • y‖ ≤ 48 * ‖x - y‖ := by
  have ha := alpha_nonneg ‖x‖
  have hb := alpha_nonneg ‖y‖
  have ha4 : alpha ‖x‖ ≤ 4 := (alpha_le_four_min ‖x‖).trans (by nlinarith [min_le_right (‖x‖ ^ 2) 1])
  have hb4 : alpha ‖y‖ ≤ 4 := (alpha_le_four_min ‖y‖).trans (by nlinarith [min_le_right (‖y‖ ^ 2) 1])
  have hab : alpha ‖x‖ * alpha ‖y‖ ≤ 48 ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right ha4 hb]
  have hd : 0 ≤ ‖x‖ * ‖y‖ - ⟪x, y⟫ := sub_nonneg.mpr (real_inner_le_norm _ _)
  have hf := radialFirst_lipschitz (norm_nonneg x) (norm_nonneg y)
  rw [radialFirst_eq_alpha, radialFirst_eq_alpha] at hf
  have hf2 := pow_le_pow_left₀ (abs_nonneg _) hf 2
  simp only [mul_pow, sq_abs] at hf2
  have hm := mul_le_mul_of_nonneg_right hab (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd)
  have he : ‖alpha ‖x‖ • x - alpha ‖y‖ • y‖ ^ 2 ≤ 48 ^ 2 * ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left,
      inner_smul_right, conj_trivial]
    nlinarith
  nlinarith [norm_nonneg (alpha ‖x‖ • x - alpha ‖y‖ • y), norm_nonneg (x - y)]
open LongTails.Proofs.SymmetricReverseFisherRidge

lemma scaled_ridge_lipschitz {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    |a * ridgeForce a c - a * ridgeForce a d| ≤ 9 * |c - d| := by
  have hd (x : ℝ) : HasDerivAt (fun y => a * ridgeForce a y) (a * ridgeDerivative a x) x :=
    (hasDerivAt_ridgeForce a x).const_mul a
  have hb (x : ℝ) : ‖a * ridgeDerivative a x‖ ≤ 9 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ha]
    have h := ridgeDerivative_bound ha.le x
    nlinarith
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := univ) (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x)
    convex_univ (mem_univ d) (mem_univ c)
lemma ridge_gradient_lipschitz {p : Params} (μ x y : Space p) :
    ‖ridgeForce ‖μ‖ ⟪x, μ⟫ • μ - ridgeForce ‖μ‖ ⟪y, μ⟫ • μ‖ ≤ 9 * ‖μ‖ * ‖x - y‖ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have h := scaled_ridge_lipschitz hpos ⟪x, μ⟫ ⟪y, μ⟫
  have hi : |⟪x, μ⟫ - ⟪y, μ⟫| ≤ ‖μ‖ * ‖x - y‖ := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)
  calc
    _ = |‖μ‖ * ridgeForce ‖μ‖ ⟪x, μ⟫ - ‖μ‖ * ridgeForce ‖μ‖ ⟪y, μ⟫| := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (norm_nonneg μ)]
      ring
    _ ≤ 9 * |⟪x, μ⟫ - ⟪y, μ⟫| := h
    _ ≤ _ := by nlinarith
lemma gradient_loss_lipschitz {p : Params} (μ x y : Space p) :
    ‖gradient (loss μ) x - gradient (loss μ) y‖ ≤ (48 + 20 * ‖μ‖) * ‖x - y‖ := by
  rw [gradient_loss, gradient_loss]
  have he : alpha ‖x‖ • x - ridgeForce ‖μ‖ ⟪x, μ⟫ • μ -
      (alpha ‖y‖ • y - ridgeForce ‖μ‖ ⟪y, μ⟫ • μ) =
      (alpha ‖x‖ • x - alpha ‖y‖ • y) -
      (ridgeForce ‖μ‖ ⟪x, μ⟫ • μ - ridgeForce ‖μ‖ ⟪y, μ⟫ • μ) := by abel
  rw [he]
  have h := norm_sub_le (alpha ‖x‖ • x - alpha ‖y‖ • y)
    (ridgeForce ‖μ‖ ⟪x, μ⟫ • μ - ridgeForce ‖μ‖ ⟪y, μ⟫ • μ)
  have hr := radial_gradient_lipschitz x y
  have ht := ridge_gradient_lipschitz μ x y
  nlinarith [mul_nonneg (norm_nonneg μ) (norm_nonneg (x - y))]

end LongTails.Proofs.SymmetricReverseFisherGradient
