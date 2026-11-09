import LongTails.Proofs.CovarianceAcceleratedGaussian
import Mathlib.Probability.Moments.Tilted

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.CovarianceAcceleratedTilt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_exp_inner (z : E) :
    Integrable (fun u => Real.exp ⟪z, u⟫) (stdGaussian E) := by
  have h := (CovarianceAcceleratedGaussian.gaussian_law_subgaussian
    (CovarianceAcceleratedGaussian.gaussian_dual_law (innerSL ℝ z))).integrable_exp_mul 1
  simpa using h

lemma integral_exp_inner (z : E) :
    (∫ u, Real.exp ⟪z, u⟫ ∂stdGaussian E) = Real.exp (‖z‖ ^ 2 / 2) := by
  have h := mgf_gaussianReal
    (CovarianceAcceleratedGaussian.gaussian_dual_law (innerSL ℝ z)) 1
  simpa [mgf, innerSL_apply_norm, Real.toNNReal_of_nonneg (sq_nonneg ‖z‖)] using h

lemma gaussian_density_integrable (z : E) :
    Integrable (fun u => Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2)) (stdGaussian E) := by
  simpa only [Real.exp_sub] using (integrable_exp_inner z).div_const (Real.exp (‖z‖ ^ 2 / 2))

lemma gaussian_density_integral (z : E) :
    (∫ u, Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) ∂stdGaussian E) = 1 := by
  simp_rw [Real.exp_sub]
  rw [integral_div, integral_exp_inner, div_self (Real.exp_pos _).ne']

lemma tilted_inner_mgf (z y : E) (t : ℝ) :
    mgf (fun u => ⟪y, u⟫) ((stdGaussian E).tilted (fun u => ⟪z, u⟫)) t =
      Real.exp (t * ⟪z, y⟫ + t ^ 2 * ‖y‖ ^ 2 / 2) := by
  unfold mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  have hn : (∫ u, Real.exp (⟪z, u⟫ + t * ⟪y, u⟫) ∂stdGaussian E) =
      Real.exp (‖z + t • y‖ ^ 2 / 2) := by
    have he (u : E) : ⟪z, u⟫ + t * ⟪y, u⟫ = ⟪z + t • y, u⟫ := by
      rw [inner_add_left, real_inner_smul_left]
    simp_rw [he]
    exact integral_exp_inner _
  rw [hn, integral_exp_inner, ← Real.exp_sub]
  congr 1
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  ring

lemma integral_exp_scaled_inner (y : E) (t : ℝ) :
    (∫ u, Real.exp (t * ⟪y, u⟫) ∂stdGaussian E) = Real.exp (t ^ 2 * ‖y‖ ^ 2 / 2) := by
  simpa [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow] using integral_exp_inner (t • y)

lemma translated_inner_mgf (z y : E) (t : ℝ) :
    mgf (fun u => ⟪y, u⟫) ((stdGaussian E).map (fun u => z + u)) t =
      Real.exp (t * ⟪z, y⟫ + t ^ 2 * ‖y‖ ^ 2 / 2) := by
  unfold mgf
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_add_right, mul_add, Real.exp_add]
  rw [integral_const_mul, integral_exp_scaled_inner, ← Real.exp_add, real_inner_comm z y]
  exact Real.exp_add _ _

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma complexMGF_inner_I (μ : Measure E) (y : E) :
    complexMGF (fun u => ⟪y, u⟫) μ Complex.I = charFun μ y := by
  unfold complexMGF charFun
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [(real_inner_comm y u).symm]
    congr 1
    ring

lemma tilted_gaussian_eq_translation (z : E) :
    (stdGaussian E).tilted (fun u => ⟪z, u⟫) = (stdGaussian E).map (fun u => z + u) := by
  let μ := (stdGaussian E).tilted (fun u => ⟪z, u⟫)
  let ν := (stdGaussian E).map (fun u => z + u)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted (integrable_exp_inner z)
  change μ = ν
  apply Measure.ext_of_charFun
  funext y
  have hmgf : mgf (fun u => ⟪y, u⟫) μ = mgf (fun u => ⟪y, u⟫) ν := by
    funext t
    exact (tilted_inner_mgf z y t).trans (translated_inner_mgf z y t).symm
  have hdomain : integrableExpSet (fun u => ⟪y, u⟫) μ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    apply mgf_pos_iff.mp
    rw [show mgf (fun u => ⟪y, u⟫) μ t =
      Real.exp (t * ⟪z, y⟫ + t ^ 2 * ‖y‖ ^ 2 / 2) from tilted_inner_mgf z y t]
    exact Real.exp_pos _
  have hc := eqOn_complexMGF_of_mgf hmgf (by simp [hdomain] :
    Complex.I ∈ {w : ℂ | w.re ∈ interior (integrableExpSet (fun u => ⟪y, u⟫) μ)})
  simpa only [complexMGF_inner_I] using hc

lemma tilted_gaussian_integrable_id (z : E) :
    Integrable (fun u : E => u) ((stdGaussian E).tilted (fun u => ⟪z, u⟫)) := by
  rw [tilted_gaussian_eq_translation]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (integrable_const z).add IsGaussian.integrable_id

lemma tilted_gaussian_mean (z : E) :
    (∫ u : E, u ∂(stdGaussian E).tilted (fun u => ⟪z, u⟫)) = z := by
  rw [tilted_gaussian_eq_translation, integral_map (by fun_prop) (by fun_prop)]
  rw [integral_add (integrable_const z) (show Integrable (fun u : E => u) (stdGaussian E) from IsGaussian.integrable_id)]
  simp [integral_id_stdGaussian]

lemma gaussian_density_mul_integrable (z : E) :
    Integrable (fun u => Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) • u) (stdGaussian E) := by
  have h := (integrable_tilted_iff (integrable_exp_inner z) (fun u : E => u)).mp
    (tilted_gaussian_integrable_id z)
  have hc := h.smul (Real.exp (‖z‖ ^ 2 / 2))⁻¹
  apply hc.congr
  filter_upwards [] with u
  simp only [Real.exp_sub, Pi.smul_apply, smul_smul, div_eq_inv_mul]

lemma gaussian_density_mean (z : E) :
    (∫ u, Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) • u ∂stdGaussian E) = z := by
  have h := tilted_gaussian_mean z
  rw [integral_tilted, integral_exp_inner] at h
  simpa only [Real.exp_sub] using h

lemma gaussian_density_affine_integrable (z y : E) (b : ℝ) :
    Integrable (fun u => Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) * (⟪y, u⟫ + b))
      (stdGaussian E) := by
  have h := (innerSL ℝ y).integrable_comp (gaussian_density_mul_integrable z)
  have hb := (gaussian_density_integrable z).mul_const b
  apply (h.add hb).congr
  filter_upwards [] with u
  simp only [map_smul, smul_eq_mul, innerSL_apply_apply, Pi.add_apply, mul_add]

lemma gaussian_density_affine_integral (z y : E) (b : ℝ) :
    (∫ u, Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) * (⟪y, u⟫ + b) ∂stdGaussian E) =
      ⟪y, z⟫ + b := by
  have h := (innerSL ℝ y).integral_comp_comm (gaussian_density_mul_integrable z)
  simp only [map_smul, smul_eq_mul, innerSL_apply_apply, gaussian_density_mean] at h
  simp_rw [mul_add]
  rw [integral_add (gaussian_density_affine_integrable z y 0 |>.congr (by simp))
    ((gaussian_density_integrable z).mul_const b)]
  rw [h, integral_mul_const, gaussian_density_integral, one_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_density_log_ratio (z w u : E) :
    Real.log (Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) /
      Real.exp (⟪w, u⟫ - ‖w‖ ^ 2 / 2)) =
      ⟪z - w, u⟫ + (‖w‖ ^ 2 - ‖z‖ ^ 2) / 2 := by
  rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp,
    inner_sub_left]
  ring

lemma gaussian_density_kl_integrable (z w : E) :
    Integrable (fun u => Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) *
      Real.log (Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) /
        Real.exp (⟪w, u⟫ - ‖w‖ ^ 2 / 2))) (stdGaussian E) := by
  simp_rw [gaussian_density_log_ratio]
  exact gaussian_density_affine_integrable _ _ _

lemma gaussian_density_kl (z w : E) :
    (∫ u, Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) *
      Real.log (Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2) /
        Real.exp (⟪w, u⟫ - ‖w‖ ^ 2 / 2)) ∂stdGaussian E) = ‖z - w‖ ^ 2 / 2 := by
  simp_rw [gaussian_density_log_ratio]
  rw [gaussian_density_affine_integral, inner_sub_left, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, real_inner_comm z w]
  ring

end LongTails.Proofs.CovarianceAcceleratedTilt
