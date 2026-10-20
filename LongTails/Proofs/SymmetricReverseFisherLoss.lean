import LongTails.Setups.SymmetricGaussianReverseFisher
import LongTails.Proofs.SymmetricReverseFisherGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SymmetricReverseFisherLoss

open LongTails.Setups.SymmetricGaussianReverseFisher

lemma continuous_score {p : Params} (θ : Space p) : Continuous (score θ) := by
  unfold score
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact (((Real.continuous_sinh.comp (continuous_const.inner continuous_id)).div
    (Real.continuous_cosh.comp (continuous_const.inner continuous_id))
    (fun x => ne_of_gt (Real.cosh_pos _))).smul continuous_const).sub continuous_id

lemma norm_score_sub_le {p : Params} (μ θ x : Space p) :
    ‖score θ x - score μ x‖ ≤ ‖θ‖ + ‖μ‖ := by
  have he : score θ x - score μ x =
      Real.tanh ⟪θ, x⟫ • θ - Real.tanh ⟪μ, x⟫ • μ := by
    unfold score
    abel
  rw [he]
  calc
    _ ≤ ‖Real.tanh ⟪θ, x⟫ • θ‖ + ‖Real.tanh ⟪μ, x⟫ • μ‖ := norm_sub_le _ _
    _ ≤ ‖θ‖ + ‖μ‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_tanh_lt_one _).le)
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_tanh_lt_one _).le)

lemma integrable_score_difference {p : Params} (μ θ ν : Space p) :
    Integrable (fun z => ‖score θ (ν + z) - score μ (ν + z)‖ ^ 2)
      (ProbabilityTheory.stdGaussian (Space p)) := by
  have hc : Continuous (fun z => ‖score θ (ν + z) - score μ (ν + z)‖ ^ 2) :=
    (((continuous_score θ).comp (continuous_const.add continuous_id)).sub
      ((continuous_score μ).comp (continuous_const.add continuous_id))).norm.pow 2
  refine (integrable_const ((‖θ‖ + ‖μ‖) ^ 2)).mono' hc.aestronglyMeasurable ?_
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_score_sub_le μ θ (ν + z)) 2)

lemma loss_nonneg {p : Params} (μ θ : Space p) : 0 ≤ loss μ θ := by
  unfold loss
  positivity

lemma loss_self {p : Params} (μ : Space p) : loss μ μ = 0 := by
  simp [loss]

lemma score_neg {p : Params} (θ x : Space p) : score (-θ) x = score θ x := by
  simp [score, Real.tanh_neg]

lemma loss_neg_parameter {p : Params} (μ θ : Space p) : loss μ (-θ) = loss μ θ := by
  simp only [loss, neg_neg, score_neg]
  rw [add_comm]

lemma loss_neg_target {p : Params} (μ θ : Space p) : loss (-μ) θ = loss μ θ := by
  simp only [loss, score_neg]
open LongTails.Proofs.SymmetricReverseFisherGaussian

lemma integral_stdGaussian_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : Measurable f) :
    (∫ z, f (-z) ∂stdGaussian E) = ∫ z, f z ∂stdGaussian E := by
  have hm := stdGaussian_map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)
  have hi := integral_map (μ := stdGaussian E)
    (φ := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)) (by fun_prop) hf.aestronglyMeasurable
  rw [hm] at hi
  exact hi.symm

lemma score_neg_input {p : Params} (θ x : Space p) : score θ (-x) = -score θ x := by
  simp [score, Real.tanh_neg]
  abel

lemma loss_single_component {p : Params} (μ θ : Space p) :
    loss μ θ = ∫ z, ‖score θ (θ + z) - score μ (θ + z)‖ ^ 2 ∂stdGaussian (Space p) := by
  have hc : Measurable (fun z => ‖score θ (-θ + z) - score μ (-θ + z)‖ ^ 2) :=
    ((((continuous_score θ).comp (continuous_const.add continuous_id)).sub
      ((continuous_score μ).comp (continuous_const.add continuous_id))).norm.pow 2).measurable
  have he : (∫ z, ‖score θ (-θ + z) - score μ (-θ + z)‖ ^ 2 ∂stdGaussian (Space p)) =
      ∫ z, ‖score θ (θ + z) - score μ (θ + z)‖ ^ 2 ∂stdGaussian (Space p) := by
    rw [← integral_stdGaussian_neg _ hc]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      dsimp only
      rw [show -θ + -z = -(θ + z) by abel, score_neg_input, score_neg_input,
        show -score θ (θ + z) - -score μ (θ + z) = -(score θ (θ + z) - score μ (θ + z)) by abel,
        norm_neg])
  unfold loss
  rw [he]
  ring

lemma score_difference_sq {p : Params} (μ θ x : Space p) :
    ‖score θ x - score μ x‖ ^ 2 =
      ‖θ‖ ^ 2 * Real.tanh ⟪θ, x⟫ ^ 2 + ‖μ‖ ^ 2 * Real.tanh ⟪μ, x⟫ ^ 2 -
        2 * ⟪θ, μ⟫ * (Real.tanh ⟪θ, x⟫ * Real.tanh ⟪μ, x⟫) := by
  have he : score θ x - score μ x = Real.tanh ⟪θ, x⟫ • θ - Real.tanh ⟪μ, x⟫ • μ := by
    unfold score
    abel
  rw [he, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left, inner_smul_right,
    conj_trivial]
  ring

lemma gaussian_projection_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (u v : E) :
    (stdGaussian E).map (fun z => ⟪u, v + z⟫) = gaussianReal ⟪u, v⟫ (‖u‖ ^ 2).toNNReal := by
  calc
    _ = ((stdGaussian E).map (fun z => ⟪u, z⟫)).map (fun x => ⟪u, v⟫ + x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      ext z
      simp [inner_add_right]
    _ = _ := by rw [gaussian_projection, gaussianReal_map_const_add]; simp
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherGaussian

lemma score_cross_posterior {p : Params} (μ θ : Space p) :
    (∫ z, Real.tanh ⟪θ, θ + z⟫ * Real.tanh ⟪μ, θ + z⟫ ∂stdGaussian (Space p)) =
      ∫ z, Real.tanh ⟪μ, θ + z⟫ ∂stdGaussian (Space p) := by
  by_cases hθ0 : θ = 0
  · subst θ
    simp only [zero_add, inner_zero_left, Real.tanh_zero, zero_mul, integral_zero]
    have hm := integral_stdGaussian_neg (fun z : Space p => Real.tanh ⟪μ, z⟫)
      (by fun_prop)
    simp only [inner_neg_right, Real.tanh_neg, integral_neg] at hm
    linarith
  let R := ‖θ‖
  have hR : 0 < R := norm_pos_iff.mpr hθ0
  let u := R⁻¹ • θ
  let b := ⟪u, μ⟫
  let v := μ - b • u
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    change R⁻¹ * R = 1
    exact inv_mul_cancel₀ hR.ne'
  have hθ : θ = R • u := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huv : ⟪u, v⟫ = 0 := by
    dsimp only [v, b]
    rw [inner_sub_right, inner_smul_right, huu]
    ring
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hμ : μ = b • u + v := by dsimp only [v]; abel
  have hs (z : Space p) : ⟪θ, θ + z⟫ = R * (R + ⟪u, z⟫) := by
    rw [hθ]
    simp only [inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, huu]
    ring
  have ht (z : Space p) : ⟪μ, θ + z⟫ = b * (R + ⟪u, z⟫) + ⟪v, z⟫ := by
    rw [hμ, hθ]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, huu, hvu]
    ring
  simp_rw [hs, ht]
  exact gaussian_orthogonal_posterior u v hu huv R b

open LongTails.Proofs.SymmetricReverseFisherHyperbolic
lemma integrable_tanh_projection {p : Params} (u v : Space p) :
    Integrable (fun z => Real.tanh ⟪u, v + z⟫) (stdGaussian (Space p)) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all _ (fun z => (Real.abs_tanh_lt_one _).le)
lemma integrable_tanh_projection_sq {p : Params} (u v : Space p) :
    Integrable (fun z => Real.tanh ⟪u, v + z⟫ ^ 2) (stdGaussian (Space p)) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := Real.abs_tanh_lt_one ⟪u, v + z⟫
    exact (sq_le_one_iff_abs_le_one _).mpr h.le)
lemma integrable_tanh_projection_prod {p : Params} (u v w : Space p) :
    Integrable (fun z => Real.tanh ⟪u, w + z⟫ * Real.tanh ⟪v, w + z⟫)
      (stdGaussian (Space p)) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1 * |Real.tanh ⟪v, w + z⟫| := mul_le_mul_of_nonneg_right
        (Real.abs_tanh_lt_one _).le (abs_nonneg _)
      _ ≤ 1 := by simpa using (Real.abs_tanh_lt_one ⟪v, w + z⟫).le)
lemma loss_expansion {p : Params} (μ θ : Space p) :
    loss μ θ = ‖θ‖ ^ 2 * (∫ z, Real.tanh ⟪θ, θ + z⟫ ^ 2 ∂stdGaussian (Space p)) +
      ‖μ‖ ^ 2 * (∫ z, Real.tanh ⟪μ, θ + z⟫ ^ 2 ∂stdGaussian (Space p)) -
      2 * ⟪θ, μ⟫ * (∫ z, Real.tanh ⟪μ, θ + z⟫ ∂stdGaussian (Space p)) := by
  rw [loss_single_component]
  simp_rw [score_difference_sq]
  erw [integral_sub ((integrable_tanh_projection_sq θ θ).const_mul _ |>.add
    ((integrable_tanh_projection_sq μ θ).const_mul _))
    ((integrable_tanh_projection_prod θ μ θ).const_mul _),
    integral_add ((integrable_tanh_projection_sq θ θ).const_mul _)
      ((integrable_tanh_projection_sq μ θ).const_mul _)]
  simp only [integral_const_mul]
  rw [score_cross_posterior]
lemma integral_projection_shift {p : Params} (u v : Space p) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ z, f ⟪u, v + z⟫ ∂stdGaussian (Space p)) =
      ∫ x, f x ∂gaussianReal ⟪u, v⟫ (‖u‖ ^ 2).toNNReal := by
  rw [← gaussian_projection_shift u v]
  exact (integral_map (by fun_prop) hf.aestronglyMeasurable).symm
noncomputable def radialSelf (r : ℝ) : ℝ :=
  r ^ 2 * ∫ x, Real.tanh (r * x) ^ 2 ∂gaussianReal r 1

noncomputable def scalarPotential (a c : ℝ) : ℝ :=
  a ^ 2 * (1 - ∫ y, sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal) -
    2 * c * ∫ y, Real.tanh y ∂gaussianReal c (a ^ 2).toNNReal

lemma gaussian_tanh_sq (c : ℝ) (v : NNReal) :
    (∫ y, Real.tanh y ^ 2 ∂gaussianReal c v) =
      1 - ∫ y, sech y ^ 2 ∂gaussianReal c v := by
  have hi : Integrable (fun y => sech y ^ 2) (gaussianReal c v) := by
    refine (integrable_const (1 : ℝ)).mono' (by unfold sech; fun_prop) ?_
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [tanh_sq_add_sech_sq y, sq_nonneg (Real.tanh y)])
  have he (y : ℝ) : Real.tanh y ^ 2 = 1 - sech y ^ 2 := by
    linarith [tanh_sq_add_sech_sq y]
  simp_rw [he]
  rw [integral_sub (integrable_const _) hi]
  simp

lemma loss_scalar_decomposition {p : Params} (μ θ : Space p) :
    loss μ θ = radialSelf ‖θ‖ + scalarPotential ‖μ‖ ⟪θ, μ⟫ := by
  rw [loss_expansion]
  rw [integral_projection_shift θ θ (fun y => Real.tanh y ^ 2) (by fun_prop),
    integral_projection_shift μ θ (fun y => Real.tanh y ^ 2) (by fun_prop),
    integral_projection_shift μ θ Real.tanh (by fun_prop)]
  rw [real_inner_self_eq_norm_sq, real_inner_comm μ θ]
  have hs := gaussian_integral_scale ‖θ‖ ‖θ‖ (fun y => Real.tanh y ^ 2) (by fun_prop)
  rw [← pow_two ‖θ‖] at hs
  rw [hs]
  rw [gaussian_tanh_sq]
  unfold radialSelf scalarPotential
  ring

lemma gaussian_density_even_tilt (r x : ℝ) :
    (gaussianPDFReal r 1 x + gaussianPDFReal r 1 (-x)) * sech (r * x) ^ 2 =
      2 * Real.exp (-r ^ 2 / 2) * gaussianPDFReal 0 1 x * sech (r * x) := by
  rw [gaussian_density_split, gaussian_density_split, gaussian_density_split]
  simp only [neg_sq, mul_neg, zero_pow (by norm_num : 2 ≠ 0), add_zero, zero_mul,
    Real.exp_zero, mul_one]
  have he : Real.exp (-(x ^ 2 + r ^ 2) / 2) =
      Real.exp (-r ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hc : Real.exp (r * x) + Real.exp (-(r * x)) = 2 * Real.cosh (r * x) := by
    rw [Real.cosh_eq]
    ring
  have hs : Real.cosh (r * x) * sech (r * x) ^ 2 = sech (r * x) := by
    unfold sech
    field_simp
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-r ^ 2 / 2) * Real.exp (-x ^ 2 / 2) *
        (Real.exp (r * x) + Real.exp (-(r * x))) * sech (r * x) ^ 2 := by ring
    _ = _ := by
      rw [hc]
      linear_combination
        2 * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-r ^ 2 / 2) * Real.exp (-x ^ 2 / 2) * hs

lemma gaussian_sech_sq_tilt (r : ℝ) :
    (∫ x, sech (r * x) ^ 2 ∂gaussianReal r 1) =
      Real.exp (-r ^ 2 / 2) * ∫ z, sech (r * z) ∂gaussianReal 0 1 := by
  have hi : Integrable (fun x => sech (r * x) ^ 2) (gaussianReal r 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by unfold sech; fun_prop) ?_
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sech_pos (r * x), sech_le_one (r * x)])
  let f := fun x => gaussianPDFReal r 1 x * sech (r * x) ^ 2
  have hf : Integrable f := (integrable_gaussian_iff r 1 one_ne_zero _).mp hi
  have hs : (∫ x, f x + f (-x)) = 2 * ∫ x, f x := by
    rw [integral_add hf hf.comp_neg, integral_neg_eq_self]
    ring
  have he (x : ℝ) : f x + f (-x) =
      2 * Real.exp (-r ^ 2 / 2) * (gaussianPDFReal 0 1 x * sech (r * x)) := by
    dsimp only [f]
    rw [mul_neg, sech_neg]
    nlinarith [gaussian_density_even_tilt r x]
  simp_rw [he] at hs
  rw [integral_const_mul] at hs
  simp_rw [integral_gaussianReal_eq_integral_smul (show (1 : NNReal) ≠ 0 by norm_num),
    smul_eq_mul]
  change (∫ x, f x) = _
  linarith
end LongTails.Proofs.SymmetricReverseFisherLoss
