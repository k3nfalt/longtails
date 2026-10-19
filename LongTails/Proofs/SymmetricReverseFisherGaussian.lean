import LongTails.Proofs.SymmetricReverseFisherHyperbolic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace LongTails.Proofs.SymmetricReverseFisherGaussian

lemma integrable_gaussian_iff (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero m hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF m v)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

lemma hasDerivAt_gaussian_density (m x : ℝ) :
    HasDerivAt (gaussianPDFReal m 1) (-(x - m) * gaussianPDFReal m 1 x) x := by
  convert (((((hasDerivAt_id x).sub_const m).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹ using 1
  · ext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, NNReal.coe_one, mul_one, id_eq, Pi.neg_apply, Pi.pow_apply]
    ring

lemma gaussian_stein (m : ℝ) (f f' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal m 1))
    (hf' : Integrable f' (gaussianReal m 1))
    (hxf : Integrable (fun x => (x - m) * f x) (gaussianReal m 1)) :
    (∫ x, f' x ∂gaussianReal m 1) = ∫ x, (x - m) * f x ∂gaussianReal m 1 := by
  have hp := (integrable_gaussian_iff m 1 one_ne_zero f).mp hf
  have hp' := (integrable_gaussian_iff m 1 one_ne_zero f').mp hf'
  have hxp := (integrable_gaussian_iff m 1 one_ne_zero (fun x => (x - m) * f x)).mp hxf
  have hd' (x : ℝ) : HasDerivAt (fun y => gaussianPDFReal m 1 y * f y)
      (gaussianPDFReal m 1 x * f' x - gaussianPDFReal m 1 x * ((x - m) * f x)) x := by
    convert (hasDerivAt_gaussian_density m x).mul (hd x) using 1
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd' (hp'.sub hxp) hp
  rw [integral_sub hp' hxp] at hz
  simp_rw [integral_gaussianReal_eq_integral_smul (show (1 : ℝ≥0) ≠ 0 by norm_num),
    smul_eq_mul]
  exact sub_eq_zero.mp hz

lemma gaussian_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (v : E) :
    (stdGaussian E).map (fun x => ⟪v, x⟫) = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  change (stdGaussian E).map (innerSL ℝ v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]

lemma orthogonal_projections_independent {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (h : ⟪u, v⟫ = 0) :
    IndepFun (fun z => ⟪u, z⟫) (fun z => ⟪v, z⟫) (stdGaussian E) := by
  let L := (innerSL ℝ u).prod (innerSL ℝ v)
  have hg : HasGaussianLaw (fun z : E => (⟪u, z⟫, ⟪v, z⟫)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map L
  apply hg.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian]
  exact h

lemma joint_orthogonal_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (h : ⟪u, v⟫ = 0) :
    (stdGaussian E).map (fun z => (⟪u, z⟫, ⟪v, z⟫)) =
      (gaussianReal 0 (‖u‖ ^ 2).toNNReal).prod (gaussianReal 0 (‖v‖ ^ 2).toNNReal) := by
  rw [(orthogonal_projections_independent u v h).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), gaussian_projection, gaussian_projection]

lemma gaussian_density_split (m x : ℝ) :
    gaussianPDFReal m 1 x = (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(x ^ 2 + m ^ 2) / 2) * Real.exp (m * x) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_posterior_balance (m x : ℝ) :
    gaussianPDFReal m 1 x * (1 - Real.tanh (m * x)) =
      gaussianPDFReal m 1 (-x) * (1 + Real.tanh (m * x)) := by
  rw [gaussian_density_split, gaussian_density_split, Real.tanh_eq]
  simp only [neg_sq, mul_neg]
  field_simp
  ring

lemma integral_odd_zero (f : ℝ → ℝ) (h : ∀ x, f (-x) = -f x) : (∫ x, f x) = 0 := by
  have he := integral_neg_eq_self f volume
  simp_rw [h] at he
  rw [integral_neg] at he
  linarith

lemma gaussian_posterior_odd (m : ℝ) (h : ℝ → ℝ)
    (hodd : ∀ x, h (-x) = -h x)
    (hi : Integrable h (gaussianReal m 1))
    (hti : Integrable (fun x => Real.tanh (m * x) * h x) (gaussianReal m 1)) :
    (∫ x, Real.tanh (m * x) * h x ∂gaussianReal m 1) = ∫ x, h x ∂gaussianReal m 1 := by
  let f := fun x => gaussianPDFReal m 1 x * (1 - Real.tanh (m * x)) * h x
  have hf (x : ℝ) : f (-x) = -f x := by
    calc
      f (-x) = -(gaussianPDFReal m 1 (-x) * (1 + Real.tanh (m * x)) * h x) := by
        simp [f, hodd, Real.tanh_neg]
      _ = -f x := by rw [← gaussian_posterior_balance]
  have hp := (integrable_gaussian_iff m 1 one_ne_zero h).mp hi
  have htp := (integrable_gaussian_iff m 1 one_ne_zero (fun x => Real.tanh (m * x) * h x)).mp hti
  have he : (∫ x, f x) = (∫ x, gaussianPDFReal m 1 x * h x) -
      ∫ x, gaussianPDFReal m 1 x * (Real.tanh (m * x) * h x) := by
    rw [← integral_sub hp htp]
    congr 1
    ext x
    dsimp [f]
    ring
  have hz := integral_odd_zero f hf
  rw [he] at hz
  simp_rw [integral_gaussianReal_eq_integral_smul (show (1 : ℝ≥0) ≠ 0 by norm_num),
    smul_eq_mul]
  exact (sub_eq_zero.mp hz).symm

lemma integral_positive_half (f : ℝ → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ x in Set.Ioi (0 : ℝ), f x + f (-x) := by
  have he := integral_comp_neg_Ioi (0 : ℝ) f
  simp only [neg_zero] at he
  rw [← integral_add_compl measurableSet_Ioi hf, Set.compl_Ioi, ← he,
    ← integral_add hf.integrableOn hf.comp_neg.integrableOn]

lemma gaussian_odd_positive_half (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal m v)) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂gaussianReal m v) =
      ∫ x in Set.Ioi (0 : ℝ), f x * (gaussianPDFReal m v x - gaussianPDFReal m v (-x)) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [integral_positive_half _ ((integrable_gaussian_iff m v hv f).mp hf)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [hodd]; ring)

lemma gaussian_density_reflection_le {m x : ℝ} (v : ℝ≥0) (hm : 0 ≤ m) (hx : 0 ≤ x) :
    gaussianPDFReal m v (-x) ≤ gaussianPDFReal m v x := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg hm hx]

lemma gaussian_odd_nonneg {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal m v)) (hodd : ∀ x, f (-x) = -f x)
    (hpos : ∀ x, 0 < x → 0 ≤ f x) : 0 ≤ ∫ x, f x ∂gaussianReal m v := by
  rw [gaussian_odd_positive_half m v hv f hf hodd]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (hpos x hx) (sub_nonneg.mpr (gaussian_density_reflection_le v hm hx.le))

lemma gaussian_odd_integral_mono {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0)
    (f g : ℝ → ℝ) (hf : Integrable f (gaussianReal m v))
    (hg : Integrable g (gaussianReal m v))
    (hfo : ∀ x, f (-x) = -f x) (hgo : ∀ x, g (-x) = -g x)
    (hle : ∀ x, 0 < x → f x ≤ g x) :
    (∫ x, f x ∂gaussianReal m v) ≤ ∫ x, g x ∂gaussianReal m v := by
  by_cases hv : v = 0
  · subst v
    simp only [gaussianReal_zero_var, integral_dirac]
    rcases hm.eq_or_lt with hm | hm
    · have hf0 := hfo 0
      have hg0 := hgo 0
      simp only [neg_zero] at hf0 hg0
      subst m
      linarith
    · exact hle m hm
  · have hn := gaussian_odd_nonneg hm v hv (fun x => g x - f x) (hg.sub hf)
      (fun x => by rw [hfo, hgo]; ring)
      (fun x hx => sub_nonneg.mpr (hle x hx))
    rw [integral_sub hg hf] at hn
    linarith

def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

lemma clip_monotone : Monotone clip := by
  intro x y h
  exact max_le_max_left _ (min_le_min_left _ h)

lemma clip_of_mem {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : clip x = x := by
  simp [clip, min_eq_right hx.2, max_eq_right hx.1]

lemma clip_neg (x : ℝ) : clip (-x) = -clip x := by
  unfold clip
  rcases le_total x (-1) with hx | hx
  · rw [min_eq_left (by linarith : 1 ≤ -x), max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
      min_eq_right (by linarith : x ≤ 1), max_eq_left hx]
    norm_num
  · rcases le_total x 1 with hy | hy
    · rw [min_eq_right (by linarith : -x ≤ 1), max_eq_right (by linarith : -1 ≤ -x),
        min_eq_right hy, max_eq_right hx]
    · rw [min_eq_right (by linarith : -x ≤ 1), max_eq_left (by linarith : -x ≤ -1),
        min_eq_left hy, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]

lemma clip_shift_difference {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : ℝ) :
    r * (Set.Icc (-1 : ℝ) 0).indicator (fun _ => (1 : ℝ)) x ≤ clip (x + r) - clip x := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 0
  · rw [Set.indicator_of_mem hx, mul_one,
      clip_of_mem (show x + r ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2]),
      clip_of_mem (show x ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2])]
    linarith
  · rw [Set.indicator_of_notMem hx, mul_zero]
    exact sub_nonneg.mpr (clip_monotone (by linarith))

lemma clip_scale {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    min a 1 * clip x ≤ clip (a * x) := by
  have hc {y : ℝ} (hy : 0 ≤ y) : clip y = min 1 y := by
    exact max_eq_right (le_min (by norm_num) (by linarith))
  rw [hc hx, hc (mul_nonneg ha hx)]
  apply le_min
  · exact (mul_le_mul_of_nonneg_right (min_le_right a 1) (le_min zero_le_one hx)).trans (by simp)
  · exact mul_le_mul (min_le_left a 1) (min_le_right 1 x) (le_min zero_le_one hx) ha

lemma abs_clip_le_one (x : ℝ) : |clip x| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma integrable_clip_shift (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x => clip (x + r)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · unfold clip
    fun_prop
  · exact ae_of_all _ (fun x => abs_clip_le_one (x + r))

lemma integral_clip_shift_lower (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r * μ.real (Set.Icc (-1 : ℝ) 0) ≤
      (∫ x, clip (x + r) ∂μ) - ∫ x, clip x ∂μ := by
  have hi : Integrable (fun x : ℝ => clip x) μ := by
    simpa using integrable_clip_shift μ 0
  have hind := (integrable_const (1 : ℝ) (μ := μ)).indicator (s := Set.Icc (-1 : ℝ) 0) measurableSet_Icc
  have h := integral_mono (hind.const_mul r) ((integrable_clip_shift μ r).sub hi)
    (clip_shift_difference hr hr1)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_clip_shift μ r) hi, integral_const_mul,
    integral_indicator measurableSet_Icc] at h
  simp only [setIntegral_const, smul_eq_mul, mul_one] at h
  exact h

lemma gaussian_density_lower_unit {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    (1 - x ^ 2 / 2) / 3 ≤ gaussianPDFReal 0 1 x := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  have hn : 0 ≤ 1 - x ^ 2 / 2 := by nlinarith [hx.1, hx.2]
  have he : 1 - x ^ 2 / 2 ≤ Real.exp (-(x ^ 2) / 2) := by
    linarith [Real.add_one_le_exp (-(x ^ 2) / 2)]
  have hi : (1 : ℝ) / 3 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [← one_div (Real.sqrt (2 * Real.pi))]
    apply (le_div_iff₀ hs).mpr
    linarith
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    (1 - x ^ 2 / 2) / 3 = (1 / 3) * (1 - x ^ 2 / 2) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) :=
      mul_le_mul hi he hn (inv_nonneg.mpr hs.le)

lemma gaussian_unit_interval_mass :
    (5 : ℝ) / 18 ≤ (gaussianReal 0 1).real (Set.Icc (-1 : ℝ) 0) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  have hi : IntegrableOn (fun x : ℝ => (1 - x ^ 2 / 2) / 3) (Set.Icc (-1 : ℝ) 0) :=
    (by fun_prop : Continuous (fun x : ℝ => (1 - x ^ 2 / 2) / 3)).integrableOn_Icc
  have hm := setIntegral_mono_on hi (integrable_gaussianPDFReal 0 1).integrableOn
    measurableSet_Icc (fun x hx => gaussian_density_lower_unit hx)
  have he : (∫ x in Set.Icc (-1 : ℝ) 0, (1 - x ^ 2 / 2) / 3) = 5 / 18 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
    norm_num [intervalIntegral.integral_div, intervalIntegral.integral_sub,
      intervalIntegral.integral_const]
  rwa [he] at hm

lemma integral_clip_centered : (∫ x, clip x ∂gaussianReal 0 1) = 0 := by
  have hi : Integrable clip (gaussianReal 0 1) := by simpa using integrable_clip_shift (gaussianReal 0 1) 0
  rw [gaussian_odd_positive_half 0 1 one_ne_zero clip hi clip_neg]
  simp [gaussianPDFReal]

lemma gaussian_clip_shift_lower {r : ℝ} (hr : 0 ≤ r) :
    min r 1 / 4 ≤ ∫ x, clip (x + r) ∂gaussianReal 0 1 := by
  have hsmall (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      t / 4 ≤ ∫ x, clip (x + t) ∂gaussianReal 0 1 := by
    have h := integral_clip_shift_lower (gaussianReal 0 1) ht ht1
    rw [integral_clip_centered, sub_zero] at h
    have hm := gaussian_unit_interval_mass
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hm)]
  rcases le_total r 1 with h | h
  · rw [min_eq_left h]
    exact hsmall r hr h
  · rw [min_eq_right h]
    exact (hsmall 1 zero_le_one le_rfl).trans (integral_mono
      (integrable_clip_shift _ 1) (integrable_clip_shift _ r)
      (fun x => clip_monotone (by linarith)))

lemma gaussian_integral_shift (r : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂gaussianReal r 1) = ∫ z, f (z + r) ∂gaussianReal 0 1 := by
  have hm := gaussianReal_map_add_const (μ := 0) (v := 1) r
  rw [zero_add] at hm
  rw [← hm, integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma gaussian_integral_scale (r a : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂gaussianReal (a * r) (a ^ 2).toNNReal) =
      ∫ x, f (a * x) ∂gaussianReal r 1 := by
  have hv : (⟨a ^ 2, sq_nonneg a⟩ : NNReal) * 1 = (a ^ 2).toNNReal := by
    ext
    simp [Real.coe_toNNReal', max_eq_left (sq_nonneg a)]
  have hm := gaussianReal_map_const_mul (μ := r) (v := 1) a
  erw [hv] at hm
  rw [← hm, integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma gaussian_clip_lower {r : ℝ} (hr : 0 ≤ r) :
    min r 1 / 4 ≤ ∫ x, clip x ∂gaussianReal r 1 := by
  rw [gaussian_integral_shift r clip (by unfold clip; fun_prop)]
  exact gaussian_clip_shift_lower hr

lemma gaussian_integrable_scale (r a : ℝ) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal (a * r) (a ^ 2).toNNReal)) :
    Integrable (fun x => f (a * x)) (gaussianReal r 1) := by
  have hv : (NNReal.mk (a ^ 2) (sq_nonneg a)) * 1 = (a ^ 2).toNNReal := by
    ext
    simp [Real.coe_toNNReal', max_eq_left (sq_nonneg a)]
  have hm := gaussianReal_map_const_mul (μ := r) (v := 1) a
  rw [hv] at hm
  rw [← hm] at hf
  exact hf.comp_measurable (by fun_prop)

lemma gaussian_odd_clip_lower {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (f : ℝ → ℝ) (hf : Integrable f (gaussianReal r 1))
    (ho : ∀ x, f (-x) = -f x)
    (hl : ∀ x, 0 < x → C * clip x ≤ f x) :
    C * (min r 1 / 4) ≤ ∫ x, f x ∂gaussianReal r 1 := by
  have hi : Integrable clip (gaussianReal r 1) := by
    simpa using integrable_clip_shift (gaussianReal r 1) 0
  have hm := gaussian_odd_integral_mono hr 1 (fun x => C * clip x) f
    (hi.const_mul C) hf (fun x => by rw [clip_neg]; ring) ho hl
  rw [integral_const_mul] at hm
  exact (mul_le_mul_of_nonneg_left (gaussian_clip_lower hr) hC).trans hm

lemma integrable_gaussian_odd_half (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ)
    (hf : Integrable f (gaussianReal m v)) (ho : ∀ x, f (-x) = -f x) :
    IntegrableOn (fun x => f x * (gaussianPDFReal m v x - gaussianPDFReal m v (-x))) (Set.Ioi 0) := by
  have hi := (integrable_gaussian_iff m v hv f).mp hf
  have hj := (hi.add hi.comp_neg).integrableOn (s := Set.Ioi 0)
  convert hj using 1
  ext x
  simp only [Pi.add_apply, ho]
  ring
open LongTails.Proofs.SymmetricReverseFisherHyperbolic

lemma gaussian_posterior_two_linear (r b : ℝ) (v : NNReal) :
    (∫ s, ∫ t, Real.tanh (r * s) * Real.tanh (b * s + t) ∂gaussianReal 0 v ∂gaussianReal r 1) =
      ∫ s, ∫ t, Real.tanh (b * s + t) ∂gaussianReal 0 v ∂gaussianReal r 1 := by
  let h := fun s : ℝ => ∫ t, Real.tanh (b * s + t) ∂gaussianReal 0 v
  have hm : StronglyMeasurable h := by
    have hf : StronglyMeasurable (fun p : ℝ × ℝ => Real.tanh (b * p.1 + p.2)) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.tanh (b * p.1 + p.2))).stronglyMeasurable
    exact hf.integral_prod_right'
  have hb (s : ℝ) : |h s| ≤ 1 := by
    have hnorm := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
      (ae_of_all _ (fun t => (show ‖Real.tanh (b * s + t)‖ ≤ 1 by
        simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one (b * s + t)).le)))
    simpa [h, Real.norm_eq_abs] using hnorm
  have ho (s : ℝ) : h (-s) = -h s := by
    have hmap := gaussianReal_map_neg (μ := 0) (v := v)
    rw [neg_zero] at hmap
    have hi := integral_map (μ := gaussianReal 0 v) (φ := fun t : ℝ => -t)
      (by fun_prop) (f := fun t => Real.tanh (b * (-s) + t)) (by fun_prop)
    rw [hmap] at hi
    change (∫ t, Real.tanh (b * (-s) + t) ∂gaussianReal 0 v) = -h s
    rw [hi]
    have he : (fun t : ℝ => Real.tanh (b * (-s) + -t)) = fun t => -Real.tanh (b * s + t) := by
      ext t
      rw [show b * (-s) + -t = -(b * s + t) by ring, Real.tanh_neg]
    rw [he, integral_neg]
  have hi : Integrable h (gaussianReal r 1) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ hb)
  have hti : Integrable (fun s => Real.tanh (r * s) * h s) (gaussianReal r 1) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((by fun_prop : AEStronglyMeasurable (fun s => Real.tanh (r * s)) (gaussianReal r 1)).mul
        hm.aestronglyMeasurable) ?_
    exact ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one _).le).trans (hb s))
  simp_rw [integral_const_mul]
  exact gaussian_posterior_odd r h ho hi hti

lemma integral_orthogonal_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) (m : ℝ)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) {C : ℝ} (hb : ∀ p, |F p| ≤ C) :
    (∫ z, F (m + ⟪u, z⟫, ⟪v, z⟫) ∂stdGaussian E) =
      ∫ s, ∫ t, F (s, t) ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal ∂gaussianReal m 1 := by
  have hm := joint_orthogonal_projection u v huv
  simp only [hu, one_pow, Real.toNNReal_one] at hm
  have hc : Continuous (fun p : ℝ × ℝ => F (m + p.1, p.2)) := by fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => F (m + p.1, p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 (‖v‖ ^ 2).toNNReal)) := by
    exact (integrable_const C).mono' hc.aestronglyMeasurable (ae_of_all _ (fun p => hb _))
  have hh : Measurable (fun s => ∫ t, F (s, t) ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  calc
    _ = ∫ p, F (m + p.1, p.2) ∂(stdGaussian E).map (fun z => (⟪u, z⟫, ⟪v, z⟫)) := by
      rw [integral_map (by fun_prop) hc.aestronglyMeasurable]
    _ = ∫ s, ∫ t, F (m + s, t) ∂gaussianReal 0 (‖v‖ ^ 2).toNNReal ∂gaussianReal 0 1 := by
      rw [hm, integral_prod _ hi]
    _ = _ := by
      rw [gaussian_integral_shift m _ hh]
      congr 1
      ext s
      simp only [add_comm m s]

lemma gaussian_orthogonal_posterior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (hu : ‖u‖ = 1) (huv : ⟪u, v⟫ = 0) (r b : ℝ) :
    (∫ z, Real.tanh (r * (r + ⟪u, z⟫)) *
      Real.tanh (b * (r + ⟪u, z⟫) + ⟪v, z⟫) ∂stdGaussian E) =
    ∫ z, Real.tanh (b * (r + ⟪u, z⟫) + ⟪v, z⟫) ∂stdGaussian E := by
  have hc1 : Continuous (fun p : ℝ × ℝ => Real.tanh (r * p.1) * Real.tanh (b * p.1 + p.2)) := by
    fun_prop
  have hc2 : Continuous (fun p : ℝ × ℝ => Real.tanh (b * p.1 + p.2)) := by fun_prop
  have hb1 (p : ℝ × ℝ) : |Real.tanh (r * p.1) * Real.tanh (b * p.1 + p.2)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one _).le).trans
      (Real.abs_tanh_lt_one _).le
  have h1 := integral_orthogonal_shift u v hu huv r _ hc1 hb1
  have h2 := integral_orthogonal_shift u v hu huv r _ hc2
    (fun p => (Real.abs_tanh_lt_one (b * p.1 + p.2)).le)
  rw [h1, h2]
  exact gaussian_posterior_two_linear r b (‖v‖ ^ 2).toNNReal

end LongTails.Proofs.SymmetricReverseFisherGaussian
