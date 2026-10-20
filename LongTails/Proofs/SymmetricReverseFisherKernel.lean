import LongTails.Proofs.SymmetricReverseFisherHyperbolic
import LongTails.Proofs.SymmetricReverseFisherGeometry
import LongTails.Proofs.SymmetricReverseFisherGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LongTails.Proofs.SymmetricReverseFisherKernel

open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGeometry
open LongTails.Proofs.SymmetricReverseFisherGaussian

lemma integrable_linear_exp (A B : ℝ) :
    IntegrableOn (fun x : ℝ => (A + B * x) * Real.exp (-x)) (Ioi 0) := by
  have hx : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_rpow
      (p := 1) (s := 1) (by norm_num) (by norm_num)
  change Integrable _ (volume.restrict (Ioi 0))
  convert ((integrableOn_exp_neg_Ioi 0).const_mul A).add (hx.const_mul B) using 1
  ext x
  simp only [Pi.add_apply]
  ring

lemma continuous_kernelPrimitive : Continuous kernelPrimitive :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_kernelPrimitive x).continuousAt)

lemma continuous_kernelW_sinh : Continuous (fun x => kernelW x * Real.sinh x) := by
  have ht : Continuous Real.tanh :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)
  have hs : Continuous sech :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_sech x).continuousAt)
  unfold kernelW
  fun_prop

lemma integrable_kernelPrimitive : IntegrableOn kernelPrimitive (Ioi 0) := by
  have hi : IntegrableOn (fun x => 4 * (2 * x + 1) * Real.exp (-x)) (Ioi 0) := by
    convert integrable_linear_exp 4 8 using 1
    ext x
    ring
  refine hi.mono' continuous_kernelPrimitive.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact kernelPrimitive_bound hx.le

lemma integrable_kernelW_sinh :
    IntegrableOn (fun x => kernelW x * Real.sinh x) (Ioi 0) := by
  have hi : IntegrableOn (fun x => 4 * (3 + 5 * x) * Real.exp (-x)) (Ioi 0) := by
    convert integrable_linear_exp 12 20 using 1
    ext x
    ring
  refine hi.mono' continuous_kernelW_sinh.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact kernelW_sinh_bound hx.le

lemma integral_kernelW_sinh_zero : (∫ x in Ioi (0 : ℝ), kernelW x * Real.sinh x) = 0 := by
  have hl := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun x (_ : x ∈ Ioi (0 : ℝ)) => hasDerivAt_kernelPrimitive x)
    integrable_kernelW_sinh integrable_kernelPrimitive
  simpa only [kernelPrimitive_zero, sub_zero] using
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x (_ : x ∈ Ici (0 : ℝ)) => hasDerivAt_kernelPrimitive x)
      integrable_kernelW_sinh hl

lemma kernel_weight_nonneg (h : ℝ → ℝ) (hmono : AntitoneOn h (Ioi 0))
    (hi : IntegrableOn (fun x => (kernelW x * Real.sinh x) * h x) (Ioi 0)) :
    0 ≤ ∫ x in Ioi (0 : ℝ), (kernelW x * Real.sinh x) * h x := by
  obtain ⟨b, hb, _, hleft, hright⟩ := exists_kernel_crossing
  have hb' : 0 < b := by linarith [hb.1]
  apply weighted_zero_nonneg (fun x => kernelW x * Real.sinh x) h (h b)
    integrable_kernelW_sinh hi integral_kernelW_sinh_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hs : 0 ≤ Real.sinh x := (Real.sinh_pos_iff.mpr hx).le
  rcases le_total x b with hxb | hbx
  · exact mul_nonneg (mul_nonneg (hleft x hx hxb) hs)
      (sub_nonneg.mpr (hmono hx hb' hxb))
  · exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (hright x hbx) hs)
      (sub_nonpos.mpr (hmono hb' hx hbx))

noncomputable def gaussianRatioWeight (a t x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * a ^ 2)) * (Real.sinh (t * x) / Real.sinh x)

lemma gaussianRatioWeight_bounds {a t x : ℝ} (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : 0 < x) : 0 ≤ gaussianRatioWeight a t x ∧ gaussianRatioWeight a t x ≤ 1 := by
  have hx' : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have htx : 0 ≤ Real.sinh (t * x) := (Real.sinh_pos_iff.mpr (mul_pos ht hx)).le
  have hrat : Real.sinh (t * x) / Real.sinh x ≤ 1 := by
    apply (div_le_one hx').mpr
    exact Real.sinh_le_sinh.mpr (mul_le_of_le_one_left hx.le ht1)
  have hexp : Real.exp (-(x ^ 2) / (2 * a ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hrat0 : 0 ≤ Real.sinh (t * x) / Real.sinh x := div_nonneg htx hx'.le
  unfold gaussianRatioWeight
  exact ⟨mul_nonneg (Real.exp_pos _).le hrat0,
    (mul_le_mul hexp hrat hrat0 (by norm_num)).trans_eq (one_mul 1)⟩

lemma gaussianRatioWeight_antitoneOn {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1) :
    AntitoneOn (gaussianRatioWeight a t) (Ioi 0) := by
  intro x hx y hy hxy
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.le hxy 2
  have he : Real.exp (-(y ^ 2) / (2 * a ^ 2)) ≤ Real.exp (-(x ^ 2) / (2 * a ^ 2)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
  have hr := sinh_ratio_antitoneOn ht ht1 hx hy hxy
  exact mul_le_mul he hr
    (div_nonneg (Real.sinh_pos_iff.mpr (mul_pos ht hy)).le (Real.sinh_pos_iff.mpr hy).le)
    (Real.exp_pos _).le

lemma weighted_gaussian_kernel_nonneg {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ ∫ x in Ioi (0 : ℝ), kernelW x * Real.sinh (t * x) *
      Real.exp (-(x ^ 2) / (2 * a ^ 2)) := by
  have hm : Measurable (gaussianRatioWeight a t) := by unfold gaussianRatioWeight; fun_prop
  have hi : IntegrableOn (fun x => (kernelW x * Real.sinh x) * gaussianRatioWeight a t x)
      (Ioi 0) := by
    refine integrable_kernelW_sinh.abs.mono'
      (continuous_kernelW_sinh.measurable.mul hm).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := gaussianRatioWeight_bounds ha ht ht1 hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hb.2
  have hn := kernel_weight_nonneg (gaussianRatioWeight a t)
    (gaussianRatioWeight_antitoneOn ha ht ht1) hi
  have he : (∫ x in Ioi (0 : ℝ), (kernelW x * Real.sinh x) * gaussianRatioWeight a t x) =
      ∫ x in Ioi (0 : ℝ), kernelW x * Real.sinh (t * x) *
        Real.exp (-(x ^ 2) / (2 * a ^ 2)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold gaussianRatioWeight
    field_simp [ne_of_gt (Real.sinh_pos_iff.mpr hx)]
  rwa [he] at hn

lemma integrable_kernelW_gaussian (m : ℝ) (v : NNReal) : Integrable kernelW (gaussianReal m v) := by
  have hi : Integrable (fun x : ℝ => 6 + 10 * |x|) (gaussianReal m v) :=
    (integrable_const 6).add (IsGaussian.integrable_id.abs.const_mul 10)
  exact hi.mono' continuous_kernelW.aestronglyMeasurable (ae_of_all _ kernelW_linear_bound)

lemma gaussian_scaled_density_difference {a : ℝ} (ha : 0 < a) (r x : ℝ) :
    gaussianPDFReal (a * r) (a ^ 2).toNNReal x -
        gaussianPDFReal (a * r) (a ^ 2).toNNReal (-x) =
      (2 * (Real.sqrt (2 * Real.pi * a ^ 2))⁻¹ * Real.exp (-(r ^ 2) / 2)) *
        (Real.exp (-(x ^ 2) / (2 * a ^ 2)) * Real.sinh ((r / a) * x)) := by
  have h1 : -(x - a * r) ^ 2 / (2 * a ^ 2) =
      -(r ^ 2) / 2 + -(x ^ 2) / (2 * a ^ 2) + (r / a) * x := by
    field_simp
    ring
  have h2 : -(-x - a * r) ^ 2 / (2 * a ^ 2) =
      -(r ^ 2) / 2 + -(x ^ 2) / (2 * a ^ 2) + -((r / a) * x) := by
    field_simp
    ring
  simp only [gaussianPDFReal, Real.coe_toNNReal', max_eq_left (sq_nonneg a), h1, h2,
    Real.exp_add, Real.sinh_eq]
  ring

lemma gaussian_kernelW_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hra : r ≤ a) :
    0 ≤ ∫ y, kernelW y ∂gaussianReal (a * r) (a ^ 2).toNNReal := by
  have hv : (a ^ 2).toNNReal ≠ 0 := by positivity
  rw [gaussian_odd_positive_half (a * r) (a ^ 2).toNNReal hv kernelW
    (integrable_kernelW_gaussian _ _) kernelW_neg]
  simp_rw [gaussian_scaled_density_difference ha]
  have he : (∫ x in Ioi (0 : ℝ), kernelW x *
      ((2 * (Real.sqrt (2 * Real.pi * a ^ 2))⁻¹ * Real.exp (-(r ^ 2) / 2)) *
        (Real.exp (-(x ^ 2) / (2 * a ^ 2)) * Real.sinh ((r / a) * x)))) =
      (2 * (Real.sqrt (2 * Real.pi * a ^ 2))⁻¹ * Real.exp (-(r ^ 2) / 2)) *
        (∫ x in Ioi (0 : ℝ), kernelW x * Real.sinh ((r / a) * x) *
          Real.exp (-(x ^ 2) / (2 * a ^ 2))) := by
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  rw [he]
  apply mul_nonneg (by positivity)
  exact weighted_gaussian_kernel_nonneg ha (div_pos hr ha) ((div_le_one ha).mpr hra)

lemma gaussian_scaled_kernelW_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hra : r ≤ a) :
    0 ≤ ∫ x, kernelW (a * x) ∂gaussianReal r 1 := by
  rw [← gaussian_integral_scale r a kernelW continuous_kernelW.measurable]
  exact gaussian_kernelW_nonneg ha hr hra

lemma integrable_kernelV_gaussian (m : ℝ) (v : NNReal) : Integrable kernelV (gaussianReal m v) := by
  have hi : Integrable (fun x : ℝ => 1 + 3 * |x| + 2 * x ^ 2) (gaussianReal m v) :=
    ((integrable_const 1).add (IsGaussian.integrable_id.abs.const_mul 3)).add
      (IsGaussian.memLp_two_id.integrable_sq.const_mul 2)
  exact hi.mono' (by unfold kernelV; fun_prop) (ae_of_all _ kernelV_quadratic_bound)

noncomputable def kernelDerivative (a x : ℝ) : ℝ := 2 * kernelV (a * x) + a ^ 2 * kernelW (a * x)

lemma integrable_kernelDerivative (a r : ℝ) : Integrable (kernelDerivative a) (gaussianReal r 1) := by
  exact ((gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2).add
    ((gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)).const_mul (a ^ 2))

lemma kernelDerivative_neg (a x : ℝ) : kernelDerivative a (-x) = -kernelDerivative a x := by
  simp [kernelDerivative, kernelV_neg, kernelW_neg]
  ring

lemma bounded_kernelDerivative_lower {a r : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3) (hr : 0 ≤ r) :
    min a 1 * min r 1 / 60 ≤ ∫ x, kernelDerivative a x ∂gaussianReal r 1 := by
  have hm := gaussian_odd_clip_lower hr (show 0 ≤ min a 1 / 15 by positivity)
    (kernelDerivative a) (integrable_kernelDerivative a r) (kernelDerivative_neg a) ?_
  · convert hm using 1
    ring
  · intro x hx
    have h := kernel_combination_lower ha ha3 (mul_nonneg ha hx.le)
    have hs := clip_scale ha hx.le
    have hc : clip (a * x) = min (a * x) 1 := by
      unfold clip
      rw [max_eq_right (le_min (by norm_num) (by linarith [mul_nonneg ha hx.le])), min_comm]
    rw [hc] at hs
    unfold kernelDerivative
    linarith

lemma gaussian_kernelV_lower {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    min a 1 * min r 1 / 60 ≤ ∫ x, 2 * kernelV (a * x) ∂gaussianReal r 1 := by
  have hm := gaussian_odd_clip_lower hr (show 0 ≤ min a 1 / 15 by positivity)
    (fun x => 2 * kernelV (a * x))
    ((gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2)
    (fun x => by simp [kernelV_neg]) ?_
  · convert hm using 1
    ring
  · intro x hx
    have h := kernel_combination_lower (a := 0) (by norm_num) (by norm_num) (mul_nonneg ha hx.le)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h
    have hs := clip_scale ha hx.le
    have hc : clip (a * x) = min (a * x) 1 := by
      unfold clip
      rw [max_eq_right (le_min (by norm_num) (by linarith [mul_nonneg ha hx.le])), min_comm]
    rw [hc] at hs
    linarith

lemma inner_kernelDerivative_lower {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hra : r ≤ a) :
    min a 1 * min r 1 / 60 ≤ ∫ x, kernelDerivative a x ∂gaussianReal r 1 := by
  have hv := (gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2
  have hw := (gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)).const_mul (a ^ 2)
  unfold kernelDerivative
  rw [integral_add hv hw, integral_const_mul (a ^ 2)]
  exact (gaussian_kernelV_lower ha.le hr.le).trans
    (le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) (gaussian_scaled_kernelW_nonneg ha hr hra)))

end LongTails.Proofs.SymmetricReverseFisherKernel
