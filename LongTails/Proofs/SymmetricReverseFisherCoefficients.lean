import LongTails.Proofs.SymmetricReverseFisherScalar
open MeasureTheory ProbabilityTheory Set
namespace LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherRadial
open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherScalar
noncomputable def tanhMean (a c : ℝ) : ℝ :=
  ∫ y, Real.tanh y ∂gaussianReal c (a ^ 2).toNNReal
noncomputable def sechMean (a c : ℝ) : ℝ :=
  ∫ y, sech y ^ 2 ∂gaussianReal c (a ^ 2).toNNReal
lemma hasDerivAt_tanhMean (a c : ℝ) : HasDerivAt (tanhMean a) (sechMean a c) c :=
  hasDerivAt_gaussian_location_integral (a ^ 2).toNNReal Real.tanh (fun y => sech y ^ 2)
    (by fun_prop) hasDerivAt_tanh (fun y => (Real.abs_tanh_lt_one y).le) abs_sech_sq_le_one c
lemma sechMean_nonneg (a c : ℝ) : 0 ≤ sechMean a c := integral_nonneg (fun y => sq_nonneg (sech y))
lemma sechMean_le_one (a c : ℝ) : sechMean a c ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal c (a ^ 2).toNNReal)
    (ae_of_all _ (fun y => show ‖sech y ^ 2‖ ≤ 1 from abs_sech_sq_le_one y))
  have h' : |sechMean a c| ≤ 1 := by simpa [sechMean] using h
  exact (le_abs_self _).trans h'
lemma tanhMean_zero (a : ℝ) : tanhMean a 0 = 0 := by
  have hm := gaussianReal_map_neg (μ := 0) (v := (a ^ 2).toNNReal)
  simp only [neg_zero] at hm
  have h := integral_map (μ := gaussianReal 0 (a ^ 2).toNNReal) (φ := fun y : ℝ => -y)
    (by fun_prop) (f := Real.tanh) (by fun_prop)
  rw [hm] at h
  simp only [Real.tanh_neg, integral_neg] at h
  unfold tanhMean
  linarith
lemma tanhMean_nonneg {a c : ℝ} (hc : 0 ≤ c) : 0 ≤ tanhMean a c := by
  have hm : Monotone (tanhMean a) := monotone_of_hasDerivAt_nonneg (hasDerivAt_tanhMean a)
    (fun y => sechMean_nonneg a y)
  simpa only [tanhMean_zero] using hm hc
lemma tanhMean_le_argument {a c : ℝ} (hc : 0 ≤ c) : tanhMean a c ≤ c := by
  have hm : Antitone (fun t => tanhMean a t - t) := antitone_of_hasDerivAt_nonpos
    (fun t => (hasDerivAt_tanhMean a t).sub (hasDerivAt_id t))
    (fun t => sub_nonpos.mpr (sechMean_le_one a t))
  have h := hm hc
  have h' : tanhMean a c - c ≤ 0 := by simpa only [tanhMean_zero, sub_zero] using h
  linarith
lemma tanhMean_le_one (a c : ℝ) : tanhMean a c ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal c (a ^ 2).toNNReal)
    (ae_of_all _ (fun y => show ‖Real.tanh y‖ ≤ 1 from (Real.abs_tanh_lt_one y).le))
  have h' : |tanhMean a c| ≤ 1 := by simpa [tanhMean] using h
  exact (le_abs_self _).trans h'
lemma sq_mul_exp_le_one (r : ℝ) : r ^ 2 * Real.exp (-r ^ 2 / 2) ≤ 1 := by
  have ht := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ r ^ 2 / 2) 3
  norm_num [Finset.sum_range_succ] at ht
  have he : r ^ 2 ≤ Real.exp (r ^ 2 / 2) := by nlinarith [sq_nonneg (r ^ 2 - 2)]
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-r ^ 2 / 2)).le
  have hid : Real.exp (r ^ 2 / 2) * Real.exp (-r ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rwa [hid] at h
lemma self_tanhMean (r : ℝ) :
    (∫ x, Real.tanh (r * x) ∂gaussianReal r 1) = tanhMean r (r ^ 2) := by
  unfold tanhMean
  have h := gaussian_integral_scale r r Real.tanh (by fun_prop)
  rw [← pow_two r] at h
  exact h.symm
lemma sech_four_mean_le_exp (r : ℝ) :
    (∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1) ≤ Real.exp (-r ^ 2 / 2) := by
  calc
    _ ≤ ∫ x, sech (r * x) ^ 2 ∂gaussianReal r 1 :=
      integral_mono (integrable_sech_four_scaled r r) (integrable_sech_sq_scaled r r)
        (fun x => by
          have h : sech (r * x) ^ 2 ≤ 1 := by
            rw [← abs_of_nonneg (sq_nonneg (sech (r * x)))]
            exact abs_sech_sq_le_one _
          nlinarith [sq_nonneg (sech (r * x)), mul_nonneg (sq_nonneg (sech (r * x))) (sub_nonneg.mpr h)])
    _ = Real.exp (-r ^ 2 / 2) * sechAverage r := gaussian_sech_sq_tilt r
    _ ≤ Real.exp (-r ^ 2 / 2) := mul_le_of_le_one_right (Real.exp_pos _).le
      ((le_abs_self _).trans (sechAverage_bound r))
lemma sech_four_mean_le_one (r : ℝ) : (∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1) ≤ 1 :=
  (sech_four_mean_le_exp r).trans (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r]))
lemma alpha_nonneg (r : ℝ) : 0 ≤ alpha r := by
  unfold alpha
  rw [self_tanhMean]
  exact add_nonneg (mul_nonneg (by norm_num) (tanhMean_nonneg (sq_nonneg r)))
    (mul_nonneg (by positivity) (integral_nonneg (fun x => by positivity)))
lemma alpha_le_four_min (r : ℝ) : alpha r ≤ 4 * min (r ^ 2) 1 := by
  have ht0 := tanhMean_le_argument (a := r) (sq_nonneg r)
  have ht1 := tanhMean_le_one r (r ^ 2)
  have hs := sech_four_mean_le_one r
  have hs' : r ^ 2 * (∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (sech_four_mean_le_exp r) (sq_nonneg r)).trans (sq_mul_exp_le_one r)
  unfold alpha
  rw [self_tanhMean]
  rcases le_total (r ^ 2) 1 with h | h
  · rw [min_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg r)]
  · rw [min_eq_right h]
    nlinarith
lemma radialSelf_nonneg (r : ℝ) : 0 ≤ radialSelf r := by
  rw [radialSelf_posterior, self_tanhMean]
  exact mul_nonneg (sq_nonneg _) (tanhMean_nonneg (sq_nonneg _))
lemma radialSelf_le_fourth (r : ℝ) : radialSelf r ≤ r ^ 4 := by
  rw [radialSelf_posterior, self_tanhMean]
  have h := mul_le_mul_of_nonneg_left (tanhMean_le_argument (a := r) (sq_nonneg r)) (sq_nonneg r)
  nlinarith
lemma tanh_monotone : Monotone Real.tanh := monotone_of_hasDerivAt_nonneg hasDerivAt_tanh
  (fun x => sq_nonneg (sech x))
lemma tanh_one_lower : (1 : ℝ) / 2 ≤ Real.tanh 1 := by
  rw [tanh_eq_exp_two]
  have h := Real.add_one_le_exp (2 : ℝ)
  norm_num only [mul_one]
  apply (le_div_iff₀ (by positivity : 0 < Real.exp 2 + 1)).mpr
  linarith
lemma tanh_clip_lower {y : ℝ} (hy : 0 < y) : (1 : ℝ) / 2 * clip y ≤ Real.tanh y := by
  rcases le_total y 1 with h | h
  · rw [clip_of_mem ⟨by linarith, h⟩]
    have hs := tanh_scale_le (x := 1) (by norm_num) hy h
    simp only [mul_one] at hs
    nlinarith [mul_le_mul_of_nonneg_left tanh_one_lower hy.le]
  · have hc : clip y = 1 := by unfold clip; simp [min_eq_left h]
    rw [hc]
    simpa using tanh_one_lower.trans (tanh_monotone h)
lemma gaussian_affine_integral (a c : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂gaussianReal c (a ^ 2).toNNReal) =
      ∫ z, f (a * z + c) ∂gaussianReal 0 1 := by
  rw [gaussian_location_integral]
  have h := gaussian_integral_scale 0 a (fun y => f (y + c)) (hf.comp (by fun_prop))
  simpa only [mul_zero] using h
  exact hf
lemma gaussian_centered_odd_zero (v : NNReal) (f : ℝ → ℝ) (hf : Measurable f)
    (ho : ∀ x, f (-x) = -f x) : (∫ x, f x ∂gaussianReal 0 v) = 0 := by
  have hm := gaussianReal_map_neg (μ := 0) (v := v)
  simp only [neg_zero] at hm
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun y : ℝ => -y)
    (by fun_prop) (f := f) hf.aestronglyMeasurable
  rw [hm] at h
  simp_rw [ho, integral_neg] at h
  linarith
lemma integrable_clip_affine (a c : ℝ) :
    Integrable (fun z => clip (a * z + c)) (gaussianReal 0 1) := by
  simpa using integrable_weighted_bounded (gaussianReal 0 1) (fun _ => 1) clip
    (integrable_const 1) (by unfold clip; fun_prop) abs_clip_le_one a c
lemma clip_scaled_shift_difference {a c : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (z : ℝ) :
    c * (Icc (-1 : ℝ) 0).indicator (fun _ => 1) z ≤ clip (a * z + c) - clip (a * z) := by
  by_cases hz : z ∈ Icc (-1 : ℝ) 0
  · rw [indicator_of_mem hz]
    have haz : a * z ∈ Icc (-1 : ℝ) 0 := ⟨by nlinarith [hz.1, mul_nonneg (sub_nonneg.mpr ha1) (neg_nonneg.mpr hz.2)], mul_nonpos_of_nonneg_of_nonpos ha hz.2⟩
    rw [clip_of_mem ⟨by linarith [haz.1], by linarith [haz.2]⟩,
      clip_of_mem ⟨haz.1, by linarith [haz.2]⟩]
    linarith
  · rw [indicator_of_notMem hz, mul_zero]
    exact sub_nonneg.mpr (clip_monotone (by linarith))
lemma clip_small_scale_lower {a c : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    c / 4 ≤ ∫ z, clip (a * z + c) ∂gaussianReal 0 1 := by
  have hi := (integrable_const (1 : ℝ) (μ := gaussianReal 0 1)).indicator (s := Icc (-1 : ℝ) 0) measurableSet_Icc
  have h := integral_mono (hi.const_mul c) ((integrable_clip_affine a c).sub (integrable_clip_affine a 0))
    (fun z => by simpa only [add_zero, Pi.sub_apply] using clip_scaled_shift_difference ha ha1 hc hc1 z)
  have hz : (∫ z, clip (a * z + 0) ∂gaussianReal 0 1) = 0 := by
    apply gaussian_centered_odd_zero 1 _ (by unfold clip; fun_prop)
    intro x
    simp only [add_zero, mul_neg, clip_neg]
  erw [integral_sub (integrable_clip_affine a c) (integrable_clip_affine a 0), hz,
    integral_const_mul, integral_indicator measurableSet_Icc] at h
  simp only [sub_zero, setIntegral_const, smul_eq_mul, mul_one] at h
  have hm := mul_le_mul_of_nonneg_left gaussian_unit_interval_mass hc
  linarith
lemma tanhMean_monotone (a : ℝ) : Monotone (tanhMean a) :=
  monotone_of_hasDerivAt_nonneg (hasDerivAt_tanhMean a) (fun y => sechMean_nonneg a y)
lemma tanhMean_clip_lower {a c : ℝ} (hc : 0 ≤ c) :
    (1 : ℝ) / 2 * (∫ y, clip y ∂gaussianReal c (a ^ 2).toNNReal) ≤ tanhMean a c := by
  have hi : Integrable clip (gaussianReal c (a ^ 2).toNNReal) := by
    simpa using integrable_clip_shift (gaussianReal c (a ^ 2).toNNReal) 0
  have ht : Integrable Real.tanh (gaussianReal c (a ^ 2).toNNReal) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact ae_of_all _ (fun y => (Real.abs_tanh_lt_one y).le)
  have h := gaussian_odd_integral_mono hc (a ^ 2).toNNReal (fun y => (1 : ℝ) / 2 * clip y)
    Real.tanh (hi.const_mul _) ht (fun y => by rw [clip_neg]; ring) Real.tanh_neg
    (fun y hy => tanh_clip_lower hy)
  rw [integral_const_mul] at h
  exact h
lemma tanhMean_lower_small_scale {a c : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c) :
    min c 1 / 8 ≤ tanhMean a c := by
  have hm0 : 0 ≤ min c 1 := le_min hc (by norm_num)
  have hclip := clip_small_scale_lower ha ha1 hm0 (min_le_right c 1)
  have h := tanhMean_clip_lower (a := a) hm0
  rw [gaussian_affine_integral a (min c 1) clip (by unfold clip; fun_prop)] at h
  have hmono := tanhMean_monotone a (min_le_left c 1)
  linarith
lemma tanhMean_lower_large_scale {a c : ℝ} (ha : 1 ≤ a) (hc : 0 ≤ c) :
    min c a / (8 * a) ≤ tanhMean a c := by
  have ha0 : 0 < a := by linarith
  have h := gaussian_odd_clip_lower (r := c / a) (C := (1 : ℝ) / 2)
    (div_nonneg hc ha0.le) (by norm_num) (fun x => Real.tanh (a * x))
    (integrable_tanh_scaled (c / a) a) (fun x => by rw [mul_neg, Real.tanh_neg])
    (fun x hx => (tanh_clip_lower hx).trans (tanh_monotone (by nlinarith)))
  have he : tanhMean a c = ∫ x, Real.tanh (a * x) ∂gaussianReal (c / a) 1 := by
    unfold tanhMean
    conv_lhs => rw [show c = a * (c / a) by field_simp]
    exact gaussian_integral_scale (c / a) a Real.tanh (by fun_prop)
  rw [← he] at h
  have hm : min c a / (8 * a) = (1 : ℝ) / 2 * (min (c / a) 1 / 4) := by
    rcases le_total c a with hca | hac
    · rw [min_eq_left hca, min_eq_left ((div_le_one ha0).mpr hca)]
      ring
    · rw [min_eq_right hac, min_eq_right ((one_le_div ha0).mpr hac)]
      field_simp
      norm_num
  rwa [hm]
lemma tanhMean_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    min c (max a 1) / (8 * max a 1) ≤ tanhMean a c := by
  rcases le_total a 1 with ha1 | ha1
  · rw [max_eq_right ha1, mul_one]
    exact tanhMean_lower_small_scale ha ha1 hc
  · rw [max_eq_left ha1]
    exact tanhMean_lower_large_scale ha1 hc
lemma alpha_lower {r : ℝ} (hr : 0 ≤ r) : min (r ^ 2) 1 / 120 ≤ alpha r := by
  have h := tanhMean_lower hr (sq_nonneg r)
  have hs : 0 ≤ ∫ x, sech (r * x) ^ 4 ∂gaussianReal r 1 := integral_nonneg (fun x => by positivity)
  unfold alpha
  rw [self_tanhMean]
  rcases le_total r 1 with hr1 | hr1
  · rw [max_eq_right hr1, mul_one, min_eq_left (by nlinarith : r ^ 2 ≤ 1)] at h
    rw [min_eq_left (by nlinarith : r ^ 2 ≤ 1)]
    nlinarith [mul_nonneg (sq_nonneg r) hs]
  · have hr0 : 0 < r := by linarith
    rw [max_eq_left hr1, min_eq_right (by nlinarith : r ≤ r ^ 2)] at h
    have he : r / (8 * r) = 1 / 8 := by field_simp
    rw [he] at h
    rw [min_eq_right (by nlinarith : 1 ≤ r ^ 2)]
    nlinarith [mul_nonneg (sq_nonneg r) hs]
end LongTails.Proofs.SymmetricReverseFisherCoefficients
