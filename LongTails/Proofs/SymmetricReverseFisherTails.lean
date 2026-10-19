import LongTails.Proofs.SymmetricReverseFisherKernel

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LongTails.Proofs.SymmetricReverseFisherTails

open LongTails.Proofs.SymmetricReverseFisherHyperbolic
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherKernel

lemma integrable_linear_exp_rate {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    IntegrableOn (fun x : ℝ => (A + B * x) * Real.exp (-c * x)) (Ioi 0) := by
  have hx : IntegrableOn (fun x : ℝ => x * Real.exp (-c * x)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
  have he : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  change Integrable _ (volume.restrict (Ioi 0))
  convert (he.const_mul A).add (hx.const_mul B) using 1
  ext x
  simp only [Pi.add_apply]
  ring

lemma integral_linear_exp_tail {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    (∫ x in Ioi t, x * Real.exp (-c * x)) = (t / c + 1 / c ^ 2) * Real.exp (-c * t) := by
  let F := fun x : ℝ => -(x / c + 1 / c ^ 2) * Real.exp (-c * x)
  have hd (x : ℝ) : HasDerivAt F (x * Real.exp (-c * x)) x := by
    convert (((((hasDerivAt_id x).div_const c).add_const (1 / c ^ 2)).neg).mul
      (((hasDerivAt_id x).const_mul (-c)).exp)) using 1
    · rfl
    · dsimp only [id_eq, Pi.neg_apply, Pi.add_apply]
      field_simp
      ring
  have hi0 : IntegrableOn (fun x : ℝ => x * Real.exp (-c * x)) (Ioi 0) := by
    simpa using integrable_linear_exp_rate hc 0 1
  have hi := hi0.mono_set (Ioi_subset_Ioi ht)
  have hF0 : IntegrableOn F (Ioi 0) := by
    convert integrable_linear_exp_rate hc (-(1 / c ^ 2)) (-(1 / c)) using 1
    ext x
    dsimp only [F]
    ring
  have hF := hF0.mono_set (Ioi_subset_Ioi ht)
  have hl := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun x (_ : x ∈ Ioi t) => hd x) hi hF
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x (_ : x ∈ Ici t) => hd x) hi hl
  rw [he]
  dsimp only [F]
  ring

lemma gaussian_density_le_peak (r x : ℝ) :
    gaussianPDFReal r 1 x ≤ gaussianPDFReal 0 1 0 := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x - r)]))

lemma sqrt_two_pi_lower : (12 : ℝ) / 5 ≤ Real.sqrt (2 * Real.pi) := by
  have h := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_gt_three
  nlinarith [Real.sqrt_nonneg (2 * Real.pi)]

lemma gaussian_peak_le_one : gaussianPDFReal 0 1 0 ≤ 1 := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one]
  exact inv_le_one_of_one_le₀ (by linarith [sqrt_two_pi_lower])

lemma gaussian_three_bound : 48 * gaussianPDFReal 0 1 3 ≤ 5 / 22 := by
  have hehalf : (22 : ℝ) / 5 ≤ Real.exp (3 / 2) := by
    have he : Real.exp 3 = Real.exp (3 / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have h := exp_three_lower
    rw [he] at h
    nlinarith [Real.exp_pos ((3 : ℝ) / 2)]
  have he : 88 ≤ Real.exp (9 / 2) := by
    have h := mul_le_mul exp_three_lower hehalf (by norm_num : (0 : ℝ) ≤ 22 / 5) (Real.exp_pos 3).le
    rw [← Real.exp_add] at h
    norm_num at h
    exact h
  have hm := mul_le_mul sqrt_two_pi_lower he (by norm_num : (0 : ℝ) ≤ 88)
    (Real.sqrt_nonneg (2 * Real.pi))
  have hp : 0 < Real.sqrt (2 * Real.pi) * Real.exp (9 / 2) := by positivity
  have hd : 48 * gaussianPDFReal 0 1 3 = 48 / (Real.sqrt (2 * Real.pi) * Real.exp (9 / 2)) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    norm_num only
    rw [Real.exp_neg]
    field_simp
  rw [hd]
  apply (div_le_iff₀ hp).mpr
  nlinarith

lemma exponential_eighteen_bound :
    228 * gaussianPDFReal 0 1 0 * Real.exp (-18) ≤ 1 / 1000 := by
  have he : (64000000 : ℝ) ≤ Real.exp 18 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) exp_three_lower 6
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hm := mul_le_mul_of_nonneg_right gaussian_peak_le_one (Real.exp_pos (-18)).le
  have hh : 228 * Real.exp (-18) ≤ 1 / 1000 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  nlinarith

lemma gaussian_linear_tail_antitone :
    AntitoneOn (fun x : ℝ => x * gaussianPDFReal 0 1 x) (Ici 3) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x * gaussianPDFReal 0 1 x)
      ((1 - x ^ 2) * gaussianPDFReal 0 1 x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_gaussian_density 0 x) using 1
    · rfl
    · simp only [id_eq, sub_zero]
      ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
    (fun x _ => (hd x).hasDerivWithinAt)
  intro x hx
  have hx3 : 3 < x := by simpa using hx
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (gaussianPDFReal_nonneg _ _ _)

lemma polynomial_tail_antitone :
    AntitoneOn (fun x : ℝ => (8 * x ^ 3 + 4 * x) * Real.exp (-2 * x ^ 2)) (Ici 3) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (8 * x ^ 3 + 4 * x) * Real.exp (-2 * x ^ 2))
      ((8 * x ^ 2 + 4 - 32 * x ^ 4) * Real.exp (-2 * x ^ 2)) x := by
    convert ((((hasDerivAt_id x).pow 3).const_mul 8).add ((hasDerivAt_id x).const_mul 4)).mul
      ((((hasDerivAt_id x).pow 2).const_mul (-2)).exp) using 1
    · rfl
    · simp only [id_eq, Pi.add_apply, Pi.pow_apply]
      ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn
    (fun x _ => (hd x).hasDerivWithinAt)
  intro x hx
  have hx3 : 3 < x := by simpa using hx
  apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
  nlinarith [sq_nonneg (x ^ 2 - 1)]

lemma gaussian_density_near {r a x : ℝ} (hx : x ≤ a) (hra : a ≤ r) :
    gaussianPDFReal r 1 x ≤ gaussianPDFReal 0 1 a * Real.exp (a * x - x ^ 2 / 2) := by
  have hm : gaussianPDFReal r 1 x ≤ gaussianPDFReal a 1 x := by
    unfold gaussianPDFReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    norm_num only [NNReal.coe_one, mul_one]
    nlinarith [sq_nonneg (r - a), mul_nonneg (sub_nonneg.mpr hra) (sub_nonneg.mpr hx)]
  have he : gaussianPDFReal a 1 x = gaussianPDFReal 0 1 a * Real.exp (a * x - x ^ 2 / 2) := by
    rw [gaussian_density_split]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [he] at hm

lemma gaussian_weighted_near {r a x : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (hra : a ≤ r) :
    x * Real.exp (-2 * a * x) * gaussianPDFReal r 1 x ≤
      gaussianPDFReal 0 1 a * (x * Real.exp (-a * x)) := by
  have h := mul_le_mul_of_nonneg_left (gaussian_density_near hxa hra)
    (show 0 ≤ x * Real.exp (-2 * a * x) by positivity)
  have he : x * Real.exp (-2 * a * x) *
      (gaussianPDFReal 0 1 a * Real.exp (a * x - x ^ 2 / 2)) =
      gaussianPDFReal 0 1 a * x * Real.exp (-a * x - x ^ 2 / 2) := by
    calc
      _ = gaussianPDFReal 0 1 a * x *
          (Real.exp (-2 * a * x) * Real.exp (a * x - x ^ 2 / 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [he] at h
  apply h.trans
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (gaussianPDFReal_nonneg _ _ _) hx)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg x]

lemma gaussian_tail_envelope_bound {a : ℝ} (ha : 3 ≤ a) :
    16 * a * gaussianPDFReal 0 1 a +
      gaussianPDFReal 0 1 0 * ((8 * a ^ 3 + 4 * a) * Real.exp (-2 * a ^ 2)) ≤ 1 / 4 := by
  have h1 := gaussian_linear_tail_antitone (show (3 : ℝ) ∈ Ici 3 by simp) ha ha
  have h2 := polynomial_tail_antitone (show (3 : ℝ) ∈ Ici 3 by simp) ha ha
  norm_num at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (gaussianPDFReal_nonneg 0 1 0)
  dsimp only at h1
  simp only [neg_mul] at h2 h3 ⊢
  nlinarith [gaussian_three_bound, exponential_eighteen_bound]

lemma integrable_weighted_gaussian_tail {a : ℝ} (ha : 0 < a) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-2 * a * x) * gaussianPDFReal r 1 x) (Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ => x * Real.exp (-2 * a * x)) (Ioi 0) := by
    simpa [neg_mul] using integrable_linear_exp_rate (show 0 < 2 * a by positivity) 0 1
  refine hi.mono' (by unfold gaussianPDFReal; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _))]
  exact mul_le_of_le_one_right (by positivity) ((gaussian_density_le_peak r x).trans gaussian_peak_le_one)

lemma weighted_gaussian_tail_bound {a r : ℝ} (ha : 0 < a) (hra : a ≤ r) :
    (∫ x in Ioi (0 : ℝ), x * Real.exp (-2 * a * x) * gaussianPDFReal r 1 x) ≤
      gaussianPDFReal 0 1 a / a ^ 2 +
        gaussianPDFReal 0 1 0 * ((a / (2 * a) + 1 / (2 * a) ^ 2) * Real.exp (-(2 * a) * a)) := by
  have hi1 : IntegrableOn (fun x : ℝ => x * Real.exp (-a * x)) (Ioi 0) := by
    simpa using integrable_linear_exp_rate ha 0 1
  have hi2 : IntegrableOn (fun x : ℝ => x * Real.exp (-2 * a * x)) (Ioi 0) := by
    simpa [neg_mul] using integrable_linear_exp_rate (show 0 < 2 * a by positivity) 0 1
  have hi3 := Integrable.indicator (s := Ioi a) hi2 measurableSet_Ioi
  have hm := setIntegral_mono_on (integrable_weighted_gaussian_tail ha r)
    ((hi1.const_mul (gaussianPDFReal 0 1 a)).add (hi3.const_mul (gaussianPDFReal 0 1 0)))
    measurableSet_Ioi (fun x hx => ?_)
  · simp only [Pi.add_apply] at hm
    rw [integral_add (hi1.const_mul _) (hi3.const_mul _), integral_const_mul,
      integral_const_mul, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      sup_eq_right.mpr ha.le, integral_linear_exp_tail ha (by norm_num)] at hm
    have he : (∫ x in Ioi a, x * Real.exp (-2 * a * x)) =
        (a / (2 * a) + 1 / (2 * a) ^ 2) * Real.exp (-(2 * a) * a) := by
      simpa only [neg_mul] using integral_linear_exp_tail (show 0 < 2 * a by positivity) ha.le
    rw [he] at hm
    simpa only [zero_div, zero_mul, mul_zero, one_mul, Real.exp_zero, add_zero, zero_add, mul_one, div_eq_mul_inv] using hm
  · dsimp only [Pi.add_apply]
    have hx0 : 0 ≤ x := hx.le
    by_cases hxA : x ≤ a
    · rw [indicator_of_notMem (show x ∉ Ioi a from not_lt.mpr hxA), mul_zero, add_zero]
      exact gaussian_weighted_near hx.le hxA hra
    · rw [indicator_of_mem (show x ∈ Ioi a from lt_of_not_ge hxA)]
      have h := mul_le_mul_of_nonneg_left (gaussian_density_le_peak r x)
        (show 0 ≤ x * Real.exp (-2 * a * x) by positivity)
      have hn : 0 ≤ gaussianPDFReal 0 1 a * (x * Real.exp (-a * x)) :=
        mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by positivity)
      nlinarith

lemma gaussian_kernelW_tail_lower {a r : ℝ} (ha : 0 < a) (hra : a ≤ r) :
    -16 * a * (∫ x in Ioi (0 : ℝ), x * Real.exp (-2 * a * x) * gaussianPDFReal r 1 x) ≤
      ∫ x, kernelW (a * x) ∂gaussianReal r 1 := by
  have hi := gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)
  have ho (x : ℝ) : kernelW (a * -x) = -kernelW (a * x) := by rw [mul_neg, kernelW_neg]
  rw [gaussian_odd_positive_half r 1 one_ne_zero _ hi ho]
  have hj := integrable_gaussian_odd_half r 1 one_ne_zero _ hi ho
  have hm := setIntegral_mono_on ((integrable_weighted_gaussian_tail ha r).const_mul (-16 * a))
    hj measurableSet_Ioi (fun x hx => ?_)
  · rwa [integral_const_mul] at hm
  · have hx0 : 0 ≤ x := hx.le
    have hd := gaussian_density_reflection_le (1 : NNReal) (ha.le.trans hra) hx0
    have hw := kernelW_lower_exp (mul_nonneg ha.le hx0)
    rw [show -2 * (a * x) = -2 * a * x by ring] at hw
    have hlow := mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hd)
    have hn : 0 ≤ 16 * (a * x) * Real.exp (-2 * a * x) := by positivity
    have hp := mul_nonneg hn (gaussianPDFReal_nonneg r 1 (-x))
    nlinarith

lemma gaussian_kernelW_lower_quarter {a r : ℝ} (ha : 3 ≤ a) (hra : a ≤ r) :
    -(1 : ℝ) / 4 ≤ a ^ 2 * (∫ x, kernelW (a * x) ∂gaussianReal r 1) := by
  have ha0 : 0 < a := by linarith
  have hlow := mul_le_mul_of_nonneg_left (gaussian_kernelW_tail_lower ha0 hra) (sq_nonneg a)
  have hup := mul_le_mul_of_nonneg_left (weighted_gaussian_tail_bound ha0 hra)
    (show 0 ≤ 16 * a ^ 3 by positivity)
  have he : 16 * a ^ 3 * (gaussianPDFReal 0 1 a / a ^ 2 +
      gaussianPDFReal 0 1 0 * ((a / (2 * a) + 1 / (2 * a) ^ 2) * Real.exp (-(2 * a) * a))) =
      16 * a * gaussianPDFReal 0 1 a +
        gaussianPDFReal 0 1 0 * ((8 * a ^ 3 + 4 * a) * Real.exp (-2 * a ^ 2)) := by
    rw [show -(2 * a) * a = -2 * a ^ 2 by ring]
    field_simp
    ring
  rw [he] at hup
  nlinarith [gaussian_tail_envelope_bound ha]

lemma gaussian_shifted_interval_mass (r : ℝ) :
    (5 : ℝ) / 18 ≤ ∫ x in Icc (r - 1) r, gaussianPDFReal r 1 x := by
  have hm := gaussianReal_map_add_const (μ := 0) (v := 1) r
  rw [zero_add] at hm
  have hs : (fun x : ℝ => x + r) ⁻¹' Icc (r - 1) r = Icc (-1) 0 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have he : (gaussianReal r 1).real (Icc (r - 1) r) =
      (gaussianReal 0 1).real (Icc (-1) 0) := by
    rw [measureReal_def, ← hm, Measure.map_apply (by fun_prop) measurableSet_Icc, hs]
    rfl
  have h := gaussian_unit_interval_mass
  rw [← he, measureReal_def, gaussianReal_apply_eq_integral r one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))] at h
  exact h

lemma gaussian_density_ratio (r x : ℝ) :
    gaussianPDFReal r 1 (-x) = gaussianPDFReal r 1 x * Real.exp (-2 * r * x) := by
  rw [gaussian_density_split, gaussian_density_split]
  simp only [neg_sq, mul_neg]
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_density_gap {r x : ℝ} (hr : 3 ≤ r) (hx : r - 1 ≤ x) :
    (3 : ℝ) / 4 * gaussianPDFReal r 1 x ≤ gaussianPDFReal r 1 x - gaussianPDFReal r 1 (-x) := by
  have he : 20 ≤ Real.exp (2 * r * x) :=
    exp_three_lower.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hsmall : Real.exp (-2 * r * x) ≤ 1 / 4 := by
    rw [show -2 * r * x = -(2 * r * x) by ring, Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have h := mul_le_mul_of_nonneg_left hsmall (gaussianPDFReal_nonneg r 1 x)
  rw [gaussian_density_ratio]
  nlinarith

lemma kernelV_interval_lower {a r x : ℝ} (ha : 3 ≤ a) (hra : a ≤ r) (hx : x ∈ Icc (r - 1) r) :
    (27 : ℝ) / 25 * gaussianPDFReal r 1 x ≤
      2 * kernelV (a * x) * (gaussianPDFReal r 1 x - gaussianPDFReal r 1 (-x)) := by
  have hr : 3 ≤ r := ha.trans hra
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hv := kernelV_lower_large (show 3 ≤ a * x by nlinarith [hx.1])
  have hg := gaussian_density_gap hr hx.1
  have h := mul_le_mul (show (36 : ℝ) / 25 ≤ 2 * kernelV (a * x) by linarith) hg
    (mul_nonneg (by norm_num) (gaussianPDFReal_nonneg r 1 x)) (by linarith)
  nlinarith

lemma gaussian_kernelV_lower_large {a r : ℝ} (ha : 3 ≤ a) (hra : a ≤ r) :
    (3 : ℝ) / 10 ≤ ∫ x, 2 * kernelV (a * x) ∂gaussianReal r 1 := by
  have hi := (gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2
  have ho (x : ℝ) : 2 * kernelV (a * -x) = -(2 * kernelV (a * x)) := by simp [kernelV_neg]
  rw [gaussian_odd_positive_half r 1 one_ne_zero _ hi ho]
  have hj := integrable_gaussian_odd_half r 1 one_ne_zero _ hi ho
  have hind := Integrable.indicator (s := Icc (r - 1) r)
    ((integrable_gaussianPDFReal r 1).integrableOn (s := Ioi 0)) measurableSet_Icc
  have hm := setIntegral_mono_on (hind.const_mul ((27 : ℝ) / 25)) hj
    measurableSet_Ioi (fun x hx => ?_)
  · rw [integral_const_mul, setIntegral_indicator measurableSet_Icc] at hm
    have hs : Icc (r - 1) r ⊆ Ioi (0 : ℝ) := by
      intro x hx
      have hr := ha.trans hra
      show 0 < x
      linarith [hx.1]
    rw [inter_eq_right.mpr hs] at hm
    have hmass := mul_le_mul_of_nonneg_left (gaussian_shifted_interval_mass r)
      (by norm_num : (0 : ℝ) ≤ 27 / 25)
    norm_num at hmass
    exact hmass.trans hm
  · by_cases hxI : x ∈ Icc (r - 1) r
    · rw [indicator_of_mem hxI]
      exact kernelV_interval_lower ha hra hxI
    · rw [indicator_of_notMem hxI, mul_zero]
      have hx0 : 0 < x := hx
      have ha0 : 0 < a := by linarith
      exact mul_nonneg (mul_nonneg (by norm_num) (kernelV_pos (mul_pos ha0 hx0)).le)
        (sub_nonneg.mpr (gaussian_density_reflection_le 1 (by linarith) hx0.le))

lemma large_kernelDerivative_lower {a r : ℝ} (ha : 3 ≤ a) (hra : a ≤ r) :
    (1 : ℝ) / 20 ≤ ∫ x, kernelDerivative a x ∂gaussianReal r 1 := by
  have hv := (gaussian_integrable_scale r a kernelV (integrable_kernelV_gaussian _ _)).const_mul 2
  have hw := (gaussian_integrable_scale r a kernelW (integrable_kernelW_gaussian _ _)).const_mul (a ^ 2)
  unfold kernelDerivative
  rw [integral_add hv hw, integral_const_mul (a ^ 2)]
  linarith [gaussian_kernelV_lower_large ha hra, gaussian_kernelW_lower_quarter ha hra]

lemma kernelDerivative_lower {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    min a 1 * min r 1 / 60 ≤ ∫ x, kernelDerivative a x ∂gaussianReal r 1 := by
  by_cases ha3 : a ≤ 3
  · exact bounded_kernelDerivative_lower ha.le ha3 hr.le
  by_cases hra : r ≤ a
  · exact inner_kernelDerivative_lower ha hr hra
  have hl := large_kernelDerivative_lower (le_of_not_ge ha3) (le_of_not_ge hra)
  have hm : min a 1 * min r 1 ≤ 1 := by
    have h := mul_le_mul (min_le_right a 1) (min_le_right r 1) (le_min hr.le zero_le_one) zero_le_one
    simpa using h
  linarith

end LongTails.Proofs.SymmetricReverseFisherTails
