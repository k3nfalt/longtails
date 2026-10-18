import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Group.Integral

namespace LongTails.Proofs.CharacteristicLogEstimator

open MeasureTheory

lemma abs_sin_sub_self_le (u : ℝ) : |Real.sin u - u| ≤ u ^ 2 / 2 := by
  have ha := abs_nonneg u
  have hs : |u| ^ 2 = u ^ 2 := sq_abs u
  by_cases h : |u| ≤ 3
  · have hb := Real.abs_sub_sin_le u
    rw [abs_sub_comm] at hb
    nlinarith [mul_nonneg (sq_nonneg |u|) (sub_nonneg.mpr h)]
  · have hb : |Real.sin u - u| ≤ 1 + |u| :=
      (abs_sub _ _).trans (add_le_add (Real.abs_sin_le_one u) (le_refl _))
    have hu : 3 ≤ |u| := (lt_of_not_ge h).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)]

lemma integrable_sin_scale (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun z : ℝ => Real.sin (t * z)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t * z)

lemma symmetric_sin_integral {S : Measure ℝ}
    (hS : S.map (fun z : ℝ => -z) = S) (t : ℝ) :
    (∫ z : ℝ, Real.sin (t * z) ∂S) = 0 := by
  have h := integral_map (μ := S) (φ := fun z : ℝ => -z)
    measurable_neg.aemeasurable
    (f := fun z : ℝ => Real.sin (t * z)) (by fun_prop)
  rw [hS] at h
  simp only [mul_neg, Real.sin_neg, integral_neg] at h
  linarith

lemma centered_sin_integral_bound {A : Measure ℝ} [IsFiniteMeasure A] {M : ℝ}
    (hi : Integrable (fun z : ℝ => z) A) (hc : (∫ z : ℝ, z ∂A) = 0)
    (hi2 : Integrable (fun z : ℝ => z ^ 2) A) (hM : (∫ z : ℝ, z ^ 2 ∂A) ≤ M)
    (t : ℝ) : |∫ z : ℝ, Real.sin (t * z) ∂A| ≤ t ^ 2 * M / 2 := by
  have h := norm_integral_le_of_norm_le (hi2.const_mul (t ^ 2 / 2))
    (f := fun z : ℝ => Real.sin (t * z) - t * z)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      convert abs_sin_sub_self_le (t * z) using 1
      ring)
  rw [integral_sub (integrable_sin_scale A t) (hi.const_mul t),
    integral_const_mul, hc, mul_zero, sub_zero, Real.norm_eq_abs,
    integral_const_mul] at h
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ t ^ 2 / 2)
  nlinarith

lemma mixture_sin_integral_bound {μ S A : Measure ℝ} [IsFiniteMeasure μ] {M : ℝ}
    (hμ : μ = S + A) (hS : S.map (fun z : ℝ => -z) = S)
    (hi : Integrable (fun z : ℝ => z) A) (hc : (∫ z : ℝ, z ∂A) = 0)
    (hi2 : Integrable (fun z : ℝ => z ^ 2) A) (hM : (∫ z : ℝ, z ^ 2 ∂A) ≤ M)
    (t : ℝ) : |∫ z : ℝ, Real.sin (t * z) ∂μ| ≤ t ^ 2 * M / 2 := by
  have hSle : S ≤ μ := by rw [hμ]; exact Measure.le_add_right le_rfl
  have hAle : A ≤ μ := by rw [hμ, add_comm]; exact Measure.le_add_right le_rfl
  let : IsFiniteMeasure S := isFiniteMeasure_of_le μ hSle
  let : IsFiniteMeasure A := isFiniteMeasure_of_le μ hAle
  rw [hμ, integral_add_measure (integrable_sin_scale S t) (integrable_sin_scale A t),
    symmetric_sin_integral hS t, zero_add]
  exact centered_sin_integral_bound hi hc hi2 hM t

lemma phase_increment_norm_le_two (u : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖Complex.exp (Complex.I * (u : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num

lemma integrable_phase_square (μ : Measure ℝ) [IsFiniteMeasure μ] (t g : ℝ) :
    Integrable (fun z : ℝ => ‖Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1‖ ^ 2) μ := by
  apply Integrable.of_bound (by fun_prop) 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := phase_increment_norm_le_two (t * (g + z))
  have hn := norm_nonneg (Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1)
  nlinarith

lemma phase_square_quantile_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {t g r : ℝ} (ht : 0 ≤ t) (htr : t * (|g| + r) ≤ 1 / 4)
    (hq : μ {z | r < |z|} ≤ 1 / 64) :
    (∫ z : ℝ, ‖Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1‖ ^ 2 ∂μ) ≤
      1 / 8 := by
  let B := {z : ℝ | r < |z|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const continuous_abs.measurable
  have hbi : Integrable (B.indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hbound (z : ℝ) :
      ‖Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1‖ ^ 2 ≤
        1 / 16 + 4 * B.indicator (fun _ : ℝ => (1 : ℝ)) z := by
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      have h := phase_increment_norm_le_two (t * (g + z))
      have hn := norm_nonneg (Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1)
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      have hzr : |z| ≤ r := le_of_not_gt hz
      have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * (g + z))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht] at he
      have ha := mul_le_mul_of_nonneg_left ((abs_add_le g z).trans
        (add_le_add (le_refl |g|) hzr)) ht
      have hn := norm_nonneg (Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) - 1)
      nlinarith
  have hm := integral_mono (integrable_phase_square μ t g)
    ((integrable_const (1 / 16 : ℝ)).add (hbi.const_mul 4)) hbound
  simp only [Pi.add_apply] at hm
  have hind : (∫ z, B.indicator (fun _ : ℝ => (1 : ℝ)) z ∂μ) = μ.real B := by
    rw [integral_indicator hB]
    simp
  rw [integral_add (integrable_const (1 / 16 : ℝ)) (hbi.const_mul 4),
    integral_const_mul, hind] at hm
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
  have hqr : μ.real B ≤ 1 / 64 := by
    have h := ENNReal.toReal_mono (by norm_num : (1 / 64 : ENNReal) ≠ ⊤) hq
    simpa [Measure.real, B] using h
  linarith

lemma logTaylor_neg_eq (n : ℕ) (z : ℂ) :
    Complex.logTaylor n (-z) = -∑ k ∈ Finset.range n, z ^ k / k := by
  simp only [Complex.logTaylor, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_pow, pow_succ]
  ring_nf
  rw [mul_comm k 2, pow_mul]
  norm_num

lemma abs_log_im_le {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    |(Complex.log z).im| ≤ 2 * |z.im| := by
  have hr : 0 < z.re := by linarith
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  have he : Real.arctan (z.im / z.re) = Complex.arg z := by
    rw [← Complex.tan_arg]
    exact Real.arctan_tan (abs_lt.mp ha).1 (abs_lt.mp ha).2
  rw [Complex.log_im, ← he]
  calc
    _ ≤ |z.im / z.re| := Real.abs_arctan_le_abs
    _ = |z.im| / z.re := by rw [abs_div, abs_of_pos hr]
    _ ≤ 2 * |z.im| := by
      apply (div_le_iff₀ hr).mpr
      nlinarith [abs_nonneg z.im]

lemma log_rotate {z : ℂ} (hz : 0 < z.re) {u : ℝ} (hu : |u| ≤ 1 / 4) :
    Complex.log (Complex.exp (Complex.I * (u : ℂ)) * z) =
      Complex.I * (u : ℂ) + Complex.log z := by
  have hu' := abs_le.mp hu
  have hp := Real.two_le_pi
  have he : Complex.log (Complex.exp (Complex.I * (u : ℂ))) = Complex.I * (u : ℂ) := by
    apply Complex.log_exp <;> simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] <;> linarith
  have hae : Complex.arg (Complex.exp (Complex.I * (u : ℂ))) = u := by
    simpa only [Complex.log_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] using
      congrArg Complex.im he
  have haz := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [Complex.log_mul (Complex.exp_ne_zero _) hz0]
  · rw [he]
  · rw [hae]
    constructor <;> linarith

lemma log_series_remainder (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 - z) + ∑ k ∈ Finset.range (n + 1), z ^ k / k‖ ≤
      ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have h := Complex.norm_log_sub_logTaylor_le n (z := -z) (by simpa using hz)
  simpa only [norm_neg, logTaylor_neg_eq, sub_neg_eq_add, ← sub_eq_add_neg] using h

lemma mean_norm_le_half_of_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℂ}
    (hi : Integrable U P) (hi2 : Integrable (fun ω => ‖U ω‖ ^ 2) P)
    (hq : (∫ ω, ‖U ω‖ ^ 2 ∂P) ≤ 1 / 8) : ‖∫ ω, U ω ∂P‖ ≤ 1 / 2 := by
  have h := integral_mono hi.norm (hi2.add (integrable_const (1 / 4 : ℝ)))
    (fun ω => by dsimp; nlinarith [sq_nonneg (‖U ω‖ - 1 / 2)])
  simp only [Pi.add_apply] at h
  rw [integral_add hi2 (integrable_const (1 / 4 : ℝ))] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hn := norm_integral_le_integral_norm (f := U) (μ := P)
  linarith

lemma integrable_phase (μ : Measure ℝ) [IsFiniteMeasure μ] (t g : ℝ) :
    Integrable (fun z : ℝ => Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ))) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall fun z => (Complex.norm_exp_I_mul_ofReal _).le

lemma phase_mean_close {μ : Measure ℝ} [IsProbabilityMeasure μ] {t g r : ℝ}
    (ht : 0 ≤ t) (htr : t * (|g| + r) ≤ 1 / 4)
    (hq : μ {z | r < |z|} ≤ 1 / 64) :
    ‖(∫ z : ℝ, Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) ∂μ) - 1‖ ≤ 1 / 2 := by
  have h := mean_norm_le_half_of_square
    ((integrable_phase μ t g).sub (integrable_const 1)) (integrable_phase_square μ t g)
    (phase_square_quantile_bound ht htr hq)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_phase μ t g) (integrable_const 1)] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

lemma log_series_remainder_half (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z) + ∑ k ∈ Finset.range (n + 1), z ^ k / k‖ ≤
      (1 / 2 : ℝ) ^ n := by
  have hn : (1 : ℝ) ≤ n + 1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hd : 0 < 1 - ‖z‖ := by linarith
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    linarith
  calc
    _ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) :=
      log_series_remainder n (by linarith)
    _ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ := div_le_self (by positivity) hn
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * 2 :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _) hi (by positivity) (by positivity)
    _ = _ := by rw [pow_succ]; ring

lemma phase_log_bias {μ : Measure ℝ} [IsProbabilityMeasure μ] {t g r M : ℝ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) (htr : t * (|g| + r) ≤ 1 / 4)
    (hq : μ {z | r < |z|} ≤ 1 / 64)
    (hs : |∫ z, Real.sin (t * z) ∂μ| ≤ t ^ 2 * M / 2) :
    |(Complex.log (∫ z : ℝ,
      Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) ∂μ)).im - t * g| ≤ t ^ 2 * M := by
  let c := ∫ z : ℝ, Complex.exp (Complex.I * ((t * z : ℝ) : ℂ)) ∂μ
  have hc : ‖c - 1‖ ≤ 1 / 2 := by
    simpa [c] using phase_mean_close (g := 0) ht
      (by simpa using (show t * r ≤ 1 / 4 by nlinarith [mul_nonneg ht (abs_nonneg g)])) hq
  have hre : 1 / 2 ≤ c.re := by
    have h := Complex.abs_re_le_norm (c - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    have hl := (abs_le.mp (h.trans hc)).1
    linarith
  have him : c.im = ∫ z, Real.sin (t * z) ∂μ := by
    have h := integral_im (integrable_phase μ t 0)
    simpa only [c, zero_add, RCLike.im_eq_complex_im, mul_comm Complex.I,
      Complex.exp_ofReal_mul_I_im] using h.symm
  have hfactor : (∫ z : ℝ,
      Complex.exp (Complex.I * ((t * (g + z) : ℝ) : ℂ)) ∂μ) =
        Complex.exp (Complex.I * ((t * g : ℝ) : ℂ)) * c := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, log_rotate (by linarith : 0 < c.re)
    (show |t * g| ≤ 1 / 4 by rw [abs_mul, abs_of_nonneg ht]; nlinarith [mul_nonneg ht hr])]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, add_sub_cancel_left]
  have hb := abs_log_im_le hre
  rw [him] at hb
  linarith

end LongTails.Proofs.CharacteristicLogEstimator
