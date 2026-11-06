import LongTails.Proofs.RelativeQuasarHolding
import LongTails.Proofs.GradientOnlyQuasarProbability

open MeasureTheory ProbabilityTheory Set Filter

namespace OracleTemplate.StochasticQuasar

lemma measurable_holding_nonincrease {B D J : ℝ → ℝ} {CB CD CJ : ℝ}
    (hB : Continuous B) (hD : Continuous D) (hJ : Measurable J)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ 0) :
    (∫ t, J t ∂expMeasure 1) ≤ B 0 := by
  have hBi := ContinuizedSimilarQuasar.weighted_integrable hB hb
  have hDi := ContinuizedSimilarQuasar.weighted_integrable hD hd
  have hJi := ContinuizedSimilarQuasar.measurable_weighted_integrable hJ hj
  have he := ContinuizedSimilarQuasar.weighted_derivative_integral hB hD hderiv hb hd
  have hh : (∫ t in Ioi 0,
      Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t ≤ 0
    have hg := mul_le_mul_of_nonneg_left (hgen t ht.le) (Real.exp_pos (-t)).le
    nlinarith
  rw [integral_sub (f := fun t => Real.exp (-t) * D t + Real.exp (-t) * J t)
    (hDi.add hJi) hBi, integral_add hDi hJi] at hh
  rw [ContinuizedSimilarQuasar.integral_expMeasure_one]
  linarith

lemma compensated_holding_nonincrease {B D J R r : ℝ → ℝ} {CB CD CJ Cr : ℝ}
    (hB : Continuous B) (hD : Continuous D) (hJ : Measurable J)
    (hR : Continuous R) (hr : Continuous r)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hRderiv : ∀ t, HasDerivAt R (r t) t)
    (hRnonneg : ∀ t, 0 ≤ t → 0 ≤ R t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ) (hrb : ∀ t, 0 ≤ t → ‖r t‖ ≤ Cr)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ r t * B t) :
    (∫ t, Real.exp (-R t) * J t ∂expMeasure 1) ≤ Real.exp (-R 0) * B 0 := by
  have hc : Continuous (fun t => Real.exp (-R t)) := Real.continuous_exp.comp hR.neg
  have he (t : ℝ) (ht : 0 ≤ t) : ‖Real.exp (-R t)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hRnonneg t ht))
  have hder (t : ℝ) : HasDerivAt (fun t => Real.exp (-R t) * B t)
      (Real.exp (-R t) * (D t - r t * B t)) t := by
    convert ((hRderiv t).neg.exp).mul (hderiv t) using 1
    simp only [Pi.neg_apply]
    ring
  apply measurable_holding_nonincrease (hc.mul hB) (hc.mul (hD.sub (hr.mul hB)))
    (hc.measurable.mul hJ) hder
    (CB := CB) (CD := CD + Cr * CB) (CJ := CJ)
  · intro t ht
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (he t ht) (norm_nonneg _)).trans (by simpa using hb t ht)
  · intro t ht
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [norm_mul]
    calc
      ‖Real.exp (-R t)‖ * ‖D t - r t * B t‖ ≤ ‖D t - r t * B t‖ := by
        simpa using mul_le_mul_of_nonneg_right (he t ht) (norm_nonneg (D t - r t * B t))
      _ ≤ ‖D t‖ + ‖r t * B t‖ := norm_sub_le _ _
      _ ≤ CD + Cr * CB := by
        rw [norm_mul]
        exact add_le_add (hd t ht) (mul_le_mul (hrb t ht) (hb t ht)
          (norm_nonneg _) ((norm_nonneg (r t)).trans (hrb t ht)))
  · intro t ht
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (he t ht) (norm_nonneg _)).trans (by simpa using hj t ht)
  · intro t ht
    have hg := mul_le_mul_of_nonneg_left (hgen t ht) (Real.exp_pos (-R t)).le
    simp only [Pi.mul_apply, Pi.sub_apply]
    nlinarith

lemma integral_positive_exp_holding : (∫ t : ℝ, Real.exp (max 0 t / 2)
    ∂(RelativeQuasar.holdingLaw : Measure ℝ)) = 2 := by
  change (∫ t : ℝ, Real.exp (max 0 t / 2) ∂expMeasure 1) = _
  rw [ContinuizedSimilarQuasar.integral_expMeasure_one]
  have he : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.exp (max 0 t / 2)) =
      ∫ t in Ioi (0 : ℝ), Real.exp ((-1 / 2) * t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [max_eq_right (mem_Ioi.mp ht).le, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0)]
  norm_num

lemma positive_exp_holding_integrable : Integrable (fun t : ℝ => Real.exp (max 0 t / 2))
    (RelativeQuasar.holdingLaw : Measure ℝ) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_positive_exp_holding] at hz
  norm_num at hz

lemma positive_exp_clock_eq_prod {k : ℕ} (samples : Fin k → ℝ) :
    Real.exp (GradientOnlyQuasar.clockSum samples / 2) =
      ∏ i, Real.exp (max 0 (samples i) / 2) := by
  rw [GradientOnlyQuasar.clockSum, Finset.sum_div, Real.exp_sum]

lemma positive_exp_clock_integrable (k : ℕ) : Integrable (fun samples : Fin k → ℝ =>
    Real.exp (GradientOnlyQuasar.clockSum samples / 2))
    (RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ)) := by
  simp only [positive_exp_clock_eq_prod]
  exact Integrable.fintype_prod (fun _ : Fin k => positive_exp_holding_integrable)

lemma integral_positive_exp_clock (k : ℕ) : (∫ samples : Fin k → ℝ,
    Real.exp (GradientOnlyQuasar.clockSum samples / 2)
    ∂(RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ))) = (2 : ℝ) ^ k := by
  simp only [positive_exp_clock_eq_prod]
  change (∫ samples : Fin k → ℝ, ∏ i, Real.exp (max 0 (samples i) / 2)
    ∂Measure.pi (fun _ => (RelativeQuasar.holdingLaw : Measure ℝ))) = _
  have hh := integral_fintype_prod_eq_pow (ι := Fin k)
    (μ := (RelativeQuasar.holdingLaw : Measure ℝ)) (fun t : ℝ => Real.exp (max 0 t / 2))
  simpa only [integral_positive_exp_holding, Fintype.card_fin] using hh

lemma clock_upper_tail (k : ℕ) (T : ℝ) :
    (RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ))
      {samples | T < GradientOnlyQuasar.clockSum samples} ≤
      ENNReal.ofReal (Real.exp (-T / 2) * (2 : ℝ) ^ k) := by
  have hi := (positive_exp_clock_integrable k).const_mul (Real.exp (-T / 2))
  have hn : 0 ≤ᵐ[(RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ))]
      (fun samples => Real.exp (-T / 2) * Real.exp (GradientOnlyQuasar.clockSum samples / 2)) :=
    Eventually.of_forall (fun _ => by positivity)
  have hh := hi.measure_le_integral hn
    (s := {samples | T < GradientOnlyQuasar.clockSum samples}) (by
      intro samples hs
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by change T < GradientOnlyQuasar.clockSum samples at hs; linarith))
  rw [integral_const_mul, integral_positive_exp_clock] at hh
  exact hh

end OracleTemplate.StochasticQuasar
