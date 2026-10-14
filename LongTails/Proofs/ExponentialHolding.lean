import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LongTails.Proofs.ContinuizedQuasarEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

lemma integral_expMeasure_one (f : ℝ → ℝ) :
    (∫ t, f t ∂expMeasure 1) = ∫ t in Ioi 0, Real.exp (-t) * f t := by
  rw [expMeasure, gammaMeasure]
  change (∫ t, f t ∂volume.withDensity (fun t => ENNReal.ofReal (gammaPDFReal 1 1 t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal 1 1).ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  change (∫ t, (gammaPDF 1 1 t).toReal • f t) = _
  have hi (t : ℝ) : (gammaPDF 1 1 t).toReal • f t =
      (Ici 0).indicator (fun t => Real.exp (-t) * f t) t := by
    by_cases ht : 0 ≤ t
    · simp [gammaPDF, gammaPDFReal, ht, ENNReal.toReal_ofReal, Real.exp_nonneg]
    · simp [gammaPDF, gammaPDFReal, ht]
  simp_rw [hi]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

lemma weighted_integrable {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) * f t) (Ioi 0) := by
  apply ((integrableOn_exp_neg_Ioi 0).mul_const C).mono'
    ((Real.continuous_exp.comp continuous_neg).mul hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Real.exp (-t) * f t‖ ≤ Real.exp (-t) * C
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb t ht.le) (Real.exp_pos _).le

lemma weighted_tendsto_zero {f : ℝ → ℝ} {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ‖f t‖ ≤ C) :
    Tendsto (fun t => Real.exp (-t) * f t) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t => Real.exp (-t) * C)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
  · simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const C

lemma weighted_derivative_integral {B D : ℝ → ℝ} {CB CD : ℝ}
    (hB : Continuous B) (hD : Continuous D)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD) :
    (∫ t in Ioi 0, Real.exp (-t) * D t) -
      (∫ t in Ioi 0, Real.exp (-t) * B t) = -B 0 := by
  have hBi := weighted_integrable hB hb
  have hDi := weighted_integrable hD hd
  have hf (t : ℝ) : HasDerivAt (fun t => Real.exp (-t) * B t)
      (Real.exp (-t) * D t - Real.exp (-t) * B t) t := by
    convert (((hasDerivAt_id t).neg.exp).mul (hderiv t)) using 1
    · rfl
    · simp only [Pi.neg_apply, id_eq]
      ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hf t)
    (hDi.sub hBi) (weighted_tendsto_zero hb)
  rw [integral_sub hDi hBi] at h
  simpa using h

lemma holding_contraction {B D J : ℝ → ℝ} {CB CD CJ c b A : ℝ}
    (hc : 0 ≤ c) (hB : Continuous B) (hD : Continuous D) (hJ : Continuous J)
    (hderiv : ∀ t, HasDerivAt B (D t) t)
    (hb : ∀ t, 0 ≤ t → ‖B t‖ ≤ CB) (hd : ∀ t, 0 ≤ t → ‖D t‖ ≤ CD)
    (hj : ∀ t, 0 ≤ t → ‖J t‖ ≤ CJ)
    (hgen : ∀ t, 0 ≤ t → D t + J t - B t ≤ -c * B t + b * A)
    (hjump : ∀ t, 0 ≤ t → J t ≤ 4 * B t + b * A) :
    (∫ t, J t ∂expMeasure 1) ≤ 4 / (4 + c) * B 0 + b * A := by
  have hBi := weighted_integrable hB hb
  have hDi := weighted_integrable hD hd
  have hJi := weighted_integrable hJ hj
  have hAi := (integrableOn_exp_neg_Ioi 0).mul_const (b * A)
  have he := weighted_derivative_integral hB hD hderiv hb hd
  have hg := integral_mono_ae ((hDi.add hJi).sub hBi)
    ((hBi.const_mul (-c)).add hAi) (show
      (fun t => Real.exp (-t) * D t + Real.exp (-t) * J t - Real.exp (-t) * B t) ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t => -c * (Real.exp (-t) * B t) + Real.exp (-t) * (b * A)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have h := mul_le_mul_of_nonneg_left (hgen t ht.le) (Real.exp_pos (-t)).le
      nlinarith)
  have hj' := integral_mono_ae hJi ((hBi.const_mul 4).add hAi) (show
      (fun t => Real.exp (-t) * J t) ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t => 4 * (Real.exp (-t) * B t) + Real.exp (-t) * (b * A)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have h := mul_le_mul_of_nonneg_left (hjump t ht.le) (Real.exp_pos (-t)).le
      nlinarith)
  simp only [Pi.add_apply, Pi.sub_apply] at hg hj'
  rw [integral_sub (f := fun t => Real.exp (-t) * D t + Real.exp (-t) * J t)
      (hDi.add hJi) hBi, integral_add hDi hJi,
    integral_add (hBi.const_mul (-c)) hAi, integral_const_mul,
    integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] at hg
  rw [integral_add (hBi.const_mul 4) hAi, integral_const_mul,
    integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] at hj'
  rw [integral_expMeasure_one]
  exact resolvent_contraction hc (by linarith) hj'

end OracleTemplate.ContinuizedSimilarQuasar
