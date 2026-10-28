import LongTails.Proofs.GradientOnlyQuasarHolding
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

noncomputable section

def clockSum {k : ℕ} (samples : Fin k → ℝ) : ℝ := ∑ i, max 0 (samples i)

lemma clockSum_nonneg {k : ℕ} (samples : Fin k → ℝ) : 0 ≤ clockSum samples :=
  Finset.sum_nonneg (fun _ _ => le_max_left _ _)

lemma continuous_clockSum (k : ℕ) : Continuous (clockSum (k := k)) := by
  unfold clockSum
  fun_prop

lemma run_clock (q : Params) (g : q.E → q.E) (k : ℕ) (s : ℝ × q.E × q.E)
    (samples : Fin k → ℝ) : (run q g k s samples).1 = s.1 + clockSum samples := by
  induction k generalizing s with
  | zero => simp [run, ContinuizedSimilarQuasar.iterateSamples, clockSum]
  | succ k ih =>
      change (run q g k (advance q g s (samples 0)) (fun i => samples i.succ)).1 = _
      rw [ih]
      simp only [advance, jump, flow, clockSum, Fin.sum_univ_succ]
      ring

lemma exp_holding_integrable : Integrable (fun t : ℝ => Real.exp (-max 0 t))
    (RelativeQuasar.holdingLaw : Measure ℝ) := by
  apply (integrable_const (1 : ℝ)).mono'
    (show Continuous (fun t : ℝ => Real.exp (-max 0 t)) by fun_prop).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left _ _))

lemma integral_exp_holding : (∫ t : ℝ, Real.exp (-max 0 t)
    ∂(RelativeQuasar.holdingLaw : Measure ℝ)) = 1 / 2 := by
  change (∫ t : ℝ, Real.exp (-max 0 t) ∂expMeasure 1) = _
  rw [ContinuizedSimilarQuasar.integral_expMeasure_one]
  have he : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.exp (-max 0 t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp ((-2) * t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [max_eq_right (mem_Ioi.mp ht).le, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
  norm_num

lemma exp_clockSum_eq_prod {k : ℕ} (samples : Fin k → ℝ) :
    Real.exp (-clockSum samples) = ∏ i, Real.exp (-max 0 (samples i)) := by
  rw [clockSum, ← Finset.sum_neg_distrib, Real.exp_sum]

lemma exp_clockSum_integrable (k : ℕ) : Integrable (fun samples : Fin k → ℝ =>
    Real.exp (-clockSum samples)) (RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ)) := by
  simp only [exp_clockSum_eq_prod]
  exact Integrable.fintype_prod (fun _ : Fin k => exp_holding_integrable)

lemma integral_exp_clockSum (k : ℕ) : (∫ samples : Fin k → ℝ, Real.exp (-clockSum samples)
    ∂(RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ))) = (1 / 2 : ℝ) ^ k := by
  simp only [exp_clockSum_eq_prod]
  change (∫ samples : Fin k → ℝ, ∏ i, Real.exp (-max 0 (samples i))
    ∂Measure.pi (fun _ => (RelativeQuasar.holdingLaw : Measure ℝ))) = _
  have hh := integral_fintype_prod_eq_pow (ι := Fin k)
    (μ := (RelativeQuasar.holdingLaw : Measure ℝ)) (fun t : ℝ => Real.exp (-max 0 t))
  simpa only [integral_exp_holding, Fintype.card_fin] using hh

lemma clock_lower_tail (k : ℕ) (T : ℝ) :
    (RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ)) {samples | clockSum samples < T} ≤
      ENNReal.ofReal (Real.exp T * (1 / 2 : ℝ) ^ k) := by
  have hi := (exp_clockSum_integrable k).const_mul (Real.exp T)
  have hn : 0 ≤ᵐ[(RelativeQuasar.samplesLaw k : Measure (Fin k → ℝ))]
      (fun samples => Real.exp T * Real.exp (-clockSum samples)) :=
    Eventually.of_forall (fun _ => by positivity)
  have hh := hi.measure_le_integral hn (s := {samples | clockSum samples < T}) (by
    intro samples hs
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by change clockSum samples < T at hs; linarith))
  rw [integral_const_mul, integral_exp_clockSum] at hh
  exact hh

end

end OracleTemplate.GradientOnlyQuasar
