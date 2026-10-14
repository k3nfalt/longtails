import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.FiniteVariance

lemma expected_accuracy_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Ω → ℝ} (hg : Measurable g)
    {a M δ : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hbound : ∀ ω, 0 ≤ g ω ∧ g ω ≤ M)
    (htail : P {ω | a < g ω} ≤ ENNReal.ofReal δ) :
    Integrable g P ∧ (∫ ω, g ω ∂P) ≤ a + M*δ := by
  have hi : Integrable g P := (integrable_const M).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1] using (hbound ω).2))
  let s := {ω | a < g ω}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hg
  have hI : Integrable (s.indicator (fun _ : Ω => M)) P := (integrable_const M).indicator hs
  have hp (ω : Ω) : g ω ≤ a + s.indicator (fun _ : Ω => M) ω := by
    by_cases h : ω ∈ s
    · simp only [Set.indicator_of_mem h]
      linarith [(hbound ω).2]
    · have hh : g ω ≤ a := le_of_not_gt h
      simpa only [Set.indicator_of_notMem h, add_zero] using hh
  have h := integral_mono hi ((integrable_const a).add hI) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const a) hI, integral_const, integral_indicator_const M hs] at h
  simp only [probReal_univ, smul_eq_mul] at h
  have hm : P.real s ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ htail
  refine ⟨hi, h.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hm hM]

end OracleTemplate.FiniteVariance
