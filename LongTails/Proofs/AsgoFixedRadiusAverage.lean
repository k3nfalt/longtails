import LongTails.Setups.AsgoFixedRadius
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory OracleTemplate.Muon

namespace OracleTemplate.AsgoFixedRadius

lemma average_measurable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (T : ℕ) (x : ℕ → Ω → Mat m n) (hx : ∀ t < T, Measurable (x t)) :
    Measurable (fun ω => (1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) := by
  exact (Finset.measurable_fun_sum (Finset.range T)
    (fun t ht => hx t (Finset.mem_range.mp ht))).const_smul (1 / (T : ℝ))

lemma average_gap_integrable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (T : ℕ) (hT : 1 ≤ T)
    (f : Mat m n → ℝ) (hf : Continuous f) (hc : ConvexOn ℝ Set.univ f)
    (Wstar : Mat m n) (hmin : ∀ X, f Wstar ≤ f X)
    (x : ℕ → Ω → Mat m n) (hx : ∀ t < T, Measurable (x t))
    (hi : ∀ t < T, Integrable (fun ω => f (x t ω) - f Wstar) P.toMeasure) :
    Integrable (fun ω => f ((1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) -
      f Wstar) P.toMeasure := by
  have hT0 : (T : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : T ≠ 0)
  have ha : 0 ≤ 1 / (T : ℝ) := by positivity
  have hweights : (∑ t ∈ Finset.range T, (1 / (T : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_one_div_cancel hT0
  have hpoint (ω : Ω) :
      f ((1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) - f Wstar ≤
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar) := by
    have hj := hc.map_sum_le (t := Finset.range T)
      (w := fun _ => 1 / (T : ℝ)) (p := fun t => x t ω)
      (fun _ _ => ha) hweights (fun _ _ => Set.mem_univ _)
    rw [← Finset.smul_sum] at hj
    simp only [smul_eq_mul, ← Finset.mul_sum] at hj
    have he :
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar) =
          (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, f (x t ω) - f Wstar := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_sub, ← mul_assoc, one_div_mul_cancel hT0, one_mul]
    rw [he]
    exact sub_le_sub_right hj _
  have hupper : Integrable
      (fun ω => (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar))
      P.toMeasure :=
    (integrable_finsetSum (Finset.range T)
      (fun t ht => hi t (Finset.mem_range.mp ht))).const_mul _
  apply hupper.mono'
    ((hf.measurable.comp (average_measurable T x hx)).sub measurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    change ‖f ((1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) - f Wstar‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin _))]
    exact hpoint ω)

lemma average_jensen {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (T : ℕ) (hT : 1 ≤ T)
    (f : Mat m n → ℝ) (hf : Continuous f) (hc : ConvexOn ℝ Set.univ f)
    (Wstar : Mat m n) (hmin : ∀ X, f Wstar ≤ f X)
    (x : ℕ → Ω → Mat m n) (hx : ∀ t < T, Measurable (x t))
    (hi : ∀ t < T, Integrable (fun ω => f (x t ω) - f Wstar) P.toMeasure) :
    (∫ ω, f ((1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) - f Wstar ∂P.toMeasure) ≤
      (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∫ ω, f (x t ω) - f Wstar ∂P.toMeasure := by
  have hT0 : (T : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : T ≠ 0)
  have ha : 0 ≤ 1 / (T : ℝ) := by positivity
  have hweights : (∑ t ∈ Finset.range T, (1 / (T : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_one_div_cancel hT0
  have hpoint (ω : Ω) :
      f ((1 / (T : ℝ)) • ∑ t ∈ Finset.range T, x t ω) - f Wstar ≤
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar) := by
    have hj := hc.map_sum_le (t := Finset.range T)
      (w := fun _ => 1 / (T : ℝ)) (p := fun t => x t ω)
      (fun _ _ => ha) hweights (fun _ _ => Set.mem_univ _)
    rw [← Finset.smul_sum] at hj
    simp only [smul_eq_mul, ← Finset.mul_sum] at hj
    have he :
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar) =
          (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, f (x t ω) - f Wstar := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_sub, ← mul_assoc, one_div_mul_cancel hT0, one_mul]
    rw [he]
    exact sub_le_sub_right hj _
  have hupper : Integrable
      (fun ω => (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (x t ω) - f Wstar))
      P.toMeasure :=
    (integrable_finsetSum (Finset.range T)
      (fun t ht => hi t (Finset.mem_range.mp ht))).const_mul _
  have hlow := average_gap_integrable P T hT f hf hc Wstar hmin x hx hi
  have hh := integral_mono hlow hupper hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun t ht => hi t (Finset.mem_range.mp ht))] at hh
  exact hh

end OracleTemplate.AsgoFixedRadius
