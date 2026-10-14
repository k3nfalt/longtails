import LongTails.Algorithms.RobustValue
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OracleTemplate.FiniteVariance

lemma average_deviation {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hX : MemLp X 2 p)
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (Measure.pi fun _ : Fin n => p)
      {ξ | a ≤ |(∑ i : Fin n, X (ξ i)) / n - ∫ ω, X ω ∂p|} ≤
      ENNReal.ofReal (variance X p / (n * a ^ 2)) := by
  let Q : Measure (Fin n → Ω) := Measure.pi fun _ => p
  have hcoord (i : Fin n) : MemLp (fun ξ : Fin n → Ω => X (ξ i)) 2 Q :=
    hX.comp_measurePreserving (measurePreserving_eval _ i)
  have hsum : MemLp (fun ξ : Fin n → Ω => ∑ i : Fin n, X (ξ i)) 2 Q :=
    memLp_finsetSum _ (fun i _ => hcoord i)
  have havg := hsum.const_mul (n : ℝ)⁻¹
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hint : (∫ ξ, (n : ℝ)⁻¹ * ∑ i : Fin n, X (ξ i) ∂Q) = ∫ ω, X ω ∂p := by
    rw [integral_const_mul, integral_finsetSum]
    · have hi (i : Fin n) : (∫ ξ, X (ξ i) ∂Q) = ∫ ω, X ω ∂p := by
        have hp := measurePreserving_eval (fun _ : Fin n => p) i
        have he := integral_map hp.measurable.aemeasurable
          (show AEStronglyMeasurable X (Q.map (fun ξ => ξ i)) from by
            rw [hp.map_eq]; exact hX.aestronglyMeasurable)
        rw [hp.map_eq] at he
        exact he.symm
      simp_rw [hi]
      simp [hn']
    · exact fun i _ => (hcoord i).integrable (by norm_num)
  have hv : variance (fun ξ : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i : Fin n, X (ξ i)) Q =
      variance X p / n := by
    rw [variance_const_mul]
    have he := variance_sum_pi (μ := fun _ : Fin n => p) (X := fun _ => X) (fun _ => hX)
    have hf : (∑ i : Fin n, fun ξ : Fin n → Ω => X (ξ i)) = (fun ξ => ∑ i : Fin n, X (ξ i)) := by
      ext ξ
      simp
    rw [hf] at he
    rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hb := meas_ge_le_variance_div_sq havg ha
  rw [hint, hv] at hb
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev] using hb

lemma average_deviation_of_centered {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {X : Ω → ℝ} (hX : Measurable X)
    {b v : ℝ} (hmean : (∫ ω, X ω ∂p) = b)
    (hi : Integrable (fun ω => (X ω - b)^2) p)
    (hv : (∫ ω, (X ω - b)^2 ∂p) ≤ v)
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (Measure.pi fun _ : Fin n => p)
      {ξ | a ≤ |(∑ i : Fin n, X (ξ i)) / n - b|} ≤
      ENNReal.ofReal (v / (n * a ^ 2)) := by
  have hm : MemLp (fun ω => X ω - b) 2 p :=
    (memLp_two_iff_integrable_sq (hX.sub_const b).aestronglyMeasurable).mpr hi
  have hm' : MemLp X 2 p := by
    convert hm.add (memLp_const b) using 1
    ext ω
    simp
  have hvar : variance X p ≤ v := by
    rwa [variance_eq_integral hX.aemeasurable, hmean]
  have h := average_deviation hm' hn ha
  rw [hmean] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (by positivity)))

lemma median3_mem {a b c l u : ℝ}
    (h : (a ∈ Set.Icc l u ∧ b ∈ Set.Icc l u) ∨
      (b ∈ Set.Icc l u ∧ c ∈ Set.Icc l u) ∨
      (c ∈ Set.Icc l u ∧ a ∈ Set.Icc l u)) :
    median3 a b c ∈ Set.Icc l u := by
  simp only [median3, Set.mem_Icc, le_max_iff, le_min_iff, max_le_iff, min_le_iff] at *
  tauto

lemma median3_bad {a b c m r : ℝ}
    (h : r < |median3 a b c - m|) :
    (r < |a - m| ∧ r < |b - m|) ∨
    (r < |b - m| ∧ r < |c - m|) ∨
    (r < |c - m| ∧ r < |a - m|) := by
  by_contra hb
  have hgood : (|a - m| ≤ r ∧ |b - m| ≤ r) ∨
      (|b - m| ≤ r ∧ |c - m| ≤ r) ∨
      (|c - m| ≤ r ∧ |a - m| ≤ r) := by
    by_cases ha : r < |a - m| <;>
      by_cases hb' : r < |b - m| <;>
      by_cases hc : r < |c - m| <;> simp_all only [not_lt] <;> tauto
  have hi (x : ℝ) : |x - m| ≤ r ↔ x ∈ Set.Icc (m-r) (m+r) := by
    rw [abs_le, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [hi] at hgood
  have hm := median3_mem hgood
  exact (not_le.mpr h) ((hi _).mpr hm)

lemma median3_deviation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y Z : Ω → ℝ} (hXY : IndepFun X Y P) (hYZ : IndepFun Y Z P)
    (hZX : IndepFun Z X P) {m r : ℝ} {q : ℝ≥0∞}
    (hX : P {ω | r < |X ω - m|} ≤ q)
    (hY : P {ω | r < |Y ω - m|} ≤ q)
    (hZ : P {ω | r < |Z ω - m|} ≤ q) :
    P {ω | r < |median3 (X ω) (Y ω) (Z ω) - m|} ≤ 3 * q ^ 2 := by
  let B : Set ℝ := {x | r < |x - m|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_id.sub_const m))
  have hs : {ω | r < |median3 (X ω) (Y ω) (Z ω) - m|} ⊆
      (X ⁻¹' B ∩ Y ⁻¹' B) ∪ ((Y ⁻¹' B ∩ Z ⁻¹' B) ∪ (Z ⁻¹' B ∩ X ⁻¹' B)) := by
    intro ω hω
    exact median3_bad hω
  calc
    _ ≤ P ((X ⁻¹' B ∩ Y ⁻¹' B) ∪ ((Y ⁻¹' B ∩ Z ⁻¹' B) ∪ (Z ⁻¹' B ∩ X ⁻¹' B))) := measure_mono hs
    _ ≤ P (X ⁻¹' B ∩ Y ⁻¹' B) + (P (Y ⁻¹' B ∩ Z ⁻¹' B) + P (Z ⁻¹' B ∩ X ⁻¹' B)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ = P (X ⁻¹' B) * P (Y ⁻¹' B) +
        (P (Y ⁻¹' B) * P (Z ⁻¹' B) + P (Z ⁻¹' B) * P (X ⁻¹' B)) := by
      rw [hXY.measure_inter_preimage_eq_mul B B hB hB,
        hYZ.measure_inter_preimage_eq_mul B B hB hB,
        hZX.measure_inter_preimage_eq_mul B B hB hB]
    _ ≤ q*q + (q*q + q*q) := add_le_add (mul_le_mul' hX hY)
      (add_le_add (mul_le_mul' hY hZ) (mul_le_mul' hZ hX))
    _ = 3 * q ^ 2 := by ring

end OracleTemplate.FiniteVariance
