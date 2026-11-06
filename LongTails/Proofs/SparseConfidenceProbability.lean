import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseConfidenceProbability

lemma bounded_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hb : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ |∑ i, (X i ω - ∫ z, X i z ∂P)|} ≤
      2 * Real.exp (-2 * t ^ 2 / n) := by
  let Y := fun i ω => X i ω - ∫ z, X i z ∂P
  have hY : iIndepFun Y P := hind.comp (fun i z => z - ∫ ω, X i ω ∂P)
    (fun _ => measurable_id.sub_const _)
  have hsg (i : Fin n) : HasSubgaussianMGF (Y i) (1 / 4) P := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (hm i).aemeasurable
      (Filter.Eventually.of_forall (hb i))
    norm_num only [sub_zero, nnnorm_one, one_div, inv_pow, one_pow] at h
    convert h using 1
  have hs : HasSubgaussianMGF (fun ω => ∑ i, Y i ω) ((n : NNReal) / 4) P := by
    have h := HasSubgaussianMGF.sum_of_iIndepFun hY
      (s := Finset.univ) (fun i _ => hsg i)
    simpa [div_eq_mul_inv] using h
  have hu := hs.measure_ge_le ht
  have hl := hs.neg.measure_ge_le ht
  have hsub : {ω | t ≤ |∑ i, Y i ω|} ⊆
      {ω | t ≤ ∑ i, Y i ω} ∪ {ω | t ≤ -(∑ i, Y i ω)} := by
    intro ω hω
    change t ≤ |∑ i, Y i ω| at hω
    change t ≤ ∑ i, Y i ω ∨ t ≤ -(∑ i, Y i ω)
    exact le_abs.mp hω
  have hprob := (measureReal_mono (μ := P) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hu hl))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp : -t ^ 2 / (2 * ((n : NNReal) / 4 : NNReal)) = -2 * t ^ 2 / (n : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
    field_simp
    ring
  simpa only [Pi.neg_apply, hexp, ← two_mul] using hprob

lemma bounded_mean_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hb : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (m r : ℝ) (hmean : ∀ i, (∫ z, X i z ∂P) = m) (hr : 0 ≤ r) :
    P.real {ω | r < |(∑ i, X i ω) / (n : ℝ) - m|} ≤
      2 * Real.exp (-2 * n * r ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hid (ω : Ω) : ∑ i, (X i ω - ∫ z, X i z ∂P) =
      (n : ℝ) * ((∑ i, X i ω) / (n : ℝ) - m) := by
    simp_rw [hmean, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsub : {ω | r < |(∑ i, X i ω) / (n : ℝ) - m|} ⊆
      {ω | (n : ℝ) * r ≤ |∑ i, (X i ω - ∫ z, X i z ∂P)|} := by
    intro ω hω
    change r < |(∑ i, X i ω) / (n : ℝ) - m| at hω
    change (n : ℝ) * r ≤ |∑ i, (X i ω - ∫ z, X i z ∂P)|
    rw [hid ω, abs_mul, abs_of_nonneg hnpos.le]
    exact mul_le_mul_of_nonneg_left hω.le hnpos.le
  have h := (measureReal_mono (μ := P) hsub).trans
    (bounded_sum_abs_tail P hn X hm hind hb ((n : ℝ) * r) (mul_nonneg hnpos.le hr))
  have he : -2 * ((n : ℝ) * r) ^ 2 / (n : ℝ) = -2 * n * r ^ 2 := by
    field_simp
  simpa only [he] using h

end LongTails.Proofs.SparseConfidenceProbability
