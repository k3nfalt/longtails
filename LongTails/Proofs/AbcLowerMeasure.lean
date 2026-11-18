import LongTails.Proofs.AbcHardCounting
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Proofs.AbcLowerMeasure

open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardExecution

noncomputable def stream : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => unif)

instance : IsProbabilityMeasure stream := by unfold stream; infer_instance

lemma stream_iid :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → ℝ) => ξ k) unif stream :=
  OracleTemplate.StochasticGeneralized.infinitePi_iid unif

lemma coinCount_eq_sum (qbar : ℝ) (ω : ℕ → ℝ) (N : ℕ) :
    (coinCount qbar ω N : ℝ) = ∑ t ∈ Finset.range N, Set.indicator {ξ : ℕ → ℝ | ξ t ≤ qbar}
      (fun _ => (1 : ℝ)) ω := by
  induction N with
  | zero => simp [coinCount]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [coinCount, Nat.cast_add, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> simp

lemma measurableSet_coord_le (t : ℕ) (qbar : ℝ) :
    MeasurableSet {ξ : ℕ → ℝ | ξ t ≤ qbar} :=
  measurableSet_le (measurable_pi_apply t) measurable_const

lemma coinCount_measurable (qbar : ℝ) (N : ℕ) :
    Measurable (fun ω : ℕ → ℝ => (coinCount qbar ω N : ℝ)) := by
  simp_rw [coinCount_eq_sum]
  exact Finset.measurable_sum _ (fun t _ => measurable_const.indicator (measurableSet_coord_le t qbar))

lemma stream_coord_le (t : ℕ) (qbar : ℝ) (h0 : 0 ≤ qbar) (h1 : qbar ≤ 1) :
    stream.real {ξ : ℕ → ℝ | ξ t ≤ qbar} = qbar := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => unif) t
  have hs : {ξ : ℕ → ℝ | ξ t ≤ qbar} = (fun ξ : ℕ → ℝ => ξ t) ⁻¹' {ω | ω ≤ qbar} := rfl
  rw [Measure.real, hs, ← Measure.map_apply (measurable_pi_apply t) (setOf_le_measurable qbar)]
  unfold stream
  rw [h, unif_le qbar h1, ENNReal.toReal_ofReal h0]

lemma coinCount_le (qbar : ℝ) (ω : ℕ → ℝ) (N : ℕ) : coinCount qbar ω N ≤ N := by
  induction N with
  | zero => simp [coinCount]
  | succ N ih => simp only [coinCount]; split_ifs <;> omega

lemma coinCount_integral (qbar : ℝ) (h0 : 0 ≤ qbar) (h1 : qbar ≤ 1) (N : ℕ) :
    ∫ ω, (coinCount qbar ω N : ℝ) ∂stream = N * qbar := by
  simp_rw [coinCount_eq_sum]
  rw [integral_finsetSum _ (fun t _ => (integrable_const _).indicator (measurableSet_coord_le t qbar))]
  simp_rw [integral_indicator (measurableSet_coord_le _ qbar), setIntegral_const, smul_eq_mul,
    mul_one, stream_coord_le _ qbar h0 h1]
  simp

lemma coinCount_tail (qbar : ℝ) (h0 : 0 ≤ qbar) (h1 : qbar ≤ 1) (N M : ℕ) :
    stream.real {ω | M + 1 ≤ coinCount qbar ω N} ≤ N * qbar / (M + 1) := by
  have hint : Integrable (fun ω => (coinCount qbar ω N : ℝ)) stream := by
    apply (integrable_const (N : ℝ)).mono' (coinCount_measurable qbar N).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast coinCount_le qbar ω N
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := stream)
    (f := fun ω => (coinCount qbar ω N : ℝ))
    (Filter.Eventually.of_forall (fun ω => by show (0 : ℝ) ≤ _; exact Nat.cast_nonneg _))
    hint ((M : ℝ) + 1)
  rw [coinCount_integral qbar h0 h1] at hm
  have he : {ω | ((M : ℝ) + 1) ≤ (coinCount qbar ω N : ℝ)} = {ω | M + 1 ≤ coinCount qbar ω N} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> exact_mod_cast h
  rw [he] at hm
  rw [le_div_iff₀ (by positivity)]
  linarith

end LongTails.Proofs.AbcLowerMeasure
