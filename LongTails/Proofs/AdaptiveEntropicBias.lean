import LongTails.Proofs.AdaptiveEntropicEvents
import LongTails.Proofs.AdaptiveEntropicQuantileProcess

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def cappedBiasScore (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (s : State q) (ω : Ω) : ℝ := by
  classical
  exact if cappedActive q μ σ A s then cappedExcess q A s (g (queryPoint q s) ω) / A else 0

lemma measurable_cappedBiasScore (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ A : ℝ) :
    Measurable (Function.uncurry (cappedBiasScore q g μ σ A)) := by
  apply Measurable.ite ((measurableSet_cappedActive q hμ σ A).preimage measurable_fst)
  · exact ((measurable_cappedExcess q A).comp
      (measurable_fst.prodMk (hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        measurable_snd)))).div_const A
  · exact measurable_const

lemma cappedBiasScore_unit (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 < A) (s : State q) (ω : Ω) :
    0 ≤ cappedBiasScore q g μ σ A s ω ∧ cappedBiasScore q g μ σ A s ω ≤ 1 := by
  unfold cappedBiasScore
  split_ifs with h
  · exact ⟨div_nonneg (cappedExcess_nonneg _ _ _ _) hA.le,
      (div_le_one hA).mpr (cappedExcess_le q hA.le s h.2.1 _)⟩
  · norm_num

lemma cappedBiasScore_le (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 < A) (s : State q) (ω : Ω) :
    cappedBiasScore q g μ σ A s ω ≤ cappedExcess q A s (g (queryPoint q s) ω) / A := by
  unfold cappedBiasScore
  split_ifs
  · rfl
  · exact div_nonneg (cappedExcess_nonneg _ _ _ _) hA.le

lemma accumulated_cappedBiasScore_le (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 < A) (N : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (firstScore (cappedBiasScore q g μ σ A)) N (initialState q) ξ ≤ trimCount q := by
  rw [StochasticGeneralized.accumulated_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range N, cappedExcess q A
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1 (primaryReply q g ξ j) / A := by
      apply Finset.sum_le_sum
      intro j hj
      let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j
      have hc : 0 < analysisCost q tr.1 := by unfold analysisCost; split_ifs <;> norm_num
      change firstScore (cappedBiasScore q g μ σ A) (analysisCost q tr.1) tr.1
        (fun i => tr.2 i) ≤ _
      simp only [firstScore, dite_eq_left hc]
      have he : g (queryPoint q tr.1) (tr.2 0) = primaryReply q g ξ j := by
        change g (queryPoint q tr.1) (tr.2 0) = g (queryPoint q tr.1) (ξ _)
        congr 1
        simpa only [Nat.add_zero] using StochasticGeneralized.blockTrace_tail
          (analysisCost q) (blockUpdate q g) (initialState q) ξ j 0
      simpa only [he] using cappedBiasScore_le q g μ σ hA tr.1 (tr.2 0)
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact (div_le_iff₀ hA).mpr (accumulated_cappedExcess_le q g A hA.le N ξ)

lemma cappedBias_compensator_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ : ℝ)
    {A : ℝ} (hA : 0 < A) (N : ℕ) (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 2 * (trimCount q : ℝ) + 4 * H < StochasticGeneralized.accumulated
        (analysisCost q) (blockUpdate q g)
        (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g μ σ A) n s b
          ∂Measure.pi (fun _ : Fin n => P)) N (initialState q) ξ} ≤
      ENNReal.ofReal (Real.exp (-H)) := by
  have h := AdaptiveEntropicConcentration.accumulated_inverse_tail P
    (analysisCost q) (blockUpdate q g) (firstScore (cappedBiasScore q g μ σ A))
    (measurable_analysisCost q) (measurable_blockUpdate q hg)
    (measurable_firstScore (measurable_cappedBiasScore q hg hμ σ A))
    (firstScore_unit (cappedBiasScore_unit q g μ σ hA)) N (initialState q) H
  apply le_trans (measure_mono ?_) h
  intro ξ hξ
  have hc := accumulated_cappedBiasScore_le q g μ σ hA N ξ
  change 2 * _ + 4 * H < _
  exact lt_of_le_of_lt (by linarith) hξ

end OracleTemplate.AdaptiveHeavyTailSimplex
