import LongTails.Proofs.AdaptiveEntropicProcess
import LongTails.Proofs.AdaptiveEntropicExecution

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def weightedInnovation (q : Public) (s : State q) (g : Vector q.d) : ℝ :=
  (s.completed + 1 : ℕ) * max 0
    (dualNorm (g - medianCenter (s.history.take (window q (s.completed + 1)))) - driftRadius q s)

noncomputable def cappedExcess (q : Public) (A : ℝ) (s : State q) (g : Vector q.d) : ℝ :=
  if s.warmup = 0 then max 0 (min (weightedInnovation q s g) A - min (empiricalQuantile q s) A)
  else 0

lemma cappedExcess_nonneg (q : Public) (A : ℝ) (s : State q) (g : Vector q.d) :
    0 ≤ cappedExcess q A s g := by
  unfold cappedExcess
  split_ifs
  · exact le_max_left _ _
  · rfl

lemma blockFromStream_cappedMass (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ξ : ℕ → Ω)
    (hp : s.pending = none) (A : ℝ) :
    QuantileClipping.cappedMass (blockFromStream q g (analysisCost q s) s ξ).extremes A =
      QuantileClipping.cappedMass s.extremes A + cappedExcess q A s (g (queryPoint q s) (ξ 0)) := by
  by_cases hw : 0 < s.warmup
  · simp only [analysisCost, ite_eq_left hw]
    simp [hw, blockFromStream, blockUpdate, updateState, cappedExcess,
      show s.warmup ≠ 0 by omega]
  · have hw0 : s.warmup = 0 := by omega
    simp only [analysisCost, hw0, Nat.lt_irrefl, ite_false]
    change QuantileClipping.cappedMass
      (blockFromStream q g 2 s ξ).extremes A = _
    simp only [blockFromStream, blockUpdate, updateState, hw0, Nat.lt_irrefl, ite_false, hp]
    change QuantileClipping.cappedMass
      (QuantileClipping.insert s.extremes (quantileIndex q s)
        (weightedInnovation q s (g (queryPoint q s) (ξ 0)))) A = _
    rw [QuantileClipping.cappedMass_insert]
    simp only [cappedExcess, hw0, ite_true, empiricalQuantile]

lemma accumulated_cappedExcess (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (ξ : ℕ → Ω) :
    (∑ j ∈ Finset.range N, cappedExcess q A
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1 (primaryReply q g ξ j)) =
      QuantileClipping.cappedMass
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ N).1.extremes A := by
  induction N with
  | zero => simp [StochasticGeneralized.blockTrace_zero, initialState,
      QuantileClipping.cappedMass, min_eq_left hA]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, StochasticGeneralized.blockTrace_succ]
    let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ N
    change QuantileClipping.cappedMass tr.1.extremes A +
      cappedExcess q A tr.1 (primaryReply q g ξ N) =
        QuantileClipping.cappedMass (blockFromStream q g (analysisCost q tr.1) tr.1 tr.2).extremes A
    rw [blockFromStream_cappedMass q g tr.1 tr.2 (blockTrace_structure q g ξ N).1 A]
    congr 2
    change g (queryPoint q tr.1) (ξ _) = g (queryPoint q tr.1) (tr.2 0)
    congr 1
    simpa only [Nat.add_zero] using (StochasticGeneralized.blockTrace_tail
      (analysisCost q) (blockUpdate q g) (initialState q) ξ N 0).symm

lemma accumulated_cappedExcess_le (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (ξ : ℕ → Ω) :
    (∑ j ∈ Finset.range N, cappedExcess q A
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1 (primaryReply q g ξ j)) ≤ trimCount q * A := by
  rw [accumulated_cappedExcess q g A hA N ξ]
  exact QuantileClipping.cappedMass_le _ _

lemma cappedExcess_le (q : Public) {A : ℝ} (hA : 0 ≤ A) (s : State q)
    (hQ : 0 ≤ empiricalQuantile q s) (g : Vector q.d) : cappedExcess q A s g ≤ A := by
  unfold cappedExcess
  split_ifs
  · apply max_le hA
    have hmin : 0 ≤ min (empiricalQuantile q s) A := le_min hQ hA
    linarith [min_le_right (weightedInnovation q s g) A]
  · exact hA

lemma measurable_weightedInnovation (q : Public) :
    Measurable (Function.uncurry (weightedInnovation q)) := by
  have hc := (measurable_medianCenter q.d).comp ((measurable_windowHistory q).comp
    (measurable_fst : Measurable (fun w : State q × Vector q.d => w.1)))
  have hx := (measurable_dualNorm q.d).comp (measurable_snd.sub hc)
  have ht : Measurable (fun w : State q × Vector q.d => ((w.1.completed + 1 : ℕ) : ℝ)) := by
    fun_prop
  exact ht.mul (measurable_const.max (hx.sub ((measurable_driftRadius q).comp measurable_fst)))

lemma measurable_cappedExcess (q : Public) (A : ℝ) :
    Measurable (Function.uncurry (cappedExcess q A)) := by
  unfold cappedExcess
  apply Measurable.ite (measurableSet_eq_fun ((measurable_warmup q).comp measurable_fst) measurable_const)
  · exact measurable_const.max (((measurable_weightedInnovation q).min measurable_const).sub
      (((measurable_empiricalQuantile q).comp measurable_fst).min measurable_const))
  · exact measurable_const

noncomputable def exceedSignal (q : Public) (A : ℝ) (s : State q) (g : Vector q.d) : ℕ :=
  if s.warmup = 0 then if A < weightedInnovation q s g then 1 else 0 else 0

lemma blockFromStream_exceedCount (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ξ : ℕ → Ω)
    (hp : s.pending = none) (A : ℝ) :
    QuantileClipping.exceedCount (blockFromStream q g (analysisCost q s) s ξ).extremes A ≤
      QuantileClipping.exceedCount s.extremes A + exceedSignal q A s (g (queryPoint q s) (ξ 0)) := by
  by_cases hw : 0 < s.warmup
  · simp only [analysisCost, ite_eq_left hw]
    simp [hw, blockFromStream, blockUpdate, updateState, exceedSignal,
      show s.warmup ≠ 0 by omega]
  · have hw0 : s.warmup = 0 := by omega
    simp only [analysisCost, hw0, Nat.lt_irrefl, ite_false]
    change QuantileClipping.exceedCount (blockFromStream q g 2 s ξ).extremes A ≤ _
    simp only [blockFromStream, blockUpdate, updateState, hw0, Nat.lt_irrefl, ite_false, hp]
    change QuantileClipping.exceedCount
      (QuantileClipping.insert s.extremes (quantileIndex q s)
        (weightedInnovation q s (g (queryPoint q s) (ξ 0)))) A ≤ _
    simpa only [exceedSignal, hw0, ite_true] using QuantileClipping.exceedCount_insert_le
      s.extremes (quantileIndex q s) (weightedInnovation q s (g (queryPoint q s) (ξ 0))) A

lemma trace_exceedCount_le (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (ξ : ℕ → Ω) :
    QuantileClipping.exceedCount
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ N).1.extremes A ≤
      ∑ j ∈ Finset.range N, exceedSignal q A
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1 (primaryReply q g ξ j) := by
  induction N with
  | zero => simp [StochasticGeneralized.blockTrace_zero, initialState,
      QuantileClipping.exceedCount, not_lt.mpr hA]
  | succ N ih =>
    rw [Finset.sum_range_succ, StochasticGeneralized.blockTrace_succ]
    let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ N
    have h := blockFromStream_exceedCount q g tr.1 tr.2 (blockTrace_structure q g ξ N).1 A
    have he : g (queryPoint q tr.1) (tr.2 0) = primaryReply q g ξ N := by
      change g (queryPoint q tr.1) (tr.2 0) = g (queryPoint q tr.1) (ξ _)
      congr 1
      simpa only [Nat.add_zero] using StochasticGeneralized.blockTrace_tail
        (analysisCost q) (blockUpdate q g) (initialState q) ξ N 0
    rw [he] at h
    exact h.trans (Nat.add_le_add_right ih _)

lemma quantile_crossing_count (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (ξ : ℕ → Ω)
    (hQ : A < empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q)
      (blockUpdate q g) (initialState q) ξ N).1) :
    trimCount q ≤ ∑ j ∈ Finset.range N, exceedSignal q A
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1 (primaryReply q g ξ j) := by
  let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ N).1
  have hc : QuantileClipping.exceedCount s.extremes A = trimCount q :=
    QuantileClipping.exceedCount_eq_of_lt_min s.extremes (quantileIndex q s)
      (empiricalQuantile_le q s) hQ
  rw [← hc]
  exact trace_exceedCount_le q g A hA N ξ

end OracleTemplate.AdaptiveHeavyTailSimplex
