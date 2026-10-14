import LongTails.Proofs.AdaptiveEntropicStateMeasurable
import LongTails.Proofs.AdaptiveEntropicConcentration
import Mathlib.MeasureTheory.Integral.Pi
import LongTails.Proofs.AdaptiveEntropicProcess

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def firstScore {S Ω : Type*} (X : S → Ω → ℝ)
    (n : ℕ) (s : S) (b : Fin n → Ω) : ℝ :=
  if h : 0 < n then X s (b ⟨0, h⟩) else 0

lemma measurable_firstScore {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {X : S → Ω → ℝ} (hX : Measurable (Function.uncurry X)) (n : ℕ) :
    Measurable (Function.uncurry (firstScore X n)) := by
  classical
  change Measurable (fun w : S × (Fin n → Ω) =>
    if h : 0 < n then X w.1 (w.2 ⟨0, h⟩) else 0)
  by_cases h : 0 < n
  · simp only [dite_eq_left h]
    exact hX.comp (measurable_fst.prodMk ((measurable_pi_apply (⟨0, h⟩ : Fin n)).comp measurable_snd))
  · simp only [dite_eq_right h]
    exact measurable_const

lemma firstScore_unit {S Ω : Type*} {X : S → Ω → ℝ}
    (hb : ∀ s ω, 0 ≤ X s ω ∧ X s ω ≤ 1) (n : ℕ) (s : S) (b : Fin n → Ω) :
    0 ≤ firstScore X n s b ∧ firstScore X n s b ≤ 1 := by
  unfold firstScore
  split_ifs
  · exact hb _ _
  · norm_num

lemma integral_firstScore {S Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : S → Ω → ℝ}
    (s : S) (hX : Measurable (X s)) {n : ℕ} (hn : 0 < n) :
    (∫ b, firstScore X n s b ∂Measure.pi (fun _ : Fin n => P)) = ∫ ω, X s ω ∂P := by
  simp only [firstScore, dite_eq_left hn]
  exact integral_comp_eval hX.aestronglyMeasurable

noncomputable def noiseFlag (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (s : State q) (ω : Ω) : ℝ :=
  if 8 * σ < dualNorm (g (queryPoint q s) ω - μ (queryPoint q s)) then 1 else 0

lemma measurable_noiseFlag (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ : ℝ) :
    Measurable (Function.uncurry (noiseFlag q g μ σ)) := by
  have hq := (measurable_queryPoint q).comp (measurable_fst : Measurable (fun w : State q × Ω => w.1))
  have hn := (measurable_dualNorm q.d).comp ((hg.comp (hq.prodMk measurable_snd)).sub (hμ.comp hq))
  exact Measurable.ite (measurableSet_lt measurable_const hn) measurable_const measurable_const

lemma noiseFlag_unit (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (s : State q) (ω : Ω) :
    0 ≤ noiseFlag q g μ σ s ω ∧ noiseFlag q g μ σ s ω ≤ 1 := by
  unfold noiseFlag
  split_ifs <;> norm_num

lemma integral_noiseFlag (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω}
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p) (s : State q) :
    (∫ ω, noiseFlag q g μ σ s ω ∂P) ≤ 1 / 8 := by
  let A := {ω | 8 * σ < dualNorm (g (queryPoint q s) ω - μ (queryPoint q s))}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    ((measurable_dualNorm q.d).comp ((hg.comp measurable_prodMk_left).sub_const _))
  have he : noiseFlag q g μ σ s = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [noiseFlag, Set.indicator_apply, A, Set.mem_ofPred_eq]
  rw [he]
  change (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂P) ≤ 1 / 8
  rw [integral_indicator_one hA]
  exact AdaptiveEntropicConcentration.noise_tail_eighth (fun ω => norm_nonneg _)
    hp hσ (hi _) (hm _)

lemma measurable_oracle_mean (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {g : simplex q.d → Ω → Vector q.d}
    (hg : Measurable (Function.uncurry g)) : Measurable (fun x => ∫ ω, g x ω ∂P) :=
  hg.stronglyMeasurable.integral_prod_right.measurable

noncomputable def selectedNoiseFlag (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (I : Finset ℕ) (s : State q) (ω : Ω) : ℝ :=
  (if s.history.length ∈ I then 1 else 0) * noiseFlag q g μ σ s ω

lemma measurable_selectedNoiseFlag (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ : ℝ) (I : Finset ℕ) :
    Measurable (Function.uncurry (selectedNoiseFlag q g μ σ I)) := by
  have hl := AdaptiveList.measurable_length.comp ((measurable_history q).comp
    (measurable_fst : Measurable (fun w : State q × Ω => w.1)))
  exact ((measurable_of_countable (fun n : ℕ => if n ∈ I then (1 : ℝ) else 0)).comp hl).mul
    (measurable_noiseFlag q hg hμ σ)

lemma selectedNoiseFlag_unit (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (I : Finset ℕ) (s : State q) (ω : Ω) :
    0 ≤ selectedNoiseFlag q g μ σ I s ω ∧ selectedNoiseFlag q g μ σ I s ω ≤ 1 := by
  by_cases h : s.history.length ∈ I
  · simpa only [selectedNoiseFlag, ite_eq_left h, one_mul] using noiseFlag_unit q g μ σ s ω
  · simp [selectedNoiseFlag, h]

lemma integral_selectedNoiseFlag (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω}
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (I : Finset ℕ) (s : State q) :
    (∫ ω, selectedNoiseFlag q g μ σ I s ω ∂P) ≤
      if s.history.length ∈ I then 1 / 8 else 0 := by
  by_cases h : s.history.length ∈ I
  · simp only [selectedNoiseFlag, ite_eq_left h, one_mul]
    exact integral_noiseFlag q hg μ hσ hp hi hm s
  · simp [selectedNoiseFlag, h]

lemma selected_noise_mean_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (I : Finset ℕ) (N : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (selectedNoiseFlag q g μ σ I) n s b
        ∂Measure.pi (fun _ : Fin n => P)) N (initialState q) ξ ≤ (I.card : ℝ) / 8 := by
  rw [StochasticGeneralized.accumulated_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range N, if j ∈ I then (1 / 8 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      have hlen : s.history.length = j := (blockTrace_structure q g ξ j).2.1
      have hc : 0 < analysisCost q s := by unfold analysisCost; split_ifs <;> norm_num
      change (∫ b, firstScore (selectedNoiseFlag q g μ σ I) (analysisCost q s) s b
        ∂Measure.pi (fun _ : Fin (analysisCost q s) => P)) ≤ _
      rw [integral_firstScore s ((measurable_selectedNoiseFlag q hg hμ σ I).comp
        measurable_prodMk_left) hc]
      simpa only [hlen] using integral_selectedNoiseFlag q hg μ hσ hp hi hm I s
    _ = (((Finset.range N).filter (fun j => j ∈ I)).card : ℝ) / 8 := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Finset.card_le_card (show (Finset.range N).filter (fun j => j ∈ I) ⊆ I from
        fun j hj => (Finset.mem_filter.mp hj).2)

lemma selected_noise_majority_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (I : Finset ℕ) (N : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (I.card : ℝ) / 2 ≤ StochasticGeneralized.accumulated
        (analysisCost q) (blockUpdate q g) (firstScore (selectedNoiseFlag q g μ σ I))
        N (initialState q) ξ} ≤ ENNReal.ofReal (Real.exp (-(I.card : ℝ) / 8)) := by
  exact AdaptiveEntropicConcentration.accumulated_rare_tail P (analysisCost q) (blockUpdate q g)
    (firstScore (selectedNoiseFlag q g μ σ I)) (measurable_analysisCost q)
    (measurable_blockUpdate q hg)
    (measurable_firstScore (measurable_selectedNoiseFlag q hg hμ σ I))
    (firstScore_unit (selectedNoiseFlag_unit q g μ σ I)) N (initialState q) I.card
    (selected_noise_mean_sum q hg hμ hσ hp hi hm I N)

end OracleTemplate.AdaptiveHeavyTailSimplex
