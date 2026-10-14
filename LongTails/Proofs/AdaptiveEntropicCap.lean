import LongTails.Proofs.AdaptiveEntropicInnovation

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def centerExceedScore (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (s : State q) (ω : Ω) : ℝ := by
  classical
  exact if centerActive q μ σ s then
    if A < weightedInnovation q s (g (queryPoint q s) ω) then 1 else 0 else 0

lemma measurable_centerExceedScore (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ A : ℝ) :
    Measurable (Function.uncurry (centerExceedScore q g μ σ A)) := by
  apply Measurable.ite ((measurableSet_centerActive q hμ σ).preimage measurable_fst)
  · apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_lt measurable_const ((measurable_weightedInnovation q).comp
      (measurable_fst.prodMk (hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        measurable_snd))))
  · exact measurable_const

lemma centerExceedScore_unit (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (s : State q) (ω : Ω) :
    0 ≤ centerExceedScore q g μ σ A s ω ∧ centerExceedScore q g μ σ A s ω ≤ 1 := by
  unfold centerExceedScore
  split_ifs <;> norm_num

lemma centerExceedScore_mean (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p) (s : State q) :
    (∫ ω, centerExceedScore q g μ σ A s ω ∂P) ≤
      if s.warmup = 0 then 130 * ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p / A ^ p else 0 := by
  classical
  by_cases hs : centerActive q μ σ s
  · simp only [centerExceedScore, ite_eq_left hs, ite_eq_left hs.1]
    exact weightedInnovation_exceed_mean q hg μ hσ hp hp2 hA hi hm s hs.2
  · simp only [centerExceedScore, ite_eq_right hs, integral_zero]
    split_ifs <;> positivity

lemma centerExceedScore_warm (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (s : State q) (hw : s.warmup ≠ 0) (ω : Ω) :
    centerExceedScore q g μ σ A s ω = 0 := by
  simp [centerExceedScore, centerActive, hw]

lemma centerExceed_compensator_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (centerExceedScore q g μ σ A) n s b
        ∂Measure.pi (fun _ : Fin n => P)) (preload q + T) (initialState q) ξ ≤
      T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) := by
  classical
  rw [StochasticGeneralized.accumulated_eq_sum]
  let C := 130 * (T : ℝ) ^ p * σ ^ p / A ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (preload q + T),
        if j ∈ Finset.Ico (preload q) (preload q + T) then C else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      have hc : 0 < analysisCost q s := by unfold analysisCost; split_ifs <;> norm_num
      change (∫ b, firstScore (centerExceedScore q g μ σ A) (analysisCost q s) s b
        ∂Measure.pi (fun _ : Fin (analysisCost q s) => P)) ≤ _
      rw [integral_firstScore s ((measurable_centerExceedScore q hg hμ σ A).comp
        measurable_prodMk_left) hc]
      have hw : s.warmup = preload q - j := (blockTrace_structure q g ξ j).2.2.1
      have ht : s.completed = j - preload q := (blockTrace_structure q g ξ j).2.2.2
      by_cases hjm : preload q ≤ j
      · have hjT := Finset.mem_range.mp hj
        have hmem : j ∈ Finset.Ico (preload q) (preload q + T) := Finset.mem_Ico.mpr ⟨hjm, hjT⟩
        rw [ite_eq_left hmem]
        have hs0 : s.warmup = 0 := by omega
        have htime : ((s.completed + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast (show s.completed + 1 ≤ T by omega)
        have hrpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (s.completed + 1 : ℕ))
          htime (show 0 ≤ p by linarith)
        have hb := centerExceedScore_mean q hg μ hσ hp hp2 hA hi hm s
        rw [ite_eq_left hs0] at hb
        apply hb.trans
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (Real.rpow_nonneg hσ p))
          (Real.rpow_nonneg hA.le p)
      · have hmem : j ∉ Finset.Ico (preload q) (preload q + T) := by simp only [Finset.mem_Ico]; omega
        rw [ite_eq_right hmem]
        have hs0 : s.warmup ≠ 0 := by omega
        simp only [centerExceedScore_warm q g μ σ A s hs0, integral_zero, le_refl]
    _ = _ := by
      rw [← Finset.sum_filter]
      have he : (Finset.range (preload q + T)).filter
          (fun j => j ∈ Finset.Ico (preload q) (preload q + T)) =
          Finset.Ico (preload q) (preload q + T) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [he]
      simp [C]

lemma centerExceed_rare_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hbudget : T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) ≤ (trimCount q : ℝ) / 8) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (trimCount q : ℝ) / 2 ≤ StochasticGeneralized.accumulated
        (analysisCost q) (blockUpdate q g) (firstScore (centerExceedScore q g μ σ A))
        (preload q + T) (initialState q) ξ} ≤
      ENNReal.ofReal (Real.exp (-(trimCount q : ℝ) / 8)) := by
  apply AdaptiveEntropicConcentration.accumulated_rare_tail P (analysisCost q) (blockUpdate q g)
    (firstScore (centerExceedScore q g μ σ A)) (measurable_analysisCost q)
    (measurable_blockUpdate q hg) (measurable_firstScore (measurable_centerExceedScore q hg hμ σ A))
    (firstScore_unit (centerExceedScore_unit q g μ σ A))
  intro ξ
  exact (centerExceed_compensator_sum q hg hμ hσ hp hp2 hA hi hm T ξ).trans hbudget

lemma centerExceedScore_eq_exceedSignal (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (s : State q) (hs : s.warmup = 0 → centerGood q μ σ s) (ω : Ω) :
    centerExceedScore q g μ σ A s ω = (exceedSignal q A s (g (queryPoint q s) ω) : ℝ) := by
  classical
  by_cases hw : s.warmup = 0
  · have ha : centerActive q μ σ s := ⟨hw, hs hw⟩
    simp only [centerExceedScore, ite_eq_left ha, exceedSignal, ite_eq_left hw]
    split_ifs <;> norm_num
  · simp [centerExceedScore, centerActive, exceedSignal, hw]

lemma accumulated_centerExceed_eq (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (N : ℕ) (ξ : ℕ → Ω)
    (hs : ∀ j < N, let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ j).1; s.warmup = 0 → centerGood q μ σ s) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (firstScore (centerExceedScore q g μ σ A)) N (initialState q) ξ =
      ((∑ j ∈ Finset.range N, exceedSignal q A
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1 (primaryReply q g ξ j)) : ℕ) := by
  rw [StochasticGeneralized.accumulated_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ j
  have hc : 0 < analysisCost q tr.1 := by unfold analysisCost; split_ifs <;> norm_num
  change firstScore (centerExceedScore q g μ σ A) (analysisCost q tr.1) tr.1
    (fun i => tr.2 i) = _
  simp only [firstScore, dite_eq_left hc]
  rw [centerExceedScore_eq_exceedSignal q g μ σ A tr.1 (hs j (Finset.mem_range.mp hj))]
  have he : g (queryPoint q tr.1) (tr.2 0) = primaryReply q g ξ j := by
    change g (queryPoint q tr.1) (tr.2 0) = g (queryPoint q tr.1) (ξ _)
    congr 1
    simpa only [Nat.add_zero] using StochasticGeneralized.blockTrace_tail
      (analysisCost q) (blockUpdate q g) (initialState q) ξ j 0
  rw [he]


lemma quantile_cap_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hbudget : T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) ≤ (trimCount q : ℝ) / 8) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (∀ j < preload q + T,
        let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1
        s.warmup = 0 → centerGood q μ σ s) ∧
        A < empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q)
          (blockUpdate q g) (initialState q) ξ (preload q + T)).1} ≤
      ENNReal.ofReal (Real.exp (-(trimCount q : ℝ) / 8)) := by
  apply le_trans (measure_mono ?_)
    (centerExceed_rare_tail q P hg hμ hσ hp hp2 hA hi hm T hbudget)
  intro ξ hξ
  have hc := quantile_crossing_count q g A hA.le (preload q + T) ξ hξ.2
  change (trimCount q : ℝ) / 2 ≤ _
  rw [accumulated_centerExceed_eq q g μ σ A (preload q + T) ξ hξ.1]
  have hcr : (trimCount q : ℝ) ≤ ((∑ j ∈ Finset.range (preload q + T), exceedSignal q A
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1 (primaryReply q g ξ j)) : ℕ) := by exact_mod_cast hc
  linarith [Nat.cast_nonneg (α := ℝ) (trimCount q)]

end OracleTemplate.AdaptiveHeavyTailSimplex
