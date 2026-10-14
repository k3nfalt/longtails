import LongTails.Proofs.AdaptiveEntropicVariance
import LongTails.Proofs.AdaptiveEntropicConcentration

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def pairedVariation (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (n : ℕ) (s : State q) (b : Fin n → Ω) : ℝ :=
  pairScore (fun s a b =>
    ‖weightedResidual q μ σ A T s (g (queryPoint q s) a) -
      weightedResidual q μ σ A T s (g (queryPoint q s) b)‖ ^ 2) n s b

lemma measurable_pairedVariation (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ A : ℝ) (T n : ℕ) :
    Measurable (Function.uncurry (pairedVariation q g μ σ A T n)) := by
  have hZ : Measurable (fun w : State q × Ω =>
      weightedResidual q μ σ A T w.1 (g (queryPoint q w.1) w.2)) :=
    (measurable_weightedResidual q hμ σ A T).comp
      (measurable_fst.prodMk (hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        measurable_snd)))
  have h1 : Measurable (fun w : State q × (Ω × Ω) =>
      weightedResidual q μ σ A T w.1 (g (queryPoint q w.1) w.2.1)) :=
    hZ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable (fun w : State q × (Ω × Ω) =>
      weightedResidual q μ σ A T w.1 (g (queryPoint q w.1) w.2.2)) :=
    hZ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact measurable_pairScore ((h1.sub h2).norm.pow_const 2) n

lemma pairedVariation_range (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T n : ℕ)
    (s : State q) (b : Fin n → Ω) :
    0 ≤ pairedVariation q g μ σ A T n s b ∧
      pairedVariation q g μ σ A T n s b ≤
        4 * (24 * q.L * window q (T + 1) + A) ^ 2 := by
  unfold pairedVariation pairScore
  split_ifs
  · exact ⟨sq_nonneg _, weightedResidual_pair_range q μ σ hA hL T s _ _⟩
  · constructor <;> positivity

lemma accumulated_div_const {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (C : ℝ) (N : ℕ) (s : S) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated cost next (fun n s b => X n s b / C) N s ξ =
      StochasticGeneralized.accumulated cost next X N s ξ / C := by
  simp only [StochasticGeneralized.accumulated_eq_sum, Finset.sum_div]

lemma pairedVariation_forward_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ) (σ : ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T N : ℕ)
    (hU : 0 < 24 * q.L * window q (T + 1) + A) (H : ℝ) :
    let X := pairedVariation q g μ σ A T
    let m := fun n s (_ : Fin n → Ω) => ∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) m N
        (initialState q) ξ + 8 * (24 * q.L * window q (T + 1) + A) ^ 2 * H ≤
          StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X N
            (initialState q) ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro X m
  let C := 4 * (24 * q.L * window q (T + 1) + A) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let Y := fun n s b => X n s b / C
  have hY : ∀ n, Measurable (Function.uncurry (Y n)) := by
    intro n
    exact (measurable_pairedVariation q hg hμ σ A T n).div_const C
  have hb : ∀ n s b, 0 ≤ Y n s b ∧ Y n s b ≤ 1 := by
    intro n s b
    have hh := pairedVariation_range q g μ σ hA hL T n s b
    exact ⟨div_nonneg hh.1 hC.le, (div_le_one₀ hC).mpr hh.2⟩
  have h := AdaptiveEntropicConcentration.accumulated_forward_tail P
    (analysisCost q) (blockUpdate q g) Y (measurable_analysisCost q)
    (measurable_blockUpdate q hg) hY hb N (initialState q) H
  have he : (fun n s (_ : Fin n → Ω) => ∫ b, Y n s b ∂Measure.pi (fun _ : Fin n => P)) =
      fun n s b => m n s b / C := by
    funext n s b
    exact integral_div C _
  rw [he] at h
  simp only [Y, accumulated_div_const] at h
  apply le_trans (measure_mono ?_) h
  intro ξ hξ
  change 2 * (_ / C) + 2 * H ≤ _ / C
  apply (le_div_iff₀ hC).mpr
  simp only [add_mul, mul_assoc, div_mul_cancel₀ _ hC.ne']
  dsimp [C] at *
  nlinarith

lemma pairedVariation_inactive (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T n : ℕ) (s : State q) (b : Fin n → Ω)
    (hs : ¬ boundedActive q μ σ A T s) :
    pairedVariation q g μ σ A T n s b = 0 := by
  classical
  unfold pairedVariation pairScore
  split_ifs <;> simp [weightedResidual, hs]

lemma pairedVariation_pair_identity (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (b : Fin 2 → Ω)
    (hs : boundedActive q μ σ A T s) :
    pairedVariation q g μ σ A T 2 s b =
      ((s.completed + 1 : ℕ) : ℝ) ^ 2 *
        dualNorm (clippedReply (clippingThreshold q s) (historyCenter q s)
          (g (queryPoint q s) (b 0)) -
            clippedReply (clippingThreshold q s) (historyCenter q s)
              (g (queryPoint q s) (b 1))) ^ 2 := by
  change ‖weightedResidual q μ σ A T s (g (queryPoint q s) (b 0)) -
    weightedResidual q μ σ A T s (g (queryPoint q s) (b 1))‖ ^ 2 = _
  exact weightedResidual_difference q μ σ A T s _ _ hs

lemma pairedVariation_le_block_increment (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (ξ : ℕ → Ω) (hp : s.pending = none) :
    pairedVariation q g μ σ A T (analysisCost q s) s (fun i => ξ i) ≤
      (blockFromStream q g (analysisCost q s) s ξ).variation - s.variation := by
  classical
  by_cases hs : boundedActive q μ σ A T s
  · have hw : s.warmup = 0 := hs.1.1.1
    have hc : analysisCost q s = 2 := by simp [analysisCost, hw]
    have hv : pairedVariation q g μ σ A T (analysisCost q s) s (fun i => ξ i) =
        ((s.completed + 1 : ℕ) : ℝ) ^ 2 *
          dualNorm (clippedReply (clippingThreshold q s) (historyCenter q s)
            (g (queryPoint q s) (ξ 0)) -
              clippedReply (clippingThreshold q s) (historyCenter q s)
                (g (queryPoint q s) (ξ 1))) ^ 2 := by
      unfold pairedVariation pairScore
      rw [dite_eq_left hc]
      simp only [Fin.val_cast]
      exact weightedResidual_difference q μ σ A T s _ _ hs
    rw [hv, hc]
    have he := (blockFromStream_pair_dynamics q g s ξ hw hp).2.2
    change (blockFromStream q g 2 s ξ).variation = _ at he
    change _ ≤ _
    dsimp only [historyCenter]
    rw [he]
    linarith
  · rw [pairedVariation_inactive q g μ σ A T _ s _ hs]
    have hm := blockUpdate_observable_le q g (fun s => s.variation)
      (update_variation_mono q) (analysisCost q s) s (fun i => ξ i)
    change s.variation ≤ (blockFromStream q g (analysisCost q s) s ξ).variation at hm
    linarith

lemma pairedVariation_mean (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A) (s : State q) (n : ℕ) :
    (∫ b, pairedVariation q g μ σ A T n s b ∂Measure.pi (fun _ : Fin n => P)) ≤
      16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p := by
  by_cases hn : n = 2
  · subst n
    exact weightedResidual_pair_mean q hμ hg hA hL hp hp2 hi hm T hU s
  · simp only [pairedVariation, pairScore, dite_eq_right hn, integral_zero]
    positivity

lemma pairedVariation_warm (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T n : ℕ) (s : State q) (b : Fin n → Ω) (hw : s.warmup ≠ 0) :
    pairedVariation q g μ σ A T n s b = 0 := by
  apply pairedVariation_inactive q g μ σ A T n s b
  intro hs
  exact hw hs.1.1.1

lemma pairedVariation_compensator_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, pairedVariation q g μ σ A T n s b
        ∂Measure.pi (fun _ : Fin n => P)) (preload q + T) (initialState q) ξ ≤
      T * (16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        (T : ℝ) ^ p * σ ^ p) := by
  classical
  rw [StochasticGeneralized.accumulated_eq_sum]
  let C := 16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) * (T : ℝ) ^ p * σ ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (preload q + T),
        if j ∈ Finset.Ico (preload q) (preload q + T) then C else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      have hw : s.warmup = preload q - j := (blockTrace_structure q g ξ j).2.2.1
      have ht : s.completed = j - preload q := (blockTrace_structure q g ξ j).2.2.2
      change (∫ b, pairedVariation q g μ σ A T (analysisCost q s) s b
        ∂Measure.pi (fun _ : Fin (analysisCost q s) => P)) ≤ _
      by_cases hjm : preload q ≤ j
      · have hjT := Finset.mem_range.mp hj
        have hmem : j ∈ Finset.Ico (preload q) (preload q + T) := Finset.mem_Ico.mpr ⟨hjm, hjT⟩
        rw [ite_eq_left hmem]
        have htime : ((s.completed + 1 : ℕ) : ℝ) ≤ T := by
          exact_mod_cast (show s.completed + 1 ≤ T by omega)
        have hrpow := Real.rpow_le_rpow (Nat.cast_nonneg (s.completed + 1))
          htime (show 0 ≤ p by linarith)
        apply (pairedVariation_mean q hg hμ hσ hA hL hp hp2 hi hm T hU s _).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow
          (show 0 ≤ 16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) by positivity))
          (Real.rpow_nonneg hσ p)
      · have hmem : j ∉ Finset.Ico (preload q) (preload q + T) := by
          simp only [Finset.mem_Ico]; omega
        rw [ite_eq_right hmem]
        have hs0 : s.warmup ≠ 0 := by omega
        simp only [pairedVariation_warm q g μ σ A T _ s _ hs0, integral_zero, le_refl]
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

lemma pairedVariation_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A) (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 2 * T * (16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        (T : ℝ) ^ p * σ ^ p) + 8 * (24 * q.L * window q (T + 1) + A) ^ 2 * H ≤
          StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
            (pairedVariation q g μ σ A T) (preload q + T) (initialState q) ξ} ≤
      ENNReal.ofReal (Real.exp (-H)) := by
  have h := pairedVariation_forward_tail q P hg hμ σ hA hL T (preload q + T) hU H
  apply le_trans (measure_mono ?_) h
  intro ξ hξ
  have hm' := pairedVariation_compensator_sum q hg hμ hσ hA hL hp hp2 hi hm T hU ξ
  change 2 * _ + 8 * (24 * q.L * window q (T + 1) + A) ^ 2 * H ≤ _
  exact le_trans (by linarith) hξ

lemma pairedVariation_stream_cost_congr (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (ξ : ℕ → Ω) {n m : ℕ} (hn : n = m) :
    pairedVariation q g μ σ A T n s (fun i => ξ i) =
      pairedVariation q g μ σ A T m s (fun i => ξ i) := by
  subst n
  rfl

lemma pairedVariation_eq_block_increment (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (ξ : ℕ → Ω) (hp : s.pending = none)
    (hs : s.warmup = 0 → boundedActive q μ σ A T s) :
    pairedVariation q g μ σ A T (analysisCost q s) s (fun i => ξ i) =
      (blockFromStream q g (analysisCost q s) s ξ).variation - s.variation := by
  classical
  by_cases hw : s.warmup = 0
  · have hc : analysisCost q s = 2 := by simp [analysisCost, hw]
    rw [pairedVariation_stream_cost_congr q g μ σ A T s ξ hc, hc]
    rw [pairedVariation_pair_identity q g μ σ A T s _ (hs hw)]
    have he := (blockFromStream_pair_dynamics q g s ξ hw hp).2.2
    dsimp only [historyCenter]
    rw [he]
    norm_num
  · have hi : ¬ boundedActive q μ σ A T s := by intro h; exact hw h.1.1.1
    rw [pairedVariation_inactive q g μ σ A T _ s _ hi]
    have hwpos : 0 < s.warmup := Nat.pos_of_ne_zero hw
    have hc : analysisCost q s = 1 := by simp [analysisCost, hwpos]
    rw [hc]
    simp [blockFromStream, blockUpdate, updateState, hwpos]

lemma accumulated_pairedVariation_le_actual (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T N : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairedVariation q g μ σ A T) N (initialState q) ξ ≤
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ N).1.variation := by
  rw [StochasticGeneralized.accumulated_eq_sum]
  let W := fun n => (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ n).1.variation
  calc
    _ ≤ ∑ j ∈ Finset.range N, (W (j + 1) - W j) := by
      apply Finset.sum_le_sum
      intro j hj
      let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j
      have hp : tr.1.pending = none := (blockTrace_structure q g ξ j).1
      have h := pairedVariation_le_block_increment q g μ σ A T tr.1 tr.2 hp
      change _ ≤ W (j + 1) - W j
      simpa only [W, tr, StochasticGeneralized.blockTrace_succ,
        StochasticGeneralized.blockAdvance, blockFromStream] using h
    _ = _ := by
      rw [Finset.sum_range_sub]
      simp [W, StochasticGeneralized.blockTrace_zero, initialState]

lemma accumulated_pairedVariation_eq_actual (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T N : ℕ) (ξ : ℕ → Ω)
    (hs : ∀ j < N,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → boundedActive q μ σ A T s) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (pairedVariation q g μ σ A T) N (initialState q) ξ =
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ N).1.variation := by
  rw [StochasticGeneralized.accumulated_eq_sum]
  let W := fun n => (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ n).1.variation
  calc
    _ = ∑ j ∈ Finset.range N, (W (j + 1) - W j) := by
      apply Finset.sum_congr rfl
      intro j hj
      let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j
      have hp : tr.1.pending = none := (blockTrace_structure q g ξ j).1
      have h := pairedVariation_eq_block_increment q g μ σ A T tr.1 tr.2 hp
        (hs j (Finset.mem_range.mp hj))
      change _ = W (j + 1) - W j
      simpa only [W, tr, StochasticGeneralized.blockTrace_succ,
        StochasticGeneralized.blockAdvance, blockFromStream] using h
    _ = _ := by
      rw [Finset.sum_range_sub]
      simp [W, StochasticGeneralized.blockTrace_zero, initialState]

lemma boundedActive_prefix (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + T)).1 ≤ A) :
    ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → boundedActive q μ σ A T s := by
  intro j hj
  let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ j).1
  change s.warmup = 0 → boundedActive q μ σ A T s
  intro hw
  have hqn : 0 ≤ empiricalQuantile q s := trace_quantile_nonneg q g ξ j
  have hqm : empiricalQuantile q s ≤ A :=
    (blockTrace_observable_mono q g (empiricalQuantile q) (update_quantile_mono q)
      ξ hj.le).trans hQ
  have hw' : s.warmup = preload q - j := (blockTrace_structure q g ξ j).2.2.1
  have ht : s.completed = j - preload q := (blockTrace_structure q g ξ j).2.2.2
  exact ⟨⟨⟨hw, hc j hj hw⟩, hqn, hqm⟩, by omega⟩

lemma actual_variation_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A) (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (∀ j < preload q + T,
        let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1
        s.warmup = 0 → centerGood q μ σ s) ∧
        empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ (preload q + T)).1 ≤ A ∧
        2 * T * (16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
          (T : ℝ) ^ p * σ ^ p) + 8 * (24 * q.L * window q (T + 1) + A) ^ 2 * H ≤
          (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
            (initialState q) ξ (preload q + T)).1.variation} ≤
      ENNReal.ofReal (Real.exp (-H)) := by
  apply le_trans (measure_mono ?_)
    (pairedVariation_tail q P hg hμ hσ hA hL hp hp2 hi hm T hU H)
  intro ξ hξ
  have he := accumulated_pairedVariation_eq_actual q g μ σ A T (preload q + T) ξ
    (boundedActive_prefix q g μ σ A T ξ hξ.1 hξ.2.1)
  change 2 * T * (16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
    (T : ℝ) ^ p * σ ^ p) + 8 * (24 * q.L * window q (T + 1) + A) ^ 2 * H ≤
      StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (pairedVariation q g μ σ A T) (preload q + T) (initialState q) ξ
  rw [he]
  exact hξ.2.2

end OracleTemplate.AdaptiveHeavyTailSimplex
