import LongTails.Proofs.AdaptiveEntropicEvents
import LongTails.Proofs.AdaptiveEntropicQuantileProcess
import LongTails.Proofs.AdaptiveEntropicClipping

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma weightedInnovation_nonneg (q : Public) (s : State q) (g : Vector q.d) :
    0 ≤ weightedInnovation q s g := by
  exact mul_nonneg (by positivity) (le_max_left _ _)

lemma weightedInnovation_moment (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (s : State q) (hs : centerGood q μ σ s) :
    Integrable (fun ω => weightedInnovation q s (g (queryPoint q s) ω) ^ p) P ∧
      (∫ ω, weightedInnovation q s (g (queryPoint q s) ω) ^ p ∂P) ≤
        130 * ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p := by
  have hh := innovation_moment (hg.comp measurable_prodMk_left) (historyCenter q s)
    (μ (queryPoint q s)) hσ hp hp2 hs (hi _) (hm _)
  have he : (fun ω => weightedInnovation q s (g (queryPoint q s) ω) ^ p) =
      fun ω => ((s.completed + 1 : ℕ) : ℝ) ^ p *
        max 0 (dualNorm (g (queryPoint q s) ω - historyCenter q s) - driftRadius q s) ^ p := by
    funext ω
    exact Real.mul_rpow (by positivity) (le_max_left _ _)
  rw [he]
  refine ⟨hh.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hh.2
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (s.completed + 1 : ℕ)) p)
  calc
    _ ≤ ((s.completed + 1 : ℕ) : ℝ) ^ p * (130 * σ ^ p) := hb
    _ = _ := by ring

lemma weightedInnovation_tail_mean (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (s : State q) (hs : centerGood q μ σ s) :
    Integrable (fun ω => max 0 (weightedInnovation q s (g (queryPoint q s) ω) - A)) P ∧
      (∫ ω, max 0 (weightedInnovation q s (g (queryPoint q s) ω) - A) ∂P) ≤
        130 * ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p / A ^ (p - 1) := by
  have hh := weightedInnovation_moment q hg μ hσ hp hp2 hi hm s hs
  have hx : Measurable (fun ω => weightedInnovation q s (g (queryPoint q s) ω)) :=
    (measurable_weightedInnovation q).comp (measurable_const.prodMk
      (hg.comp measurable_prodMk_left))
  have hb (ω : Ω) := positive_part_tail_moment (weightedInnovation_nonneg q s
    (g (queryPoint q s) ω)) hA hp
  have hi' : Integrable (fun ω => max 0 (weightedInnovation q s (g (queryPoint q s) ω) - A)) P := by
    apply (hh.1.div_const (A ^ (p - 1))).mono' (measurable_const.max (hx.sub_const A)).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show (0 : ℝ) ≤ max 0 (weightedInnovation q s (g (queryPoint q s) ω) - A) from le_max_left _ _)]
    exact hb ω
  refine ⟨hi', ?_⟩
  have hbound := integral_mono hi' (hh.1.div_const (A ^ (p - 1))) hb
  rw [integral_div] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right hh.2 (Real.rpow_nonneg hA.le _))

lemma weightedInnovation_exceed_mean (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (μ : simplex q.d → Vector q.d) {σ p A : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hA : 0 < A)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (s : State q) (hs : centerGood q μ σ s) :
    (∫ ω, if A < weightedInnovation q s (g (queryPoint q s) ω) then (1 : ℝ) else 0 ∂P) ≤
      130 * ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p / A ^ p := by
  have hh := weightedInnovation_moment q hg μ hσ hp hp2 hi hm s hs
  have hx : Measurable (fun ω => weightedInnovation q s (g (queryPoint q s) ω)) :=
    (measurable_weightedInnovation q).comp (measurable_const.prodMk
      (hg.comp measurable_prodMk_left))
  have he : Measurable (fun ω => if A < weightedInnovation q s (g (queryPoint q s) ω)
      then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hx) measurable_const measurable_const
  have hi' : Integrable (fun ω => if A < weightedInnovation q s (g (queryPoint q s) ω)
      then (1 : ℝ) else 0) P := by
    apply Integrable.of_bound he.aestronglyMeasurable 1
    filter_upwards [] with ω
    split_ifs <;> norm_num
  have hb (ω : Ω) := tail_indicator_moment
    (weightedInnovation_nonneg q s (g (queryPoint q s) ω)) hA (show 0 ≤ p by linarith)
  have hbound := integral_mono hi' (hh.1.div_const (A ^ p)) hb
  rw [integral_div] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right hh.2 (Real.rpow_nonneg hA.le _))

end OracleTemplate.AdaptiveHeavyTailSimplex
