import LongTails.Proofs.AdaptiveEntropicCenterAccuracy

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def historyCenter (q : Public) (s : State q) : Vector q.d :=
  medianCenter (s.history.take (window q (s.completed + 1)))

def centerGood (q : Public) (μ : simplex q.d → Vector q.d) (σ : ℝ) (s : State q) : Prop :=
  dualNorm (μ (queryPoint q s) - historyCenter q s) ≤ 8 * σ + driftRadius q s

def centerActive (q : Public) (μ : simplex q.d → Vector q.d) (σ : ℝ) (s : State q) : Prop :=
  s.warmup = 0 ∧ centerGood q μ σ s

def cappedActive (q : Public) (μ : simplex q.d → Vector q.d) (σ A : ℝ) (s : State q) : Prop :=
  centerActive q μ σ s ∧ 0 ≤ empiricalQuantile q s ∧ empiricalQuantile q s ≤ A

lemma measurable_historyCenter (q : Public) : Measurable (historyCenter q) :=
  (measurable_medianCenter q.d).comp (measurable_windowHistory q)

lemma measurableSet_centerGood (q : Public) {μ : simplex q.d → Vector q.d}
    (hμ : Measurable μ) (σ : ℝ) : MeasurableSet {s | centerGood q μ σ s} := by
  exact measurableSet_le ((measurable_dualNorm q.d).comp
    ((hμ.comp (measurable_queryPoint q)).sub (measurable_historyCenter q)))
    (measurable_const.add (measurable_driftRadius q))

lemma measurableSet_centerActive (q : Public) {μ : simplex q.d → Vector q.d}
    (hμ : Measurable μ) (σ : ℝ) : MeasurableSet {s | centerActive q μ σ s} :=
  (measurableSet_eq_fun (measurable_warmup q) measurable_const).inter
    (measurableSet_centerGood q hμ σ)

lemma measurableSet_cappedActive (q : Public) {μ : simplex q.d → Vector q.d}
    (hμ : Measurable μ) (σ A : ℝ) : MeasurableSet {s | cappedActive q μ σ A s} :=
  (measurableSet_centerActive q hμ σ).inter
    ((measurableSet_le measurable_const (measurable_empiricalQuantile q)).inter
      (measurableSet_le (measurable_empiricalQuantile q) measurable_const))

lemma dualNorm_sub_comm {d : ℕ} (a b : Vector d) : dualNorm (a - b) = dualNorm (b - a) := by
  change ‖(fun i => a i) - (fun i => b i)‖ = ‖(fun i => b i) - (fun i => a i)‖
  exact norm_sub_rev _ _

lemma centerGood_trace_iff (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d) (σ : ℝ)
    (ξ : ℕ → Ω) {t : ℕ} (ht : 0 < t) :
    centerGood q μ σ (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + t - 1)).1 ↔
      dualNorm (medianCenter ((StochasticGeneralized.blockTrace (analysisCost q)
        (blockUpdate q g) (initialState q) ξ (preload q + t - 1)).1.history.take (window q t)) -
        μ (queryTrajectory q g ξ t)) ≤ 8 * σ + 24 * q.L * window q t / t := by
  let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ (preload q + t - 1)).1
  have hc : s.completed + 1 = t := by
    have hs := (blockTrace_structure q g ξ (preload q + t - 1)).2.2.2
    change s.completed = _ at hs
    omega
  have hq : queryPoint q s = queryTrajectory q g ξ t := by
    change blockQuery q g ξ (preload q + t - 1) = _
    rw [blockQuery_eq_trajectory]
    congr 1
    omega
  change dualNorm (μ (queryPoint q s) - medianCenter (s.history.take
    (window q (s.completed + 1)))) ≤ 8 * σ +
    24 * q.L * window q (s.completed + 1) / (s.completed + 1) ↔ _
  have hcr : (s.completed : ℝ) + 1 = t := by exact_mod_cast hc
  rw [hc, hq, dualNorm_sub_comm, hcr]

lemma centerGood_trace_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (hL : 0 ≤ q.L) (hH : 2 ≤ confidence q)
    (hsmooth : ∀ x y, dualNorm (μ x - μ y) ≤ q.L * oneNorm (x.val - y.val))
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    {t : ℕ} (ht : 0 < t) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | ¬ centerGood q μ σ (StochasticGeneralized.blockTrace (analysisCost q)
        (blockUpdate q g) (initialState q) ξ (preload q + t - 1)).1} ≤
      ENNReal.ofReal (Real.exp (-confidence q) / ((t : ℝ) * (t + 1))) := by
  simp_rw [centerGood_trace_iff q g μ σ _ ht, not_le]
  exact rolling_median_failure q hg hμ hL hH hsmooth hσ hp hi hm ht

lemma all_centers_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (hL : 0 ≤ q.L) (hH : 2 ≤ confidence q)
    (hsmooth : ∀ x y, dualNorm (μ x - μ y) ≤ q.L * oneNorm (x.val - y.val))
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p) (N : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P)
      (⋃ i ∈ Finset.range N, {ξ | ¬ centerGood q μ σ
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ (preload q + i)).1}) ≤ ENNReal.ofReal (Real.exp (-confidence q)) := by
  apply finite_window_union
  intro i hiN
  have h := centerGood_trace_failure q hg hμ hL hH hsmooth hσ hp hi hm
    (t := i + 1) (by omega)
  simpa [Nat.add_assoc, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h

end OracleTemplate.AdaptiveHeavyTailSimplex
