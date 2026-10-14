import LongTails.Proofs.AdaptiveEntropicWindow
import LongTails.Proofs.AdaptiveEntropicExecution

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma dualNorm_sub_triangle {d : ℕ} (a b c : Vector d) :
    dualNorm (a - c) ≤ dualNorm (a - b) + dualNorm (b - c) := by
  have he : (fun i => (a - c) i) = (fun i => (a - b) i) + (fun i => (b - c) i) := by
    funext i
    simp only [Pi.add_apply, PiLp.sub_apply]
    ring
  unfold dualNorm
  rw [he]
  exact norm_add_le _ _

lemma oneNorm_sub_comm {d : ℕ} (a b : Vector d) : oneNorm (a - b) = oneNorm (b - a) := by
  simp only [oneNorm, PiLp.sub_apply]
  exact Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)

lemma median_history_accuracy (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (hL : 0 ≤ q.L)
    (hsmooth : ∀ x y, dualNorm (μ x - μ y) ≤ q.L * oneNorm (x.val - y.val))
    {σ : ℝ} (hσ : 0 ≤ σ) (ξ : ℕ → Ω) {t k : ℕ} (ht : 0 < t)
    (hk : k ≤ preload q + t - 1)
    (hbad : (∑ i : Fin k,
      if 8 * σ < dualNorm (primaryReply q g ξ (preload q + t - 1 - 1 - i) -
        μ (blockQuery q g ξ (preload q + t - 1 - 1 - i))) then (1 : ℝ) else 0) <
        (k : ℝ) / 2) :
    dualNorm (medianCenter ((StochasticGeneralized.blockTrace (analysisCost q)
      (blockUpdate q g) (initialState q) ξ (preload q + t - 1)).1.history.take k) -
        μ (queryTrajectory q g ξ t)) ≤ 8 * σ + 24 * q.L * k / t := by
  classical
  rw [blockTrace_window_eq q g ξ hk]
  apply medianCenter_of_bad_count
    (fun i : Fin k => primaryReply q g ξ (preload q + t - 1 - 1 - i))
    (fun i => decide (8 * σ < dualNorm
      (primaryReply q g ξ (preload q + t - 1 - 1 - i) -
        μ (blockQuery q g ξ (preload q + t - 1 - 1 - i)))))
  · positivity
  · intro i hi
    simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_lt] at hi
    let j := preload q + t - 1 - 1 - i.val
    have hjt : j + 1 - preload q ≤ t := by dsimp [j]; omega
    have hjk : t - k ≤ j + 1 - preload q := by dsimp [j]; omega
    have hd := window_trajectory_distance (queryTrajectory q g ξ)
      (queryTrajectory_distance q g ξ) ht hjt hjk
    have hm := hsmooth (blockQuery q g ξ j) (queryTrajectory q g ξ t)
    rw [blockQuery_eq_trajectory q g ξ j, oneNorm_sub_comm] at hm
    have hmul := mul_le_mul_of_nonneg_left hd hL
    have htri := dualNorm_sub_triangle (primaryReply q g ξ j)
      (μ (blockQuery q g ξ j)) (μ (queryTrajectory q g ξ t))
    have he : q.L * (24 * (k : ℝ) / t) = 24 * q.L * k / t := by ring
    rw [he] at hmul
    have hm' := hm.trans hmul
    rw [← blockQuery_eq_trajectory q g ξ j] at hm'
    exact htri.trans (add_le_add hi hm')
  · simpa only [decide_eq_true_eq] using hbad

lemma median_history_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (hL : 0 ≤ q.L)
    (hsmooth : ∀ x y, dualNorm (μ x - μ y) ≤ q.L * oneNorm (x.val - y.val))
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    {t k : ℕ} (ht : 0 < t) (hk : k ≤ preload q + t - 1) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 8 * σ + 24 * q.L * k / t < dualNorm
        (medianCenter ((StochasticGeneralized.blockTrace (analysisCost q)
          (blockUpdate q g) (initialState q) ξ (preload q + t - 1)).1.history.take k) -
          μ (queryTrajectory q g ξ t))} ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) / 8)) := by
  apply le_trans (measure_mono ?_)
    (window_noise_majority_failure q hg hμ hσ hp hi hm (preload q + t - 1) k hk)
  intro ξ hξ
  change (k : ℝ) / 2 ≤ _
  by_contra hb
  have ha := median_history_accuracy q g μ hL hsmooth hσ ξ ht hk (lt_of_not_ge hb)
  exact (not_lt_of_ge ha) hξ

lemma rolling_median_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
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
      {ξ | 8 * σ + 24 * q.L * window q t / t < dualNorm
        (medianCenter ((StochasticGeneralized.blockTrace (analysisCost q)
          (blockUpdate q g) (initialState q) ξ (preload q + t - 1)).1.history.take (window q t)) -
          μ (queryTrajectory q g ξ t))} ≤
        ENNReal.ofReal (Real.exp (-confidence q) / ((t : ℝ) * (t + 1))) := by
  have hk : window q t ≤ preload q + t - 1 := by
    have h := window_history_bound q hH (t - 1)
    simpa only [Nat.sub_add_cancel ht, Nat.add_sub_assoc ht] using h
  exact (median_history_failure q hg hμ hL hsmooth hσ hp hi hm ht hk).trans
    (ENNReal.ofReal_le_ofReal (window_failure_bound q (by linarith) ht))

lemma reciprocal_window_sum (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / (((i : ℝ) + 1) * (i + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp; ring

lemma finite_window_union {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (H : ℝ) (N : ℕ)
    (hb : ∀ i < N, P (E i) ≤ ENNReal.ofReal
      (Real.exp (-H) / (((i : ℝ) + 1) * (i + 2)))) :
    P (⋃ i ∈ Finset.range N, E i) ≤ ENNReal.ofReal (Real.exp (-H)) := by
  apply (measure_biUnion_finset_le (Finset.range N) E).trans
  calc
    ∑ i ∈ Finset.range N, P (E i) ≤ ∑ i ∈ Finset.range N,
        ENNReal.ofReal (Real.exp (-H) / (((i : ℝ) + 1) * (i + 2))) := by
      exact Finset.sum_le_sum (fun i hi => hb i (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal (Real.exp (-H) * (1 - 1 / ((N : ℝ) + 1))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      congr 1
      simpa only [one_div, one_mul] using reciprocal_window_sum N
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hp : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      nlinarith [Real.exp_pos (-H)]

end OracleTemplate.AdaptiveHeavyTailSimplex
