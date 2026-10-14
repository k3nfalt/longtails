import LongTails.Proofs.AdaptiveEntropicNoise
import LongTails.Proofs.AdaptiveEntropicCenter

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma selected_noise_accumulated (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (I : Finset ℕ) (N : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (firstScore (selectedNoiseFlag q g μ σ I)) N (initialState q) ξ =
      ∑ j ∈ Finset.range N, if j ∈ I then
        (if 8 * σ < dualNorm (primaryReply q g ξ j - μ (blockQuery q g ξ j))
          then (1 : ℝ) else 0) else 0 := by
  classical
  rw [StochasticGeneralized.accumulated_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ j
  have hc : 0 < analysisCost q tr.1 := by unfold analysisCost; split_ifs <;> norm_num
  have hl : tr.1.history.length = j := (blockTrace_structure q g ξ j).2.1
  change firstScore (selectedNoiseFlag q g μ σ I) (analysisCost q tr.1) tr.1
    (fun i => tr.2 i) = _
  simp only [firstScore, dite_eq_left hc, selectedNoiseFlag, hl, noiseFlag]
  have ht : tr.2 0 = ξ (StochasticGeneralized.blockCalls (analysisCost q)
      (blockUpdate q g) (initialState q) ξ j) := by
    simpa only [Nat.add_zero] using StochasticGeneralized.blockTrace_tail
      (analysisCost q) (blockUpdate q g) (initialState q) ξ j 0
  simp only [ht]
  by_cases h : j ∈ I
  · simp only [ite_eq_left h, one_mul]
    rfl
  · simp [h]

lemma window_noise_accumulated (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (n k : ℕ) (hk : k ≤ n) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (firstScore (selectedNoiseFlag q g μ σ (Finset.Ico (n - k) n))) n (initialState q) ξ =
      ∑ i : Fin k, if 8 * σ < dualNorm (primaryReply q g ξ (n - 1 - i) -
        μ (blockQuery q g ξ (n - 1 - i))) then (1 : ℝ) else 0 := by
  classical
  rw [selected_noise_accumulated, ← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j ∈ Finset.Ico (n - k) n) =
      Finset.Ico (n - k) n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, ← sum_reverse_window _ hk, ← Fin.sum_univ_eq_sum_range]

lemma window_noise_majority_failure (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (n k : ℕ) (hk : k ≤ n) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (k : ℝ) / 2 ≤ ∑ i : Fin k,
        if 8 * σ < dualNorm (primaryReply q g ξ (n - 1 - i) -
          μ (blockQuery q g ξ (n - 1 - i))) then (1 : ℝ) else 0} ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ) / 8)) := by
  have h := selected_noise_majority_failure q hg hμ hσ hp hi hm (Finset.Ico (n - k) n) n
  have hc : (Finset.Ico (n - k) n).card = k := by simp; omega
  simp only [hc, window_noise_accumulated q g μ σ n k hk] at h
  exact h

end OracleTemplate.AdaptiveHeavyTailSimplex
