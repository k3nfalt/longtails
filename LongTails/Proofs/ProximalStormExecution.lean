import LongTails.Proofs.ProximalStormProcess
import LongTails.Proofs.SampledQueryPlan

open MeasureTheory

namespace OracleTemplate.ProximalStorm

open OracleTemplate.QueryPlan

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma eval_stormPlan (g : E → Ω → E) (lam eta a : ℝ) (xt : E) (S n0 : ℕ) (ξ : ℕ → Ω) :
    ∀ m t sel, sel = (if S ≤ t then (innerRun g lam eta a xt ξ n0 S).1 else xt) →
      sampledEval (fun q ω => (g q.1 ω, g q.2 ω)) ξ
        (stormPlan lam eta a xt S m (innerRun g lam eta a xt ξ n0 t).1
          (innerRun g lam eta a xt ξ n0 t).2 sel t) (n0 + t + 1) =
        (if S ≤ t + m then (innerRun g lam eta a xt ξ n0 S).1 else xt)
  | 0, t, sel, h => by simp only [stormPlan, sampledEval, Nat.add_zero]; exact h
  | m + 1, t, sel, h => by
      simp only [stormPlan, sampledEval]
      have hstep : innerRun g lam eta a xt ξ n0 (t + 1) =
          ((innerRun g lam eta a xt ξ n0 t).1 - eta • (innerRun g lam eta a xt ξ n0 t).2,
            g ((innerRun g lam eta a xt ξ n0 t).1 - eta • (innerRun g lam eta a xt ξ n0 t).2)
              (ξ (n0 + t + 1)) + (1 / lam) • ((innerRun g lam eta a xt ξ n0 t).1 -
                eta • (innerRun g lam eta a xt ξ n0 t).2 - xt) +
              (1 - a) • ((innerRun g lam eta a xt ξ n0 t).2 -
                (g (innerRun g lam eta a xt ξ n0 t).1 (ξ (n0 + t + 1)) +
                  (1 / lam) • ((innerRun g lam eta a xt ξ n0 t).1 - xt)))) := rfl
      have ih := eval_stormPlan g lam eta a xt S n0 ξ m (t + 1)
        (if t + 1 = S then (innerRun g lam eta a xt ξ n0 (t + 1)).1 else sel) (by
          split_ifs with h1 h2 h2
          · rw [h1]
          · omega
          · rw [h]; split_ifs with h3
            · rfl
            · omega
          · rw [h]; split_ifs with h3
            · omega
            · rfl)
      rw [hstep] at ih
      rw [show n0 + (t + 1) + 1 = n0 + t + 1 + 1 by ring] at ih
      rw [show t + 1 + m = t + (m + 1) by ring] at ih
      exact ih

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma eval_innerPlan (g : E → Ω → E) (lam eta a : ℝ) (L : ℕ) (xt : E) {S : ℕ} (hS : S ≤ L)
    (n0 : ℕ) (ξ : ℕ → Ω) :
    sampledEval (fun q ω => (g q.1 ω, g q.2 ω)) ξ (innerPlan lam eta a L xt S) n0 =
      (innerRun g lam eta a xt ξ n0 S).1 := by
  simp only [innerPlan, sampledEval]
  have h := eval_stormPlan g lam eta a xt S n0 ξ L 0 xt (by
    split_ifs with h0
    · obtain rfl : S = 0 := by omega
      rfl
    · rfl)
  simp only [Nat.add_zero, zero_add] at h
  have h0 : innerRun g lam eta a xt ξ n0 0 = (xt, g xt (ξ n0)) := rfl
  rw [h0] at h
  simp only [h, hS, ite_true]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma eval_batchPlan (g : E → Ω → E) (y : E) (ξ : ℕ → Ω) :
    ∀ m acc call, sampledEval (fun q ω => (g q.1 ω, g q.2 ω)) ξ (batchPlan y m acc) call =
      acc + ∑ i ∈ Finset.range m, g y (ξ (call + i))
  | 0, acc, call => by simp [batchPlan, sampledEval]
  | m + 1, acc, call => by
      simp only [batchPlan, sampledEval]
      rw [eval_batchPlan g y ξ m (acc + g y (ξ call)) (call + 1), Finset.sum_range_succ',
        add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring_nf

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma eval_blockPlan (g : E → Ω → E) (lam eta a : ℝ) (T0 Wm B j : ℕ) (hj : j ≤ Wm) (n : ℕ)
    (o : ℝ × E × E) (ξ : ℕ → Ω) :
    sampledEval (fun q ω => (g q.1 ω, g q.2 ω)) ξ (blockPlan lam eta a (T0 + Wm) B (T0 + j) o) n =
      blockStep g lam eta a T0 (Wm + 1) B j n o ξ := by
  simp only [blockPlan]
  rw [sampledEval_bind, sampledEval_map, eval_innerPlan g lam eta a (T0 + Wm) _ (by omega),
    eval_batchPlan, zero_add]
  simp only [blockStep, batchSum]
  congr 4
  ring_nf

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma eval_fullPlan (g : E → Ω → E) (lam eta a : ℝ) (T0 Wm B : ℕ) (x0 : E) {τ : ℕ → ℕ}
    (hτ : ∀ i, τ i ≤ Wm) (ξ : ℕ → Ω) :
    ∀ m k, sampledEval (fun q ω => (g q.1 ω, g q.2 ω)) ξ
        (fullPlan lam eta a (T0 + Wm) B T0 τ m
          (outerRun g lam eta a T0 (Wm + 1) B x0 τ ξ k) k) (k * (B + (T0 + (Wm + 1)))) =
      outerRun g lam eta a T0 (Wm + 1) B x0 τ ξ (k + m)
  | 0, k => by simp [fullPlan, sampledEval]
  | m + 1, k => by
      simp only [fullPlan]
      rw [sampledEval_bind, eval_blockPlan g lam eta a T0 Wm B (τ k) (hτ k)]
      have h1 : blockStep g lam eta a T0 (Wm + 1) B (τ k) (k * (B + (T0 + (Wm + 1))))
          (outerRun g lam eta a T0 (Wm + 1) B x0 τ ξ k) ξ =
          outerRun g lam eta a T0 (Wm + 1) B x0 τ ξ (k + 1) := rfl
      rw [h1, show k * (B + (T0 + (Wm + 1))) + (B + (T0 + Wm + 1)) =
        (k + 1) * (B + (T0 + (Wm + 1))) by ring, eval_fullPlan g lam eta a T0 Wm B x0 hτ ξ m (k + 1)]
      congr 1; ring

end OracleTemplate.ProximalStorm
