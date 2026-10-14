import LongTails.Algorithms.GapStrongGrowthAccelerated
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

open StochasticGradient (advance execute_advance)
open HeavyTailedMarkovGradient (advance_add)

noncomputable def rawAdvance (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : State p.E) : State p.E :=
  advance (fun k state => (algorithm p).update state (g (((algorithm p).query state).2) (ξ k))) n call s

lemma rawAdvance_add (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n m call : ℕ) (s : State p.E) :
    rawAdvance p g ξ (n + m) call s =
      rawAdvance p g ξ m (call + n) (rawAdvance p g ξ n call s) := advance_add _ _ _ _ _

lemma rawAdvance_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call j : ℕ) (s : p.E × p.E) (hj : j < batchSize p) :
    rawAdvance p g ξ j call (n, s, 0, 0) =
      (n, s, j, ∑ i ∈ Finset.range j, g (queryPoint p n s) (ξ (call + i))) := by
  induction j with
  | zero => simp [rawAdvance, advance]
  | succ j ih =>
    rw [show j + 1 = j + 1 from rfl, rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ite_true, Finset.sum_range_succ]

lemma rawAdvance_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : p.E × p.E) (hb : 0 < batchSize p) :
    rawAdvance p g ξ (batchSize p) call (n, s, 0, 0) =
      (n + 1, step p n s (StochasticGeneralized.batchReply g (queryPoint p n s)
        (fun i : Fin (batchSize p) => ξ (call + i))), 0, 0) := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have hbj : batchSize p = j + 1 := hj
  rw [hbj, rawAdvance_add, rawAdvance_prefix p g ξ n call j s (by omega)]
  simp only [rawAdvance, advance, algorithm, ← hbj, lt_self_iff_false, ite_false]
  congr 2
  unfold StochasticGeneralized.batchReply
  rw [hbj, ← Finset.sum_range_succ, Finset.sum_range]

lemma rawAdvance_run (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (hb : 0 < batchSize p) (n : ℕ) :
    rawAdvance p g ξ (n * batchSize p) 0 (0, (p.x0, p.x0), 0, 0) =
      (n, run p g (fun k i => ξ (k * batchSize p + i)) n, 0, 0) := by
  induction n with
  | zero => simp [rawAdvance, advance, run]
  | succ n ih =>
    rw [Nat.succ_mul, rawAdvance_add, ih, Nat.zero_add, rawAdvance_block p g ξ n _ _ hb]
    rfl

lemma execute_run (p : Params) (g : p.E → p.Ω → p.E)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω)) (ξ : ℕ → p.Ω)
    (hb : 0 < batchSize p) (n : ℕ) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm p) (fun _ => (n * batchSize p)) () ξ =
      (run p g (fun k i => ξ (k * batchSize p + i)) n).1 := by
  erw [execute_advance]
  change (algorithm p).output (rawAdvance p g ξ (n * batchSize p) 0
    (0, (p.x0, p.x0), 0, 0)) = _
  rw [rawAdvance_run p g ξ hb n]
  rfl

end OracleTemplate.GapStrongGrowth
