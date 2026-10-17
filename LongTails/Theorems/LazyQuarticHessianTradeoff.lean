import LongTails.Setups.ThirdDerivativeSmoothNonconvex
import LongTails.Algorithms.LazyQuarticMetric
import LongTails.Proofs.LazyQuarticBudget

namespace LongTails.Theorems.LazyQuarticHessianTradeoff

open OracleTemplate MeasureTheory
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.LazyQuarticConvergence

noncomputable def budget : (let S := LongTails.Setups.ThirdDerivativeSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 0 then ⌈2 ^ 90 * (1 + p.Δ ^ (5 / 4 : ℝ) * p.L₃ ^ (5 / 12 : ℝ) / p.ε ^ (5 / 3 : ℝ)) * Real.log (2 + p.H₀ * p.Δ / p.ε ^ 2 + p.L₃ * p.Δ ^ 3 / p.ε ^ 4)⌉₊ else ⌈2 ^ 62 * (1 + p.Δ ^ (3 / 4 : ℝ) * p.L₃ ^ (1 / 4 : ℝ) / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.ThirdDerivativeSmoothNonconvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  obtain ⟨hf, hT, hgap, hH₀, hg, hH⟩ := hO
  let h : LongTails.Proofs.LazyQuarticTransition.Data p f := ⟨hp, hf, hT, hgap, hH₀⟩
  have hanswer : ∀ k q seed, O.answer k q seed = replies p f q := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simpa [replies] using hg k x seed
    · simpa [replies] using hH k x seed
  have hbudget (i : Fin 2) : LongTails.Proofs.EnergyHessianExecution.counts
      (replies p f) (plan p) i ≤ budget p i := by
    fin_cases i
    · simpa [budget, logarithmArgument] using
        LongTails.Proofs.LazyQuarticBudget.ordinary_calls p f hp
    · simpa [budget] using
        LongTails.Proofs.LazyQuarticBudget.hessian_calls p f h
  apply Filter.Eventually.of_forall
  intro seed
  change ‖gradient f (execute O (algorithm p) (budget p) seed.1 seed.2)‖ ≤ p.ε
  simp only [algorithm]
  rw [LongTails.Proofs.EnergyHessianExecution.execute_of_counts
    (replies p f) (0, p.x0) p.x0 (plan p) O (budget p) hanswer hbudget seed.1 seed.2]
  exact plan_accuracy p f h

end LongTails.Theorems.LazyQuarticHessianTradeoff
