import LongTails.Setups.ThirdDerivativeSmoothNonconvex
import LongTails.Algorithms.LogFreeProxNewton
import LongTails.Proofs.LogFreeBudget

namespace LongTails.Theorems.LogFreeSecondOrderThirdSmooth

open OracleTemplate MeasureTheory
open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeExecution LongTails.Proofs.LogFreeTransition
  LongTails.Proofs.LogFreeInvariant LongTails.Proofs.LogFreeBudget

noncomputable def budget : (let S := LongTails.Setups.ThirdDerivativeSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 30 * (1 + p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ) + Real.log (2 + p.H₀ * p.Δ / p.ε ^ 2 + p.L₃ * p.Δ ^ 3 / p.ε ^ 4))⌉₊

theorem result : Convergence LongTails.Setups.ThirdDerivativeSmoothNonconvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  obtain ⟨hf, hT, hgap, hH₀, hg, hH⟩ := hO
  have ha : Admissible p f := ⟨hf, hT, hgap, hH₀⟩
  have hanswer : ∀ k q seed, O.answer k q seed = replies p f q := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simpa [replies] using hg k x seed
    · simpa [replies] using hH k x seed
  have hbudget (i : Fin 2) : LongTails.Proofs.EnergyHessianExecution.counts
      (replies p f) (plan p) i ≤ budget p i := plan_budget p hp (replies p f) i
  apply Filter.Eventually.of_forall
  intro seed
  change ‖gradient f (execute O (algorithm p) (budget p) seed.1 seed.2)‖ ≤ p.ε
  simp only [algorithm]
  rw [LongTails.Proofs.EnergyHessianExecution.execute_of_counts
    (replies p f) (0, p.x0) p.x0 (plan p) O (budget p) hanswer hbudget seed.1 seed.2]
  exact plan_accuracy p f hp ha

end LongTails.Theorems.LogFreeSecondOrderThirdSmooth
