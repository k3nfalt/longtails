import LongTails.Setups.GradientDependentHessian
import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Proofs.EnergyHessianConvergence
import LongTails.Proofs.EnergyHessianBudget

namespace LongTails.Theorems.EnergyHessianReuse

open OracleTemplate MeasureTheory
open LongTails.Setups.GradientDependentHessian
open LongTails.Algorithms.EnergyHessianReuse

noncomputable def budget : (let S := LongTails.Setups.GradientDependentHessian.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => ⌈Real.log (1 + p.L₁ * p.G₀ / (p.m * p.L₀)) / Real.log (4 / 3)⌉₊ + if i = 0 then ⌈27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) + 15000 * p.Δ * Real.sqrt (p.m * p.L₁) / p.ε⌉₊ + p.m + 74 else ⌈54000 * p.Δ * Real.sqrt (p.L₀ / p.m) / (p.ε * Real.sqrt p.ε) + 30000 * p.Δ * Real.sqrt (p.L₁ / p.m) / p.ε⌉₊ + 146

theorem result : Convergence LongTails.Setups.GradientDependentHessian.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hv f O hO
  obtain ⟨hf, hT, hgap, hG, hgrad, hH⟩ := hO
  have hanswer : ∀ k q seed, O.answer k q seed =
      LongTails.Proofs.EnergyHessianExecution.replies p f q := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simpa [LongTails.Proofs.EnergyHessianExecution.replies] using hgrad k x seed
    · simpa [LongTails.Proofs.EnergyHessianExecution.replies] using hH k x seed
  have hbudget (i : Fin 2) : LongTails.Proofs.EnergyHessianExecution.counts
      (LongTails.Proofs.EnergyHessianExecution.replies p f) (plan p) i ≤ budget p i := by
    simpa only [budget, burnCount] using
      LongTails.Proofs.EnergyHessianBudget.counts_sufficient p
        (LongTails.Proofs.EnergyHessianExecution.replies p f) hv i
  apply Filter.Eventually.of_forall
  intro seed
  change ‖gradient f (execute O (algorithm p) (budget p) seed.1 seed.2)‖ ≤ p.ε
  simp only [algorithm]
  rw [LongTails.Proofs.EnergyHessianExecution.execute_of_counts
    (LongTails.Proofs.EnergyHessianExecution.replies p f) (0, p.x0) p.x0 (plan p)
    O (budget p) hanswer hbudget seed.1 seed.2]
  exact LongTails.Proofs.EnergyHessianConvergence.plan_accuracy p f hv hf hT hgap hG

end LongTails.Theorems.EnergyHessianReuse
