import LongTails.Setups.HessianLipschitzTemporalDiscrepancy
import LongTails.Proofs.Execution
import LongTails.Proofs.NonlinearTemporalRate
import LongTails.Proofs.NonlinearTemporalBudget

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => if p.Δ ≤ p.ε then 0 else ⌈10 ^ 9 * (Real.sqrt (p.L / p.μ) * (1 + p.M * p.D / p.μ ^ 2) + p.D / Real.sqrt (p.μ * p.ε) + 1) * Real.log (2 + p.Δ / p.ε + p.M ^ 2 * p.Δ / p.μ ^ 3)⌉₊

theorem result : Convergence LongTails.Setups.HessianLipschitzTemporalDiscrepancy.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨nonlinearTemporalAccelerated, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  obtain ⟨hf, hs, hlip, hH, ⟨e, hO, he⟩, u, hmin, hgap⟩ := ho
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · let Good (A : Algorithm p.E p.E p.E) : Prop :=
      ∀ seed : A.Seed × ((k : ℕ) → O.Seed k),
        f (execute O A (fun _ => (budget p 0)) seed.1 seed.2) - f u ≤ p.ε
    change Good (nonlinearTemporalAccelerated p)
    by_cases hεΔ : p.Δ ≤ p.ε
    · rw [nonlinearTemporalAccelerated, ite_eq_left hεΔ]
      rintro ⟨seed, ξ⟩
      rw [show budget p 0 = 0 by simp only [budget, ite_eq_left hεΔ], StochasticGradient.execute_advance]
      exact hgap.trans hεΔ
    · have hK := execution_budget_bound p hp (lt_of_not_ge hεΔ)
      rw [nonlinearTemporalAccelerated, ite_eq_right hεΔ]
      rintro ⟨seed, ξ⟩
      apply execute_twoPhase_accuracy p hp (lt_of_not_ge hεΔ) f hf hs hlip hH u hmin hgap O e hO he
      simpa only [budget, ite_eq_right hεΔ] using hK

end OracleTemplate.NonlinearTemporalDiscrepancy
