import LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.CoarseGeneralizedConvergence
import LongTails.Proofs.CoarseGeneralizedBudget

open MeasureTheory

namespace OracleTemplate.CoarseGeneralized.FiniteVarianceGeneralizedRadiusAcceleratedConvex

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2^70*(1+p.L1*p.R+Real.sqrt (p.L0*p.R^2/p.ε)+p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1*(2+p.L0*p.R^2/p.ε+p.L1*p.R+p.σ*p.R/p.ε)/p.δ)^3⌉₊

theorem result : Convergence LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  rcases hadm with ⟨g, μ, P, hIID, rfl, hc, hf, hg, hH, ⟨u, hmin, hdist, _⟩, ho⟩
  refine ⟨measurable_execute_output p P ho.measurable (budget p 0), u, hmin, ?_⟩
  have hb := simplified_budget_suffices p hp
  change warmCost p ≤ budget p 0 ∧ ∀ x : p.E,
    (4194304 * RobustGeneralized.shape (restartParams p x) +
      140737488355328 * (p.σ ^ 2 * p.R ^ 2 * RobustGeneralized.confidence (restartParams p x) ^ 2 / p.ε ^ 2)) *
      RobustGeneralized.logScale (restartParams p x) ≤ (budget p 0 - warmCost p : ℕ) at hb
  have hh := execution_high_probability p hp hc hf hg hH u hmin hdist μ P hIID ho
    (budget p 0 - warmCost p) hb.2
  rwa [Nat.add_sub_of_le hb.1] at hh

end OracleTemplate.CoarseGeneralized.FiniteVarianceGeneralizedRadiusAcceleratedConvex
