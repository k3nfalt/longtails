import LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.RobustGeneralizedConvergence
import LongTails.Proofs.RobustGeneralizedOutput

open MeasureTheory

namespace OracleTemplate.RobustGeneralized.FiniteVarianceGeneralizedAcceleratedConvex

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2^22*(1+Real.sqrt (p.L0*p.R^2/p.ε)+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))+2^47*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)^2/p.ε^2)*Real.log (Real.exp 1*(1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)⌉₊

theorem result : Convergence LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  rcases hadm with ⟨g, μ, P, hIID, rfl, hc, hg, hdiff, hH, ⟨u, hmin, hdist, hgap⟩, ho⟩
  refine ⟨measurable_execute_output p P ho.measurable (budget p 0), u, hmin, ?_⟩
  apply execution_high_probability p hp hc hg hdiff hH u hmin hdist hgap μ P hIID ho (budget p 0)
  exact public_budget_ge p

end OracleTemplate.RobustGeneralized.FiniteVarianceGeneralizedAcceleratedConvex
