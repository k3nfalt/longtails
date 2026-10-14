import LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveRobustGeneralizedPublic
import LongTails.Proofs.AdaptiveRobustGeneralizedOutput

open MeasureTheory

namespace OracleTemplate.RobustGeneralized.AdaptiveRobustGeneralizedAcceleratedConvex

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open AdaptiveRobustGeneralized (algorithm inflate inflate_valid inflate_smooth
  measurable_execute_output execution_high_probability public_budget_ge)

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2^21*(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))+2^40*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)+2^48*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)^2/Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))+2^21*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)*(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))/Real.log (Real.exp 1+(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))*Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))/(2^26*(p.σ^2*p.R^2/p.ε^2)*Real.log (Real.exp 1/p.δ)^2+(1+Real.sqrt (p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))*Real.sqrt (1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2)))*Real.exp (-28*Real.log (Real.exp 1*(1+(p.L0*p.R^2/p.ε+Real.log (Real.exp 1/p.δ)^2*(p.σ^2*p.R^2/p.ε^2))+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ))))⌉₊

theorem result : Convergence LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => algorithm (inflate p), ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  rcases hadm with ⟨g, μ, P, hIID, rfl, hc, hg, hdiff, hH, ⟨u, hmin, hdist, hgap⟩, ho⟩
  have hp' := inflate_valid p hp
  have hH' := inflate_smooth p hp.2.2.2.2.2.1 hH
  refine ⟨measurable_execute_output (inflate p) P ho.measurable (budget p 0), u, hmin, ?_⟩
  apply execution_high_probability (inflate p) hp' hc hg hdiff hH' u hmin hdist hgap μ P hIID ho (budget p 0)
  exact public_budget_ge p hp

end OracleTemplate.RobustGeneralized.AdaptiveRobustGeneralizedAcceleratedConvex
