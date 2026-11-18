import LongTails.Setups.SublevelPLBoundedVariance
import LongTails.Proofs.SublevelWeightedResult

namespace OracleTemplate.SublevelPLWeightedGradient

open LongTails.Setups.SublevelPLBoundedVariance

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈110000 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α) * (1 + p.σ ^ 2 * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α))⌉₊

theorem result : Convergence LongTails.Setups.SublevelPLBoundedVariance.spec budget := by
  refine ⟨SublevelWeighted.method, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  exact SublevelWeighted.execution_success p hp f O hadm (budget p 0) (fun _ => le_rfl)

end OracleTemplate.SublevelPLWeightedGradient
