import LongTails.Setups.ScalarHolderStochastic
import LongTails.Proofs.Execution
import LongTails.Proofs.ScalarHolderBudget

open MeasureTheory

namespace OracleTemplate.ScalarHolderStochastic

open LongTails.Setups.ScalarHolderStochastic

open ScalarHolderSearch

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(2 : ℝ) ^ (200 / (q.p - 1)) * (1 + 1 / q.ν) * (1 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε + (q.σ / q.ε) ^ (q.p / (q.p - 1)) * Real.log (2 + q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε))⌉₊

theorem result : Convergence LongTails.Setups.ScalarHolderStochastic.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  rcases hadm with ⟨oracle, μ, P, hIID, rfl, hderiv, hholder, ⟨lower, hlower, hgap⟩, ho⟩
  have hK : executionCalls q ≤ budget q 0 := executionCalls_le_publicBudget q hq
  exact execution_successful q hq μ P hIID ho hderiv hholder hlower hgap (budget q 0) hK

end OracleTemplate.ScalarHolderStochastic
