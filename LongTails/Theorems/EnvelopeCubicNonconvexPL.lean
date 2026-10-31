import LongTails.Setups.NonconvexPLSecondOrder
import LongTails.Proofs.PLMinimaxConvergence
import LongTails.Proofs.PLMinimaxBudget

namespace OracleTemplate.PLMinimax.EnvelopeCubicNonconvexPL

open LongTails.Setups.NonconvexPLSecondOrder

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈10000000000 * (1 + p.L / p.μ + p.Δ * Real.sqrt p.ρ * (p.L / p.μ) ^ (3 / 4 : ℝ) / p.ε ^ (3 / 2 : ℝ) + p.Δ * p.ρ ^ 2 / p.μ ^ 3) * Real.log (2 + p.L / p.μ + p.ρ ^ 2 * (p.Δ + p.D) / p.μ ^ 3 + p.ρ * p.ε / p.μ ^ 2 + p.μ ^ 2 / (p.ρ * p.ε)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.NonconvexPLSecondOrder.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨method, ?_, fun _ _ => trivial⟩
  intro p hv f oracle hf
  have hd := setup_value_twice_differentiable hv hf
  refine ⟨hd.1, hd.2, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, seed⟩
  have hK := (explicit_execution_budget hv).trans (Nat.le_ceil _)
  exact output_accuracy_of_budget hv hf (budget p 0) hK seed

end OracleTemplate.PLMinimax.EnvelopeCubicNonconvexPL
