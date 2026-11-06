import LongTails.Setups.StochasticSurjectiveInequalities
import LongTails.Algorithms.SurjectiveProxLinear
import LongTails.Proofs.SurjectiveProxLinearConvergence
import LongTails.Proofs.SurjectiveProxLinearBudget

namespace LongTails.Theorems.SurjectiveStochasticInequalityKkt

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈69 + (2 ^ 29 * p.m ^ 2 * p.H ^ 10 * p.Δ + 2 ^ 44 * p.m ^ 4 * p.H ^ 18 * p.σ ^ 2) / p.ε ^ 2 + 2 ^ 48 * p.m ^ 4 * p.H ^ 19 * p.Δ * p.σ / p.ε ^ 3⌉₊

theorem result : Convergence LongTails.Setups.StochasticSurjectiveInequalities.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I oracle hadm
    exact LongTails.Proofs.SurjectiveProxLinearConvergence.execution_success p hp I oracle hadm _
      (LongTails.Proofs.SurjectiveProxLinearBudget.total_call_budget p hp)
  · intro p hp
    trivial

end LongTails.Theorems.SurjectiveStochasticInequalityKkt
