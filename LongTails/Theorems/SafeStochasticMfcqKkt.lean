import LongTails.Setups.StochasticMfcqInequalities
import LongTails.Algorithms.StochasticMfcq
import LongTails.Proofs.StochasticMfcqGuarantee
import LongTails.Proofs.StochasticMfcqBudget

namespace LongTails.Theorems.SafeStochasticMfcqKkt

open OracleTemplate
open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcq

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈3500 * (1600 * p.H ^ 2 * p.σ ^ 2 / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2) + (2 + 3200 * p.H ^ 3 * p.Δ / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2)) * (1 + 40 * p.σ * p.L / (p.μ * min p.ε (min 1 p.τ))))⌉₊ * (1 + ⌈Real.log ((2 + 3200 * p.H ^ 3 * p.Δ / (p.μ ^ 2 * (min p.ε (min 1 p.τ)) ^ 2)) / p.ρ) / Real.log 4⌉₊)

theorem result : Convergence LongTails.Setups.StochasticMfcqInequalities.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I O hadm
    exact LongTails.Proofs.StochasticMfcqGuarantee.execution_success p hp I O hadm _
      (LongTails.Proofs.StochasticMfcqBudget.explicit_call_budget p hp)
  · intro p hp
    trivial

end LongTails.Theorems.SafeStochasticMfcqKkt
