import LongTails.Setups.StochasticProximalEf21
import LongTails.Algorithms.ProximalEf21Homotopy
import LongTails.Proofs.ProximalEf21Execution

noncomputable section

namespace LongTails.Theorems.ProximalEf21Homotopy

noncomputable def budget : (let S := LongTails.Setups.StochasticProximalEf21.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 3 then 0 else if i = 0 then ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 + (1 / p.δ + p.σ ^ 2 / (p.L ^ 2 * p.R ^ 2)) * Real.log (2 + p.H / (p.L * p.R ^ 2)))⌉₊ else ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + Real.log (2 + p.H / (p.L * p.R ^ 2)) / p.δ)⌉₊

theorem result : OracleTemplate.Convergence
    LongTails.Setups.StochasticProximalEf21.spec budget := by
  refine ⟨LongTails.Algorithms.ProximalEf21Homotopy.make, ?_, ?_⟩
  · intro p hp I O hO
    rcases hO with ⟨hg, ho⟩
    change LongTails.Setups.StochasticProximalEf21.spec.successful p I
      (fun ω : LongTails.Setups.StochasticProximalEf21.Randomness p O =>
        LongTails.Algorithms.ProximalEf21Homotopy.outputWithCounts p O
          (LongTails.Proofs.ProximalEf21BudgetBridge.budget p) ω.1 ω.2)
      ((p.initialLaw).prod O.law)
    exact LongTails.Proofs.ProximalEf21Execution.execute_success O hp hg ho
  · intro p hp
    rfl

end LongTails.Theorems.ProximalEf21Homotopy
