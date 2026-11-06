import LongTails.Setups.StochasticConstrainedQuasar
import LongTails.Proofs.StochasticQuasarSpecification
import LongTails.Proofs.StochasticQuasarBudgetCost

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(2 : ℝ) ^ 96 * (2 + ⌈8 * Real.log (8 / q.δ)⌉₊) * (1 + Nat.clog 2 ⌈2 + q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε)⌉₊) ^ 2 * (1 + Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ + q.σ ^ 2 * q.D ^ 2 / (q.γ ^ 2 * q.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.StochasticConstrainedQuasar.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hv I O hO
  apply successful_execution q hv I O hO (budget q)
  intro seed i
  apply (Nat.cast_le (α := ℝ)).mp
  apply (program_cost_bound hv seed).trans
  simpa only [budget, outerOrder, complexityLog, complexityScale, rateScale, noiseScale, Nat.cast_add, Nat.cast_ofNat] using
    (Nat.le_ceil ((2 : ℝ) ^ 96 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q))

end OracleTemplate.StochasticQuasar
