import LongTails.Setups.AdaptiveHeavyTailSimplex
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveEntropicConvergence

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈256 * Real.log (100 / p.δ) + 67108864 * Real.sqrt (p.L * (Real.log (2 * (p.d : ℝ)) + Real.log (100 / p.δ)) / p.ε * (Real.log (100 / p.δ) + Real.log (2 + p.L * (Real.log (2 * (p.d : ℝ)) + Real.log (100 / p.δ)) / p.ε))) + 4 * (Real.log (2 * (p.d : ℝ)) + Real.log (100 / p.δ)) * (274877906944 * p.σ / p.ε) ^ (p.p / (p.p - 1))⌉₊

theorem result : Convergence LongTails.Setups.AdaptiveHeavyTailSimplex.spec budget := by
  apply convergence_of_call_budget (fun p => budget p 0)
  intro p hp
  exact Nat.le_ceil _

end OracleTemplate.AdaptiveHeavyTailSimplex
