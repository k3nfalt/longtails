import LongTails.Setups.HigherSmoothBilevel
import LongTails.Proofs.BilevelConvergence
import LongTails.Proofs.BilevelBudget

namespace OracleTemplate.BilevelFirstOrderCurvature

open LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated
open LongTails.Proofs.BilevelConvergence LongTails.Proofs.BilevelBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 40 * (p.L * (p.L / p.μ) ^ 3 / p.ε) ^ ((1 : ℝ) / 4) * (1 + p.Δ * Real.sqrt (p.L * (p.L / p.μ) ^ 4 / p.ε ^ 3)) * Real.log (2 * (p.L / p.μ) * (1 + p.L / p.ε) * (1 + p.Δ / p.ε) * (1 + p.G / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.HigherSmoothBilevel.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hv I O ha
  apply Filter.Eventually.of_forall
  intro ω
  exact execute_accuracy hv ha (budget p 0) (fun hs => oracle_cost_bound hv hs) ω.1 ω.2

end OracleTemplate.BilevelFirstOrderCurvature
