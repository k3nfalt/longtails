import outputs.Setups.BirchCycleSgd
import outputs.Proofs.BirchMethodsConvergence

namespace OracleTemplate.BirchCycleSgd
open OracleTemplate

noncomputable def budget : (let S := outputs.Setups.BirchCycleSgd.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * ⌈8 * p.n ^ 2 * p.L * p.Δ / (p.s * p.ε) + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence outputs.Setups.BirchCycleSgd.spec budget := by
  refine ⟨OracleTemplate.BirchSgd.birch, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.BirchMethods.cycle_success p hp I O hO

end OracleTemplate.BirchCycleSgd
