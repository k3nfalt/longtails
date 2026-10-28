import LongTails.Setups.BirchLocalSgd
import LongTails.Proofs.BirchMethodsConvergence

namespace OracleTemplate.BirchLocalSgd
open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.BirchLocalSgd.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * ⌈4 * p.B * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.BirchLocalSgd.spec budget := by
  refine ⟨OracleTemplate.BirchSgd.birch, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.BirchMethods.local_success p hp I O hO

end OracleTemplate.BirchLocalSgd
