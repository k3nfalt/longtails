import LongTails.Setups.BirchSgd
import LongTails.Proofs.BirchSgdConvergence

namespace OracleTemplate.BirchSgd
open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.BirchSgd.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.branch ⌈4 * (p.R + 1) * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.BirchSgd.spec budget := by
  refine ⟨OracleTemplate.BirchSgd.birch, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.BirchSgd.birch_success p hp I O hO

end OracleTemplate.BirchSgd
