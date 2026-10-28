import LongTails.Setups.RingmasterIterations
import LongTails.Proofs.RingmasterExecution

namespace OracleTemplate.RingmasterIterations
open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.RingmasterIterations.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈8 * p.R * p.L * p.Δ / p.ε + 16 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.RingmasterIterations.spec budget := by
  refine ⟨OracleTemplate.RingmasterAsgd.ringmasterPoint, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.RingmasterAsgd.iterations_success p hp I O hO

end OracleTemplate.RingmasterIterations
