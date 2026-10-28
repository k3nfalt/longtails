import LongTails.Setups.RingmasterUniversalTime
import LongTails.Proofs.RingmasterExecution

namespace OracleTemplate.RingmasterUniversalTime
open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.RingmasterUniversalTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈p.σ ^ 2 / p.ε⌉₊ * ⌈48 * p.L * p.Δ / p.ε⌉₊

theorem result : Convergence LongTails.Setups.RingmasterUniversalTime.spec budget := by
  refine ⟨OracleTemplate.RingmasterAsgd.ringmaster, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.RingmasterAsgd.universal_success p hp I O hO

end OracleTemplate.RingmasterUniversalTime
