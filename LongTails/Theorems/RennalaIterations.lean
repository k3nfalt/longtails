import LongTails.Setups.RennalaIterations
import LongTails.Proofs.SingleOracleCounted
import LongTails.Proofs.IterationConvergence

namespace OracleTemplate.RennalaIterations

noncomputable def budget : (let S := LongTails.Setups.RennalaIterations.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈24 * p.Delta * p.L / p.eps⌉₊ + p.extra

theorem result : Convergence LongTails.Setups.RennalaIterations.spec budget := by
  classical
  refine ⟨BatchIterations.algorithm, ?_, ?_⟩
  · intro p hp I O hO
    exact execution_success p hp I O hO
  · intro p hp
    rfl

end OracleTemplate.RennalaIterations
