import LongTails.Setups.ClassicalSgd
import LongTails.Proofs.SingleOracleCounted
import LongTails.Proofs.IterationConvergence

namespace OracleTemplate.ClassicalSgd

noncomputable def budget : (let S := LongTails.Setups.ClassicalSgd.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈4 * p.Delta * p.L / p.eps + 8 * p.Delta * p.L * p.v / p.eps ^ 2⌉₊ + p.extra

theorem result : Convergence LongTails.Setups.ClassicalSgd.spec budget := by
  classical
  refine ⟨BatchIterations.algorithm, ?_, ?_⟩
  · intro p hp I O hO
    exact execution_success p hp I O hO
  · intro p hp
    rfl

end OracleTemplate.ClassicalSgd
