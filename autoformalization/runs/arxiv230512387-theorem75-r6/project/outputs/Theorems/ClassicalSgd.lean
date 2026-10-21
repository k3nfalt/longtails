import outputs.Setups.ClassicalSgd
import outputs.Proofs.SingleOracleCounted
import outputs.Proofs.IterationConvergence

namespace OracleTemplate.ClassicalSgd

noncomputable def budget : outputs.Setups.ClassicalSgd.spec.Params → Fin outputs.Setups.ClassicalSgd.spec.numOracles → ℕ := fun p _ => max 1 ⌈4 * p.Delta * p.L / p.eps + 8 * p.Delta * p.L * p.v / p.eps ^ 2⌉₊ + p.extra

theorem result : Convergence outputs.Setups.ClassicalSgd.spec budget := by
  classical
  refine ⟨BatchIterations.algorithm, ?_, ?_⟩
  · intro p hp I O hO
    exact execution_success p hp I O hO
  · intro p hp
    rfl

end OracleTemplate.ClassicalSgd
