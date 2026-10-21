import outputs.Setups.RennalaIterations
import outputs.Proofs.SingleOracleCounted
import outputs.Proofs.IterationConvergence

namespace OracleTemplate.RennalaIterations

noncomputable def budget : outputs.Setups.RennalaIterations.spec.Params → Fin outputs.Setups.RennalaIterations.spec.numOracles → ℕ := fun p _ => max 1 ⌈24 * p.Delta * p.L / p.eps⌉₊ + p.extra

theorem result : Convergence outputs.Setups.RennalaIterations.spec budget := by
  classical
  refine ⟨BatchIterations.algorithm, ?_, ?_⟩
  · intro p hp I O hO
    exact execution_success p hp I O hO
  · intro p hp
    rfl

end OracleTemplate.RennalaIterations
