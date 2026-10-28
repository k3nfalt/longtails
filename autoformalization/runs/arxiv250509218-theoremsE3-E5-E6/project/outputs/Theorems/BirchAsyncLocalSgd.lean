import outputs.Setups.BirchAsyncLocalSgd
import outputs.Proofs.BirchMethodsConvergence

namespace OracleTemplate.BirchAsyncLocalSgd
open OracleTemplate

noncomputable def budget : (let S := outputs.Setups.BirchAsyncLocalSgd.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * ⌈4 * (p.B + p.M - 1) * p.L * p.Δ / p.ε + 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result : Convergence outputs.Setups.BirchAsyncLocalSgd.spec budget := by
  refine ⟨OracleTemplate.BirchSgd.birch, ?_, fun p _ => rfl⟩
  intro p hp I O hO
  exact OracleTemplate.BirchMethods.async_success p hp I O hO

end OracleTemplate.BirchAsyncLocalSgd
