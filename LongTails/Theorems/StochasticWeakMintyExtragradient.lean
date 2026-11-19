import LongTails.Setups.StochasticWeakMinty
import LongTails.Proofs.MinibatchExtragradientRun

namespace LongTails.Theorems.StochasticWeakMintyExtragradient

open OracleTemplate LongTails.Proofs.MinibatchExtragradientRun

noncomputable def budget : (let S := LongTails.Setups.StochasticWeakMinty.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 19 * (1 + q.L ^ 2 * q.R ^ 2 / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.StochasticWeakMinty.spec budget := by
  refine ⟨minibatchAlgorithm, ?_, fun _ _ => trivial⟩
  intro q hq F O had
  exact success q hq F O had

end LongTails.Theorems.StochasticWeakMintyExtragradient
