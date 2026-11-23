import LongTails.TemplateLowerBound
import LongTails.Setups.HighDimensionalSharpLipschitzConvex
import LongTails.Proofs.SharpChainLowerBound

namespace LongTails.Theorems.SharpLipschitzConvexLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalSharpLipschitzConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε)) / 4608⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalSharpLipschitzConvex.spec budget := by
  intro p hp A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact LongTails.Proofs.SharpChainLowerBound.exists_failure p hp (b 0) (hb 0) A

end LongTails.Theorems.SharpLipschitzConvexLowerBound
