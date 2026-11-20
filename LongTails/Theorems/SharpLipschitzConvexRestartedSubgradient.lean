import LongTails.Setups.SharpLipschitzConvex
import LongTails.Proofs.RestartedSubgradient

namespace LongTails.Theorems.SharpLipschitzConvexRestartedSubgradient

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.SharpLipschitzConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈4 * p.L ^ 2 / p.μ ^ 2⌉₊ * (Nat.clog 2 ⌈p.μ * p.D / p.ε⌉₊ + 1)

theorem result : Convergence LongTails.Setups.SharpLipschitzConvex.spec budget := by
  refine ⟨fun p => restartedSubgradient p.L p.D (LongTails.Proofs.RestartedSubgradient.phaseLength p) p.x0,
    fun p hp f O hadm => ?_, fun _ _ => trivial⟩
  exact LongTails.Proofs.RestartedSubgradient.convergence p hp f O hadm

end LongTails.Theorems.SharpLipschitzConvexRestartedSubgradient
