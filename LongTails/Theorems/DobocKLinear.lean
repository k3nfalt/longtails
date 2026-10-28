import LongTails.Setups.DobocK
import LongTails.Proofs.DobocKConvergence

namespace OracleTemplate.DobocKLinear

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.DobocK.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 * (p.M + 2 / p.lam) * (1 + (p.M + 2 / p.lam) + (p.M + 2 / p.lam) ^ 2 * (p.K : ℝ) ^ 2 / p.m + Real.sqrt ((p.M + 2 / p.lam) ^ 4 * (2 * (p.M + 2 / p.lam)) ^ (3 / 2 : ℝ) * (p.K : ℝ) ^ 3 * p.L * Real.sqrt p.Δ / (6 * p.m ^ 5))) / p.m ^ 2 * Real.log (max 1 (p.Δ / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.DobocK.spec budget := by
  refine ⟨OracleTemplate.DobocKTuning.algorithm, ?_, ?_⟩
  · intro p hp f O hadm
    dsimp only
    intro ω
    exact OracleTemplate.DobocKTuning.execution_accuracy p hp f O hadm ω.1 ω.2
  · intro p hp
    rfl

end OracleTemplate.DobocKLinear
