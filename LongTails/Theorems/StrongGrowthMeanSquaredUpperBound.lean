import LongTails.Setups.EuclideanStrongGrowthMeanSquared
import LongTails.Proofs.StrongGrowthMeanSquaredInclusion

namespace LongTails.Theorems.StrongGrowthMeanSquaredUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.EuclideanStrongGrowthMeanSquared.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈Real.sqrt (2 * q.Lbar * q.R ^ 2 / ((1 + q.Γ) * q.ε))⌉₊ * ⌈(1 + q.Γ) ^ 2 * (4810 + 3200 * Real.log (1 + q.Γ))⌉₊

theorem result : Convergence LongTails.Setups.EuclideanStrongGrowthMeanSquared.spec budget :=
  LongTails.Proofs.StrongGrowthMeanSquaredInclusion.transfer (fun q => budget q 0) (fun _ _ => rfl)

end LongTails.Theorems.StrongGrowthMeanSquaredUpperBound
