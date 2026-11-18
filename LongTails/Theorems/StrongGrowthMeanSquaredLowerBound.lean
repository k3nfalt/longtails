import LongTails.TemplateLowerBound
import LongTails.Setups.EuclideanStrongGrowthMeanSquared
import LongTails.Proofs.StrongGrowthMeanSquaredLowerBound

namespace LongTails.Theorems.StrongGrowthMeanSquaredLowerBound

open OracleTemplate LongTails.Proofs.StrongGrowthMeanSquaredLowerBound

noncomputable def budget : (let S := LongTails.Setups.EuclideanStrongGrowthMeanSquared.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊Real.sqrt ((1 + q.Γ ^ 2) * Real.sqrt (1 + q.Γ ^ 2) * q.Lbar * q.R ^ 2 / q.ε) / 8192⌋₊

theorem result : NonConvergence LongTails.Setups.EuclideanStrongGrowthMeanSquared.spec budget := by
  intro q hq A _ b hb
  have hn : (b 0 : ℝ) ≤
      Real.sqrt ((1 + q.Γ ^ 2) * Real.sqrt (1 + q.Γ ^ 2) * q.Lbar * q.R ^ 2 / q.ε) / 8192 := by
    have h1 : (b 0 : ℝ) ≤ (budget q 0 : ℝ) := by exact_mod_cast hb 0
    exact h1.trans (Nat.floor_le (by positivity))
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact exists_failure q hq A (b 0) hn

end LongTails.Theorems.StrongGrowthMeanSquaredLowerBound
