import LongTails.TemplateLowerBound
import LongTails.Setups.InterpolatedDistanceGrowingSubgradient
import LongTails.Proofs.BlumGladyshevLowerBound

open OracleTemplate

namespace LongTails.Theorems.DistanceGrowingSubgradientLowerBound

noncomputable def budget : (let S := LongTails.Setups.InterpolatedDistanceGrowingSubgradient.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.R ^ 2 * (p.G ^ 2 + p.B ^ 2 * p.R ^ 2) * Real.log (1 / p.δ) / (2 ^ 28 * p.ε ^ 2)⌋₊

theorem result : NonConvergence LongTails.Setups.InterpolatedDistanceGrowingSubgradient.spec budget := by
  intro p hp A _ b hb
  have hlog : 0 ≤ Real.log (1 / p.δ) :=
    Real.log_nonneg ((le_div_iff₀ hp.2.2.2.2.2.2.1).mpr (by linarith [hp.2.2.2.2.2.2.2]))
  have hn : (b 0 : ℝ) ≤ (budget p 0 : ℝ) := by exact_mod_cast hb 0
  have h := LongTails.Proofs.BlumGladyshevLowerBound.exists_failure p hp A (b 0)
    (hn.trans (Nat.floor_le (by positivity)))
  rw [show b = fun _ => b 0 from funext fun i => congrArg b (Subsingleton.elim i 0)]
  exact h

end LongTails.Theorems.DistanceGrowingSubgradientLowerBound
