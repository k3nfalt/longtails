import LongTails.Setups.HighDimensionalAverageMixingMarkovSmoothNonconvex
import LongTails.Proofs.MarkovFrontierLower
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.AverageMixingMarkovSmoothNonconvexLowerBound

open OracleTemplate Setups.AverageMixingMarkovSmoothNonconvex

noncomputable def budget : (let S := LongTails.Setups.HighDimensionalAverageMixingMarkovSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.τ * p.L * p.Δ * p.σ ^ 2 * Real.log (p.σ / p.ε) / (2 ^ 65 * p.ε ^ 4)⌋₊

theorem result : NonConvergence LongTails.Setups.HighDimensionalAverageMixingMarkovSmoothNonconvex.spec budget := by
  intro p hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain ⟨π, hπ⟩ := Proofs.MarkovFrontierLower.exists_failure p hv A (b 0) (hb 0)
  exact ⟨_, _, Proofs.MarkovFrontierOracle.admissible p hv π, hπ⟩

end LongTails.Theorems.AverageMixingMarkovSmoothNonconvexLowerBound
