import LongTails.TemplateLowerBound
import LongTails.Setups.GeneralizedSmoothConvexTransient
import LongTails.Proofs.GeneralizedSmoothTransientLowerBound

namespace LongTails.Theorems.RandomizedGeneralizedSmoothTransientLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.GeneralizedSmoothConvexTransient.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊

theorem result : NonConvergence LongTails.Setups.GeneralizedSmoothConvexTransient.spec budget := by
  intro p hp A _ b hb
  have hN := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact LongTails.Proofs.GeneralizedSmoothTransientLowerBound.exists_failure p hp (b 0) hN A

end LongTails.Theorems.RandomizedGeneralizedSmoothTransientLowerBound
