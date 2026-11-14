import LongTails.TemplateLowerBound
import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.FullGeneralizedSmoothParameters
import LongTails.Proofs.FullGeneralizedSmoothTransient
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery
import LongTails.Proofs.MollifiedSmoothLowerBound

namespace LongTails.Theorems.FullGeneralizedSmoothConvexLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.GeneralizedSmoothConvexFull.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + p.L1 * p.R / Real.log (2 + p.L1 * p.R)) / 8388608⌋₊

theorem result : NonConvergence LongTails.Setups.GeneralizedSmoothConvexFull.spec budget := by
  intro p hp A _ b hb
  have hN := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  obtain hzero | haccuracy | htransient := LongTails.Proofs.FullGeneralizedSmoothParameters.budget_cases
    (Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) (p.L1 * p.R) (Real.sqrt_nonneg _)
    (mul_nonneg hp.2.1 hp.2.2.1.le) (b 0) hN
  · rw [hzero]
    exact LongTails.Proofs.FullGeneralizedSmoothZeroQuery.exists_failure p hp
      (LongTails.Proofs.FullGeneralizedSmoothParameters.dimension_pos p hp) A
  · exact LongTails.Proofs.MollifiedSmoothLowerBound.exists_failure p hp (b 0) haccuracy.1 haccuracy.2 A
  · exact LongTails.Proofs.FullGeneralizedSmoothTransient.exists_failure p hp htransient.1 (b 0) htransient.2 A

end LongTails.Theorems.FullGeneralizedSmoothConvexLowerBound
