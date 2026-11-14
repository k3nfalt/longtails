import LongTails.TemplateLowerBound
import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.FullGeneralizedSmoothParameters
import LongTails.Proofs.GapBudget
import LongTails.Proofs.GapTransientLowerBound
import LongTails.Proofs.GapSmoothLowerBound
import LongTails.Proofs.GapGeneralizedSmoothZeroQuery

namespace LongTails.Theorems.GapGeneralizedSmoothConvexLowerBound

open OracleTemplate
open LongTails.Proofs

noncomputable def budget : (let S := LongTails.Setups.GapGeneralizedSmoothConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + min (p.L1 * p.R / (1 + Real.log (2 + p.L1 * p.R))) ((p.L1 * p.R * Real.log (p.Δ / (8 * p.ε)) / (1 + Real.log (2 + p.L1 * p.R))) ^ (2 / 3 : ℝ))) / 16777216⌋₊

theorem result : NonConvergence LongTails.Setups.GapGeneralizedSmoothConvex.spec budget := by
  intro p hp A _ b hb
  have hN := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  have hh : 0 < GapTransientParameters.gapLog p := by
    have := GapTransientParameters.gapLog_ge_half p hp
    linarith
  obtain hzero | hsmooth | htransient := GapBudget.cases
    (Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) (GapTransientParameters.scale p)
    (GapTransientParameters.gapLog p) (GapTransientParameters.logarithm p)
    (Real.sqrt_nonneg _) (mul_nonneg hp.2.1 hp.2.2.1.le) hh
    (GapTransientParameters.logarithm_ge_one p hp) (b 0) hN
  · rw [hzero]
    exact GapGeneralizedSmoothZeroQuery.exists_failure p hp
      (FullGeneralizedSmoothParameters.dimension_pos (GapGeneralizedSmoothUpper.radiusParams p)
        (GapGeneralizedSmoothUpper.radius_valid p hp)) A
  · exact GapSmoothLowerBound.exists_failure p hp (b 0) hsmooth A
  · exact GapTransientLowerBound.exists_failure p hp (b 0) htransient.1 htransient.2.1 htransient.2.2 A

end LongTails.Theorems.GapGeneralizedSmoothConvexLowerBound
