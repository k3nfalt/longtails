import LongTails.Setups.PolynomialMixingHeavyTailedConvex
import LongTails.Proofs.PolynomialMixingLowerBound
import LongTails.TemplateLowerBound

namespace LongTails.Theorems.PolynomialMixingHeavyTailedConvexLowerBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊q.τ / q.β * ((q.σ * q.R / q.ε) ^ q.α / (2 : ℝ) ^ (4 * q.α - 1)) ^ ((q.β + 1) / (q.β * (q.α - 1)))⌋₊

theorem result : NonConvergence LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec budget :=
  LongTails.Proofs.PolynomialMixingLowerBound.polynomialMixing_lower

end LongTails.Theorems.PolynomialMixingHeavyTailedConvexLowerBound
