import LongTails.Setups.MarkovSmoothNonconvex

namespace LongTails.Setups.HighDimensionalMarkovSmoothNonconvex

open MarkovSmoothNonconvex

def Valid (p : Params) : Prop :=
  0 < p.L ∧ 0 < p.ε ∧ 1 ≤ p.τ ∧ 2 ^ 26 * p.ε ^ 2 ≤ p.L * p.Δ ∧
    2 ^ 16 * p.ε ≤ p.σ ∧
    2 ^ 40 * (1 + p.L * p.Δ / p.ε ^ 2) ^ 4 *
      (1 + p.τ * (p.σ / p.ε) ^ 2 * Real.log (p.σ / p.ε)) ≤ p.d

abbrev spec : OracleTemplate.Setup := { MarkovSmoothNonconvex.spec with valid := Valid }

end LongTails.Setups.HighDimensionalMarkovSmoothNonconvex
