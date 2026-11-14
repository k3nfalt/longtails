import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.PolynomialMixingHeavyTailedConvex

abbrev Params := HeavyTailedMarkovSmoothAndConvex.Params

abbrev spec : OracleTemplate.Setup :=
  { HeavyTailedMarkovSmoothAndConvex.spec with
    valid := fun q =>
      HeavyTailedMarkovSmoothAndConvex.spec.valid q ∧
      0 < q.R ∧ 0 < q.σ ∧
      (∃ v : q.E, ‖v‖ = 1) ∧
      (∃ a b : q.Ω, a ≠ b ∧ MeasurableSet ({a} : Set q.Ω) ∧
        MeasurableSet ({b} : Set q.Ω)) ∧
      16 ≤ q.L * q.R ^ 2 / q.ε ∧
      q.L * q.R ^ 2 / q.ε ≤ (q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) ∧
      (2 : ℝ) ^ (4 * q.α - 1) ≤ (q.σ * q.R / q.ε) ^ q.α ∧
      q.β * ((2 : ℝ) ^ (4 * q.α - 1) / (q.σ * q.R / q.ε) ^ q.α) ^
        (1 / (q.β * (q.α - 1))) ≤ q.τ }

end LongTails.Setups.PolynomialMixingHeavyTailedConvex
