import LongTails.Setups.SharpLipschitzConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Setups.HighDimensionalSharpLipschitzConvex

open OracleTemplate

abbrev spec : Setup where
  Params := LongTails.Setups.SharpLipschitzConvex.Params
  Public := LongTails.Setups.SharpLipschitzConvex.Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := ℝ × EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.μ ∧ 96 * p.μ ≤ p.L ∧ 0 < p.D ∧ 0 < p.ε ∧ p.ε ≤ p.μ * p.D ∧
    2 ^ 10 * (1 + (p.L / p.μ) ^ 2 * (1 + Real.log (p.μ * p.D / p.ε))) ^ 6 * (p.L * p.D / p.ε) ^ 2 ≤ p.d
  admissible p f O := LongTails.Setups.SharpLipschitzConvex.spec.admissible p f O
  successful p f output P := LongTails.Setups.SharpLipschitzConvex.spec.successful p f output P

end LongTails.Setups.HighDimensionalSharpLipschitzConvex
