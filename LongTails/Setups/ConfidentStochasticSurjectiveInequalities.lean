import LongTails.Setups.StochasticSurjectiveInequalities

open MeasureTheory

namespace LongTails.Setups.ConfidentStochasticSurjectiveInequalities

open OracleTemplate

structure Params where
  problem : StochasticSurjectiveInequalities.Params
  δ : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := StochasticSurjectiveInequalities.Problem p.problem
  Query p := p.problem.E × p.problem.E
  Reply p := StochasticSurjectiveInequalities.Primitive p.problem ×
    StochasticSurjectiveInequalities.Primitive p.problem
  Output p := p.problem.E × StochasticSurjectiveInequalities.Constraint p.problem
  publicInput p := p
  valid p := StochasticSurjectiveInequalities.spec.valid p.problem ∧ 0 < p.δ ∧ p.δ < 1
  admissible p := StochasticSurjectiveInequalities.spec.admissible p.problem
  successful p I output P := Measurable output ∧
    ENNReal.ofReal (1 - p.δ) ≤
      (P : Measure _) {ω | StochasticSurjectiveInequalities.accurate p.problem I (output ω)}

end LongTails.Setups.ConfidentStochasticSurjectiveInequalities
