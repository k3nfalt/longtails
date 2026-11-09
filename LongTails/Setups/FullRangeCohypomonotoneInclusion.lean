import LongTails.Setups.StochasticCohypomonotoneInclusion

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.FullRangeCohypomonotoneInclusion

open OracleTemplate
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params reply)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := (p.E → p.E) × (p.E → Set p.E)
  Query p := p.E ⊕ (ℝ × p.E)
  Reply p := p.E
  Output p := p.E × p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.ρ ∧ q.ρ * q.L < 1 ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q I O :=
    LongTails.Setups.StochasticCohypomonotoneInclusion.spec.admissible q I O
  successful q I output P :=
    LongTails.Setups.StochasticCohypomonotoneInclusion.spec.successful q I output P

end LongTails.Setups.FullRangeCohypomonotoneInclusion
