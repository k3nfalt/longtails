import LongTails.Setups.DistanceGrowingSubgradient
import LongTails.Algorithms.Clipping
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open OracleTemplate LongTails.Setups.TerminalClippingConvex

namespace LongTails.Algorithms.LocalizedClippedSubgradient

noncomputable def iterations (p : Public) : ℕ :=
  if p.G * p.R ≤ p.ε then 0 else
    ⌈1024 * p.R ^ 2 * (p.G ^ 2 + p.B ^ 2 * p.R ^ 2) * Real.log (8 / p.δ) / p.ε ^ 2⌉₊

noncomputable def step (p : Public) : ℝ := p.ε / (64 * (p.G ^ 2 + p.B ^ 2 * p.R ^ 2))

noncomputable def threshold (p : Public) : ℝ := 16 * p.R * (p.G ^ 2 + p.B ^ 2 * p.R ^ 2) / p.ε

noncomputable def localize (p : Public) (y : Vector p.d) : Vector p.d :=
  p.x0 + clip p.R (y - p.x0)

noncomputable def proposal (p : Public) (x g : Vector p.d) : Vector p.d :=
  localize p (x - step p • clip (threshold p) g)

inductive State (p : Public) where
  | ready (x total : Vector p.d)
  | pending (y total : Vector p.d)

noncomputable def output (p : Public) (s : State p) : Vector p.d :=
  if iterations p = 0 then p.x0 else
    match s with
    | .ready _ total | .pending _ total => ((iterations p : ℝ)⁻¹) • total

noncomputable def algorithm (p : Public) : Algorithm (Query p) (Vector p.d) (Vector p.d) where
  State := State p
  initial _ := .ready p.x0 0
  query
    | .ready x _ => (0, .subgradient x)
    | .pending y _ => (0, .projection y)
  update
    | .ready x total, g => .pending (proposal p x g) (total + x)
    | .pending _ total, x => .ready x total
  output := output p

end LongTails.Algorithms.LocalizedClippedSubgradient
