import LongTails.Setups.RelativeErrorSmoothConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Setups.SharpRelativeErrorSmoothConvex

abbrev Public := RelativeErrorSmoothConvex.Public

abbrev spec : OracleTemplate.Setup :=
  { RelativeErrorSmoothConvex.spec with
    valid := fun p => RelativeErrorSmoothConvex.spec.valid p ∧
      p.α ≤ 1 / (100 * (33 * (1 + Real.log (2 + p.L * p.R ^ 2 / p.ε))) ^ 12) }

end LongTails.Setups.SharpRelativeErrorSmoothConvex
