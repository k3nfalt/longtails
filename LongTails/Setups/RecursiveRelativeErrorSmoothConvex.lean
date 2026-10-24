import LongTails.Setups.RelativeErrorSmoothConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Setups.RecursiveRelativeErrorSmoothConvex

abbrev Public := RelativeErrorSmoothConvex.Public

abbrev spec : OracleTemplate.Setup :=
  { RelativeErrorSmoothConvex.spec with
    valid := fun p => RelativeErrorSmoothConvex.spec.valid p ∧
      p.α ≤ Real.exp (-8 * (1 + Real.sqrt (Real.log (2 + p.L * p.R ^ 2 / p.ε)))) / 100 }

end LongTails.Setups.RecursiveRelativeErrorSmoothConvex
