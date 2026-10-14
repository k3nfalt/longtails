import LongTails.Algorithms.RandomReshuffling
import LongTails.Setups.QuadraticFiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.QuadraticReshuffling

open LongTails.Setups.QuadraticFiniteSum

noncomputable def epochScale (p : Params) : ℝ :=
  32 * p.L / p.μ + 64 * p.L * Real.sqrt p.L * p.G / ((p.n : ℝ) * p.μ ^ 2 * Real.sqrt p.ε) +
    4 * (p.L ^ 3 * p.G ^ 2 / ((p.n : ℝ) * p.μ ^ 4 * p.ε)) ^ (1 / 3 : ℝ)

noncomputable def stepSize (p : Params) : ℝ := 1 / (p.μ * p.n * epochScale p)

noncomputable def epochCount (p : Params) : ℕ :=
  ⌈2 * epochScale p * Real.log (1 + p.L * p.R ^ 2 / p.ε)⌉₊

noncomputable def algorithm (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  RandomReshuffling.algorithm (stepSize p) (epochCount p) p.x0

end OracleTemplate.QuadraticReshuffling
