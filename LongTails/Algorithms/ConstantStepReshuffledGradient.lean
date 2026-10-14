import LongTails.Setups.ConstantStepReshuffledSmoothConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.ConstantStepReshuffledConvex

open LongTails.Setups.ConstantStepReshuffledSmoothConvex

noncomputable def scale (p : Params) : ℝ :=
  (p.Lmax * p.ε + p.σ ^ 2) * p.R ^ 2 / p.ε ^ 2

noncomputable def epochCount (p : Params) : ℕ :=
  ⌈1 + 32768 * (1 + Real.log p.n) * scale p * (1 + Real.log (p.n + 2 + scale p)) / p.n⌉₊

noncomputable def stepSize (p : Params) : ℝ :=
  1 / (12 * (1 + Real.log p.n) * (1 + Real.log (p.n + 2 + scale p)) *
    (536 * p.Lmax + 132 * p.σ ^ 2 / p.ε))

noncomputable def algorithm (p : Params) :=
  ReshuffledConvex.reshuffledGradient (n := p.n) (epochCount p) (fun _ => stepSize p) p.x0

end OracleTemplate.ConstantStepReshuffledConvex
