import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.NearestAiming

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def nesterovStep (L μ : ℝ) (state : E × E) (g : E) : E × E :=
  let s := 1 / (2 * Real.sqrt L)
  let q := Real.sqrt μ * s
  (state.1 + s • state.2 - s ^ 2 • g,
    ((1 - q) / (1 + q)) • (state.2 - s • g))

noncomputable def nesterov (L μ : ℝ) (x0 : E) : Algorithm E E E where
  State := E × E
  initial _ := (x0, 0)
  query state := (0, state.1 + (1 / (2 * Real.sqrt L)) • state.2)
  update := nesterovStep L μ
  output state := state.1

noncomputable def nesterovOutput (g : E → E) (L μ : ℝ) (x0 : E) (K : ℕ) : E :=
  ((fun state => nesterovStep L μ state
    (g (state.1 + (1 / (2 * Real.sqrt L)) • state.2)))^[K] (x0, 0)).1

end OracleTemplate.NearestAiming
