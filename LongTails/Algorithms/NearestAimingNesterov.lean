import LongTails.Setups.LocalStrongAiming

namespace OracleTemplate.NearestAiming

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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
