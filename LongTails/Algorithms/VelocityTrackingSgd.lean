import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.VelocityTracking

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def velocityTrackingSgd (γ β : ℝ) (x0 : E) : Algorithm E E (E × ℕ) where
  State := ℕ × E × E
  initial _ := (0, x0, 0)
  query state := (0, state.2.1 + state.2.2)
  update state reply := (state.1 + 1, state.2.1 + state.2.2 - γ • reply, state.2.2 - β • reply)
  output state := (state.2.1, state.1)

end OracleTemplate.VelocityTracking
