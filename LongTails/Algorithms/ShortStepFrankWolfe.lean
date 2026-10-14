import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shortStep (L : ℝ) (x gradient atom : E) : E :=
  x + min 1 (⟪gradient, x - atom⟫ / (L * ‖atom - x‖ ^ 2)) • (atom - x)

noncomputable def shortStepFrankWolfe (L : ℝ) (x0 : E) : Algorithm (E ⊕ E) E E where
  State := Bool × E × E
  initial _ := (false, x0, 0)
  query state := (0, if state.1 then Sum.inr state.2.2 else Sum.inl state.2.1)
  update state reply :=
    if state.1 then (false, shortStep L state.2.1 state.2.2 reply, 0)
    else (true, state.2.1, reply)
  output state := state.2.1

end OracleTemplate.FrankWolfe
