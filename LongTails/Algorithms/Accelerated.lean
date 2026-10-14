import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def acceleratedQuery (state : Nat × E × E) : E :=
  let k := (state.1 : ℝ)
  let A := k * (k + 1) / 4
  let a := (k + 1) / 2
  (A / (A + a)) • state.2.1 + (a / (A + a)) • state.2.2

noncomputable def accelerated : ℝ × E → Algorithm E E E
  | (L, x0) => {
      State := Nat × E × E
      initial _ := (0, x0, x0)
      query := fun s => (0, acceleratedQuery s)
      update state reply :=
        let a := ((state.1 : ℝ) + 1) / 2
        (state.1 + 1, acceleratedQuery state - (1 / L) • reply,
          state.2.2 - (a / L) • reply)
      output state := state.2.1 }

end OracleTemplate.Gradient
