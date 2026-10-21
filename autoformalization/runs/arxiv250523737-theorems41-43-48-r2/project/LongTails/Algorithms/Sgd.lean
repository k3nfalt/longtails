import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.StochasticGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sgd (η : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, 0)
  query state := (0, state.2.1)
  update state reply := (state.1 + 1, state.2.1 - η • reply, state.2.2 + state.2.1)
  output state := if state.1 = 0 then x0 else (state.1 : ℝ)⁻¹ • state.2.2

noncomputable def run {Ω : Type*} (oracle : E → Ω → E) (η : ℝ) :
    (K : ℕ) → E → (Fin K → Ω) → E × E
  | 0, x, _ => (x, 0)
  | K + 1, x, ξ =>
    let result := run oracle η K (x - η • oracle x (ξ 0)) (fun i => ξ i.succ)
    (result.1, x + result.2)

end OracleTemplate.StochasticGradient
