import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.MarkovQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def lastSgd (η : ℝ) (x0 : E) : Algorithm E E E where
  State := E
  initial _ := x0
  query x := (0, x)
  update x g := x - η • g
  output x := x

noncomputable def iterate {Ω : Type*} (g : E → Ω → E) (η : ℝ) (x0 : E)
    (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | k + 1 => iterate g η x0 ξ k - η • g (iterate g η x0 ξ k) (ξ k)

end OracleTemplate.MarkovQuadratic
