import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate

noncomputable def robustPolyak {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (x0 : E) : Algorithm E (ℝ × E) E where
  State := E
  initial _ := x0
  query x := (0, x)
  update x reply := x - (c * reply.1 / ‖reply.2‖ ^ 2) • reply.2
  output x := x

end OracleTemplate
