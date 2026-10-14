import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def clip (B : ℝ) (v : E) : E :=
  if ‖v‖ ≤ B then v else (B / ‖v‖) • v

end OracleTemplate
