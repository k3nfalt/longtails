import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.EllSmoothGd

open OracleTemplate

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gdStep (ℓ : ℝ → ℝ) (ε : ℝ) (x g : E) : E :=
  if ‖g‖ ≤ ε then x else x - (1 / (2 * ℓ (2 * ‖g‖))) • g

noncomputable def ellGd (ℓ : ℝ → ℝ) (ε : ℝ) (x0 : E) : Algorithm E (ℝ × E) E where
  State := E
  initial _ := x0
  query x := (0, x)
  update x r := gdStep ℓ ε x r.2
  output x := x

end LongTails.Algorithms.EllSmoothGd
