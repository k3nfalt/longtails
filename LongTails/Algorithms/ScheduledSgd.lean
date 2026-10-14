import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.ScheduledSgd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def method (η : ℕ → ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E
  initial _ := (0, x0)
  query s := (0, s.2)
  update s g := (s.1 + 1, s.2 - η s.1 • g)
  output s := s.2

end OracleTemplate.ScheduledSgd
