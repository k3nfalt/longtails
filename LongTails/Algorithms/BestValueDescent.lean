import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def bestValueDescent (η : ℝ) (x0 : E) : Algorithm E (ℝ × E) E where
  State := ℕ × E × E × ℝ
  initial _ := (0, x0, x0, 0)
  query s := (0, s.2.1)
  update s reply :=
    (s.1 + 1, s.2.1 - η • reply.2,
      if s.1 = 0 ∨ reply.1 ≤ s.2.2.2 then (s.2.1, reply.1) else s.2.2)
  output s := s.2.2.1

end OracleTemplate
