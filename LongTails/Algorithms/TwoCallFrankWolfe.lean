import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def twoCallFrankWolfe (τ : ℝ) (x0 : E) : Algorithm (E ⊕ E) E E where
  State := Bool × ℕ × E × E
  initial _ := (false, 0, x0, 0)
  query s := (0, if s.1 then Sum.inr s.2.2.2 else Sum.inl s.2.2.1)
  update s reply :=
    if s.1 then
      (false, s.2.1 + 1, (1 - 2 / (τ * s.2.1 + 2)) • s.2.2.1 +
        (2 / (τ * s.2.1 + 2)) • reply, 0)
    else (true, s.2.1, s.2.2.1, reply)
  output s := s.2.2.1

end OracleTemplate
