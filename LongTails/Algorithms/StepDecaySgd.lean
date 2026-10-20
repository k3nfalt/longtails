import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.StepDecaySgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def method (ηs ηc : ℝ) (T K : ℕ) (x0 : E) : Algorithm E E E where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := ℕ × ℕ × E
  initial τ := (τ.val, 0, x0)
  query s := (0, s.2.2)
  update s g :=
    if s.2.1 < s.1 then (s.1, s.2.1 + 1, s.2.2 - ηs • g)
    else if s.2.1 < s.1 + K then (s.1, s.2.1 + 1, s.2.2 - ηc • g)
    else s
  output s := s.2.2

end OracleTemplate.StepDecaySgd
