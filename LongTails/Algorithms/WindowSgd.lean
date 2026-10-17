import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.WindowSgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def method (η : ℝ) (Ta Tb : ℕ) (x0 : E) : Algorithm E E E where
  Seed := Fin (Tb + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure, inferInstance⟩
  State := ℕ × ℕ × E
  initial τ := (Ta + τ.val, 0, x0)
  query s := (0, s.2.2)
  update s g := if s.2.1 < s.1 then (s.1, s.2.1 + 1, s.2.2 - η • g) else s
  output s := s.2.2

end OracleTemplate.WindowSgd
