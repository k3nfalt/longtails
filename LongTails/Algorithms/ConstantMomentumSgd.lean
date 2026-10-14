import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.MomentumConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepSize (β γ : ℝ) (N k : ℕ) : ℝ := γ * ((N : ℝ) + 1 - k + β / (1 - β))

noncomputable def constantMomentumSgd (β γ : ℝ) (N : ℕ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, 0)
  query s := (0, s.2.1)
  update s g :=
    (s.1 + 1, s.2.1 - stepSize β γ N s.1 • (β • s.2.2 + (1 - β) • g), β • s.2.2 + (1 - β) • g)
  output s := s.2.1

end OracleTemplate.MomentumConvex
