import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace OracleTemplate.RelativeErrorConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def damping (α : ℝ) (N : ℕ) : ℝ :=
  (1 - α) / (8 + 2 * α ^ 2 * N)

def query (s : ℕ × E × E) : E :=
  (1 / ((s.1 : ℝ) + 2)) • ((s.1 : ℝ) • s.2.1 + (2 : ℝ) • s.2.2)

def step (L q : ℝ) (s : ℕ × E × E) (g : E) : ℕ × E × E :=
  (s.1 + 1, query s - (1 / L) • g, s.2.2 - (q * ((s.1 : ℝ) + 1) / (2 * L)) • g)

def dampedAccelerated (L q : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, x0)
  query s := (0, query s)
  update s g := step L q s g
  output s := s.2.1

end OracleTemplate.RelativeErrorConvex
