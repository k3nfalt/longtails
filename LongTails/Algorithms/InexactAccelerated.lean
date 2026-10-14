import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace OracleTemplate.InexactGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def momentum (L μ α : ℝ) : ℝ :=
  1 / (4 * Real.sqrt (L / (μ * (1 - α))) + 16 * α ^ 2 * L / (μ * (1 - α)))

def query (θ : ℝ) (s : E × E) : E :=
  (1 / (1 + θ)) • (s.1 + θ • s.2)

def step (L μ θ : ℝ) (s : E × E) (g : E) : E × E :=
  (query θ s - (1 / L) • g, (1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • g)

def inexactAccelerated (L μ α : ℝ) (x0 : E) : Algorithm E E E where
  State := E × E
  initial _ := (x0, x0)
  query s := (0, query (momentum L μ α) s)
  update s g := step L μ (momentum L μ α) s g
  output s := s.1

end OracleTemplate.InexactGradient
