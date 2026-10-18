import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.RecursiveMomentum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def momentumStep (γ : ℝ) (x d : E) : E := x - γ • d

def momentumQuery (γ : ℝ) (b0 : ℕ) (s : ℕ × ℕ × E × E) : E × E :=
  if s.2.1 < b0 then (s.2.2.1, s.2.2.1) else (momentumStep γ s.2.2.1 s.2.2.2, s.2.2.1)

noncomputable def momentumUpdate (γ a : ℝ) (b0 : ℕ) (s : ℕ × ℕ × E × E) (r : E × E) :
    ℕ × ℕ × E × E :=
  if s.2.1 < b0 then
    (s.1, s.2.1 + 1, s.2.2.1, s.2.2.2 + (1 / ((s.2.1 : ℝ) + 1)) • (r.1 - s.2.2.2))
  else if s.2.1 < b0 + s.1 then
    (s.1, s.2.1 + 1, momentumStep γ s.2.2.1 s.2.2.2, r.1 + (1 - a) • (s.2.2.2 - r.2))
  else s

noncomputable def recursiveMomentum (γ a : ℝ) (b0 T : ℕ) (x0 : E) :
    Algorithm (E × E) (E × E) E where
  Seed := Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (T + 1))).toMeasure, inferInstance⟩
  State := ℕ × ℕ × E × E
  initial τ := (τ.val, 0, x0, 0)
  query s := (0, momentumQuery γ b0 s)
  update := momentumUpdate γ a b0
  output s := s.2.2.1

end OracleTemplate.RecursiveMomentum
