import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.SampledConvex

noncomputable def scale (L R σ : ℝ) (T : ℕ) : ℝ :=
  R / (8 * L * R + σ * Real.sqrt T)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def path {Ξ : Type*} (grad : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E)
    (ξ : ℕ → Ξ) : ℕ → E
  | 0 => x0
  | k + 1 => path grad η T x0 ξ k - (η * ((T : ℝ) - k) / T) • grad (ξ k) (path grad η T x0 ξ k)

noncomputable def linearDecaySgd (η : ℝ) (T : ℕ) (x0 : E) : Algorithm E E E where
  State := ℕ × E
  initial _ := (0, x0)
  query s := (0, s.2)
  update s g := (s.1 + 1, s.2 - (η * ((T : ℝ) - s.1) / T) • g)
  output s := s.2

end OracleTemplate.SampledConvex
