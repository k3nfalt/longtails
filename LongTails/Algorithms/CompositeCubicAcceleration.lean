import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Algorithms.CompositeCubicAcceleration

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure State where
  weight : ℝ
  point : E
  momentum : E

noncomputable def trialWeight (μ A : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * μ * A)) / (2 * μ)

noncomputable def center (μ : ℝ) (s : State E) : E :=
  (s.weight + trialWeight μ s.weight)⁻¹ •
    (s.weight • s.point + trialWeight μ s.weight • s.momentum)

noncomputable def damping (μ γ : ℝ) (s : State E) (z : E) : ℝ :=
  min 1 (μ / (γ * ‖z - center E μ s‖))

noncomputable def advance (μ γ : ℝ) (s : State E) (z g : E) : State E :=
  let a := trialWeight μ s.weight
  let β := damping E μ γ s z
  let A := s.weight + β * a
  ⟨A, A⁻¹ • (((1 - β) * s.weight) • s.point + (β * (s.weight + a)) • z),
    s.momentum - (β * a) • g⟩

end LongTails.Algorithms.CompositeCubicAcceleration
