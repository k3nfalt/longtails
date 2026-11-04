import LongTails.Algorithms.CompositeCubicAcceleration

namespace LongTails.Algorithms.QuarticAcceleration

open LongTails.Algorithms.CompositeCubicAcceleration

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def parameter (γ : ℝ) (c y : E) : ℝ := γ * ‖y - c‖ ^ 2

noncomputable def damping (μ γ : ℝ) (s : State E) (y : E) : ℝ :=
  min 1 (μ / parameter E γ (center E μ s) y)

noncomputable def advance (μ γ : ℝ) (s : State E) (y g : E) : State E :=
  let a := trialWeight μ s.weight
  let β := damping E μ γ s y
  let A := s.weight + β * a
  ⟨A, A⁻¹ • (((1 - β) * s.weight) • s.point + (β * (s.weight + a)) • y),
    s.momentum - (β * a) • g⟩

noncomputable def nextGuess (μ lam : ℝ) : ℝ := if lam ≤ μ then μ / 4 else 4 * μ

end LongTails.Algorithms.QuarticAcceleration
