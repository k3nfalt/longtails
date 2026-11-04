import Mathlib.Analysis.InnerProductSpace.Calculus

namespace LongTails.Algorithms.QuarticProximal

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def value (x : E) : ℝ := ‖x‖ ^ 4 / 4

noncomputable def grad (x : E) : E := ‖x‖ ^ 2 • x

noncomputable def hess (x : E) : E →L[ℝ] E :=
  ‖x‖ ^ 2 • ContinuousLinearMap.id ℝ E + 2 • (innerSL ℝ x).smulRight x

noncomputable def penalty (γ μ : ℝ) (c y0 x : E) : ℝ :=
  γ * value (x - c) + μ / 2 * ‖x - y0‖ ^ 2

noncomputable def penaltyGrad (γ μ : ℝ) (c y0 x : E) : E :=
  γ • grad (x - c) + μ • (x - y0)

noncomputable def penaltyHess (γ μ : ℝ) (c x : E) : E →L[ℝ] E :=
  γ • hess (x - c) + μ • ContinuousLinearMap.id ℝ E

noncomputable def augment (γ μ : ℝ) (c y0 x : E)
    (reply : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (reply.1 + penaltyGrad γ μ c y0 x, reply.2 + penaltyHess γ μ c x)

end LongTails.Algorithms.QuarticProximal
