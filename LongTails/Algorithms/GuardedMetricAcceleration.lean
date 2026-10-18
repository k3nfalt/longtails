import LongTails.Algorithms.HessianSnapshot

namespace LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def extrapolate (a : ℝ) (x z : E) : E := (1 + a)⁻¹ • (x + a • z)

noncomputable def gradientStep (L : ℝ) (y g : E) : E := y - L⁻¹ • g

noncomputable def centerStep (a μ : ℝ) (y z g : E) : E :=
  (1 - a) • z + a • y - (a / μ) • g

noncomputable def regularizedValue (α : ℝ) (c x : E) (fx : ℝ) : ℝ := fx + α * ‖x - c‖ ^ 2

noncomputable def regularizedGradient (α : ℝ) (c x gx : E) : E := gx + (2 * α) • (x - c)

noncomputable def transformedGradient (S : E ≃L[ℝ] E) (g : E) : E :=
  S.symm.toContinuousLinearMap.adjoint g

noncomputable def escapePoints (η : ℝ) (u v : E) : Fin 4 → E :=
  ![u + (η / ‖u - v‖) • (u - v), u - (η / ‖u - v‖) • (u - v),
    v + (η / ‖u - v‖) • (u - v), v - (η / ‖u - v‖) • (u - v)]

end LongTails.Algorithms.GuardedMetricAcceleration
