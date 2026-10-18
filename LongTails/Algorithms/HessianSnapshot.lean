import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Algorithms.HessianSnapshot

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
noncomputable def coordinates (B : E →L[ℝ] E) : E ≃L[ℝ] E :=
  if h : ∃ S : E ≃L[ℝ] E, ∀ x, ‖S x‖ ^ 2 = ⟪B x, x⟫ then
    Classical.choose h else ContinuousLinearEquiv.refl ℝ E

end LongTails.Algorithms.HessianSnapshot
