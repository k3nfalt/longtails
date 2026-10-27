import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def residualModel (v : E) (A : E →L[ℝ] E) (ρ : ℝ) (d : E) : ℝ :=
  ‖v + A d‖ + ρ / 2 * ‖d‖ ^ 2

noncomputable def residualNewtonStep (v : E) (A : E →L[ℝ] E) (ρ : ℝ) : E :=
  Classical.epsilon (fun d => ∀ s, residualModel v A ρ d ≤ residualModel v A ρ s)

noncomputable def squaredRegularization (K : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  K.comp K + t • ContinuousLinearMap.id ℝ E

noncomputable def tikhonovResponse (K : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  K.comp (squaredRegularization K t).inverse

noncomputable def envelopeCubicModel (g : E) (B : E →L[ℝ] E) (M : ℝ) (s : E) : ℝ :=
  Inner.inner ℝ g s + (1 / 2 : ℝ) * Inner.inner ℝ s (B s) + M / 3 * ‖s‖ ^ 3

noncomputable def envelopeCubicStep (g : E) (B : E →L[ℝ] E) (M : ℝ) : E :=
  Classical.epsilon (fun s => ∀ v, envelopeCubicModel g B M s ≤ envelopeCubicModel g B M v)

noncomputable def primalInjection {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    E →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E F)

noncomputable def envelopeHessianApprox {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : ℝ) (K : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F)) (t : ℝ) : E →L[ℝ] E :=
  (2 * L) • ContinuousLinearMap.id ℝ E - (4 * L ^ 2) •
    (WithLp.fstL 2 ℝ E F).comp ((tikhonovResponse K t).comp primalInjection)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def primalBlock : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E F)).comp (WithLp.fstL 2 ℝ E F)

noncomputable def regularizedGradient (g : WithLp 2 (E × F) → WithLp 2 (E × F))
    (L : ℝ) (z : E) (w : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
  g w + WithLp.toLp 2 ((2 * L) • (w.fst - z), 0)

noncomputable def regularizedHessian (H : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F))
    (L : ℝ) : WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F) := H + (2 * L) • primalBlock

end OracleTemplate.PLMinimax
