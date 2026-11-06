import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.CovarianceAcceleratedMixture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def couple (A α : ℝ) (y z : E) : E :=
  (A / (A + α)) • y + (α / (A + α)) • z

noncomputable def density (z u : E) : ℝ := Real.exp (⟪z, u⟫ - ‖z‖ ^ 2 / 2)

noncomputable def mixture {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (u : E) : ℝ := ∑ i, w.weights i * density (z i) u

noncomputable def mean {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n)) : E :=
  ∑ i, w.weights i • z i

noncomputable def linearLoss {n : ℕ} (c : Fin n → ℝ) (w : StdSimplex ℝ (Fin n)) : ℝ :=
  ∑ i, w.weights i * c i

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def divergence {n : ℕ} (z : Fin n → E)
    (w v : StdSimplex ℝ (Fin n)) : ℝ :=
  ∫ u, mixture z w u * Real.log (mixture z w u / mixture z v u) ∂stdGaussian E

noncomputable def potential {n : ℕ} (z : Fin n → E) (a β γ : ℝ)
    (w v : StdSimplex ℝ (Fin n)) : ℝ :=
  divergence z w v + β * a ^ 2 / 2 * ‖mean z w - mean z v‖ ^ 2 +
    γ / 2 * ∑ i, (w.weights i - v.weights i) ^ 2

noncomputable def update {n : ℕ} (z : Fin n → E) (a β γ : ℝ) (c : Fin n → ℝ)
    (p : StdSimplex ℝ (Fin n)) : StdSimplex ℝ (Fin n) :=
  @Classical.epsilon _ ⟨p⟩ (fun w => ∀ u, linearLoss c w + potential z a β γ w p ≤
    linearLoss c u + potential z a β γ u p)

noncomputable def coefficients {n : ℕ} (z : Fin n → E) (x0 : E) (a α : ℝ)
    (b h g : E) (i : Fin n) : ℝ :=
  α * ⟪h, x0 + a • z i - b⟫ +
    ∫ u, density (z i) u * max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)) ∂stdGaussian E

noncomputable def step {n : ℕ} (z : Fin n → E) (x0 : E) (a α β γ : ℝ)
    (p : StdSimplex ℝ (Fin n)) (h g : E) : StdSimplex ℝ (Fin n) :=
  update z a β γ (coefficients z x0 a α (x0 + a • mean z p) h g) p

end LongTails.Algorithms.CovarianceAcceleratedMixture
