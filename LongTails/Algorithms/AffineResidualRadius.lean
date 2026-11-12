import LongTails.Algorithms.AffineResidualBudget
import LongTails.Algorithms.AffineSoftmaxOuter

namespace LongTails.Algorithms.AffineResidualRadius

noncomputable def radiusFactor (m b : ℝ) : ℝ :=
  min ((max 1 b) ^ (2 / 3 : ℝ))
    (max ((max 1 b) ^ (3 / 5 : ℝ)) (((max 1 b) ^ 2 / m) ^ (3 / 8 : ℝ)))

noncomputable def publicRadius (m : ℕ) (L R ε : ℝ) : ℝ :=
  2 * R / radiusFactor m (8 * L * R ^ 2 / ε)

noncomputable def meanCostBound (m : ℕ) (G L R ε : ℝ) : ℝ :=
  let r := publicRadius m L R ε
  let τ := ε / (2 * Real.log m)
  let H := AffineSoftmaxOuter.compilerDepth G (2 * R) r (ε / 2)
  let μ := AffineSoftmaxOuter.compilerFloor G (2 * R) r (ε / 2)
  let t := AffineSoftmaxOuter.compilerScale (2 * R) r
  30000000000000 * (H : ℝ) ^ 7 * t * (m +
    ((1 + m * L * r ^ 2 / τ) * (1 + Real.sqrt (τ * Real.log m / (μ * r ^ 2))) +
      (L / μ) ^ 2 + m * L ^ 2 * r ^ 2 / (μ * τ) + 1))

end LongTails.Algorithms.AffineResidualRadius
