import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.SymmetricGaussianReverseFisher

structure Params where
  dimension : ℕ+
  lower : ℝ
  upper : ℝ
  accuracy : ℝ
  failure : ℝ

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.dimension)

noncomputable def score {p : Params} (θ x : Space p) : Space p :=
  Real.tanh ⟪θ, x⟫ • θ - x

noncomputable def loss {p : Params} (μ θ : Space p) : ℝ :=
  ((∫ z, ‖score θ (θ + z) - score μ (θ + z)‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (Space p)) +
    (∫ z, ‖score θ (-θ + z) - score μ (-θ + z)‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (Space p))) / 2

def gdFamily (p : Params) (A : Algorithm (Space p) (Space p) (Space p)) : Prop :=
  ∃ (point : A.State → Space p) (step : A.State → ℝ),
    (∀ state, 0 < step state) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) = point state - step state • reply) ∧
    (∀ state, A.output state = point state)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance := Space
  Query := Space
  Reply := Space
  Output := Space
  publicInput := id
  valid p := 0 ≤ p.lower ∧ p.lower ≤ p.upper ∧
    0 < p.accuracy ∧ p.accuracy ≤ 1 ∧ 0 < p.failure ∧ p.failure ≤ 1
  admissible p μ oracle := p.lower ≤ ‖μ‖ ∧ ‖μ‖ ≤ p.upper ∧
    ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2
  successful p μ output P := Measurable output ∧
    ENNReal.ofReal (1 - p.failure) ≤
      (P : Measure _) {ω | min (‖output ω - μ‖ ^ 2) (‖output ω + μ‖ ^ 2) ≤ p.accuracy}
  allowedAlgorithm := gdFamily

end LongTails.Setups.SymmetricGaussianReverseFisher
