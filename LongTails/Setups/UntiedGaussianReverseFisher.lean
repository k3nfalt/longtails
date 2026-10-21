import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.UntiedGaussianReverseFisher

structure Params where
  dimension : ℕ+
  centre : ℝ
  lower : ℝ
  accuracy : ℝ
  failure : ℝ

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.dimension)

abbrev Means (p : Params) := PiLp 2 (fun _ : Fin 2 => Space p)

noncomputable def weight {p : Params} (θ : Means p) (x : Space p) (i : Fin 2) : ℝ :=
  Real.exp (-‖x - θ i‖ ^ 2 / 2) / ∑ j, Real.exp (-‖x - θ j‖ ^ 2 / 2)

noncomputable def score {p : Params} (θ : Means p) (x : Space p) : Space p :=
  (∑ i, weight θ x i • θ i) - x

noncomputable def loss {p : Params} (μ θ : Means p) : ℝ :=
  (∑ i, ∫ z, ‖score θ (θ i + z) - score μ (θ i + z)‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (Space p)) / 2

noncomputable def matchingError {p : Params} (μ θ : Means p) : ℝ :=
  min (‖θ 0 - μ 0‖ ^ 2 + ‖θ 1 - μ 1‖ ^ 2) (‖θ 0 - μ 1‖ ^ 2 + ‖θ 1 - μ 0‖ ^ 2)

def constantStepGD (p : Params) (A : Algorithm (Means p) (Means p) (Means p)) : Prop :=
  ∃ (point : A.State → Means p) (γ : ℝ), 0 < γ ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) = point state - γ • reply) ∧
    (∀ state, A.output state = point state)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance := Means
  Query := Means
  Reply := Means
  Output := Means
  publicInput := id
  valid p := 0 ≤ p.centre ∧ 0 ≤ p.lower ∧ p.lower ≤ 1 ∧
    0 < p.accuracy ∧ p.accuracy ≤ 1 ∧ 0 < p.failure ∧ p.failure ≤ 1
  admissible p μ oracle := p.lower ≤ ‖μ 0 - μ 1‖ ∧ ‖μ 0 - μ 1‖ ≤ 1 ∧
    ‖(1 / 2 : ℝ) • (μ 0 + μ 1)‖ ≤ p.centre ∧
    ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2
  successful p μ output P := Measurable output ∧
    ENNReal.ofReal (1 - p.failure) ≤
      (P : Measure _) {ω | matchingError μ (output ω) ≤ p.accuracy}
  allowedAlgorithm := constantStepGD

end LongTails.Setups.UntiedGaussianReverseFisher
