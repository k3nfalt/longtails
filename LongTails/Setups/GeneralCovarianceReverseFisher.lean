import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.GeneralCovarianceReverseFisher

structure Params where
  dimension : ℕ+
  components : ℕ+
  lower : ℝ
  upper : ℝ
  radius : ℝ
  accuracy : ℝ
  start : Fin components → EuclideanSpace ℝ (Fin dimension)

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.dimension)

abbrev Means (p : Params) := PiLp 2 (fun _ : Fin p.components => Space p)

structure Model (p : Params) where
  covarianceRoot : Space p ≃L[ℝ] Space p
  target : Space p

noncomputable def logMixture {p : Params} {k : ℕ} (A : Space p ≃L[ℝ] Space p)
    (centers : Fin k → Space p) (x : Space p) : ℝ :=
  Real.log (∑ i, Real.exp (-‖A.symm (x - centers i)‖ ^ 2 / 2))

noncomputable def loss {p : Params} (M : Model p) (θ : Means p) : ℝ :=
  (∑ ℓ, ∫ z, ‖gradient (logMixture M.covarianceRoot (fun i => θ i)) (θ ℓ + M.covarianceRoot z) -
      gradient (logMixture M.covarianceRoot (fun _ : Fin 1 => M.target))
        (θ ℓ + M.covarianceRoot z)‖ ^ 2 ∂ProbabilityTheory.stdGaussian (Space p)) /
    p.components

def spectralBounds (p : Params) (M : Model p) : Prop :=
  ∀ v, p.lower * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint
      (M.covarianceRoot : Space p →L[ℝ] Space p) v‖ ^ 2 ∧
    ‖ContinuousLinearMap.adjoint (M.covarianceRoot : Space p →L[ℝ] Space p) v‖ ^ 2 ≤
      p.upper * ‖v‖ ^ 2

def startBound (p : Params) (M : Model p) : Prop :=
  ∀ i, ‖p.start i - M.target‖ ≤ p.radius

def gdFamily (p : Params) (A : Algorithm (Means p) (Means p) (Means p)) : Prop :=
  ∃ (point : A.State → Means p) (step : A.State → ℝ),
    (∀ state, 0 < step state) ∧
    (∀ seed, point (A.initial seed) = WithLp.toLp 2 p.start) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) = point state - step state • reply) ∧
    (∀ state, A.output state = point state)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance := Model
  Query := Means
  Reply := Means
  Output := Means
  publicInput := id
  valid p := 0 < p.lower ∧ p.lower ≤ p.upper ∧ 0 ≤ p.radius ∧ 0 < p.accuracy
  admissible p M oracle := spectralBounds p M ∧ startBound p M ∧
    ∀ k query seed, oracle.answer k query seed = gradient (loss M) query.2
  successful p M output _ := ∀ ω i, ‖output ω i - M.target‖ ^ 2 ≤ p.accuracy
  allowedAlgorithm := gdFamily

end LongTails.Setups.GeneralCovarianceReverseFisher
