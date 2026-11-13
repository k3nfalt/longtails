import LongTails.TemplateTimed
import LongTails.Setups.NetworkModels
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.TimedHomogeneousSmoothNonconvex

open OracleTemplate LongTails.Setups.NetworkModels
open LongTails.Setups.StochasticSmoothAndConvex LongTails.Setups.StochasticGeneralizedSmoothAndConvex

structure Params where
  d : ℕ
  n : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  τ : Fin n → ℝ
  L : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

abbrev spec : TimedSetup where
  Params := Params
  Public := Params
  numNodes p := p.n + 1
  Instance p := Point p → ℝ
  Query p := Point p
  Reply p := Point p
  Output p := Point p
  publicInput p := p
  valid p := 0 < p.n ∧ (∀ i, 0 < p.τ i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f oracles environment :=
    environment = queueEnvironment (starNetwork p.n p.τ 0 0) ∧
    SilentOracle (oracles 0) ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f p.x0 - lower ≤ p.Δ) ∧
    ∀ i : Fin p.n, ∃ (g : Point p → p.Ω → Point p) (μ : ProbabilityMeasure p.Ω)
        (P : ProbabilityMeasure (ℕ → p.Ω)),
      IID (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      oracles i.succ = { Seed := fun _ => p.Ω, law := P, answer := fun _ q ξ => g q.2 (ξ) } ∧
      IsStochasticGradient (Point p) p.Ω μ f g p.σ
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
    ∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.TimedHomogeneousSmoothNonconvex
