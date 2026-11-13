import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.PointwiseHessianConvex

open OracleTemplate MeasureTheory

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  M₀ : ℝ
  M₁ : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Public.normedE Public.innerE Public.finiteE

structure Params extends Public where
  H₀ : ℝ

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 ≤ p.M₀ ∧ 0 ≤ p.M₁ ∧ 0 < p.R ∧ 0 < p.Δ ∧ 0 ≤ p.H₀ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 3 f ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖) ∧
    ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.H₀ ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R ∧
      f p.x0 - f xstar ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (gradient f x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.PointwiseHessianConvex
