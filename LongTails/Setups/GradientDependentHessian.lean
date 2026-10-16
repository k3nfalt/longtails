import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.GradientDependentHessian

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L₀ : ℝ
  L₁ : ℝ
  Δ : ℝ
  G₀ : ℝ
  ε : ℝ
  m : ℕ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L₀ ∧ 0 ≤ p.L₁ ∧ 0 < p.Δ ∧ 0 ≤ p.G₀ ∧ 0 < p.ε ∧ 1 ≤ p.m
  admissible p f O :=
    ContDiff ℝ 3 f ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    ‖gradient f p.x0‖ ≤ p.G₀ ∧
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (gradient f x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
  successful p f output P := ∀ᵐ ω ∂(P : Measure _), ‖gradient f (output ω)‖ ≤ p.ε

end LongTails.Setups.GradientDependentHessian
