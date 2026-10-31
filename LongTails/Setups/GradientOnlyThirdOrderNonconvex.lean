import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.GradientOnlyThirdOrderNonconvex

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L₁ : ℝ
  L₃ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L₁ ∧ 0 < p.L₃ ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 3 f ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L₁ * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ p.L₃ * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = gradient f x)
  successful p f output P := ∀ᵐ ω ∂(P : Measure _), ‖gradient f (output ω)‖ ≤ p.ε

end LongTails.Setups.GradientOnlyThirdOrderNonconvex
