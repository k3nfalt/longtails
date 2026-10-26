import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.HessianLipschitzSecondOrder

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  H : ℝ
  Δ : ℝ
  ε : ℝ
  m : ℝ
  ρ : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := (ℝ × p.E) ⊕ (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.H ∧ 0 ≤ p.Δ ∧ 0 < p.ε ∧ 1 ≤ p.m ∧ 0 < p.ρ ∧ p.ρ < 1
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.H * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = Sum.inl (f x, gradient f x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = Sum.inr (fderiv ℝ (gradient f) x))
  successful p f output P :=
    ENNReal.ofReal (1 - p.ρ) ≤ (P : Measure _) {ω |
      ‖gradient f (output ω)‖ ≤ p.ε ∧
      ∀ v, -Real.sqrt (p.H * p.ε) * ‖v‖ ^ 2 ≤
        ⟪v, fderiv ℝ (gradient f) (output ω) v⟫}

end LongTails.Setups.HessianLipschitzSecondOrder
