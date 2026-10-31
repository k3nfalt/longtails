import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.AuxiliarySimilarityNonconvex

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L : ℝ
  δ : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := (p.E → ℝ) × (p.E → ℝ)
  Query p := p.E
  Reply p := ℝ × p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 ≤ p.L ∧ 0 < p.δ ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p I O :=
    ContDiff ℝ 2 I.1 ∧ Differentiable ℝ I.2 ∧
    (∀ x y, ‖fderiv ℝ (gradient I.1) x - fderiv ℝ (gradient I.1) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∀ x y, ‖(gradient I.1 x - gradient I.2 x) - (gradient I.1 y - gradient I.2 y)‖ ≤
      p.δ * ‖x - y‖) ∧
    (∀ x y, ‖gradient I.2 x - gradient I.2 y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x, I.1 p.x0 - I.1 x ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = (I.1 x, gradient I.1 x)) ∧
    (∀ k x seed, O.answer k (1, x) seed = (I.2 x, gradient I.2 x))
  successful p I output P :=
    ∀ᵐ ω ∂(P : Measure _), ‖gradient I.1 (output ω)‖ ≤ p.ε

end LongTails.Setups.AuxiliarySimilarityNonconvex
