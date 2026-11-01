import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace LongTails.Setups.SmoothHessianLipschitzGd

open OracleTemplate MeasureTheory

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

def adaptiveGdFamily (p : Params) (A : Algorithm p.E p.E p.E) : Prop :=
  ∃ (point best : A.State → p.E) (bestNorm : A.State → ℝ) (count : A.State → ℕ)
    (step : A.State → p.E → ℝ),
    (∀ state reply, 0 < step state reply) ∧
    (∀ seed, point (A.initial seed) = p.x0 ∧ best (A.initial seed) = p.x0 ∧
      count (A.initial seed) = 0) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) = point state - step state reply • reply ∧
      count (A.update state reply) = count state + 1 ∧
      best (A.update state reply) =
        (if count state = 0 ∨ ‖reply‖ ^ 2 ≤ bestNorm state then point state else best state) ∧
      bestNorm (A.update state reply) =
        (if count state = 0 ∨ ‖reply‖ ^ 2 ≤ bestNorm state then ‖reply‖ ^ 2 else bestNorm state)) ∧
    (∀ state, A.output state = best state)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = gradient f x)
  successful p f output P :=
    ∀ᵐ ω ∂(P : Measure _), ‖gradient f (output ω)‖ ≤ p.ε
  allowedAlgorithm := adaptiveGdFamily

end LongTails.Setups.SmoothHessianLipschitzGd
