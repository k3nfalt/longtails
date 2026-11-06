import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.Extr

namespace LongTails.Setups.QuasarConvexHessianLipschitz

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  H : ℝ
  γ : ℝ
  R : ℝ
  L₀ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

def QuasarConvexAt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (γ : ℝ) (xstar : E) : Prop :=
  IsMinOn f Set.univ xstar ∧ ∀ x, γ * (f x - f xstar) ≤ ⟪gradient f x, x - xstar⟫

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := ℝ × p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.H ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧ 0 < p.R ∧ 0 ≤ p.L₀ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.H * ‖x - y‖) ∧
    ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.L₀ ∧
    (∃ xstar, QuasarConvexAt f p.γ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R) ∧
    (∀ k x seed, O.answer k (0, x) seed = (f x, gradient f x, fderiv ℝ (gradient f) x))
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.QuasarConvexHessianLipschitz
