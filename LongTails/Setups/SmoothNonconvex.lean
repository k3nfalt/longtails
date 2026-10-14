import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.SmoothNonconvex

open OracleTemplate

structure Params where
  E : Type u
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace ℝ E]
  [completeSpace : CompleteSpace E]
  [measurableSpace : MeasurableSpace E]
  L : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedAddCommGroup Params.innerProductSpace
  Params.completeSpace Params.measurableSpace

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f p.x0 - lower ≤ p.Δ)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖^2) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖^2 ∂(P : Measure _)) ≤ p.ε^2

end LongTails.Setups.SmoothNonconvex
