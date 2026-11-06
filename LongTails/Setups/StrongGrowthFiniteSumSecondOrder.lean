import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Setups.StrongGrowthFiniteSumSecondOrder

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace BigOperators

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  n : ℕ
  [nonzero : NeZero n]
  x0 : E
  κ : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E × (p.E →L[ℝ] p.E)
  Output p := p.E
  publicInput p := p
  valid p := 1 ≤ p.κ ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    (∀ i, ContDiff ℝ 2 (f i)) ∧
    (∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) x‖ ^ 2 ≤
      p.κ * ‖gradient (FiniteSumSmoothAndConvex.objective f) x‖ ^ 2) ∧
    (∀ x y, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) x - fderiv ℝ (gradient (f i)) y‖ ^ 2 ≤
        p.ρ ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ x, FiniteSumSmoothAndConvex.objective f p.x0 -
      FiniteSumSmoothAndConvex.objective f x ≤ p.Δ) ∧
    (∀ k seed i x, O.answer k (0, (i, x)) seed =
      (gradient (f i) x, fderiv ℝ (gradient (f i)) x))
  successful p f output P :=
    let event := {ω |
      ‖gradient (FiniteSumSmoothAndConvex.objective f) (output ω)‖ ≤ p.ε ∧
      ∀ v, -Real.sqrt (p.ρ * p.ε) * ‖v‖ ^ 2 ≤
        ⟪v, fderiv ℝ (gradient (FiniteSumSmoothAndConvex.objective f)) (output ω) v⟫}
    MeasurableSet event ∧ ENNReal.ofReal (2 / 3 : ℝ) ≤ (P : Measure _) event

end LongTails.Setups.StrongGrowthFiniteSumSecondOrder
