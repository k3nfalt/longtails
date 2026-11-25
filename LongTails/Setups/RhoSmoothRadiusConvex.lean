import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LongTails.Template

namespace LongTails.Setups.RhoSmoothRadiusConvex

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  L0 : ℝ
  L1 : ℝ
  ρ : ℝ
  x0 : E
  R : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.linearE Params.completeE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := id
  valid p := 0 < p.L0 ∧ 0 < p.L1 ∧ 1 < p.ρ ∧ p.ρ ≤ 2 ∧ 0 < p.R ∧ 0 < p.ε
  admissible p f oracle :=
    ConvexOn ℝ Set.univ f ∧
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ k seed, Differentiable ℝ (fun x => oracle.answer k (0, x) seed)) ∧
    (∀ k seed x, ‖fderiv ℝ (fun y => oracle.answer k (0, y) seed) x‖ ≤
      p.L0 + p.L1 * ‖oracle.answer k (0, x) seed‖ ^ p.ρ) ∧
    (∃ xstar : p.E, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R)
  successful p f output P :=
    ∃ xstar : p.E, IsMinOn f Set.univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε

end LongTails.Setups.RhoSmoothRadiusConvex
