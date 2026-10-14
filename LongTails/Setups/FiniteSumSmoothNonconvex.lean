import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Algebra.Order.BigOperators.Expect

open MeasureTheory
open scoped BigOperators

namespace LongTails.Setups.FiniteSumSmoothNonconvex

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ k seed i x, HasGradientAt (f i) (oracle.answer k (0, (i, x)) seed) x) ∧
    (∀ x y, (𝔼 i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.L ^ 2 * ‖x - y‖ ^ 2) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ LongTails.Setups.FiniteSumSmoothAndConvex.objective f x) ∧
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 - lower ≤ p.Δ)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (output ω)‖ ^ 2)
      (P : Measure _) ∧
    (∫ ω, ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.FiniteSumSmoothNonconvex
