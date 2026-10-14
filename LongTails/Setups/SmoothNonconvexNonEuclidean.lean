import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic

open MeasureTheory

namespace LongTails.Setups.SmoothNonconvexNonEuclidean

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  L : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E →L[ℝ] ℝ
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ k seed x, HasFDerivAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ x, HasFDerivAt f (fderiv ℝ f x) x) ∧
    (∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ)
  successful q f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖fderiv ℝ f (output ω)‖^2) (P : Measure _) ∧
    (∫ ω, ‖fderiv ℝ f (output ω)‖^2 ∂(P : Measure _)) ≤ q.ε^2

end LongTails.Setups.SmoothNonconvexNonEuclidean
