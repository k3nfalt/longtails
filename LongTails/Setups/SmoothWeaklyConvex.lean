import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory

namespace LongTails.Setups.SmoothWeaklyConvex

open OracleTemplate

structure Params where
  E : Type u
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace ℝ E]
  [completeSpace : CompleteSpace E]
  [measurableSpace : MeasurableSpace E]
  L : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedAddCommGroup Params.innerProductSpace
  Params.completeSpace Params.measurableSpace

def gdFamily (p : Params) (A : Algorithm p.E p.E p.E) : Prop :=
  ∃ (point best : A.State → p.E) (bestNorm : A.State → ℝ) (count : A.State → ℕ)
    (step : ℕ → ℝ),
    (∀ t, 0 < step t) ∧
    (∀ seed, point (A.initial seed) = p.x0 ∧ best (A.initial seed) = p.x0 ∧
      count (A.initial seed) = 0) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state reply, point (A.update state reply) = point state - step (count state) • reply ∧
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
  admissible p f oracle :=
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    ConvexOn ℝ Set.univ (fun x => f x + p.ρ / 2 * ‖x‖ ^ 2) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f p.x0 - lower ≤ p.Δ)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2
  allowedAlgorithm := gdFamily

end LongTails.Setups.SmoothWeaklyConvex
