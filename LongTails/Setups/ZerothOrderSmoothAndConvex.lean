import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic

open MeasureTheory

namespace LongTails.Setups.ZerothOrderSmoothAndConvex

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  d : ℕ
  L : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply _ := ℝ
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f O :=
    Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) ∧
    ∃ (g : q.E → q.Ω → ℝ) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    ProbabilityTheory.iIndepFun (fun k (ω : ℕ → q.Ω) => ω k) (P : Measure _) ∧
    (∀ k, (P : Measure (ℕ → q.Ω)).map (fun ω => ω k) = (p : Measure _)) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (p : Measure _)) ∧
    (∀ x, (∫ z, g x z ∂(p : Measure _)) = f x) ∧
    (∀ x, Integrable (fun z => (g x z - f x)^2) (p : Measure _)) ∧
    (∀ x, (∫ z, (g x z - f x)^2 ∂(p : Measure _)) ≤ q.σ^2)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.ZerothOrderSmoothAndConvex
