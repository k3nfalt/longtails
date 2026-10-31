import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.HeavyTailedTwoPointZerothOrder

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  Δ : ℝ
  σ : ℝ
  p : ℝ
  ε : ℝ
  x0 : Point d

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Point q.d → ℝ
  Query q := Point q.d × Point q.d
  Reply _ := ℝ × ℝ
  Output q := Point q.d
  publicInput q := q
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.Δ ∧ 0 ≤ q.σ ∧ 1 < q.p ∧ q.p ≤ 2 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (F : Point q.d → q.Ω → ℝ) (G : Point q.d → q.Ω → Point q.d)
      (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, y) ω => (F y.1 ω, F y.2 ω) } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f q.x0 - lower ≤ q.Δ) ∧
    Measurable (Function.uncurry F) ∧
    Measurable (Function.uncurry G) ∧
    (∀ ω x, HasGradientAt (fun y => F y ω) (G x ω) x) ∧
    (∀ ω x y, ‖G x ω - G y ω‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x, Integrable (G x) (ν : Measure _)) ∧
    (∀ x, ∫ ω, G x ω ∂(ν : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖G x ω - gradient f x‖ ^ q.p) (ν : Measure _)) ∧
    (∀ x, ∫ ω, ‖G x ω - gradient f x‖ ^ q.p ∂(ν : Measure _) ≤ q.σ ^ q.p)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.HeavyTailedTwoPointZerothOrder
