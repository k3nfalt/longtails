import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.SymmetricFirstMomentNonconvex

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  Λ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.Λ ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : EuclideanSpace ℝ (Fin q.d) → q.Ω → EuclideanSpace ℝ (Fin q.d))
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ∂p ≤ q.σ) ∧
      (∀ x y, ∫ ω, ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ∂p ≤
        q.Λ * ‖x - y‖) ∧
      (∀ x (i : Fin q.d),
        (p : Measure _).map (fun ω => (g x ω - gradient f x) i) =
        (p : Measure _).map (fun ω => -(g x ω - gradient f x) i))
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.SymmetricFirstMomentNonconvex
