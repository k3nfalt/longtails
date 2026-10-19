import LongTails.Algorithms.Adam
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.HeavyTailedAdam

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  σ : ℝ
  α : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Adam.Point d

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Adam.Point q.d → ℝ
  Query q := Adam.Point q.d
  Reply q := Adam.Point q.d
  Output q := Adam.Point q.d
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : Adam.Point q.d → q.Ω → Adam.Point q.d)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, Integrable (fun ω => ∑ i, |(g x ω - gradient f x) i| ^ q.α) p) ∧
      (∀ x, ∫ ω, ∑ i, |(g x ω - gradient f x) i| ^ q.α ∂p ≤ q.σ ^ q.α)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε
  allowedAlgorithm q A :=
    ∃ (β ρ η τ : ℝ) (n : ℕ), 0 ≤ β ∧ β < 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      0 < η ∧ 0 < τ ∧ A = Adam.method β ρ η τ n q.x0

end LongTails.Setups.HeavyTailedAdam
