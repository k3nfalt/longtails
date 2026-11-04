import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

namespace LongTails.Setups.StochasticLocalHessianConvex

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : Point d
  M₀ : ℝ
  M₁ : ℝ
  ρ : ℝ
  δ : ℝ
  σ : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  β : ℝ

attribute [instance] Params.measurableΩ

structure Instance (p : Params) where
  f : Point p.d → ℝ
  xstar : Point p.d

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance := Instance
  Query p := Point p.d
  Reply p := Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)
  Output p := Point p.d
  publicInput p := p
  valid p := 0 ≤ p.M₀ ∧ 0 ≤ p.M₁ ∧ 0 < p.ρ ∧ 0 ≤ p.δ ∧ 0 ≤ p.σ ∧
    0 < p.R ∧ 0 < p.Δ ∧ 0 < p.ε ∧ 0 < p.β ∧ p.β < 1
  admissible p I O :=
    ContDiff ℝ 2 I.f ∧ ConvexOn ℝ Set.univ I.f ∧
    IsMinOn I.f Set.univ I.xstar ∧ ‖p.x0 - I.xstar‖ ≤ p.R ∧
    I.f p.x0 - I.f I.xstar ≤ p.Δ ∧
    (∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖fderiv ℝ (gradient I.f) y - fderiv ℝ (gradient I.f) x‖ ≤
        (p.M₀ + p.M₁ * ‖gradient I.f x‖) * ‖y - x‖) ∧
    ∃ (g : Point p.d → p.Ω → Point p.d)
      (H : Point p.d → Point p.d →L[ℝ] Point p.d)
      (p0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (p0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (i, x) ω =>
            if i = 0 then Sum.inl (g x ω) else Sum.inr (H x) } ∧
    Measurable (Function.uncurry g) ∧ Measurable H ∧
    (∀ x, Integrable (g x) (p0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(p0 : Measure _) = gradient I.f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient I.f x‖ ^ 2) (p0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient I.f x‖ ^ 2 ∂(p0 : Measure _) ≤ p.σ ^ 2) ∧
    (∀ x, ‖H x - fderiv ℝ (gradient I.f) x‖ ≤ p.δ)
  successful p I output P :=
    Measurable output ∧
    (P : Measure _) {ω | p.ε < I.f (output ω) - I.f I.xstar} ≤ ENNReal.ofReal p.β

end LongTails.Setups.StochasticLocalHessianConvex
