import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.HessianAdaptiveStochasticConvex

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Public where
  d : ℕ
  C : ConvexBody (Point d)
  x0 : Point d
  D : ℝ
  ρ : ℝ
  σg : ℝ

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  σh : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

structure Instance (p : Public) where
  f : Point p.d → ℝ
  xstar : Point p.d

def IsPSD {d : ℕ} (H : Point d →L[ℝ] Point d) : Prop :=
  (∀ x y, ⟪x, H y⟫ = ⟪H x, y⟫) ∧ ∀ x, 0 ≤ ⟪x, H x⟫

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Bool × Point p.d
  Reply p := Point p.d × (Point p.d →L[ℝ] Point p.d)
  Output p := Point p.d
  publicInput p := p.toPublic
  valid p := 0 < p.D ∧ 0 < p.ρ ∧ 0 ≤ p.σg ∧ 0 ≤ p.σh ∧ 0 < p.ε ∧
    p.x0 ∈ p.C ∧ ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D
  admissible p I O :=
    I.xstar ∈ p.C ∧ IsMinOn I.f p.C I.xstar ∧ ConvexOn ℝ Set.univ I.f ∧
    (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
    Differentiable ℝ (gradient I.f) ∧
    (∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient I.f) x - fderiv ℝ (gradient I.f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    ∃ (g : Point p.d → p.Ω → Point p.d)
      (H : Point p.d → p.Ω → Point p.d →L[ℝ] Point p.d)
      (p0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (p0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, hessian, x) ω =>
            if hessian then (0, H x ω) else (g x ω, 0) } ∧
    Measurable (Function.uncurry g) ∧ Measurable (Function.uncurry H) ∧
    (∀ x ∈ p.C, Integrable (g x) (p0 : Measure _)) ∧
    (∀ x ∈ p.C, ∫ ω, g x ω ∂(p0 : Measure _) = gradient I.f x) ∧
    (∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient I.f x‖ ^ 2) (p0 : Measure _)) ∧
    (∀ x ∈ p.C, ∫ ω, ‖g x ω - gradient I.f x‖ ^ 2 ∂(p0 : Measure _) ≤ p.σg ^ 2) ∧
    (∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) ∧
    (∀ x ∈ p.C,
      Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient I.f) x‖ ^ 2) (p0 : Measure _)) ∧
    (∀ x ∈ p.C,
      ∫ ω, ‖H x ω - fderiv ℝ (gradient I.f) x‖ ^ 2 ∂(p0 : Measure _) ≤ p.σh ^ 2)
  successful p I output P :=
    Measurable output ∧ (∀ ω, output ω ∈ p.C) ∧
    Integrable (fun ω => I.f (output ω) - I.f I.xstar) (P : Measure _) ∧
    (∫ ω, I.f (output ω) - I.f I.xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.HessianAdaptiveStochasticConvex
