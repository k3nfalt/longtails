import LongTails.Setups.HessianAdaptiveStochasticConvex
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace LongTails.Setups.StochasticThirdDerivativeConvex

open MeasureTheory OracleTemplate
open HessianAdaptiveStochasticConvex (Point)

structure Public where
  d : ℕ
  x0 : Point d
  L₃ : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  σg : ℝ
  σh : ℝ

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := (Point p.d → ℝ) × Point p.d
  Query p := Point p.d
  Reply p := Point p.d × (Point p.d →L[ℝ] Point p.d)
  Output p := Point p.d
  publicInput p := p.toPublic
  valid p := 0 < p.L₃ ∧ 0 < p.R ∧ 0 < p.Δ ∧ 0 < p.ε ∧ 0 ≤ p.σg ∧ 0 ≤ p.σh
  admissible p I O :=
    ContDiff ℝ 3 I.1 ∧ ConvexOn ℝ Set.univ I.1 ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient I.1)) x -
      fderiv ℝ (fderiv ℝ (gradient I.1)) y‖ ≤ p.L₃ * ‖x - y‖) ∧
    IsMinOn I.1 Set.univ I.2 ∧ ‖p.x0 - I.2‖ ≤ p.R ∧ I.1 p.x0 - I.1 I.2 ≤ p.Δ ∧
    ∃ (g : Point p.d → p.Ω → Point p.d)
      (H : Point p.d → p.Ω → Point p.d →L[ℝ] Point p.d)
      (p0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (p0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x) ω => (g x ω, H x ω) } ∧
    StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) p.Ω
      (p0 : Measure _) I.1 g p.σg ∧
    Measurable (Function.uncurry H) ∧
    (∀ x, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient I.1) x‖ ^ 2) (p0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖H x ω - fderiv ℝ (gradient I.1) x‖ ^ 2 ∂(p0 : Measure _) ≤ p.σh ^ 2)
  successful p I output P :=
    Measurable output ∧ (∀ ω, ‖output ω - p.x0‖ ≤ p.R) ∧
    (2 / 3 : ENNReal) ≤ (P : Measure _) {ω | I.1 (output ω) - I.1 I.2 ≤ p.ε}

end LongTails.Setups.StochasticThirdDerivativeConvex
