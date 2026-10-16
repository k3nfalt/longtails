import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff Pointwise

namespace LongTails.Setups.AdaptivePairedZerothOrder

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Public where
  d : ℕ
  dimension_pos : 0 < d
  Q : Set (Point d)
  x0 : Point d
  project : Point d → Point d
  D : ℝ
  γmax : ℝ
  ε : ℝ
  ell : ℝ
  N : ℕ
  T : ℕ

structure Params extends Public where
  Ω : Type
  Ξ : Type
  [measurableΩ : MeasurableSpace Ω]
  [measurableΞ : MeasurableSpace Ξ]
  M : ℝ
  M2 : ℝ
  L : ℝ
  Δ : ℝ
  smooth : Bool

attribute [instance] Params.measurableΩ Params.measurableΞ

structure Instance (p : Public) where
  f : Point p.d → ℝ
  xstar : Point p.d

def domain (p : Public) : Set (Point p.d) := p.Q + Metric.closedBall 0 p.γmax

noncomputable def smoothRadius (p : Public) : ℝ := min p.γmax (p.D / p.N)

noncomputable def nonsmoothRadius (p : Public) : ℝ := min p.γmax (Real.sqrt (Real.sqrt p.d) * p.D / p.N)

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Point p.d
  Reply _ := ℝ
  Output p := Point p.d
  publicInput p := p.toPublic
  valid p :=
    0 < p.D ∧ 0 < p.γmax ∧ 0 < p.ε ∧ Real.log 8 ≤ p.ell ∧ 0 < p.N ∧ 0 < p.T ∧
    0 ≤ p.M ∧ 0 ≤ p.M2 ∧ 0 ≤ p.L ∧ 0 ≤ p.Δ ∧
    IsCompact p.Q ∧ Convex ℝ p.Q ∧ p.x0 ∈ p.Q ∧
    (∀ x ∈ p.Q, ∀ y ∈ p.Q, ‖x - y‖ ≤ p.D) ∧
    (∀ x, p.project x ∈ p.Q) ∧
    (∀ x, ‖x - p.project x‖ = ⨅ y : p.Q, ‖x - y‖) ∧
    (2 ^ 48 * (p.d + p.ell) * (1 + p.M2 ^ 2 * p.D ^ 2 / p.ε ^ 2) + p.N ≤ (p.T : ℝ)) ∧
    (if p.smooth then 32 * (1 + Real.sqrt (p.L * p.D ^ 2 / p.ε)) ≤ (p.N : ℝ)
      else 1024 * (1 + Real.sqrt (Real.sqrt p.d) * p.M * p.D / p.ε +
        Real.sqrt (Real.sqrt p.d) * p.D * Real.sqrt (p.M / (p.γmax * p.ε))) ≤ (p.N : ℝ)) ∧
    Real.sqrt p.d * p.Δ / (if p.smooth then smoothRadius p.toPublic else nonsmoothRadius p.toPublic) ≤
      p.ε / (16384 * p.D)
  admissible p I O :=
    I.xstar ∈ p.Q ∧ IsMinOn I.f p.Q I.xstar ∧
    ConvexOn ℝ (domain p.toPublic) I.f ∧
    (∀ x ∈ domain p.toPublic, ∀ y ∈ domain p.toPublic, |I.f x - I.f y| ≤ p.M * ‖x - y‖) ∧
    (p.smooth = true → ∃ grad : Point p.d → Point p.d,
      (∀ x ∈ interior (domain p.toPublic),
        HasGradientWithinAt I.f (grad x) (interior (domain p.toPublic)) x) ∧
      (∀ x ∈ interior (domain p.toPublic), ∀ y ∈ interior (domain p.toPublic),
        ‖grad x - grad y‖ ≤ p.L * ‖x - y‖)) ∧
    ∃ (F : Point p.d × p.Ω → ℝ) (G : Point p.d × p.Ω → Point p.d)
      (δ : Point p.d → ℝ) (sampleLaw : ProbabilityMeasure p.Ω)
      (sourceLaw : ProbabilityMeasure p.Ξ) (ξ : ℕ → p.Ξ → p.Ω),
      StochasticGeneralizedSmoothAndConvex.IID ξ (sampleLaw : Measure _) (sourceLaw : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := sourceLaw.map (fun z n => ξ (n / 2) z)
            answer := fun _ (_, x) w => F (x, w) + δ x } ∧
      Measurable F ∧ Measurable G ∧ Measurable δ ∧
      (∀ x ∈ domain p.toPublic, |δ x| ≤ p.Δ) ∧
      (∀ x ∈ domain p.toPublic, Integrable (fun w => F (x, w)) (sampleLaw : Measure _)) ∧
      (∀ x ∈ domain p.toPublic, (∫ w, F (x, w) ∂(sampleLaw : Measure _)) = I.f x) ∧
      (∀ᵐ w ∂(sampleLaw : Measure _),
        ContinuousOn (fun x => F (x, w)) (domain p.toPublic) ∧
        LocallyIntegrableOn (fun x => G (x, w)) (interior (domain p.toPublic)) volume ∧
        ∀ ψ : Point p.d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ interior (domain p.toPublic) →
          ∀ v : Point p.d, (∫ x, F (x, w) * (fderiv ℝ ψ x) v) =
            -∫ x, ⟪G (x, w), v⟫ * ψ x) ∧
      (∀ x ∈ interior (domain p.toPublic),
        Integrable (fun w => ‖G (x, w)‖ ^ 2) (sampleLaw : Measure _)) ∧
      (∀ x ∈ interior (domain p.toPublic),
        (∫ w, ‖G (x, w)‖ ^ 2 ∂(sampleLaw : Measure _)) ≤ p.M2 ^ 2)
  successful p I output P :=
    Measurable output ∧ (∀ ζ, output ζ ∈ p.Q) ∧
    Measurable (fun ζ => I.f (output ζ) - I.f I.xstar) ∧
    (P : Measure _).real {ζ | p.ε < I.f (output ζ) - I.f I.xstar} ≤ 8 * Real.exp (-p.ell)

end LongTails.Setups.AdaptivePairedZerothOrder
