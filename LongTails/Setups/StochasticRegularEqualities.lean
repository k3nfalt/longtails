import LongTails.Setups.FiniteVarianceSpectralSmooth
import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.StochasticRegularEqualities

open OracleTemplate
open LongTails.Algorithms.MatrixPolar

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Public where
  d : ℕ
  m : ℕ
  x0 : Point d
  Lf : ℝ
  Lc : ℝ
  LJ : ℝ
  ν : ℝ
  σ : ℝ
  Lnoise : ℝ
  Δ : ℝ
  C0 : ℝ
  ε : ℝ

structure Params extends Public where
  Ω : Type
  Ξ : Type
  [measurableΩ : MeasurableSpace Ω]
  [measurableΞ : MeasurableSpace Ξ]

attribute [instance] Params.measurableΩ Params.measurableΞ

structure Instance (p : Public) where
  f : Point p.d → ℝ
  c : Point p.d → Point p.m

noncomputable def jacobian {p : Public} (I : Instance p) (x : Point p.d) : Space p.d p.m :=
  (operatorEquiv p.d p.m).symm (fderiv ℝ I.c x).adjoint

abbrev Reply (p : Public) := Point p.d × Point p.m × Space p.d p.m

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Point p.d
  Reply := Reply
  Output p := Point p.d × Point p.m
  publicInput p := p.toPublic
  valid p :=
    0 < p.d ∧ 0 < p.m ∧ p.m ≤ p.d ∧ 0 < p.ν ∧
    0 ≤ p.Lf ∧ 0 ≤ p.Lc ∧ 0 ≤ p.LJ ∧
    0 ≤ p.σ ∧ 0 ≤ p.Lnoise ∧ 0 ≤ p.Δ ∧ 0 ≤ p.C0 ∧ 0 < p.ε ∧ p.ε ≤ 1
  admissible p I O :=
    (∀ x, HasGradientAt I.f (gradient I.f x) x) ∧
    Differentiable ℝ I.c ∧
    (∃ fLower : ℝ, (∀ x, fLower ≤ I.f x) ∧ I.f p.x0 - fLower ≤ p.Δ) ∧
    ‖I.c p.x0‖ ≤ p.C0 ∧
    (∀ x y, ‖gradient I.f y - gradient I.f x‖ ≤ p.Lf * ‖y - x‖) ∧
    (∀ x, ‖jacobian I x‖ ≤ p.Lc) ∧
    (∀ x y, ‖jacobian I y - jacobian I x‖ ≤ p.LJ * ‖y - x‖) ∧
    (∀ x v, p.ν * ‖v‖ ≤ ‖(fderiv ℝ I.c x).adjoint v‖) ∧
    ∃ (g : Point p.d × p.Ω → Point p.d)
      (c : Point p.d × p.Ω → Point p.m)
      (J : Point p.d × p.Ω → Space p.d p.m)
      (sampleLaw : ProbabilityMeasure p.Ω) (sourceLaw : ProbabilityMeasure p.Ξ)
      (ξ : ℕ → p.Ξ → p.Ω),
      StochasticGeneralizedSmoothAndConvex.IID ξ
        (sampleLaw : Measure _) (sourceLaw : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := sourceLaw.map (fun z n => ξ (n / 2) z)
            answer := fun _ (_, x) w => (g (x, w), c (x, w), J (x, w)) } ∧
      Measurable g ∧ Measurable c ∧ Measurable J ∧
      (∀ x, Integrable (fun w => g (x, w)) (sampleLaw : Measure _)) ∧
      (∀ x, Integrable (fun w => c (x, w)) (sampleLaw : Measure _)) ∧
      (∀ x, Integrable (fun w => J (x, w)) (sampleLaw : Measure _)) ∧
      (∀ x, (∫ w, g (x, w) ∂(sampleLaw : Measure _)) = gradient I.f x) ∧
      (∀ x, (∫ w, c (x, w) ∂(sampleLaw : Measure _)) = I.c x) ∧
      (∀ x, (∫ w, J (x, w) ∂(sampleLaw : Measure _)) = jacobian I x) ∧
      (∀ x, Integrable (fun w => ‖g (x, w) - gradient I.f x‖ ^ 2 +
        ‖c (x, w) - I.c x‖ ^ 2 + ‖J (x, w) - jacobian I x‖ ^ 2)
        (sampleLaw : Measure _)) ∧
      (∀ x, (∫ w, ‖g (x, w) - gradient I.f x‖ ^ 2 +
        ‖c (x, w) - I.c x‖ ^ 2 + ‖J (x, w) - jacobian I x‖ ^ 2
        ∂(sampleLaw : Measure _)) ≤ p.σ ^ 2) ∧
      (∀ x y, Integrable (fun w => ‖g (y, w) - g (x, w)‖ ^ 2 +
        ‖c (y, w) - c (x, w)‖ ^ 2 + ‖J (y, w) - J (x, w)‖ ^ 2)
        (sampleLaw : Measure _)) ∧
      (∀ x y, (∫ w, ‖g (y, w) - g (x, w)‖ ^ 2 +
        ‖c (y, w) - c (x, w)‖ ^ 2 + ‖J (y, w) - J (x, w)‖ ^ 2
        ∂(sampleLaw : Measure _)) ≤ p.Lnoise ^ 2 * ‖y - x‖ ^ 2)
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω).1 +
      (fderiv ℝ I.c (output ω).1).adjoint (output ω).2‖ ^ 2 +
      ‖I.c (output ω).1‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω).1 +
      (fderiv ℝ I.c (output ω).1).adjoint (output ω).2‖ ^ 2 +
      ‖I.c (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.StochasticRegularEqualities
