import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.GeneralizedAffineHessianVector

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L0 : ℝ
  L1 : ℝ
  σg : ℝ
  αg : ℝ
  σh : ℝ
  αh : ℝ
  p : ℝ
  q : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.d)

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p × Option (Space p)
  Reply p := Space p
  Output p := Space p
  publicInput p := p
  valid p := 0 ≤ p.L0 ∧ 0 ≤ p.L1 ∧
    0 ≤ p.σg ∧ 0 ≤ p.αg ∧ 0 ≤ p.σh ∧ 0 ≤ p.αh ∧
    1 < p.p ∧ p.p ≤ 2 ∧ 1 < p.q ∧ p.q ≤ 2 ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : Space p → p.Ω → Space p)
      (h : (Space p × Space p) → p.Ω → Space p)
      (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x, v) seed =>
            match v with
            | none => g x seed
            | some w => h (x, w) seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    ContDiff ℝ 1 (gradient f) ∧
    (∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖) ∧
    (∃ m : ℝ, (∀ x, m ≤ f x) ∧ f p.x0 - m ≤ p.Δ) ∧
    Measurable (Function.uncurry g) ∧
    Measurable (Function.uncurry h) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p.p) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ p.p ∂(P0 : Measure _) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖gradient f x‖ ^ p.p) ∧
    (∀ x v, Integrable (h (x, v)) (P0 : Measure _)) ∧
    (∀ x v, ∫ ω, h (x, v) ω ∂(P0 : Measure _) = fderiv ℝ (gradient f) x v) ∧
    (∀ x v, Integrable (fun ω => ‖h (x, v) ω - fderiv ℝ (gradient f) x v‖ ^ p.q)
      (P0 : Measure _)) ∧
    (∀ x v, ∫ ω, ‖h (x, v) ω - fderiv ℝ (gradient f) x v‖ ^ p.q
      ∂(P0 : Measure _) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖gradient f x‖ ^ p.q) * ‖v‖ ^ p.q)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
    (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GeneralizedAffineHessianVector
