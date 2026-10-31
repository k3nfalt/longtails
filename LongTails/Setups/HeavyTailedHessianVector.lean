import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.HeavyTailedHessianVector

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  ρ : ℝ
  σg : ℝ
  σh : ℝ
  p : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.d)

def secondOrderAccurate (p : Params) (f : Space p → ℝ) (x : Space p) : Prop :=
  ‖gradient f x‖ ≤ p.ε ∧
    ∀ v : Space p, -Real.sqrt (p.ρ * p.ε) * ‖v‖ ^ 2 ≤
      ⟪v, fderiv ℝ (gradient f) x v⟫

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p × Option (Space p)
  Reply p := Space p
  Output p := Space p
  publicInput p := p
  valid p := 0 < p.d ∧ 0 < p.L ∧ 0 < p.ρ ∧ 0 ≤ p.σg ∧ 0 ≤ p.σh ∧
    1 < p.p ∧ p.p ≤ 2 ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : Space p → p.Ω → Space p)
      (H : Space p → p.Ω → Space p →L[ℝ] Space p)
      (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x, v) seed =>
            match v with
            | none => g x seed
            | some w => H x seed w } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∃ m : ℝ, (∀ x, m ≤ f x) ∧ f p.x0 - m ≤ p.Δ) ∧
    Measurable (Function.uncurry g) ∧
    Measurable (Function.uncurry H) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p.p) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ p.p ∂(P0 : Measure _) ≤ p.σg ^ p.p) ∧
    (∀ x v, Integrable (fun ω => H x ω v) (P0 : Measure _)) ∧
    (∀ x v, ∫ ω, H x ω v ∂(P0 : Measure _) = fderiv ℝ (gradient f) x v) ∧
    (∀ x v, Integrable (fun ω => ‖H x ω v - fderiv ℝ (gradient f) x v‖ ^ p.p)
      (P0 : Measure _)) ∧
    (∀ x v, ∫ ω, ‖H x ω v - fderiv ℝ (gradient f) x v‖ ^ p.p ∂(P0 : Measure _) ≤
      p.σh ^ p.p * ‖v‖ ^ p.p)
  successful p f output P :=
    Measurable output ∧
      (P : Measure _).real {ω | secondOrderAccurate p f (output ω)} ≥ 2 / 3

end LongTails.Setups.HeavyTailedHessianVector
