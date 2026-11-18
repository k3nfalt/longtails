import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.MarkovSmoothNonconvex

open OracleTemplate HeavyTailedMarkovSmoothAndConvex

structure Params where
  d : ℕ
  L : ℝ
  Δ : ℝ
  σ : ℝ
  τ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.d)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p
  Reply p := Space p
  Output p := Space p
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.ε ∧ 1 ≤ p.τ ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ
  admissible p f O :=
    ∃ (g : Space p → ℝ → Space p) (κ : Kernel ℝ ℝ) (hκ : IsMarkovKernel κ)
        (π : ProbabilityMeasure ℝ) (fstar : ℝ),
      O = { Seed := fun _ => ℝ
            law := @pathLaw ℝ _ κ hκ π
            answer := fun _ (_, x) z => g x z } ∧
      κ ∘ₘ (π : Measure ℝ) = (π : Measure ℝ) ∧
      (∀ t, Integrable (mixingDistance κ π t) (π : Measure ℝ)) ∧
      (∀ t, (∫ z, mixingDistance κ π t z ∂(π : Measure ℝ)) ≤ 2 * Real.exp (-(t : ℝ) / p.τ)) ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
      (∀ x, fstar ≤ f x) ∧ (∀ η > 0, ∃ x, f x < fstar + η) ∧ f p.x0 - fstar ≤ p.Δ ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (π : Measure ℝ)) ∧
      (∀ x, ∫ z, g x z ∂(π : Measure ℝ) = gradient f x) ∧
      (∀ x, Integrable (fun z => ‖g x z - gradient f x‖ ^ 2) (π : Measure ℝ)) ∧
      (∀ x, (∫ z, ‖g x z - gradient f x‖ ^ 2 ∂(π : Measure ℝ)) ≤ p.σ ^ 2)
  successful p f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.MarkovSmoothNonconvex
