import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import LongTails.Setups.HighDimensionalAbcNoiseNonconvex

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
  valid p := 0 < p.L ∧ 0 < p.ε ∧ 1 ≤ p.τ ∧ 4096 * p.ε ≤ p.σ ∧
    2 ^ 26 * p.ε ^ 2 ≤ p.L * p.Δ ∧
    2 ^ 40 * (1 + p.τ * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4) ^ 4 ≤ (p.d : ℝ)
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    ∃ (Z : Type) (_ : MeasurableSpace Z) (κ : Kernel Z Z) (hκ : IsMarkovKernel κ)
        (π : ProbabilityMeasure Z) (g : Space p → Z → Space p),
      O = { Seed := fun _ => Z
            law := @pathLaw Z _ κ hκ π
            answer := fun _ (_, x) z => g x z } ∧
      κ ∘ₘ (π : Measure Z) = (π : Measure Z) ∧
      (∀ t z, mixingDistance κ π t z ≤ 2 * Real.exp (-(t : ℝ) / p.τ)) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (π : Measure Z)) ∧
      (∀ x, ∫ z, g x z ∂(π : Measure Z) = gradient f x) ∧
      (∀ x, Integrable (fun z => ‖g x z - gradient f x‖ ^ 2) (π : Measure Z)) ∧
      (∀ x, ∫ z, ‖g x z - gradient f x‖ ^ 2 ∂(π : Measure Z) ≤ p.σ ^ 2)
  successful p f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.MarkovSmoothNonconvex
