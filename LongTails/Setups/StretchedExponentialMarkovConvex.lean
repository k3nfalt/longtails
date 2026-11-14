import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import LongTails.Setups.FiniteSumNondualSmoothConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.StretchedExponentialMarkovConvex

open OracleTemplate HeavyTailedMarkovSmoothAndConvex

structure Params where
  d : ℕ
  L : ℝ
  R : ℝ
  σ : ℝ
  α : ℝ
  τ : ℝ
  γ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev Space (p : Params) := EuclideanSpace ℝ (Fin p.d)

noncomputable def Params.polynomial (p : Params) (β : ℝ) :
    HeavyTailedMarkovSmoothAndConvex.Params :=
  { E := Space p, Ω := ℝ, L := p.L, R := p.R, σ := p.σ, α := p.α,
    τ := p.τ * (β / p.γ) ^ (1 / p.γ), β := β, ε := p.ε, x0 := p.x0 }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p
  Reply p := Space p
  Output p := Space p
  publicInput p := p
  valid p := 0 < p.d ∧ 0 < p.L ∧ 0 < p.R ∧ 0 < p.σ ∧
    1 < p.α ∧ p.α ≤ 2 ∧ 1 ≤ p.τ ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧ 0 < p.ε ∧
    4 * p.ε ≤ p.L * p.R ^ 2 ∧ 32 * p.ε ≤ p.σ * p.R ∧
    p.L * p.R ^ 2 / p.ε ≤ (p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))
  admissible p f O :=
    ∃ (g : Space p → ℝ → Space p) (κ : Kernel ℝ ℝ) (hκ : IsMarkovKernel κ)
        (π : ProbabilityMeasure ℝ),
      O = { Seed := fun _ => ℝ
            law := @pathLaw ℝ _ κ hκ π
            answer := fun _ (_, x) z => g x z } ∧
      κ ∘ₘ (π : Measure ℝ) = (π : Measure ℝ) ∧
      (∀ t, Integrable (mixingDistance κ π t) (π : Measure ℝ)) ∧
      (∀ t, (∫ z, mixingDistance κ π t z ∂(π : Measure ℝ)) ≤
        Real.exp (-(((t : ℝ) / p.τ) ^ p.γ))) ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
      (∃ xstar : Space p, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.R) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (π : Measure ℝ)) ∧
      (∀ x, ∫ z, g x z ∂(π : Measure ℝ) = gradient f x) ∧
      (∀ x : Space p, Integrable (fun z => ‖g x z - gradient f x‖ ^ p.α) (π : Measure ℝ)) ∧
      (∀ x : Space p, (∫ z, ‖g x z - gradient f x‖ ^ p.α ∂(π : Measure ℝ)) ≤ p.σ ^ p.α)
  successful p f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.StretchedExponentialMarkovConvex
