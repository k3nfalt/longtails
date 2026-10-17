import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Algorithms.WindowSgd
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory

namespace LongTails.Setups.PLHessianLipschitzKurtosis

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  μ : ℝ
  ρ : ℝ
  σ : ℝ
  K : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE
  Params.borelE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 ≤ p.ρ ∧ 0 ≤ p.σ ∧ 1 ≤ p.K ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ∃ (g : p.E → p.Ω → p.E) (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => p.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧
      (∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) ∧ f p.x0 - f xstar ≤ p.Δ) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x, Integrable (g x) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, g x ω ∂(P0 : Measure _) = gradient f x) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) (P0 : Measure _)) ∧
    (∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 4) (P0 : Measure _)) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂(P0 : Measure _) ≤ p.σ ^ 2) ∧
    (∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 4 ∂(P0 : Measure _) ≤ p.K * p.σ ^ 4)
  successful p f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      ∫ ω, f (output ω) - f xstar ∂(P : Measure _) ≤ p.ε
  allowedAlgorithm p A := ∃ η : ℝ, 0 < η ∧ ∃ Ta Tb : ℕ, A = WindowSgd.method η Ta Tb p.x0

end LongTails.Setups.PLHessianLipschitzKurtosis
