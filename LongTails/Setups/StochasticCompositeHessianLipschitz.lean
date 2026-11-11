import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticCompositeHessianLipschitz

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
  ρ : ℝ
  σ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE Params.borelE
  Params.measurableΩ

inductive Query (p : Params) where
  | gradient (x : p.E)
  | prox (a : ℝ) (z v : p.E)

structure Instance (p : Params) where
  f : p.E → ℝ
  grad : p.E → p.E
  hess : p.E → (p.E →L[ℝ] p.E)
  ψ : p.E → ℝ
  Q : Set p.E
  prox : ℝ → p.E → p.E → p.E

noncomputable def objective {p : Params} (I : Instance p) (x : p.E) : ℝ := I.f x + I.ψ x

noncomputable def proxObjective {p : Params} (I : Instance p) (a : ℝ) (z v u : p.E) : ℝ :=
  ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + I.ψ u

noncomputable def gradientMapping {p : Params} (I : Instance p) (x : p.E) : p.E :=
  p.L • (x - I.prox (1 / p.L) x (I.grad x))

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.ρ ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (μ : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, query) ω => match query with
              | .gradient x => g x ω
              | .prox a z v => I.prox a z v } ∧
      (∀ x, HasGradientAt I.f (I.grad x) x) ∧
      (∀ x y, ‖I.grad x - I.grad y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, HasFDerivAt I.grad (I.hess x) x) ∧
      (∀ x y, ‖I.hess x - I.hess y‖ ≤ q.ρ * ‖x - y‖) ∧
      Convex ℝ I.Q ∧ ConvexOn ℝ I.Q I.ψ ∧
      Measurable (fun t : ℝ × q.E × q.E => if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0) ∧
      (∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q ∧
        IsMinOn (proxObjective I a z v) I.Q (I.prox a z v)) ∧
      q.x0 ∈ I.Q ∧
      (∀ x ∈ I.Q, objective I q.x0 - objective I x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) (μ : Measure _)) ∧
      (∀ x, ∫ ω, g x ω ∂(μ : Measure _) = I.grad x) ∧
      (∀ x, Integrable (fun ω => ‖g x ω - I.grad x‖ ^ 2) (μ : Measure _)) ∧
      (∀ x, ∫ ω, ‖g x ω - I.grad x‖ ^ 2 ∂(μ : Measure _) ≤ q.σ ^ 2)
  successful q I output P :=
    Measurable output ∧ (∀ᵐ ω ∂(P : Measure _), output ω ∈ I.Q) ∧
      Integrable (fun ω => ‖gradientMapping I (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradientMapping I (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticCompositeHessianLipschitz
