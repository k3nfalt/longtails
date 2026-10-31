import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LongTails.Setups.NonsmoothHiddenConvex

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  μ : ℝ
  Lc : ℝ
  LJ : ℝ
  G : ℝ
  R : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.linearE Params.finiteE Params.completeE
  Params.measurableE Params.borelE Params.countableE Params.measurableΩ

structure Instance (p : Params) where
  F : p.E → ℝ
  H : p.E → ℝ
  c : p.E ≃ₜ p.E
  J : p.E → p.E →L[ℝ] p.E
  g : p.E → p.E

def IsPulledSubgradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E → ℝ) (c : E → E) (J : E → E →L[ℝ] E) (g : E → E) (x : E) : Prop :=
  ∃ s : E, (∀ u, H (c x) + ⟪s, u - c x⟫ ≤ H u) ∧
    ∀ v, ⟪g x, v⟫ = ⟪s, J x v⟫

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := id
  valid q := 0 < q.μ ∧ q.μ ≤ q.Lc ∧ 0 ≤ q.LJ ∧ 0 < q.G ∧ 0 < q.R ∧ 0 < q.ε
  admissible q I O :=
    ∃ (oracle : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => oracle x seed } ∧
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    Measurable (Function.uncurry oracle) ∧
    (∀ x, Integrable (oracle x) (p : Measure _)) ∧
    (∀ x, Integrable (fun ω => ‖oracle x ω‖ ^ 2) (p : Measure _)) ∧
    (∀ x, ∫ ω, oracle x ω ∂(p : Measure _) = I.g x) ∧
    (∀ x, ∫ ω, ‖oracle x ω‖ ^ 2 ∂(p : Measure _) ≤ q.G ^ 2) ∧
    (∀ x, I.F x = I.H (I.c x)) ∧
    ConvexOn ℝ Set.univ I.H ∧
    (∀ x, HasFDerivAt I.c (I.J x) x) ∧
    (∀ x y, q.μ * ‖x - y‖ ≤ ‖I.c x - I.c y‖) ∧
    (∀ x y, ‖I.c x - I.c y‖ ≤ q.Lc * ‖x - y‖) ∧
    (∀ x y, ‖I.J x - I.J y‖ ≤ q.LJ * ‖x - y‖) ∧
    (∀ x, IsPulledSubgradient I.H I.c I.J I.g x) ∧
    (∀ y, ‖y‖ = q.R → I.F 0 ≤ I.F y) ∧
    (∃ xstar, IsMinOn I.F Set.univ xstar)
  successful q I output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn I.F Set.univ xstar ∧
      Integrable (fun ω => I.F (output ω) - I.F xstar) (P : Measure _) ∧
      (∫ ω, I.F (output ω) - I.F xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.NonsmoothHiddenConvex
