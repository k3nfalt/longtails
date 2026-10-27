import LongTails.Setups.CompositeGeneralizedSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.CompositeGapSmooth

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  H0 : ℝ
  H1 : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE

abbrev oraclePublic (p : Params) : CompositeGeneralizedSmooth.Public where
  E := p.E
  L0 := p.H0
  L1 := p.H1
  R := p.R
  Δ := p.Δ
  x0 := p.x0

abbrev Instance (p : Params) := CompositeGeneralizedSmooth.Instance (oraclePublic p)
abbrev Query (p : Params) := CompositeGeneralizedSmooth.Query (oraclePublic p)

noncomputable def objective {p : Params} (I : Instance p) (x : p.E) : ℝ := I.f x + I.ψ x

def AmbientGapUpperModel {p : Params} (I : Instance p) (u : p.E) : Prop :=
  ∀ x ∈ I.Q, ∀ y, Real.sqrt p.H1 * ‖y - x‖ ≤ 1 →
    I.f y ≤ I.f x + ⟪I.grad x, y - x⟫ +
      (p.H0 + p.H1 * (objective I x - objective I u)) * ‖y - x‖ ^ 2

structure Conditions (p : Params) (I : Instance p) (xstar : p.E) : Prop where
  convex_f : ConvexOn ℝ univ I.f
  gradient : ∀ x, HasGradientAt I.f (I.grad x) x
  convex_domain : Convex ℝ I.Q
  convex_regularizer : ConvexOn ℝ I.Q I.ψ
  prox : ∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q ∧
    IsMinOn (CompositeGeneralizedSmooth.proxObjective I a z v) I.Q (I.prox a z v)
  initial_feasible : p.x0 ∈ I.Q
  minimizer_feasible : xstar ∈ I.Q
  minimizer : IsMinOn (objective I) I.Q xstar
  distance : ‖p.x0 - xstar‖ ≤ p.R
  gap : objective I p.x0 - objective I xstar ≤ p.Δ
  model : AmbientGapUpperModel I xstar

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 ≤ p.H0 ∧ 0 ≤ p.H1 ∧ 0 < p.R ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p I O :=
    (∀ k seed x, O.answer k (0, .gradient x) seed = I.grad x) ∧
    (∀ k seed a z v, O.answer k (0, .prox a z v) seed = I.prox a z v) ∧
    ∃ xstar, Conditions p I xstar
  successful p I output P :=
    ∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        output ω ∈ I.Q ∧ objective I (output ω) - objective I xstar ≤ p.ε

end LongTails.Setups.CompositeGapSmooth
