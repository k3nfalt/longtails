import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shortStep (L : ℝ) (x gradient atom : E) : E :=
  x + min 1 (⟪gradient, x - atom⟫ / (L * ‖atom - x‖ ^ 2)) • (atom - x)

noncomputable def shortStepFrankWolfe (L : ℝ) (x0 : E) : Algorithm (E ⊕ E) E E where
  State := Bool × E × E
  initial _ := (false, x0, 0)
  query state := (0, if state.1 then Sum.inr state.2.2 else Sum.inl state.2.1)
  update state reply :=
    if state.1 then (false, shortStep L state.2.1 state.2.2 reply, 0)
    else (true, state.2.1, reply)
  output state := state.2.1

end OracleTemplate.FrankWolfe

open Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.UniformlyConvexHolder

open OracleTemplate OracleTemplate.FrankWolfe

def UniformlyConvexSet {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (a q : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : E, ‖z‖ ≤ 1 →
    t • x + (1 - t) • y + (a * t * (1 - t) * ‖x - y‖ ^ q) • z ∈ C

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  L : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.finiteE

structure Params extends Public where
  D : ℝ
  a : ℝ
  q : ℝ
  c : ℝ
  r : ℝ
  ε : ℝ

structure Instance (p : Public) where
  f : p.E → ℝ
  C : Set p.E

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := p.E ⊕ p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.L ∧ 0 < p.D ∧ 0 < p.a ∧ 3 < p.q ∧ 0 < p.c ∧ 2 < p.r ∧ 0 < p.ε
  admissible p I oracle :=
    IsCompact I.C ∧ UniformlyConvexSet I.C p.a p.q ∧ p.x0 ∈ I.C ∧
    (∀ x ∈ I.C, ∀ y ∈ I.C, ‖x - y‖ ≤ p.D) ∧
    ConvexOn ℝ I.C I.f ∧
    (∀ k seed x, x ∈ I.C → HasGradientAt I.f (oracle.answer k (0, (Sum.inl x)) seed) x) ∧
    (∀ k seed x, x ∈ I.C → ∀ y ∈ I.C,
      ‖oracle.answer k (0, (Sum.inl x)) seed - oracle.answer k (0, (Sum.inl y)) seed‖ ≤ p.L * ‖x - y‖) ∧
    (∀ k seed g, oracle.answer k (0, (Sum.inr g)) seed ∈ I.C ∧
      ∀ x ∈ I.C, ⟪g, oracle.answer k (0, (Sum.inr g)) seed⟫ ≤ ⟪g, x⟫) ∧
    (∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      ∀ x ∈ I.C, ∃ y ∈ I.C, IsMinOn I.f I.C y ∧
        ‖x - y‖ ≤ p.c * (I.f x - I.f xstar) ^ (1 / p.r))
  successful p I output P :=
    ∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        output ω ∈ I.C ∧ I.f (output ω) - I.f xstar ≤ p.ε
  allowedAlgorithm p A := A = shortStepFrankWolfe p.L p.x0

end LongTails.Setups.UniformlyConvexHolder
