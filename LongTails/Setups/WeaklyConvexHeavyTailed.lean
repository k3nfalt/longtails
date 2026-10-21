import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OracleTemplate.ClippedSubgradient

noncomputable def clipReply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ) (v : E) : E := if ‖v‖ ≤ B then v else (B / ‖v‖) • v

inductive Query (E : Type) where
  | subgradient : E → Query E
  | projection : E → Query E

structure State (E : Type) where
  t : ℕ
  x : E
  pending : Bool
  proposal : E
  index : ℕ
  out : E

noncomputable def method {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (η τ : ℝ) (x0 : E) : Algorithm (Query E) E E where
  Seed := Fin (K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (K + 1))).toMeasure, inferInstance⟩
  State := State E
  initial j := ⟨0, x0, false, x0, j.val, x0⟩
  query s := (0, if s.pending then .projection s.proposal else .subgradient s.x)
  update s reply :=
    if s.pending then
      ⟨s.t + 1, reply, false, reply, s.index, if s.t + 1 = s.index then reply else s.out⟩
    else
      ⟨s.t, s.x, true, s.x - η • clipReply τ reply, s.index, s.out⟩
  output s := s.out

end OracleTemplate.ClippedSubgradient

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.WeaklyConvexHeavyTailed

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
  ρ : ℝ
  G : ℝ
  σ : ℝ
  α : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE Params.borelE
  Params.measurableΩ

structure Instance (q : Params) where
  f : q.E → ℝ
  domain : Set q.E

abbrev Query (q : Params) := ClippedSubgradient.Query q.E

noncomputable def proxObj {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (ρ : ℝ) (x y : E) : ℝ :=
  f y + ρ * ‖y - x‖ ^ 2

def IsProx {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (D : Set E) (ρ : ℝ) (prox : E → E) :
    Prop :=
  ∀ x, prox x ∈ D ∧ IsMinOn (proxObj f ρ x) D (prox x)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.ρ ∧ 0 < q.G ∧ 0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (v : q.E → q.E) (projection : q.E → q.E)
      (ν : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (ν : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, query) seed => match query with
            | .subgradient x => g x seed
            | .projection x => projection x } ∧
    Convex ℝ I.domain ∧ IsClosed I.domain ∧ q.x0 ∈ I.domain ∧
    (∀ x ∈ I.domain, ∀ y ∈ I.domain,
      I.f x + ⟪v x, y - x⟫ - q.ρ / 2 * ‖y - x‖ ^ 2 ≤ I.f y) ∧
    (∀ x ∈ I.domain, ‖v x‖ ≤ q.G) ∧
    (∃ lower : ℝ, (∀ x ∈ I.domain, lower ≤ I.f x) ∧ I.f q.x0 - lower ≤ q.Δ) ∧
    Measurable projection ∧
    (∀ x, projection x ∈ I.domain) ∧
    (∀ x, ∀ u ∈ I.domain, ⟪x - projection x, u - projection x⟫ ≤ 0) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x ∈ I.domain, Integrable (g x) (ν : Measure _)) ∧
    (∀ x ∈ I.domain, ∫ ω, g x ω ∂(ν : Measure _) = v x) ∧
    (∀ x ∈ I.domain, Integrable (fun ω => ‖g x ω - v x‖ ^ q.α) (ν : Measure _)) ∧
    (∀ x ∈ I.domain, (∫ ω, ‖g x ω - v x‖ ^ q.α ∂(ν : Measure _)) ≤ q.σ ^ q.α)
  successful q I output P :=
    Measurable output ∧ (∀ ω, output ω ∈ I.domain) ∧
    (∃ prox : q.E → q.E, IsProx I.f I.domain q.ρ prox) ∧
    ∀ prox : q.E → q.E, IsProx I.f I.domain q.ρ prox →
      Integrable (fun ω => (2 * q.ρ) ^ 2 * ‖output ω - prox (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, (2 * q.ρ) ^ 2 * ‖output ω - prox (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2

  allowedAlgorithm q A :=
    ∃ (K : ℕ) (η τ : ℝ), 0 < η ∧ 0 < τ ∧
      A = ClippedSubgradient.method K η τ q.x0

end LongTails.Setups.WeaklyConvexHeavyTailed
