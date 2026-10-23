import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Setups.CompositionalEntropicRisk

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ξ : Type
  [measurableΞ : MeasurableSpace Ξ]
  n : ℕ
  [nonzero : NeZero n]
  B : ℕ
  c0 : ℝ
  c1 : ℝ
  G : ℝ
  κ : ℝ
  σ : ℝ
  R : ℝ
  ε : ℝ
  w0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΞ Params.nonzero

structure Instance (q : Params) where
  score : Fin q.n → q.E → q.Ξ → ℝ
  grad : Fin q.n → q.E → q.Ξ → q.E
  law : Fin q.n → ProbabilityMeasure q.Ξ
  domain : Set q.E

noncomputable def normalizer {q : Params} (I : Instance q) (i : Fin q.n) (w : q.E) : ℝ :=
  ∫ ξ, Real.exp (I.score i w ξ) ∂(I.law i : Measure q.Ξ)

noncomputable def objective {q : Params} (I : Instance q) (w : q.E) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, Real.log (normalizer I i w)

inductive Query (q : Params) where
  | sample : q.E → Query q
  | projection : q.E → Query q

inductive Reply (q : Params) where
  | sample : Fin q.n → ℝ × q.E → ℝ × q.E → Reply q
  | projection : q.E → Reply q

abbrev Seed (q : Params) := Fin q.n × (Fin q.n → q.Ξ) × (Fin q.n → q.Ξ)

noncomputable def sampleLaw {q : Params} (I : Instance q) : Measure (Seed q) :=
  (PMF.uniformOfFintype (Fin q.n)).toMeasure.prod
    ((Measure.pi fun i => (I.law i : Measure q.Ξ)).prod (Measure.pi fun i => (I.law i : Measure q.Ξ)))

noncomputable def sampleOracle {q : Params} (I : Instance q) (projection : q.E → q.E)
    (P : ProbabilityMeasure (ℕ → Seed q)) : Oracle (Query q) (Reply q) where
  Seed := fun _ => Seed q
  law := P
  answer := fun _ (_, query) seed => match query with
    | .sample w => .sample seed.1
        (I.score seed.1 w (seed.2.1 seed.1), I.grad seed.1 w (seed.2.1 seed.1))
        (I.score seed.1 w (seed.2.2 seed.1), I.grad seed.1 w (seed.2.2 seed.1))
    | .projection x => .projection (projection x)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply := Reply
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.B ∧ q.c0 ≤ q.c1 ∧ 0 < q.G ∧ 1 ≤ q.κ ∧ 0 ≤ q.σ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q I O :=
    ∃ (projection : q.E → q.E) (P : ProbabilityMeasure (ℕ → Seed q)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Seed q) => ξ k)
      (sampleLaw I) (P : Measure _) ∧
    O = sampleOracle I projection P ∧
    Convex ℝ I.domain ∧ IsClosed I.domain ∧ q.w0 ∈ I.domain ∧
    Measurable projection ∧
    (∀ x, projection x ∈ I.domain) ∧
    (∀ x, ∀ u ∈ I.domain, ⟪x - projection x, u - projection x⟫ ≤ 0) ∧
    (∀ i, Measurable (Function.uncurry (I.score i))) ∧
    (∀ i, Measurable (Function.uncurry (I.grad i))) ∧
    (∀ i ξ, ∀ x ∈ I.domain, ∀ y ∈ I.domain,
      I.score i x ξ + ⟪I.grad i x ξ, y - x⟫ ≤ I.score i y ξ) ∧
    (∀ i ξ, ∀ x ∈ I.domain, q.c0 ≤ I.score i x ξ ∧ I.score i x ξ ≤ q.c1) ∧
    (∀ i, ∀ x ∈ I.domain, Integrable (fun ξ => ‖I.grad i x ξ‖ ^ 2) (I.law i : Measure q.Ξ)) ∧
    (∀ i, ∀ x ∈ I.domain, (∫ ξ, ‖I.grad i x ξ‖ ^ 2 ∂(I.law i : Measure q.Ξ)) ≤ q.G ^ 2) ∧
    (∀ i, ∀ x ∈ I.domain, (∫ ξ, Real.exp (2 * I.score i x ξ) ∂(I.law i : Measure q.Ξ)) ≤
      q.κ * (normalizer I i x) ^ 2) ∧
    (∀ i, ∀ x ∈ I.domain, (∫ ξ, Real.exp (2 * I.score i x ξ) * ‖I.grad i x ξ‖ ^ 2
      ∂(I.law i : Measure q.Ξ)) ≤ q.σ ^ 2 * (normalizer I i x) ^ 2) ∧
    (∃ wstar ∈ I.domain, IsMinOn (objective I) I.domain wstar ∧ ‖q.w0 - wstar‖ ≤ q.R)
  successful q I output P :=
    Measurable output ∧ (∀ ω, output ω ∈ I.domain) ∧
    ∃ wstar ∈ I.domain, IsMinOn (objective I) I.domain wstar ∧
      Integrable (fun ω => objective I (output ω) - objective I wstar) (P : Measure _) ∧
      (∫ ω, objective I (output ω) - objective I wstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.CompositionalEntropicRisk
