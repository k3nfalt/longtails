import LongTails.Setups.CompositeGeneralizedSmooth
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory Set

namespace LongTails.Setups.StochasticCompositeGeneralizedSmooth

open OracleTemplate

structure Public extends toComposite : CompositeGeneralizedSmooth.Public where
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  σ : ℝ
  α : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Public.measurableE Public.borelE Public.countableE Public.measurableΩ

structure Params extends Public where
  G : ℝ

abbrev Instance (q : Public) := CompositeGeneralizedSmooth.Instance q.toComposite

abbrev Query (q : Public) := CompositeGeneralizedSmooth.Query q.toComposite

structure IsMomentOracle (q : Public) (I : Instance q) (μ : Measure q.Ω)
    [IsProbabilityMeasure μ] (g : q.E → q.Ω → q.E) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) μ
  unbiased : ∀ x, ∫ ω, g x ω ∂μ = gradient I.f x
  moment_integrable : ∀ x, Integrable (fun ω => ‖g x ω - gradient I.f x‖ ^ q.α) μ
  moment : ∀ x, (∫ ω, ‖g x ω - gradient I.f x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α

abbrev spec : Setup where
  Params := Params.{0}
  Public := Public.{0}
  Instance := Instance
  Query := Query
  Reply q := q.E
  Output q := q.E
  publicInput := Params.toPublic
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 < q.Δ ∧ 0 ≤ q.G ∧
    0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q I O :=
    ∃ (g : q.E → q.Ω → q.E) (μ : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (μ : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, query) seed => match query with
            | .gradient x => g x seed
            | .prox a z v => I.prox a z v } ∧
    ConvexOn ℝ univ I.f ∧
    (∀ x, HasGradientAt I.f (I.grad x) x) ∧
    Continuous I.grad ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.grad (x + θ • (y - x))‖ ≤ M) →
      ‖I.grad x - I.grad y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    Convex ℝ I.Q ∧ MeasurableSet I.Q ∧ ConvexOn ℝ I.Q I.ψ ∧ Measurable I.ψ ∧
    Measurable (fun t : ℝ × q.E × q.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0) ∧
    (∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q ∧
      IsMinOn (CompositeGeneralizedSmooth.proxObjective I a z v) I.Q (I.prox a z v)) ∧
    q.x0 ∈ I.Q ∧
    (∃ xstar ∈ I.Q, IsMinOn (CompositeGeneralizedSmooth.objective I) I.Q xstar ∧
      ‖q.x0 - xstar‖ ≤ q.R ∧
      CompositeGeneralizedSmooth.objective I q.x0 -
        CompositeGeneralizedSmooth.objective I xstar ≤ q.Δ ∧ ‖I.grad xstar‖ ≤ q.G) ∧
    IsMomentOracle q.toPublic I (μ : Measure _) g
  successful q I output P :=
    Measurable output ∧ ∃ xstar ∈ I.Q,
      IsMinOn (CompositeGeneralizedSmooth.objective I) I.Q xstar ∧
      (P : Measure _) {ω | output ω ∉ I.Q ∨
        q.ε < CompositeGeneralizedSmooth.objective I (output ω) -
          CompositeGeneralizedSmooth.objective I xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.StochasticCompositeGeneralizedSmooth
