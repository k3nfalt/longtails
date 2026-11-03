import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.TailObliviousMonotoneRootFinding

open OracleTemplate

structure HeavyTailedOperator {E Ω : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) (F : E → E) (g : E → Ω → E) (σ α : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  unbiased : ∀ x, (∫ ω, g x ω ∂p) = F x
  moment_integrable : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ α) p
  moment : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ α ∂p) ≤ σ ^ α

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  x0 : E
  L : ℝ

attribute [instance] Public.normedE Public.innerE Public.finiteE Public.measurableE
  Public.borelE

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  α : ℝ
  σ : ℝ
  R : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := q.E → q.E
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q.toPublic
  valid q := 0 < q.L ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 ≤ q.σ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q F O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    (∀ x y, 0 ≤ inner ℝ (F x - F y) (x - y)) ∧
    (∀ x y, ‖F x - F y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    HeavyTailedOperator (p : Measure _) F g q.σ q.α
  successful q F output P :=
    Measurable output ∧
    Integrable (fun ω => ‖F (output ω)‖ ^ q.α) (P : Measure _) ∧
    (∫ ω, ‖F (output ω)‖ ^ q.α ∂(P : Measure _)) ≤ q.ε ^ q.α

end LongTails.Setups.TailObliviousMonotoneRootFinding
