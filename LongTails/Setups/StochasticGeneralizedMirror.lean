import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Set

namespace LongTails.Setups.StochasticGeneralizedMirror

open OracleTemplate

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : E
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  Δ : ℝ
  G : ℝ
  σ : ℝ
  α : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Public.normedE Public.linearE Public.finiteE
  Public.measurableE Public.borelE Public.measurableΩ

abbrev Dual (q : Public) := q.E →L[ℝ] ℝ

noncomputable instance (q : Public) : MeasurableSpace (Dual q) := borel _

instance (q : Public) : BorelSpace (Dual q) := ⟨rfl⟩

inductive Query (q : Public) where
  | gradient (x : q.E)
  | prox (a : ℝ) (z : q.E) (v : Dual q)

abbrev Reply (q : Public) := Dual q ⊕ q.E

structure Instance (q : Public) where
  f : q.E → ℝ
  df : q.E → Dual q
  ψ : q.E → ℝ
  Q : Set q.E
  h : q.E → ℝ
  dh : q.E → Dual q
  U : Set q.E
  prox : ℝ → q.E → Dual q → q.E

def objective {q : Public} (I : Instance q) (x : q.E) : ℝ := I.f x + I.ψ x

def divergence {q : Public} (I : Instance q) (u z : q.E) : ℝ :=
  I.h u - I.h z - I.dh z (u - z)

def proxObjective {q : Public} (I : Instance q) (a : ℝ) (z : q.E) (v : Dual q)
    (u : q.E) : ℝ := a * (v (u - z) + I.ψ u) + divergence I u z

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Instance
  Query := Query
  Reply := Reply
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 < q.Δ ∧ 0 ≤ q.G ∧
    0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q I O :=
    ∃ (g : q.E → q.Ω → Dual q) (μ : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (μ : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, query) seed => match query with
            | .gradient x => Sum.inl (g x seed)
            | .prox a z v => Sum.inr (I.prox a z v) } ∧
    ConvexOn ℝ univ I.f ∧ (∀ x, HasFDerivAt I.f (I.df x) x) ∧ Continuous I.df ∧
    (∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖I.df (x + θ • (y - x))‖ ≤ M) →
      ‖I.df x - I.df y‖ ≤ (q.L0 + q.L1 * M) * ‖x - y‖) ∧
    Convex ℝ I.Q ∧ MeasurableSet I.Q ∧ ConvexOn ℝ I.Q I.ψ ∧ Measurable I.ψ ∧
    IsOpen I.U ∧ Convex ℝ I.U ∧
    (∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) ∧
    (∀ z ∈ I.Q ∩ I.U, ∀ u ∈ I.Q, ‖u - z‖ ^ 2 / 2 ≤ divergence I u z) ∧
    Measurable (fun t : ℝ × q.E × Dual q =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else q.x0) ∧
    (∀ a, 0 < a → ∀ z ∈ I.Q ∩ I.U, ∀ v, I.prox a z v ∈ I.Q ∩ I.U ∧
      IsMinOn (proxObjective I a z v) I.Q (I.prox a z v)) ∧
    q.x0 ∈ I.Q ∩ I.U ∧
    (∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧
      divergence I xstar q.x0 ≤ q.R ^ 2 / 2 ∧
      objective I q.x0 - objective I xstar ≤ q.Δ ∧ ‖I.df xstar‖ ≤ q.G) ∧
    Measurable (Function.uncurry g) ∧
    (∀ x ∈ I.Q, Integrable (g x) (μ : Measure _)) ∧
    (∀ x ∈ I.Q, (∫ ω, g x ω ∂(μ : Measure _)) = I.df x) ∧
    (∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) (μ : Measure _)) ∧
    (∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂(μ : Measure _)) ≤ q.σ ^ q.α)
  successful q I output P :=
    Measurable output ∧ ∃ xstar ∈ I.Q, IsMinOn (objective I) I.Q xstar ∧
      (P : Measure _) {ω | output ω ∉ I.Q ∨
        q.ε < objective I (output ω) - objective I xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.StochasticGeneralizedMirror
