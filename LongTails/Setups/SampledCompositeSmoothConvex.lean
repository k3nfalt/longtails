import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

namespace OracleTemplate.SampledComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def path {Ξ : Type*} (grad : Ξ → E → E) (prox : ℝ → E → E → E) (η : ℝ) (T : ℕ)
    (x0 : E) (ξ : ℕ → Ξ) : ℕ → E
  | 0 => x0
  | k + 1 =>
    prox (η * ((T : ℝ) - k) / T) (path grad prox η T x0 ξ k)
      (grad (ξ (2 * k)) (path grad prox η T x0 ξ k))

noncomputable def proximalLinearDecaySgd (η : ℝ) (T : ℕ) (x0 : E) :
    Algorithm (E ⊕ (ℝ × E × E)) E E where
  State := ℕ × Bool × E × E
  initial _ := (0, false, x0, 0)
  query s :=
    if s.2.1 then (0, Sum.inr (η * ((T : ℝ) - s.1) / T, s.2.2.1, s.2.2.2))
    else (0, Sum.inl s.2.2.1)
  update s r := if s.2.1 then (s.1 + 1, false, r, s.2.2.2) else (s.1, true, s.2.2.1, r)
  output s := s.2.2.1

end OracleTemplate.SampledComposite

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.SampledCompositeSmoothConvex

open OracleTemplate OracleTemplate.SampledComposite

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
  L : ℝ
  R : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE
  Params.countableE Params.measurableΞ

structure Model (E Ξ : Type*) [MeasurableSpace Ξ] where
  law : ProbabilityMeasure Ξ
  loss : Ξ → E → ℝ
  grad : Ξ → E → E
  ψ : E → ℝ
  Q : Set E
  prox : ℝ → E → E → E

noncomputable def smoothPart {E Ξ : Type*} [MeasurableSpace Ξ] (M : Model E Ξ) (x : E) : ℝ :=
  ∫ ξ, M.loss ξ x ∂(M.law : Measure Ξ)

noncomputable def objective {E Ξ : Type*} [MeasurableSpace Ξ] (M : Model E Ξ) (x : E) : ℝ :=
  smoothPart M x + M.ψ x

noncomputable def proxObjective {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ξ] (M : Model E Ξ) (a : ℝ) (z g u : E) : ℝ :=
  ‖u - z‖ ^ 2 / (2 * a) + ⟪g, u - z⟫ + M.ψ u

noncomputable def oracleAnswer {E Ξ : Type*} [MeasurableSpace Ξ] (M : Model E Ξ)
    (query : Fin 1 × (E ⊕ (ℝ × E × E))) (ξ : Ξ) : E :=
  match query.2 with
  | Sum.inl x => M.grad ξ x
  | Sum.inr (a, z, g) => M.prox a z g

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Model p.E p.Ξ
  Query p := p.E ⊕ (ℝ × p.E × p.E)
  Reply p := p.E
  Output p := p.E
  allowedAlgorithm q algorithm :=
    ∃ (η : ℝ) (T : ℕ), 0 ≤ η ∧ algorithm = proximalLinearDecaySgd η T q.x0
  publicInput p := p
  valid q := 0 < q.L ∧ 0 < q.R ∧ 0 ≤ q.Δ ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q M O :=
    ∃ P : ProbabilityMeasure (ℕ → q.Ξ),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ξ) => ξ k)
      (M.law : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ξ
          law := P
          answer := fun _ query ξ => oracleAnswer M query ξ } ∧
    Measurable (Function.uncurry M.grad) ∧
    (∀ ξ, ConvexOn ℝ Set.univ (M.loss ξ)) ∧
    (∀ ξ x, HasGradientAt (M.loss ξ) (M.grad ξ x) x) ∧
    (∀ ξ x y, ‖M.grad ξ x - M.grad ξ y‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x, Integrable (fun ξ => M.loss ξ x) (M.law : Measure q.Ξ)) ∧
    Convex ℝ M.Q ∧
    IsClosed M.Q ∧
    ConvexOn ℝ M.Q M.ψ ∧
    LowerSemicontinuous M.ψ ∧
    (∀ a, 0 < a → ∀ z g, M.prox a z g ∈ M.Q ∧ IsMinOn (proxObjective M a z g) M.Q (M.prox a z g)) ∧
    q.x0 ∈ M.Q ∧
    (∃ xstar ∈ M.Q, IsMinOn (objective M) M.Q xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      objective M q.x0 - objective M xstar ≤ q.Δ ∧
      Integrable (fun ξ => M.grad ξ xstar) (M.law : Measure q.Ξ) ∧
      Integrable (fun ξ => ‖M.grad ξ xstar - ∫ ζ, M.grad ζ xstar ∂(M.law : Measure q.Ξ)‖ ^ 2)
        (M.law : Measure q.Ξ) ∧
      ∫ ξ, ‖M.grad ξ xstar - ∫ ζ, M.grad ζ xstar ∂(M.law : Measure q.Ξ)‖ ^ 2 ∂(M.law : Measure q.Ξ) ≤
        q.σ ^ 2)
  successful q M output P :=
    Measurable output ∧
    ∃ xstar ∈ M.Q, IsMinOn (objective M) M.Q xstar ∧
      Integrable (fun ω => objective M (output ω) - objective M xstar) (P : Measure _) ∧
      ∫ ω, objective M (output ω) - objective M xstar ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.SampledCompositeSmoothConvex
