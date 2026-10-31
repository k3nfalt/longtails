import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function

namespace OracleTemplate.SampledConvex

noncomputable def scale (L R σ : ℝ) (T : ℕ) : ℝ :=
  R / (8 * L * R + σ * Real.sqrt T)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def path {Ξ : Type*} (grad : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E)
    (ξ : ℕ → Ξ) : ℕ → E
  | 0 => x0
  | k + 1 => path grad η T x0 ξ k - (η * ((T : ℝ) - k) / T) • grad (ξ k) (path grad η T x0 ξ k)

noncomputable def linearDecaySgd (η : ℝ) (T : ℕ) (x0 : E) : Algorithm E E E where
  State := ℕ × E
  initial _ := (0, x0)
  query s := (0, s.2)
  update s g := (s.1 + 1, s.2 - (η * ((T : ℝ) - s.1) / T) • g)
  output s := s.2

end OracleTemplate.SampledConvex

open MeasureTheory

namespace LongTails.Setups.SampledSmoothConvex

open OracleTemplate OracleTemplate.SampledConvex

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
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE Params.borelE
  Params.countableE Params.measurableΞ

structure Model (E Ξ : Type*) [MeasurableSpace Ξ] where
  law : ProbabilityMeasure Ξ
  loss : Ξ → E → ℝ
  grad : Ξ → E → E

noncomputable def objective {E Ξ : Type*} [MeasurableSpace Ξ] (M : Model E Ξ) (x : E) : ℝ :=
  ∫ ξ, M.loss ξ x ∂(M.law : Measure Ξ)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Model p.E p.Ξ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  allowedAlgorithm q algorithm :=
    ∃ (η : ℝ) (T : ℕ), 0 ≤ η ∧ algorithm = linearDecaySgd η T q.x0
  publicInput p := p
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q M O :=
    ∃ P : ProbabilityMeasure (ℕ → q.Ξ),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ξ) => ξ k)
      (M.law : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ξ
          law := P
          answer := fun _ (_, x) ξ => M.grad ξ x } ∧
    Measurable (Function.uncurry M.grad) ∧
    (∀ ξ, ConvexOn ℝ Set.univ (M.loss ξ)) ∧
    (∀ ξ x, HasGradientAt (M.loss ξ) (M.grad ξ x) x) ∧
    (∀ ξ x y, ‖M.grad ξ x - M.grad ξ y‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x, Integrable (fun ξ => M.loss ξ x) (M.law : Measure q.Ξ)) ∧
    (∃ xstar, IsMinOn (objective M) Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      Integrable (fun ξ => ‖M.grad ξ xstar‖ ^ 2) (M.law : Measure q.Ξ) ∧
      ∫ ξ, ‖M.grad ξ xstar‖ ^ 2 ∂(M.law : Measure q.Ξ) ≤ q.σ ^ 2)
  successful q M output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (objective M) Set.univ xstar ∧
      Integrable (fun ω => objective M (output ω) - objective M xstar) (P : Measure _) ∧
      ∫ ω, objective M (output ω) - objective M xstar ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.SampledSmoothConvex
