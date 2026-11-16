import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Setups.ManyConstraintStochasticConvex

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ξ : Type
  [measurableΞ : MeasurableSpace Ξ]
  m : ℕ
  L : ℝ
  R : ℝ
  σ : ℝ
  κ : ℝ
  ε : ℝ
  δ : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΞ

structure Model (E Ξ : Type) [MeasurableSpace Ξ] (m : ℕ) where
  law : ProbabilityMeasure Ξ
  loss : Ξ → E → ℝ
  grad : Ξ → E → E
  C : Fin m → Set E
  proj : Fin m → E → E

noncomputable def objective {E Ξ : Type} [MeasurableSpace Ξ] {m : ℕ} (M : Model E Ξ m)
    (x : E) : ℝ :=
  ∫ ξ, M.loss ξ x ∂(M.law : Measure Ξ)

def feasible {E Ξ : Type} [MeasurableSpace Ξ] {m : ℕ} (M : Model E Ξ m) : Set E :=
  ⋂ j, M.C j

noncomputable def oracleAnswer {E Ξ : Type} [MeasurableSpace Ξ] {m : ℕ} (M : Model E Ξ m)
    (query : Fin 2 × (E × Option (Fin m))) (ξ : Ξ) : E :=
  if query.1 = 0 then M.grad ξ query.2.1
  else
    match query.2.2 with
    | some j => M.proj j query.2.1
    | none => query.2.1

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance q := Model q.E q.Ξ q.m
  Query q := q.E × Option (Fin q.m)
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.m ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 1 ≤ q.κ ∧ 0 < q.ε ∧ 0 < q.δ
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
    (∀ j, Convex ℝ (M.C j) ∧ IsClosed (M.C j)) ∧
    (∀ j z, M.proj j z ∈ M.C j ∧ ∀ w ∈ M.C j, ⟪z - M.proj j z, w - M.proj j z⟫ ≤ 0) ∧
    (∀ x, Metric.infDist x (feasible M) ^ 2 ≤
      q.κ * ((1 / (q.m : ℝ)) * ∑ j, Metric.infDist x (M.C j) ^ 2)) ∧
    (∃ xstar ∈ feasible M, IsMinOn (objective M) (feasible M) xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      Integrable (fun ξ => ‖M.grad ξ xstar‖ ^ 2) (M.law : Measure q.Ξ) ∧
      ∫ ξ, ‖M.grad ξ xstar‖ ^ 2 ∂(M.law : Measure q.Ξ) ≤ q.σ ^ 2)
  successful q M output P :=
    Measurable output ∧
    ∃ xstar ∈ feasible M, IsMinOn (objective M) (feasible M) xstar ∧
      Integrable (fun ω => max (objective M (output ω) - objective M xstar) 0) (P : Measure _) ∧
      ∫ ω, max (objective M (output ω) - objective M xstar) 0 ∂(P : Measure _) ≤ q.ε ∧
      Integrable (fun ω => Metric.infDist (output ω) (feasible M) ^ 2) (P : Measure _) ∧
      ∫ ω, Metric.infDist (output ω) (feasible M) ^ 2 ∂(P : Measure _) ≤ q.δ ^ 2

end LongTails.Setups.ManyConstraintStochasticConvex
