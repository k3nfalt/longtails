import LongTails.Algorithms.AffineSoftmaxQueries
import Mathlib.Analysis.Convex.Function

namespace LongTails.Algorithms.AffineResidualSaddle

open scoped RealInnerProductSpace
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries

structure State (ι E : Type*) where
  point : E
  probability : ι → ℝ

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def linearMinimizer (C : Set E) (μ τ A : ℝ) (c : E) (d : ι → ℝ) : State ι E :=
  ⟨OracleTemplate.SaddlePoint.project C ((A * μ)⁻¹ • c), gibbsWeight (A * τ) d⟩

noncomputable def predictorScores (s : Snapshot ι E) (τ η : ℝ)
    (state : State ι E) (x : E) (i : ι) : ℝ :=
  affine s i x + τ / η * Real.log (state.probability i)

noncomputable def predictorObjective (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) (x : E) : ℝ :=
  smoothValue (τ * (1 + 1 / η)) (predictorScores s τ η state x) +
    μ / 2 * ‖x - s.anchor‖ ^ 2 + μ / (2 * η) * ‖x - state.point‖ ^ 2

noncomputable def predictor (C : Set E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state : State ι E) : State ι E :=
  let x := Classical.epsilon fun x =>
    x ∈ C ∧ IsMinOn (predictorObjective s τ μ η state) C x
  ⟨x, gibbsWeight (τ * (1 + 1 / η)) (predictorScores s τ η state x)⟩

noncomputable def correction (project : E → E) (s : Snapshot ι E) (τ μ η : ℝ)
    (state predicted : State ι E) (primalNoise : E) (dualNoise : ι → ℝ) : State ι E :=
  let field := ∑ i, predicted.probability i • s.field i
  let x := project ((μ * (1 / η + 1 / 2))⁻¹ •
    ((μ / η) • state.point + μ • s.anchor - (μ / 2) • predicted.point -
      field - primalNoise))
  let scores := fun i => τ / η * Real.log (state.probability i) +
    affine s i predicted.point - τ / 2 * Real.log (predicted.probability i) - dualNoise i
  ⟨x, gibbsWeight (τ * (1 / η + 1 / 2)) scores⟩

abbrev StepSeed := unitInterval × unitInterval

def iterationWeight (β : ℝ) (k : ℕ) : ℝ := (k : ℝ) + 1 + β

noncomputable def stepSize (β : ℝ) (k : ℕ) : ℝ := 8 / iterationWeight β k

noncomputable def coordinateReply (j : ι) (value : ℝ) (i : ι) : ℝ := by
  classical
  exact if i = j then (Fintype.card ι : ℝ) * value else 0

noncomputable def stepPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ η D : ℝ) (state : State ι E) (seed : StepSeed) :
    Program (ι × E) (ℝ × E) (State ι E × E) := by
  classical
  exact
    let predicted := predictor C s τ μ η state
    let weights := gibbsWeights (τ * (1 + 1 / η))
      (predictorScores s τ η state predicted.point)
    let i := FiniteCategoricalSampler.draw ι weights seed.1
    let j := FiniteCategoricalSampler.draw ι (gibbsWeights 1 (fun _ => 0)) seed.2
    .ask (i, predicted.point) fun primalReply =>
      .ask (j, predicted.point) fun dualReply =>
        let primalNoise := primalReply.2 - s.field i
        let dualNoise := coordinateReply j (D - (dualReply.1 - affine s j predicted.point))
        .done (correction project s τ μ η state predicted primalNoise dualNoise, predicted.point)

noncomputable def solverPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed) :
    ℕ → Program (ι × E) (ℝ × E) (State ι E × E)
  | 0 => .done (initial, 0)
  | n + 1 => (solverPlan C project s τ μ β D initial seeds n).bind fun state =>
      (stepPlan C project s τ μ (stepSize β n) D state.1 (seeds n)).map fun next =>
        (next.1, state.2 + iterationWeight β n • next.2)

noncomputable def solverState (β : ℝ) (initial : State ι E)
    (step : ℕ → State ι E → StepSeed → State ι E × E) (seeds : ℕ → StepSeed) :
    ℕ → State ι E × E
  | 0 => (initial, 0)
  | n + 1 =>
      let state := solverState β initial step seeds n
      let next := step n state.1 (seeds n)
      (next.1, state.2 + iterationWeight β n • next.2)

noncomputable def averageOutput (β : ℝ) (initial : E) (N : ℕ) (sum : E) : E :=
  if N = 0 then initial else (∑ k ∈ Finset.range N, iterationWeight β k)⁻¹ • sum

noncomputable def outputPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (project : E → E) (s : Snapshot ι E)
    (τ μ β D : ℝ) (initial : State ι E) (seeds : ℕ → StepSeed) (N : ℕ) :
    Program (ι × E) (ℝ × E) E :=
  (solverPlan C project s τ μ β D initial seeds N).map fun state =>
    averageOutput β initial.point N state.2

noncomputable def localOffset (m : ℕ) (τ L r : ℝ) : ℝ :=
  1 + (⌈8 * m * L * r ^ 2 / τ⌉₊ : ℝ)

noncomputable def localSteps (m : ℕ) (τ μ L r α : ℝ) : ℕ :=
  ⌈4 * localOffset m τ L r * Real.sqrt ((2 * μ * r ^ 2 + τ * Real.log m) / α) +
    64 * ((L * r) ^ 2 / μ + m * (L * r ^ 2 / 2) ^ 2 / τ) / α + 1⌉₊

noncomputable def localPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [StandardBorelSpace ι] (C : Set E) (s : Snapshot ι E) (τ μ L r α : ℝ)
    (seeds : ℕ → StepSeed) : Program (ι × E) (ℝ × E) E :=
  outputPlan C (OracleTemplate.SaddlePoint.project C) s τ μ
    (localOffset (Fintype.card ι) τ L r) (L * r ^ 2 / 2)
    ⟨s.anchor, fun _ => (Fintype.card ι : ℝ)⁻¹⟩ seeds
    (localSteps (Fintype.card ι) τ μ L r α)

noncomputable def proxPlan (m : ℕ) [NeZero m] (C : Set E) (center : E)
    (τ μ L r α : ℝ) (seeds : ℕ → StepSeed) : Program (Fin m × E) (ℝ × E) E :=
  (cachePlan m center).bind fun s => localPlan C s τ μ L r α seeds

end LongTails.Algorithms.AffineResidualSaddle
