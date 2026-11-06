import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LongTails.Algorithms.AffineSoftmaxQueries
import LongTails.Algorithms.ClippedTwoPoint

namespace LongTails.Algorithms.AffineSoftmaxAcceleration

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.ClippedTwoPoint (acceleratedMix acceleratedUpdate)
open OracleTemplate.ComponentEnvelope

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def solverPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ D μ : ℝ)
    (project : E → E) (initial : E) (seeds : ℕ → StepSeed) :
    ℕ → Program (ι × E) (ℝ × E) (E × E)
  | 0 => .done (initial, initial)
  | n + 1 => (solverPlan s τ D μ project initial seeds n).bind fun state =>
      let x := acceleratedMix n state.1 state.2
      (seededEstimatorPlan s τ x (seeds n)).map fun estimate =>
        acceleratedUpdate project (2 * D) n state (estimate + μ • (x - s.anchor))

noncomputable def solverState (D : ℝ) (project : E → E) (G : E → StepSeed → E)
    (initial : E) (seeds : ℕ → StepSeed) : ℕ → E × E
  | 0 => (initial, initial)
  | n + 1 =>
      let state := solverState D project G initial seeds n
      acceleratedUpdate project (2 * D) n state
        (G (acceleratedMix n state.1 state.2) (seeds n))

noncomputable def solverOutput (D : ℝ) (project : E → E) (G : E → StepSeed → E)
    (initial : E) (seeds : ℕ → StepSeed) (n : ℕ) : E :=
  (solverState D project G initial seeds n).1

noncomputable def restartPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ μ : ℝ)
    (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E) (initial : E)
    (seeds : ℕ → ℕ → StepSeed) : ℕ → Program (ι × E) (ℝ × E) E
  | 0 => .done initial
  | n + 1 => (restartPlan s τ μ D steps project initial seeds n).bind fun start =>
      (solverPlan s τ (D n) μ project start (seeds n) (steps n)).map Prod.fst

noncomputable def restartState (D : ℕ → ℝ) (steps : ℕ → ℕ) (project : E → E)
    (G : E → StepSeed → E) (initial : E) (seeds : ℕ → ℕ → StepSeed) : ℕ → E
  | 0 => initial
  | n + 1 => solverOutput (D n) project G (restartState D steps project G initial seeds n)
      (seeds n) (steps n)

noncomputable def restartGap (d : ℝ) (j : ℕ) : ℝ := d / 2 ^ j

noncomputable def restartSteps (S V μ d : ℝ) : ℕ :=
  Nat.ceil (8 * Real.sqrt (S / μ) + 256 * V / (μ * d) + 1)

noncomputable def restartScale (S V μ d : ℝ) : ℝ :=
  2 * S + 8 * (restartSteps S V μ d : ℝ) * V / d

noncomputable def restartRounds (d ε : ℝ) : ℕ := Nat.clog 2 (Nat.ceil (d / ε))

end LongTails.Algorithms.AffineSoftmaxAcceleration
