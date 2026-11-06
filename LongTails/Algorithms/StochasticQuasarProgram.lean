import LongTails.Algorithms.StochasticQuasarCleanup
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar
open LongTails.Algorithms.StochasticEnvelopeProgram

abbrev OuterSeed (q : Params) := ℝ × Fin (estimatorDepth (outerDeviation q) (outerBias q) + 1)
abbrev ProgramSeed (q : Params) := Fin (outerCount q) → OuterSeed q

noncomputable def programLaw (q : Params) : ProbabilityMeasure (ProgramSeed q) :=
  ⟨Measure.pi fun _ : Fin (outerCount q) => (RelativeQuasar.holdingLaw : Measure ℝ).prod
    (mlmcLevelLaw (estimatorDepth (outerDeviation q) (outerBias q)) : Measure _), inferInstance⟩

noncomputable def extendOuterSeeds (q : Params) (seeds : ProgramSeed q) (i : ℕ) : OuterSeed q :=
  if hi : i < outerCount q then seeds ⟨i, hi⟩ else (0, 0)

noncomputable def outerCalls (q : Params) (seeds : ProgramSeed q) : ℕ :=
  slotCalls (fun i => accelerationJumpCalls q.L q.σ q.D (outerDeviation q) (outerBias q)
    (extendOuterSeeds q seeds i).2.val) (outerCount q) 0

noncomputable def outerPlan (q : Params) (seeds : ProgramSeed q) :
    QueryPlan (Fin 2 × q.E) q.E (ℝ × q.E × q.E) (outerCalls q seeds) :=
  accelerationRunPlan (outerWeight q) (outerMirror q) (outerThreshold q) q.γ q.L q.σ q.D
    (outerDeviation q) (outerBias q) (outerStep q) q.x0 (extendOuterSeeds q seeds)
    (outerCount q) 0 (0, q.x0, q.x0)

noncomputable def cleanupCalls (q : Params) : ℕ :=
  1 + outputBatch q * (outerOrder q + 1) +
    innerCalls q.L q.σ q.D (innerStageCount q.D (outputRadius q)) * (outerOrder q + 1)

noncomputable def outerMeanCost (q : Params) : ℝ :=
  12 * innerStageCount q.D (estimatorRadius q.L (outerDeviation q) (outerBias q)) + 17 +
    3840 * (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) ^ 2 * q.σ ^ 2 / outerDeviation q ^ 2

noncomputable def outerMaxCost (q : Params) : ℝ :=
  12 * innerStageCount q.D (estimatorRadius q.L (outerDeviation q) (outerBias q)) +
    8 * (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) + 1 +
    40960 * (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) * q.σ ^ 2 *
      (1 / outerDeviation q ^ 2 + 1 / outerBias q ^ 2)

noncomputable def workCap (q : Params) : ℕ :=
  ⌈2 * (outerCount q : ℝ) * outerMeanCost q + outerMaxCost q * outerOrder q⌉₊

noncomputable def completePlan (q : Params) (seeds : ProgramSeed q) :
    QueryPlan (Fin 2 × q.E) q.E q.E (cleanupCalls q + outerCalls q seeds) :=
  (outerPlan q seeds).bind fun state =>
    cleanupPlan q.L q.σ q.D (outputRadius q) state.2.1 q.x0 (outputBatch q) (outerOrder q)

noncomputable def program (q : Params) (seeds : ProgramSeed q) : Σ k, QueryPlan (Fin 2 × q.E) q.E q.E k :=
  if 4 * q.L * q.D ^ 2 ≤ q.ε then
    ⟨_, initialCleanupPlan q.L q.x0 (outputBatch q) (outerOrder q)⟩
  else if outerCalls q seeds ≤ workCap q then ⟨_, completePlan q seeds⟩ else ⟨0, .done q.x0⟩

noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E 2 where
  Seed := ProgramSeed q
  law := programLaw q
  State := Σ k, QueryPlan (Fin 2 × q.E) q.E q.E k
  initial := program q
  query := QueryPlan.query (0, q.x0)
  update := QueryPlan.update
  output := QueryPlan.output q.x0

noncomputable def output (q : Params) (O : Oracle q.E q.E 2) (budget : Fin 2 → ℕ)
    (seed : ProgramSeed q) (ξ : (k : ℕ) → O.Seed k) : q.E := execute O (algorithm q) budget seed ξ

end OracleTemplate.StochasticQuasar
