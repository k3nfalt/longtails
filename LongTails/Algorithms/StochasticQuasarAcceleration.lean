import LongTails.Algorithms.StochasticQuasarMlmc
import LongTails.Algorithms.GradientOnlyQuasar
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Proofs.Clipping
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.StochasticQuasar

def seededStreamRun {S U Ω : Type*} (calls : S → ℕ) (advance : U → S → (ℕ → Ω) → U) :
    (k : ℕ) → U → (Fin k → S) → (ℕ → Ω) → U
  | 0, state, _, _ => state
  | k + 1, state, seeds, ξ => seededStreamRun calls advance k (advance state (seeds 0) ξ)
      (fun i => seeds i.succ) (fun j => ξ (calls (seeds 0) + j))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def accelerationWeight (A0 a T t : ℝ) : ℝ :=
  A0 + 2 * a * T ^ 2 * GradientOnlyQuasar.smoothRamp (t / (2 * T))

noncomputable def accelerationWeightSlope (a T t : ℝ) : ℝ :=
  a * T * GradientOnlyQuasar.smoothRampSlope (t / (2 * T))

noncomputable def accelerationFlow (weight : ℝ → ℝ) (γ s t : ℝ) (x z : E) : E :=
  z + (weight s / weight t) ^ (1 / γ) • (x - z)

noncomputable def accelerationJumpCalls (L σ D v β : ℝ) (j : ℕ) : ℕ :=
  1 + mlmcCalls L σ D (estimatorRadius L v β) j

noncomputable def accelerationJumpPlan (L σ D v β η c H : ℝ) (x z x0 : E)
    (j : Fin (estimatorDepth v β + 1)) :
    QueryPlan (Fin 2 × E) E (E × E) (accelerationJumpCalls L σ D v β j.val) :=
  (tunedEnvelopePlan L σ D v β x x0 j).bind fun raw =>
    .ask (1, z - c • clip H raw) fun znew => .done (x - η • clip H raw, znew)

noncomputable def accelerationAdvancePlan (weight mirror threshold : ℝ → ℝ)
    (γ L σ D v β η : ℝ) (x0 : E) (seed : ℝ × Fin (estimatorDepth v β + 1))
    (state : ℝ × E × E) :
    QueryPlan (Fin 2 × E) E (ℝ × E × E) (accelerationJumpCalls L σ D v β seed.2.val) :=
  let t := state.1 + max 0 seed.1
  let y := accelerationFlow weight γ state.1 t state.2.1 state.2.2
  (accelerationJumpPlan L σ D v β η (mirror t) (threshold t) y state.2.2 x0 seed.2).map
    (fun pair => (t, pair))

noncomputable def accelerationRunPlan (weight mirror threshold : ℝ → ℝ)
    (γ L σ D v β η : ℝ) (x0 : E) (seeds : ℕ → ℝ × Fin (estimatorDepth v β + 1))
    (k slot : ℕ) (state : ℝ × E × E) :
    QueryPlan (Fin 2 × E) E (ℝ × E × E)
      (LongTails.Algorithms.StochasticEnvelopeProgram.slotCalls
        (fun i => accelerationJumpCalls L σ D v β (seeds i).2.val) k slot) :=
  LongTails.Algorithms.StochasticEnvelopeProgram.slotPlan
    (fun i => accelerationJumpCalls L σ D v β (seeds i).2.val)
    (fun i => accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 (seeds i)) k slot state

end OracleTemplate.StochasticQuasar
