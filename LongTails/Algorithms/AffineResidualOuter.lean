import LongTails.Algorithms.AffineResidualSearch

namespace LongTails.Algorithms.AffineResidualOuter

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle (localPlan)
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineResidualSearch
open LongTails.Algorithms.AffineSoftmaxQueries (cachePlan)
open LongTails.Algorithms.CappedProximal

abbrev FinalSeed := LocalSeed × MultilevelSeed

instance : MeasurableSpace FinalSeed := MeasurableSpace.prod inferInstance inferInstance

abbrev OuterSeed := (ℕ → ProbeSeed) × FinalSeed

instance : MeasurableSpace OuterSeed := MeasurableSpace.prod inferInstance inferInstance

noncomputable def finalLaw : ProbabilityMeasure FinalSeed :=
  ⟨(localLaw : Measure LocalSeed).prod (multilevelLaw : Measure MultilevelSeed), inferInstance⟩

noncomputable def outerLaw : ProbabilityMeasure OuterSeed :=
  ⟨(Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))).prod
    (finalLaw : Measure FinalSeed), inferInstance⟩

noncomputable def finalStepPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L r D ε μ : ℝ) (H : ℕ) (seed : FinalSeed) : Program (Fin m × E) (ℝ × E) (State E) :=
  let a := nextWeight μ state.weight
  let center := predictor μ state
  let C := X ∩ Metric.closedBall center r
  (cachePlan m center).bind fun s =>
    (localPlan C s τ μ L r (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) seed.1).bind fun x =>
      (cachedProxGradientPlan C s τ μ L r (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)))
        (ε / (1000 * D)) seed.2).map fun g =>
          ⟨state.weight + a, x, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g)⟩

noncomputable def outerStepPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L r D ε floor cap : ℝ) (H b : ℕ) (seed : OuterSeed) : Program (Fin m × E) (ℝ × E) (State E) :=
  (regularizationSearchPlan m X state τ L r floor cap H b seed.1).bind fun μ =>
    finalStepPlan m X state τ L r D ε μ H seed.2

noncomputable def outerRunPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    (τ L r D ε floor cap : ℝ) (H b : ℕ) (seeds : ℕ → OuterSeed) :
    ℕ → Program (Fin m × E) (ℝ × E) (State E)
  | 0 => .done ⟨0, initial, initial⟩
  | n + 1 => (outerRunPlan m X initial τ L r D ε floor cap H b seeds n).bind fun state =>
      if 100 * D ^ 2 / ε ≤ state.weight then .done state
      else outerStepPlan m X state τ L r D ε floor cap H b (seeds n)

noncomputable def outerOutputPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    (τ L r D ε floor cap : ℝ) (H b N : ℕ) (seeds : ℕ → OuterSeed) :
    Program (Fin m × E) (ℝ × E) E :=
  (outerRunPlan m X initial τ L r D ε floor cap H b seeds N).map State.primal

end LongTails.Algorithms.AffineResidualOuter
