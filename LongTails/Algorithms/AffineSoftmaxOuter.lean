import LongTails.Algorithms.AffineSoftmaxSearch

namespace LongTails.Algorithms.AffineSoftmaxOuter

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.CappedProximal

abbrev FinalSeed := ProxSeed × MultilevelSeed

instance : MeasurableSpace FinalSeed := MeasurableSpace.prod inferInstance inferInstance

abbrev OuterSeed := (ℕ → ProbeSeed) × FinalSeed

instance : MeasurableSpace OuterSeed := MeasurableSpace.prod inferInstance inferInstance

noncomputable def finalLaw : ProbabilityMeasure FinalSeed :=
  ⟨(proxLaw : Measure ProxSeed).prod (multilevelLaw : Measure MultilevelSeed), inferInstance⟩

noncomputable def outerLaw : ProbabilityMeasure OuterSeed :=
  ⟨(Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed))).prod
    (finalLaw : Measure FinalSeed), inferInstance⟩

noncomputable def finalStepPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L G r D ε μ : ℝ) (H : ℕ) (seed : FinalSeed) : Program (Fin m × E) (ℝ × E) (State E) :=
  let a := nextWeight μ state.weight
  let center := predictor μ state
  let project := OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall center r)
  (cachePlan m center).bind fun s =>
    (cachedProxPlan s τ L G r μ (μ * r ^ 2 / (100000 * (H : ℝ) ^ 3)) project seed.1).bind fun x =>
      (cachedProxGradientPlan s τ L G r μ (Real.sqrt (μ ^ 2 * r ^ 2 / (100000 * (H : ℝ) ^ 3)))
        (ε / (1000 * D)) project seed.2).map fun g =>
          ⟨state.weight + a, x, OracleTemplate.SaddlePoint.project X (state.dual - (a / 2) • g)⟩

noncomputable def outerStepPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (state : State E)
    (τ L G r D ε floor cap : ℝ) (H b : ℕ) (seed : OuterSeed) : Program (Fin m × E) (ℝ × E) (State E) :=
  (regularizationSearchPlan m X state τ L G r floor cap H b seed.1).bind fun μ =>
    finalStepPlan m X state τ L G r D ε μ H seed.2

noncomputable def outerRunPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    (τ L G r D ε floor cap : ℝ) (H b : ℕ) (seeds : ℕ → OuterSeed) :
    ℕ → Program (Fin m × E) (ℝ × E) (State E)
  | 0 => .done ⟨0, initial, initial⟩
  | n + 1 => (outerRunPlan m X initial τ L G r D ε floor cap H b seeds n).bind fun state =>
      if 100 * D ^ 2 / ε ≤ state.weight then .done state
      else outerStepPlan m X state τ L G r D ε floor cap H b (seeds n)

noncomputable def outerOutputPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E)
    (τ L G r D ε floor cap : ℝ) (H b N : ℕ) (seeds : ℕ → OuterSeed) :
    Program (Fin m × E) (ℝ × E) E :=
  (outerRunPlan m X initial τ L G r D ε floor cap H b seeds N).map State.primal

noncomputable def compilerScale (D r : ℝ) : ℝ := (D / r) ^ (2 / 3 : ℝ)

noncomputable def compilerDepth (G D r ε : ℝ) : ℕ := 3 + Nat.clog 2 (Nat.ceil (G * D ^ 2 / (ε * r)))

noncomputable def compilerFloor (G D r ε : ℝ) : ℝ := ε * (compilerDepth G D r ε : ℝ) ^ 2 / (compilerScale D r * r ^ 2)

noncomputable def compilerCap (G D r ε : ℝ) : ℝ := 2 * compilerFloor G D r ε + 2 * G / r

noncomputable def compilerHorizon (G D r ε : ℝ) : ℕ := Nat.ceil (200 * (compilerDepth G D r ε : ℝ) * compilerScale D r)

noncomputable def compilerBoost (G D r ε : ℝ) : ℕ := Nat.clog 2 (120 * compilerHorizon G D r ε * compilerDepth G D r ε)

end LongTails.Algorithms.AffineSoftmaxOuter
