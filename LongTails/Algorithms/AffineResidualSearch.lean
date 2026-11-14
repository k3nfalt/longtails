import LongTails.Algorithms.AffineResidualProx
import LongTails.Algorithms.AffineSoftmaxSearch

namespace LongTails.Algorithms.AffineResidualSearch

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineResidualProx
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot smoothValue)
open LongTails.Algorithms.AffineSoftmaxSearch (selectTrialsPlan regularizedScorePlan searchPlan)

abbrev ProbeSeed := ℕ → LocalSeed

noncomputable def probeLaw : ProbabilityMeasure ProbeSeed :=
  ⟨Measure.infinitePi (fun _ : ℕ => (localLaw : Measure LocalSeed)), inferInstance⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def boostedCachedPlan (m : ℕ) [NeZero m] (C : Set E) (s : Snapshot (Fin m) E)
    (τ μ L r δ : ℝ) (seeds : ProbeSeed) (b : ℕ) : Program (Fin m × E) (ℝ × E) E :=
  let trial := fun j =>
    (localPlan C s τ μ L r δ (seeds j)).bind fun x =>
      (regularizedScorePlan m τ μ s.anchor x).map fun score => (x, score)
  (selectTrialsPlan trial (s.anchor, smoothValue τ s.value) b).map Prod.fst

noncomputable def probePlan (m : ℕ) [NeZero m] (C : Set E) (center : E)
    (τ μ L r : ℝ) (seeds : ProbeSeed) (b : ℕ) : Program (Fin m × E) (ℝ × E) ℝ :=
  (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m center).bind fun s =>
    (boostedCachedPlan m C s τ μ L r (μ * r ^ 2 / 32768) seeds b).map fun x => ‖x - center‖

noncomputable def regularizationSearchPlan (m : ℕ) [NeZero m] (X : Set E)
    (state : LongTails.Algorithms.CappedProximal.State E) (τ L r floor cap : ℝ)
    (H b : ℕ) (seeds : ℕ → ProbeSeed) : Program (Fin m × E) (ℝ × E) ℝ :=
  searchPlan (fun i μ =>
    let v := max floor μ
    let center := LongTails.Algorithms.CappedProximal.predictor v state
    probePlan m (X ∩ Metric.closedBall center r) center τ v L r (seeds i) b) r floor cap H

end LongTails.Algorithms.AffineResidualSearch
