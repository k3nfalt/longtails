import LongTails.Algorithms.AffineSoftmaxProx
import LongTails.Algorithms.CappedProximal

namespace LongTails.Algorithms.AffineSoftmaxSearch

open OracleTemplate.ComponentEnvelope

noncomputable def bisectPlan {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (r : ℝ) : ℕ → ℕ → ℝ → ℝ → Program Q R ℝ
  | 0, index, lower, upper =>
    (probe index ((lower + upper) / 2)).bind fun _ => .done ((lower + upper) / 2)
  | n + 1, index, lower, upper =>
    let mid := (lower + upper) / 2
    (probe index mid).bind fun observed =>
      if observed < 13 * r / 16 then bisectPlan probe r n (index + 1) lower mid
      else if 15 * r / 16 < observed then bisectPlan probe r n (index + 1) mid upper
      else .done mid

noncomputable def gridPlan {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (r floor upper : ℝ) (H : ℕ) : ℕ → ℕ → ℝ → Program Q R ℝ
  | 0, index, previous =>
    let current := max floor (upper / 2 ^ index)
    (probe index current).bind fun observed =>
      if 7 * r / 8 ≤ observed then
        if index = 0 then .done upper
        else bisectPlan probe r (H + 7) (H + 1) current previous
      else .done floor
  | n + 1, index, previous =>
    let current := max floor (upper / 2 ^ index)
    (probe index current).bind fun observed =>
      if 7 * r / 8 ≤ observed then
        if index = 0 then .done upper
        else bisectPlan probe r (H + 7) (H + 1) current previous
      else gridPlan probe r floor upper H n (index + 1) current

noncomputable def searchPlan {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (r floor upper : ℝ) (H : ℕ) : Program Q R ℝ :=
  gridPlan probe r floor upper H H 0 upper

noncomputable def selectTrialsPlan {Q R E : Type*} (trial : ℕ → Program Q R (E × ℝ))
    (initial : E × ℝ) : ℕ → Program Q R (E × ℝ)
  | 0 => .done initial
  | n + 1 => (selectTrialsPlan trial initial n).bind fun best =>
    (trial n).map fun candidate => if candidate.2 < best.2 then candidate else best

noncomputable def regularizedScorePlan {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) (τ μ : ℝ) (center x : E) : Program (Fin m × E) (ℝ × E) ℝ :=
  (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m x).map fun s =>
    LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value + μ / 2 * ‖x - center‖ ^ 2

noncomputable def boostedCachedPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ L G r μ δ : ℝ) (project : E → E)
    (seeds : ℕ → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed) (b : ℕ) :
    Program (Fin m × E) (ℝ × E) E :=
  let trial := fun j =>
    (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project (seeds j)).bind fun x =>
      (regularizedScorePlan m τ μ s.anchor x).map fun score => (x, score)
  (selectTrialsPlan trial
    (s.anchor, LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value) b).map Prod.fst

abbrev ProbeSeed := ℕ → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed

instance : MeasurableSpace ProbeSeed := MeasurableSpace.pi

noncomputable def probeLaw : MeasureTheory.ProbabilityMeasure ProbeSeed :=
  ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ =>
    (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : MeasureTheory.Measure _)), inferInstance⟩

noncomputable def probePlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L G r μ : ℝ) (project : E → E)
    (seeds : ProbeSeed) (b : ℕ) : Program (Fin m × E) (ℝ × E) ℝ :=
  (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m center).bind fun s =>
    (boostedCachedPlan m s τ L G r μ (μ * r ^ 2 / 32768) project seeds b).map fun x => ‖x - center‖

noncomputable def regularizationSearchPlan {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m : ℕ) [NeZero m] (X : Set E)
    (state : LongTails.Algorithms.CappedProximal.State E) (τ L G r floor cap : ℝ)
    (H b : ℕ) (seeds : ℕ → ProbeSeed) : Program (Fin m × E) (ℝ × E) ℝ :=
  searchPlan (fun i μ =>
    let v := max floor μ
    let center := LongTails.Algorithms.CappedProximal.predictor v state
    probePlan m center τ L G r v (OracleTemplate.SaddlePoint.project (X ∩ Metric.closedBall center r))
      (seeds i) b) r floor cap H

end LongTails.Algorithms.AffineSoftmaxSearch
