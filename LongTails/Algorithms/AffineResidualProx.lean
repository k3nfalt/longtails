import LongTails.Algorithms.AffineResidualSaddle
import LongTails.Algorithms.AffineSoftmaxAcceleration

namespace LongTails.Algorithms.AffineResidualProx

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineResidualSaddle
open LongTails.Algorithms.AffineSoftmaxEstimator (Snapshot countLaw)

abbrev LocalSeed := ℕ → StepSeed
abbrev MultilevelSeed := ℕ × (LocalSeed × LocalSeed × LocalSeed)

noncomputable def localLaw : ProbabilityMeasure LocalSeed :=
  ⟨Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval).prod volume), inferInstance⟩

noncomputable def multilevelLaw : ProbabilityMeasure MultilevelSeed :=
  ⟨(countLaw : Measure ℕ).prod ((localLaw : Measure LocalSeed).prod
    ((localLaw : Measure LocalSeed).prod (localLaw : Measure LocalSeed))), inferInstance⟩

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [StandardBorelSpace ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def levelPlan (C : Set E) (s : Snapshot ι E) (τ μ L r δ : ℝ)
    (j : ℕ) (seeds : LocalSeed) : Program (ι × E) (ℝ × E) E :=
  localPlan C s τ μ L r (δ / 2 ^ j) seeds

noncomputable def multilevelPlan (C : Set E) (s : Snapshot ι E) (τ μ L r δ : ℝ)
    (J : ℕ) (seed : MultilevelSeed) : Program (ι × E) (ℝ × E) E :=
  (levelPlan C s τ μ L r δ 0 seed.2.1).bind fun base =>
    if seed.1 + 1 ≤ J then
      (levelPlan C s τ μ L r δ (seed.1 + 1) seed.2.2.1).bind fun fine =>
        (levelPlan C s τ μ L r δ seed.1 seed.2.2.2).map fun coarse =>
          base + (2 : ℝ) ^ (seed.1 + 1) • (fine - coarse)
    else .done base

noncomputable def cachedProxGradientPlan (C : Set E) (s : Snapshot ι E)
    (τ μ L r σ β : ℝ) (seed : MultilevelSeed) : Program (ι × E) (ℝ × E) E :=
  let J := LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  (multilevelPlan C s τ μ L r δ J seed).map fun x => μ • (s.anchor - x)

end LongTails.Algorithms.AffineResidualProx
