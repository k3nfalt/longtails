import LongTails.Algorithms.AffineSoftmaxAcceleration

namespace LongTails.Algorithms.AffineSoftmaxProx

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Algorithms.AffineSoftmaxAcceleration

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev ProxSeed := ℕ → ℕ → StepSeed

noncomputable def proxLaw : ProbabilityMeasure ProxSeed :=
  ⟨Measure.infinitePi (fun _ : ℕ =>
    Measure.infinitePi fun _ : ℕ => (stepLaw : Measure StepSeed)), inferInstance⟩

noncomputable def cachedProxPlan (s : Snapshot ι E) (τ L G r μ ε : ℝ)
    (project : E → E) (seeds : ProxSeed) : Program (ι × E) (ℝ × E) E :=
  let S := L + 2 * G ^ 2 / τ + μ
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  restartPlan s τ μ (fun j => restartScale S V μ (restartGap (G * r) j))
    (fun j => restartSteps S V μ (restartGap (G * r) j)) project s.anchor seeds
    (restartRounds (G * r) ε)

noncomputable def levelPlan (s : Snapshot ι E) (τ L G r μ δ : ℝ)
    (project : E → E) (j : ℕ) (seeds : ProxSeed) : Program (ι × E) (ℝ × E) E :=
  cachedProxPlan s τ L G r μ (δ / 2 ^ j) project seeds

abbrev MultilevelSeed := ℕ × (ProxSeed × ProxSeed × ProxSeed)

noncomputable def multilevelLaw : ProbabilityMeasure MultilevelSeed :=
  ⟨(countLaw : Measure ℕ).prod ((proxLaw : Measure ProxSeed).prod
    ((proxLaw : Measure ProxSeed).prod (proxLaw : Measure ProxSeed))), inferInstance⟩

noncomputable def multilevelPlan (s : Snapshot ι E) (τ L G r μ δ : ℝ)
    (project : E → E) (J : ℕ) (seed : MultilevelSeed) : Program (ι × E) (ℝ × E) E :=
  (levelPlan s τ L G r μ δ project 0 seed.2.1).bind fun base =>
    if seed.1 + 1 ≤ J then
      (levelPlan s τ L G r μ δ project (seed.1 + 1) seed.2.2.1).bind fun fine =>
        (levelPlan s τ L G r μ δ project seed.1 seed.2.2.2).map fun coarse =>
          base + (2 : ℝ) ^ (seed.1 + 1) • (fine - coarse)
    else .done base

noncomputable def proxPlan (m : ℕ) [NeZero m] (center : E) (τ L G r μ ε : ℝ)
    (project : E → E) (seeds : ProxSeed) : Program (Fin m × E) (ℝ × E) E :=
  (cachePlan m center).bind fun s => cachedProxPlan s τ L G r μ ε project seeds

noncomputable def multilevelProxPlan (m : ℕ) [NeZero m] (center : E) (τ L G r μ δ : ℝ)
    (project : E → E) (J : ℕ) (seed : MultilevelSeed) : Program (Fin m × E) (ℝ × E) E :=
  (cachePlan m center).bind fun s => multilevelPlan s τ L G r μ δ project J seed


noncomputable def cachedProxGradientPlan (s : Snapshot ι E) (τ L G r μ σ β : ℝ)
    (project : E → E) (seed : MultilevelSeed) : Program (ι × E) (ℝ × E) E :=
  let J := restartRounds (σ ^ 2) (β ^ 2)
  let δ := σ ^ 2 / (2 * μ * (2 + 12 * (J : ℝ)))
  (multilevelPlan s τ L G r μ δ project J seed).map fun x => μ • (s.anchor - x)

end LongTails.Algorithms.AffineSoftmaxProx
