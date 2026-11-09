import Mathlib.Probability.ProductMeasure
import LongTails.Algorithms.FiniteCategoricalSampler
import Mathlib.Basic.ENNReal.BigOperators
import LongTails.Algorithms.AffineSoftmaxEstimator
import LongTails.Algorithms.ComponentEnvelope

namespace LongTails.Algorithms.AffineSoftmaxQueries

open LongTails.Algorithms.AffineSoftmaxEstimator
open OracleTemplate.ComponentEnvelope

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def reciprocalPlan (s : Snapshot ι E) (τ : ℝ) (x : E) :
    List ι → Program (ι × E) (ℝ × E) ℝ
  | [] => .done 1
  | i :: indices => .ask (i, x) fun reply =>
      (reciprocalPlan s τ x indices).map
        (fun r => (2 - Real.exp ((reply.1 - affine s i x) / τ)) * r)

noncomputable def estimatorPlan (s : Snapshot ι E) (τ : ℝ) (x : E)
    (i : ι) (indices : List ι) : Program (ι × E) (ℝ × E) E :=
  .ask (i, x) fun reply => (reciprocalPlan s τ x indices).map
    (fun r => base s τ x + r • numerator s τ x i reply)


noncomputable def gibbsWeights [Nonempty ι] (τ : ℝ) (v : ι → ℝ) :
    FiniteCategoricalSampler.Weights ι :=
  ⟨fun i => ENNReal.ofReal (gibbsWeight τ v i), by
    have h0 : ∀ i ∈ Finset.univ, 0 ≤ gibbsWeight τ v i := by
      intro i _
      unfold gibbsWeight
      positivity
    rw [← ENNReal.ofReal_sum_of_nonneg h0]
    have hp : 0 < ∑ i, Real.exp (v i / τ) :=
      Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    simp only [gibbsWeight, ← Finset.sum_div, div_self hp.ne', ENNReal.ofReal_one]⟩

noncomputable def sampledEstimatorPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (k : ℕ) (u : unitInterval) (us : Fin k → unitInterval) : Program (ι × E) (ℝ × E) E :=
  let weights := gibbsWeights τ (fun i => affine s i x)
  estimatorPlan s τ x (FiniteCategoricalSampler.draw ι weights u)
    (List.ofFn (fun j => FiniteCategoricalSampler.draw ι weights (us j)))


abbrev Rows := (k : ℕ) → Fin k → unitInterval

noncomputable def rowsLaw : MeasureTheory.ProbabilityMeasure Rows :=
  ⟨MeasureTheory.Measure.infinitePi (fun k : ℕ =>
    MeasureTheory.Measure.pi (fun _ : Fin k => (MeasureTheory.volume : MeasureTheory.Measure unitInterval))),
    inferInstance⟩

abbrev StepSeed := ℕ × unitInterval × Rows

noncomputable def stepLaw : MeasureTheory.ProbabilityMeasure StepSeed :=
  ⟨(countLaw : MeasureTheory.Measure ℕ).prod
    ((MeasureTheory.volume : MeasureTheory.Measure unitInterval).prod
      (rowsLaw : MeasureTheory.Measure Rows)), inferInstance⟩

noncomputable def seededEstimatorPlan [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (seed : StepSeed) : Program (ι × E) (ℝ × E) E :=
  sampledEstimatorPlan s τ x seed.1 seed.2.1 (seed.2.2 seed.1)


noncomputable def componentRepliesPlan (x : E) :
    (k : ℕ) → (Fin k → ι) → Program (ι × E) (ℝ × E) (Fin k → ℝ × E)
  | 0, _ => .done Fin.elim0
  | k + 1, indices => .ask (indices 0, x) fun reply =>
      (componentRepliesPlan x k (fun j => indices j.succ)).map (Fin.cons reply)

noncomputable def cachePlan (m : ℕ) (x : E) :
    Program (Fin m × E) (ℝ × E) (Snapshot (Fin m) E) :=
  (componentRepliesPlan x m id).map (fun replies =>
    ⟨x, (fun i => (replies i).1), (fun i => (replies i).2)⟩)

end LongTails.Algorithms.AffineSoftmaxQueries
