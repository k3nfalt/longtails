import LongTails.Proofs.AffineSoftmaxSampling
import LongTails.Algorithms.AffineSoftmaxQueries
import LongTails.Proofs.ComponentEnvelopeExecution

namespace LongTails.Proofs.AffineSoftmaxExecution

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open OracleTemplate.ComponentEnvelope
open MeasureTheory

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] in
lemma reciprocalPlan_eval (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (indices : List ι) :
    Program.eval reply (reciprocalPlan s τ x indices) =
      reciprocal (indices.map (fun i => Real.exp (((reply (i, x)).1 - affine s i x) / τ))) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [reciprocalPlan, Program.eval, Program.eval_map, List.map_cons, reciprocal, ih]

omit [Fintype ι] in
lemma reciprocalPlan_cost (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (indices : List ι) :
    Program.cost reply (reciprocalPlan s τ x indices) = indices.length := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simp only [reciprocalPlan, Program.cost, Program.cost_map, ih, List.length_cons]

lemma estimatorPlan_eval (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (i : ι) (indices : List ι) :
    Program.eval reply (estimatorPlan s τ x i indices) =
      estimate s τ x i (reply (i, x))
        (indices.map (fun j => Real.exp (((reply (j, x)).1 - affine s j x) / τ))) := by
  simp only [estimatorPlan, Program.eval, Program.eval_map, reciprocalPlan_eval, estimate]

lemma estimatorPlan_cost (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (i : ι) (indices : List ι) :
    Program.cost reply (estimatorPlan s τ x i indices) = indices.length + 1 := by
  simp only [estimatorPlan, Program.cost, Program.cost_map, reciprocalPlan_cost]


lemma sampledEstimatorPlan_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (k : ℕ) (u : unitInterval) (us : Fin k → unitInterval) :
    Program.cost reply (sampledEstimatorPlan s τ x k u us) = k + 1 := by
  simp only [sampledEstimatorPlan, estimatorPlan_cost, List.length_ofFn]


lemma sampledEstimatorPlan_expected_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (u : ℕ → unitInterval) (us : (k : ℕ) → Fin k → unitInterval) :
    (∫ k : ℕ, (Program.cost reply (sampledEstimatorPlan s τ x k (u k) (us k)) : ℝ)
      ∂(countLaw : Measure ℕ)) = 2 := by
  simp only [sampledEstimatorPlan_cost]
  exact AffineSoftmaxSampling.estimator_calls_mean


lemma seededEstimatorPlan_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) (seed : StepSeed) :
    Program.cost reply (seededEstimatorPlan s τ x seed) = seed.1 + 1 := by
  simp only [seededEstimatorPlan, sampledEstimatorPlan_cost]

lemma seededEstimatorPlan_expected_cost [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) :
    (∫ seed : StepSeed, (Program.cost reply (seededEstimatorPlan s τ x seed) : ℝ)
      ∂(stepLaw : Measure StepSeed)) = 2 := by
  simp only [seededEstimatorPlan_cost]
  let ν := (volume : Measure unitInterval).prod (rowsLaw : Measure Rows)
  have hi : Integrable (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) (countLaw : Measure ℕ) := by
    by_contra hnot
    have hh := AffineSoftmaxSampling.estimator_calls_mean
    rw [integral_undef hnot] at hh
    norm_num at hh
  change (∫ seed : StepSeed, ((seed.1 + 1 : ℕ) : ℝ) ∂(countLaw : Measure ℕ).prod ν) = 2
  rw [integral_prod _ (hi.comp_fst ν)]
  simpa only [integral_const, probReal_univ, one_smul] using AffineSoftmaxSampling.estimator_calls_mean


omit [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma componentRepliesPlan_eval (x : E) (reply : ι × E → ℝ × E)
    (k : ℕ) (indices : Fin k → ι) :
    Program.eval reply (componentRepliesPlan x k indices) = fun i => reply (indices i, x) := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [componentRepliesPlan, Program.eval, Program.eval_map, ih]
    funext i
    exact Fin.cases rfl (fun j => rfl) i

omit [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma componentRepliesPlan_cost (x : E) (reply : ι × E → ℝ × E)
    (k : ℕ) (indices : Fin k → ι) :
    Program.cost reply (componentRepliesPlan x k indices) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [componentRepliesPlan, Program.cost, Program.cost_map, ih]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cachePlan_eval (m : ℕ) (x : E) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (cachePlan m x) =
      (⟨x, (fun i => (reply (i, x)).1), (fun i => (reply (i, x)).2)⟩ : Snapshot (Fin m) E) := by
  simp only [cachePlan, Program.eval_map, componentRepliesPlan_eval, id_eq]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cachePlan_cost (m : ℕ) (x : E) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (cachePlan m x) = m := by
  simp only [cachePlan, Program.cost_map, componentRepliesPlan_cost]

end LongTails.Proofs.AffineSoftmaxExecution
