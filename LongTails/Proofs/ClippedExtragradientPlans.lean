import LongTails.Algorithms.LocalizedClippedExtragradient
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.FiniteProductIteration
import Mathlib.Data.List.GetD

open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
omit [NormedAddCommGroup E] in
lemma sampled_collectPlan (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (n call : ℕ) :
    QueryPlan.sampledEval g ξ (collectPlan x n) call =
      fun i : Fin n => g x (ξ (call + i.val)) := by
  induction n generalizing call with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      simp only [collectPlan, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cons_succ, Fin.val_succ]
        congr 2
        omega

lemma sampled_meanPlan (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (n call : ℕ) :
    QueryPlan.sampledEval g ξ (meanPlan n x) call =
      (n : ℝ)⁻¹ • ∑ i : Fin n, g x (ξ (call + i.val)) := by
  rw [meanPlan, QueryPlan.sampledEval_map, sampled_collectPlan]

lemma sampled_stepPlan (g : E → Ω → E) (ξ : ℕ → Ω) (p : Tuning)
    (s call : ℕ) (anchor center x : E) :
    QueryPlan.sampledEval g ξ (stepPlan p s anchor center x) call =
      let first := regularizedReply (regularization p s) anchor x
        ((batchSize p s : ℝ)⁻¹ • ∑ i : Fin (batchSize p s), g x (ξ (call + i.val)))
      let γ := stepSize (clippingScale p s) (localScale p s) first
      let y := halfStep (clippingScale p s) (localScale p s) x first
      finishStep (radius p s) γ center x
        (regularizedReply (regularization p s) anchor y
          ((batchSize p s : ℝ)⁻¹ • ∑ i : Fin (batchSize p s),
            g y (ξ (call + batchSize p s + i.val)))) := by
  simp only [stepPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map,
    sampled_meanPlan]

lemma sampled_innerPlan (g : E → Ω → E) (ξ : ℕ → Ω) (p : Tuning)
    (s n call : ℕ) (anchor center x : E) :
    QueryPlan.sampledEval g ξ (innerPlan p s anchor center n x) call =
      ContinuizedSimilarQuasar.iterateSamples
        (batchStep (batchSize p s) (clippingScale p s) (localScale p s)
          (radius p s) (regularization p s) anchor center g) n x
        (fun j : Fin n =>
          ((fun i : Fin (batchSize p s) => ξ (call + (batchSize p s + batchSize p s) * j.val + i.val)),
           (fun i : Fin (batchSize p s) => ξ (call + (batchSize p s + batchSize p s) * j.val + batchSize p s + i.val)))) := by
  induction n generalizing x call with
  | zero => rfl
  | succ n ih =>
      rw [innerPlan, QueryPlan.sampledEval_bind, ih]
      simp only [ContinuizedSimilarQuasar.iterateSamples, Fin.val_zero, mul_zero, add_zero,
        Fin.val_succ]
      rw [sampled_stepPlan]
      unfold batchStep
      simp only [one_div]
      congr 1
      funext j
      apply Prod.ext <;> funext i <;> simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

lemma sampled_confidencePlan (g : E → Ω → E) (ξ : ℕ → Ω) (p : Tuning)
    (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval g ξ (confidencePlan p s anchor center) call =
      confidenceOutput p s anchor center g
        (fun j : Fin (repetitions p) => fun k : Fin (innerSteps p s) =>
          ((fun i : Fin (batchSize p s) =>
            ξ (call + ((batchSize p s + batchSize p s) * innerSteps p s) * j.val +
              (batchSize p s + batchSize p s) * k.val + i.val)),
           (fun i : Fin (batchSize p s) =>
            ξ (call + ((batchSize p s + batchSize p s) * innerSteps p s) * j.val +
              (batchSize p s + batchSize p s) * k.val + batchSize p s + i.val)))) := by
  erw [confidencePlan, QueryPlan.sampledEval_map, QueryPlan.sampledEval_traverse]
  unfold confidenceOutput
  apply congrArg (RobustGradient.centeredClip (2 * radius p s) center)
  apply congrArg (RobustGradient.pilotCenter (radius p s))
  funext i
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
  exact sampled_innerPlan g ξ p s (innerSteps p s) _ anchor center center

end OracleTemplate.ClippedExtragradient
