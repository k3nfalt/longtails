import LongTails.Proofs.ClippedExtragradientPlans
import LongTails.Proofs.ClippedExtragradientBlocks

namespace OracleTemplate.ClippedExtragradient

open StochasticGeneralized (blockTrace)

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sampled_confidence_block (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval g ξ (confidencePlan t s anchor center) call =
      blockOutput t s anchor center g (fun i => ξ (call + i.val)) := by
  rw [sampled_confidencePlan]
  unfold blockOutput
  apply congrArg (confidenceOutput t s anchor center g)
  funext j k
  apply Prod.ext <;> funext i <;>
    simp only [splitStage, splitTrial, splitBatches, groupSamples, Nat.add_assoc]

lemma sampled_localized_trace (g : E → Ω → E) (ξ : ℕ → Ω) (t : Tuning)
    (s n call : ℕ) (anchor center : E) :
    QueryPlan.sampledEval g ξ (localizedPlan t s n anchor center) call =
      (blockTrace (stageCost t) (stageNext t g) (s, anchor, center)
        (fun j => ξ (call + j)) n).1.2.2 := by
  induction n generalizing s call anchor center with
  | zero => rfl
  | succ n ih =>
      erw [localizedPlan, QueryPlan.sampledEval_bind, sampled_confidence_block, ih,
        StochasticGeneralized.blockTrace_start_succ]
      simp only [stageNext, blockReply, stageCost, Nat.add_assoc]
      repeat' erw [dite_eq_left rfl]
      rfl

lemma execute_localized {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E)
    (t : Tuning) (x0 : E) (hR : 0 < t.R) (K : ℕ)
    (hK : remainingCalls t 0 (stageCount t) ≤ K)
    (seed : Unit) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (localizedClippedExtragradient t x0) (fun _ => K) seed ξ =
      (blockTrace (stageCost t) (stageNext t g) (0, x0, x0) ξ (stageCount t)).1.2.2 := by
  erw [StochasticGradient.execute_advance]
  change QueryPlan.output x0 (StochasticGradient.advance
    (fun j st => QueryPlan.update st (g (QueryPlan.query x0 st) (ξ j))) K 0
      (if 0 < t.R then ⟨remainingCalls t 0 (stageCount t), localizedPlan t 0 (stageCount t) x0 x0⟩
        else ⟨0, QueryPlan.done x0⟩)) = _
  rw [ite_eq_left hR, QueryPlan.advance_sampledPlan_of_le g ξ x0 _ hK]
  change QueryPlan.sampledEval g ξ (localizedPlan t 0 (stageCount t) x0 x0) 0 = _
  rw [sampled_localized_trace]
  simp only [Nat.zero_add]

lemma execute_localized_zero {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E)
    (t : Tuning) (x0 : E) (hR : ¬0 < t.R) (K : ℕ)
    (seed : Unit) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (localizedClippedExtragradient t x0) (fun _ => K) seed ξ = x0 := by
  erw [StochasticGradient.execute_advance]
  change QueryPlan.output x0 (StochasticGradient.advance
    (fun j st => QueryPlan.update st (g (QueryPlan.query x0 st) (ξ j))) K 0
      (if 0 < t.R then ⟨remainingCalls t 0 (stageCount t), localizedPlan t 0 (stageCount t) x0 x0⟩
        else ⟨0, QueryPlan.done x0⟩)) = _
  rw [ite_eq_right hR, QueryPlan.advance_sampledPlan_of_le g ξ x0 _ (Nat.zero_le K)]
  rfl

end OracleTemplate.ClippedExtragradient
