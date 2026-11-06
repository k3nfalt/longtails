import LongTails.Algorithms.StochasticQuasarCleanup
import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.RegularizedProxEgRepeat
import LongTails.Proofs.StochasticQuasarInnerExecution
import LongTails.Proofs.MultiplicativeRobustMedoid

namespace OracleTemplate.StochasticQuasar

open LongTails.Algorithms.StochasticEnvelopeProgram
open LongTails.Proofs.RecursiveEnvelopeExecution

lemma sampled_eval_eq_indexed {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {k : ℕ} (plan : QueryPlan Q R U k) (call : ℕ) :
    QueryPlan.sampledEval g ξ plan call = evalAt (fun i q => g q (ξ i)) plan call := by
  induction plan generalizing call with
  | done => rfl
  | ask q next ih => exact ih _ (call + 1)

lemma sampled_collect_plans {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {k : ℕ} (n : ℕ) (plans : Fin n → QueryPlan Q R U k) (call : ℕ) :
    QueryPlan.sampledEval g ξ (collectPlans n plans) call =
      fun i => QueryPlan.sampledEval g ξ (plans i) (call + k * i.val) := by
  simp_rw [sampled_eval_eq_indexed]
  exact LongTails.Proofs.StochasticEnvelopeExecution.evalAt_collectPlans _ n plans call

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sampled_robust_prox (g : (Fin 2 × E) → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c x0 : E) (n call : ℕ) :
    QueryPlan.sampledEval g ξ (robustProxPlan L σ D r c x0 n) call =
      MultiplicativeRobustEstimator.medoid (fun i : Fin (n + 1) =>
        QueryPlan.sampledEval g ξ (approximationPlan L σ D r c x0)
          (call + innerCalls L σ D (innerStageCount D r) * i.val)) := by
  rw [robustProxPlan, QueryPlan.sampledEval_map, sampled_collect_plans]

lemma sampled_robust_gradient (g : (Fin 2 × E) → Ω → E) (ξ : ℕ → Ω)
    (x : E) (b n call : ℕ) :
    QueryPlan.sampledEval g ξ (robustGradientPlan x b n) call =
      MultiplicativeRobustEstimator.medoid (fun i : Fin (n + 1) =>
        QueryPlan.sampledEval g ξ (ProjectedClippedExtragradient.meanPlan b x) (call + b * i.val)) := by
  rw [robustGradientPlan, QueryPlan.sampledEval_map, sampled_collect_plans]

omit [NormedSpace ℝ E] in
lemma medoid_mem {Q : Set E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : ∀ i, v i ∈ Q) : MultiplicativeRobustEstimator.medoid v ∈ Q := by
  exact hv _

lemma sampled_cleanup (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c x0 : E) (b n call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (cleanupPlan L σ D r c x0 b n) call =
      let x := QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (robustProxPlan L σ D r c x0 n) call
      let raw := QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (robustGradientPlan x b n) (call + innerCalls L σ D (innerStageCount D r) * (n + 1))
      P (x - (1 / (3 * L)) • (raw + (2 * L) • (x - c))) := by
  simp only [cleanupPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval,
    ProjectedClippedExtragradient.channelReply]
  rfl

lemma sampled_initial_cleanup (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L : ℝ) (x0 : E) (b n call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (initialCleanupPlan L x0 b n) call =
      P (x0 - (1 / (3 * L)) •
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (robustGradientPlan x0 b n) call) := by
  simp only [initialCleanupPlan, QueryPlan.sampledEval_bind, QueryPlan.sampledEval,
    ProjectedClippedExtragradient.channelReply]
  rfl

lemma sampled_robust_prox_mem {Q : Set E} {P : E → E}
    (hP : ∀ y, P y ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c : E) {x0 : E} (hx0 : x0 ∈ Q) (n call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (robustProxPlan L σ D r c x0 n) call ∈ Q := by
  rw [sampled_robust_prox]
  exact medoid_mem (fun i => sampled_inner_plan_mem hP g ξ L σ D c hx0 _ _)

lemma sampled_cleanup_mem {Q : Set E} {P : E → E}
    (hP : ∀ y, P y ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c x0 : E) (b n call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (cleanupPlan L σ D r c x0 b n) call ∈ Q := by
  rw [sampled_cleanup]
  exact hP _

lemma measurable_robust_prox_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g)) (L σ D r : ℝ) (n call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (robustProxPlan L σ D r w.1.1 w.1.2 n) call) := by
  simp_rw [sampled_robust_prox]
  exact MultiplicativeRobustEstimator.measurable_medoid.comp (Measurable.of_eval
    (fun i => measurable_inner_plan_joint hP hg L σ D (innerStageCount D r) _))

lemma measurable_robust_gradient_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] (P : E → E) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (b n call : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (robustGradientPlan w.1 b n) call) := by
  simp_rw [sampled_robust_gradient, ProjectedClippedExtragradient.sampled_meanPlan]
  apply MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro j
  apply Measurable.const_smul
  exact Finset.measurable_sum _ (fun i _ => hg.comp
    (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)))

lemma measurable_cleanup_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D r : ℝ) (b n call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (cleanupPlan L σ D r w.1.1 w.1.2 b n) call) := by
  have hX := measurable_robust_prox_joint hP hg L σ D r n call
  have hR := (measurable_robust_gradient_joint P hg b n
    (call + innerCalls L σ D (innerStageCount D r) * (n + 1))).comp (hX.prodMk measurable_snd)
  simp_rw [sampled_cleanup]
  exact hP.comp (hX.sub ((hR.add
    ((hX.sub (measurable_fst.comp measurable_fst)).const_smul (2 * L))).const_smul (1 / (3 * L))))

end OracleTemplate.StochasticQuasar
