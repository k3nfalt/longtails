import LongTails.Proofs.ProjectedClippedExecution
import LongTails.Proofs.StochasticQuasarInnerMoments

open scoped BigOperators

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sampled_inner_step (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L : ℝ) (c x : E) (b call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (innerStepPlan L c x b) call =
      P (x - (1 / (3 * L)) •
        ((1 / (b : ℝ)) • ∑ i : Fin b, g x (ξ (call + i.val)) + (2 * L) • (x - c))) := by
  simp only [innerStepPlan, QueryPlan.sampledEval_bind,
    ProjectedClippedExtragradient.sampled_meanPlan, QueryPlan.sampledEval,
    ProjectedClippedExtragradient.channelReply, Fin.isValue, Fin.one_eq_zero_iff]
  rfl

lemma sampled_inner_step_mem {Q : Set E} {P : E → E}
    (hP : ∀ z, P z ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L : ℝ) (c x : E) (b call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (innerStepPlan L c x b) call ∈ Q := by
  rw [sampled_inner_step]
  exact hP _

lemma measurable_sampled_inner_step [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L : ℝ) (c : E) (b call : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (innerStepPlan L c w.1 b) call) := by
  simp_rw [sampled_inner_step]
  apply hP.comp
  apply Measurable.sub measurable_fst
  apply Measurable.const_smul
  apply Measurable.add
  · apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply (call + i.val)).comp measurable_snd))
  · exact (measurable_fst.sub measurable_const).const_smul _

lemma sampled_inner_repeat_mem {Q : Set E} {P : E → E}
    (hP : ∀ z, P z ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L : ℝ) (c : E) (b n : ℕ) {x : E} (hx : x ∈ Q) (call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (ProjectedClippedExtragradient.repeatPlan (fun y => innerStepPlan L c y b) n x) call ∈ Q := by
  induction n generalizing x call with
  | zero => exact hx
  | succ n ih =>
    rw [ProjectedClippedExtragradient.repeatPlan, QueryPlan.sampledEval_bind]
    exact ih (sampled_inner_step_mem hP g ξ L c x b call) _

lemma sampled_inner_plan_mem {Q : Set E} {P : E → E}
    (hP : ∀ z, P z ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D : ℝ) (c : E) {x0 : E} (hx : x0 ∈ Q) (k call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (innerPlan L σ D c x0 k) call ∈ Q := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [innerPlan]
    erw [QueryPlan.sampledEval_bind]
    exact sampled_inner_repeat_mem hP g ξ L c _ 2 ih _

lemma measurable_sampled_inner_repeat [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L : ℝ) (c : E) (b n call : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (ProjectedClippedExtragradient.repeatPlan (fun y => innerStepPlan L c y b) n w.1) call) := by
  induction n generalizing call with
  | zero => exact measurable_fst
  | succ n ih =>
    simp_rw [ProjectedClippedExtragradient.repeatPlan, QueryPlan.sampledEval_bind]
    exact (ih (call + (1 + b))).comp
      ((measurable_sampled_inner_step hP hg L c b call).prodMk measurable_snd)

lemma measurable_sampled_inner_plan [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D : ℝ) (c : E) (k call : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (innerPlan L σ D c w.1 k) call) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    have he (x : E) (ξ : ℕ → Ω) :
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (innerPlan L σ D c x (k + 1)) call =
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (ProjectedClippedExtragradient.repeatPlan
            (fun y => innerStepPlan L c y (innerBatch L σ D k)) 2
            (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
              (innerPlan L σ D c x k) call)) (call + innerCalls L σ D k) := by
      rw [innerPlan]
      erw [QueryPlan.sampledEval_bind]
      rfl
    simp_rw [he]
    exact (measurable_sampled_inner_repeat hP hg L c (innerBatch L σ D k) 2
      (call + innerCalls L σ D k)).comp (ih.prodMk measurable_snd)

lemma measurable_inner_step_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g)) (L : ℝ) (b call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (innerStepPlan L w.1.1 w.1.2 b) call) := by
  simp_rw [sampled_inner_step]
  apply hP.comp
  apply Measurable.sub (measurable_snd.comp measurable_fst)
  apply Measurable.const_smul
  apply Measurable.add
  · apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact hg.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_pi_apply (call + i.val)).comp measurable_snd))
  · exact ((measurable_snd.comp measurable_fst).sub
      (measurable_fst.comp measurable_fst)).const_smul _

lemma measurable_inner_repeat_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g)) (L : ℝ) (b n call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (ProjectedClippedExtragradient.repeatPlan
          (fun x => innerStepPlan L w.1.1 x b) n w.1.2) call) := by
  induction n generalizing call with
  | zero => exact measurable_snd.comp measurable_fst
  | succ n ih =>
    simp_rw [ProjectedClippedExtragradient.repeatPlan, QueryPlan.sampledEval_bind]
    exact (ih (call + (1 + b))).comp
      (((measurable_fst.comp measurable_fst).prodMk
        (measurable_inner_step_joint hP hg L b call)).prodMk measurable_snd)

lemma measurable_inner_plan_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g)) (L σ D : ℝ) (k call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (innerPlan L σ D w.1.1 w.1.2 k) call) := by
  induction k with
  | zero => exact measurable_snd.comp measurable_fst
  | succ k ih =>
    have he (c x : E) (ξ : ℕ → Ω) :
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (innerPlan L σ D c x (k + 1)) call =
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (ProjectedClippedExtragradient.repeatPlan
            (fun y => innerStepPlan L c y (innerBatch L σ D k)) 2
            (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
              (innerPlan L σ D c x k) call)) (call + innerCalls L σ D k) := by
      rw [innerPlan]
      erw [QueryPlan.sampledEval_bind]
      rfl
    simp_rw [he]
    exact (measurable_inner_repeat_joint hP hg L (innerBatch L σ D k) 2
      (call + innerCalls L σ D k)).comp
      (((measurable_fst.comp measurable_fst).prodMk ih).prodMk measurable_snd)

end OracleTemplate.StochasticQuasar
