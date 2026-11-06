import LongTails.Algorithms.StochasticQuasarAcceleration
import LongTails.Proofs.StochasticQuasarMlmcExecution
import LongTails.Proofs.MultiplicativeRobustClipping
import LongTails.Proofs.StochasticQuasarSchedule

open MeasureTheory

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

lemma sampled_acceleration_jump (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D v β η c H : ℝ) (x z x0 : E) (j : Fin (estimatorDepth v β + 1)) (call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationJumpPlan L σ D v β η c H x z x0 j) call =
      let raw := QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (tunedEnvelopePlan L σ D v β x x0 j) call
      (x - η • clip H raw, P (z - c • clip H raw)) := by
  unfold accelerationJumpPlan
  erw [QueryPlan.sampledEval_bind]
  rfl

lemma sampled_acceleration_auxiliary_mem {Q : Set E} {P : E → E} (hP : ∀ w, P w ∈ Q)
    (g : E → Ω → E) (ξ : ℕ → Ω) (L σ D v β η c H : ℝ) (x z x0 : E)
    (j : Fin (estimatorDepth v β + 1)) (call : ℕ) :
    (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationJumpPlan L σ D v β η c H x z x0 j) call).2 ∈ Q := by
  rw [sampled_acceleration_jump]
  exact hP _

lemma sampled_acceleration_advance (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (weight mirror threshold : ℝ → ℝ) (γ L σ D v β η : ℝ) (x0 : E)
    (seed : ℝ × Fin (estimatorDepth v β + 1)) (state : ℝ × E × E) (call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 seed state) call =
      let t := state.1 + max 0 seed.1
      let y := accelerationFlow weight γ state.1 t state.2.1 state.2.2
      (t, QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (accelerationJumpPlan L σ D v β η (mirror t) (threshold t) y state.2.2 x0 seed.2) call) := by
  unfold accelerationAdvancePlan
  rw [QueryPlan.sampledEval_map]

lemma sampled_acceleration_run_succ (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (weight mirror threshold : ℝ → ℝ) (γ L σ D v β η : ℝ) (x0 : E)
    (seeds : ℕ → ℝ × Fin (estimatorDepth v β + 1)) (k slot call : ℕ) (state : ℝ × E × E) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 seeds (k + 1) slot state) call =
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 seeds k (slot + 1)
          (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
            (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 (seeds slot) state) call))
        (call + accelerationJumpCalls L σ D v β (seeds slot).2.val) := by
  unfold accelerationRunPlan
  exact QueryPlan.sampledEval_bind _ _ _ _ _

lemma sampled_acceleration_run_clock (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (weight mirror threshold : ℝ → ℝ) (γ L σ D v β η : ℝ) (x0 : E)
    (seeds : ℕ → ℝ × Fin (estimatorDepth v β + 1)) (k slot call : ℕ) (state : ℝ × E × E) :
    (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 seeds k slot state) call).1 =
      state.1 + ∑ i ∈ Finset.range k, max 0 (seeds (slot + i)).1 := by
  induction k generalizing slot call state with
  | zero => simp [accelerationRunPlan, LongTails.Algorithms.StochasticEnvelopeProgram.slotPlan,
      QueryPlan.sampledEval]
  | succ k ih =>
      rw [sampled_acceleration_run_succ, ih, sampled_acceleration_advance, Finset.sum_range_succ']
      simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm]
      ring

lemma sampled_acceleration_run_auxiliary_mem {Q : Set E} {P : E → E}
    (hP : ∀ w, P w ∈ Q) (g : E → Ω → E) (ξ : ℕ → Ω)
    (weight mirror threshold : ℝ → ℝ) (γ L σ D v β η : ℝ) (x0 : E)
    (seeds : ℕ → ℝ × Fin (estimatorDepth v β + 1)) (k slot call : ℕ) (state : ℝ × E × E)
    (hz : state.2.2 ∈ Q) :
    (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 seeds k slot state) call).2.2 ∈ Q := by
  induction k generalizing slot call state with
  | zero => exact hz
  | succ k ih =>
      rw [sampled_acceleration_run_succ]
      apply ih
      rw [sampled_acceleration_advance]
      exact sampled_acceleration_auxiliary_mem hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma sampled_acceleration_run_seeded (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (weight mirror threshold : ℝ → ℝ) (γ L σ D v β η : ℝ) (x0 : E)
    (seeds : ℕ → ℝ × Fin (estimatorDepth v β + 1)) (k slot call : ℕ) (state : ℝ × E × E) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 seeds k slot state) call =
      seededStreamRun (fun a : ℝ × Fin (estimatorDepth v β + 1) => accelerationJumpCalls L σ D v β a.2.val)
        (fun u a ζ => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ζ
          (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 a u) 0)
        k state (fun i => seeds (slot + i.val)) (fun j => ξ (call + j)) := by
  induction k generalizing slot call state with
  | zero => rfl
  | succ k ih =>
      rw [sampled_acceleration_run_succ, ih, seededStreamRun]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      rw [StochasticCohypomonotone.sampledEval_shift _
        (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 (seeds slot) state) ξ call]
      congr 1
      · funext i
        congr 1
        omega
      · funext j
        congr 1
        omega

end

variable [InnerProductSpace ℝ E]

lemma measurable_acceleration_jump_joint [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D v β η c H : ℝ) (x0 : E) (call : ℕ) :
    Measurable (fun w : (E × E) × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (accelerationJumpPlan L σ D v β η c H w.1.1 w.1.2 x0 w.2.1) call) := by
  have hraw : Measurable (fun w : (E × E) × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (tunedEnvelopePlan L σ D v β w.1.1 x0 w.2.1) call) := by
    exact (measurable_envelope_estimate_joint hP hg L σ D (estimatorRadius L v β)
      (estimatorDepth v β) call).comp
      ((((measurable_fst.comp measurable_fst).prodMk measurable_const)).prodMk measurable_snd)
  have hclip := (measurable_clip H).comp hraw
  simp_rw [sampled_acceleration_jump]
  exact ((measurable_fst.comp measurable_fst).sub (hclip.const_smul η)).prodMk
    (hP.comp ((measurable_snd.comp measurable_fst).sub (hclip.const_smul c)))

lemma measurable_acceleration_jump_parameters {S : Type*} [MeasurableSpace S]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : E → E} {g : E → Ω → E} (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D v β : ℝ) (x0 : E) (call : ℕ)
    {x z : S → E} {η c H : S → ℝ} {j : S → Fin (estimatorDepth v β + 1)} {ξ : S → (ℕ → Ω)}
    (hx : Measurable x) (hz : Measurable z) (hη : Measurable η) (hc : Measurable c)
    (hH : Measurable H) (hj : Measurable j) (hξ : Measurable ξ) :
    Measurable (fun s => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (ξ s)
      (accelerationJumpPlan L σ D v β (η s) (c s) (H s) (x s) (z s) x0 (j s)) call) := by
  have hraw : Measurable (fun s => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (ξ s)
      (tunedEnvelopePlan L σ D v β (x s) x0 (j s)) call) :=
    (measurable_envelope_estimate_joint hP hg L σ D (estimatorRadius L v β)
      (estimatorDepth v β) call).comp ((hx.prodMk measurable_const).prodMk (hj.prodMk hξ))
  have hclip := MultiplicativeRobustEstimator.measurable_variable_clip.comp (hH.prodMk hraw)
  simp_rw [sampled_acceleration_jump]
  exact (hx.sub (hη.smul hclip)).prodMk (hP.comp (hz.sub (hc.smul hclip)))

lemma measurable_acceleration_advance_parameters {S : Type*} [MeasurableSpace S]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : E → E} {g : E → Ω → E} (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    {weight mirror threshold : ℝ → ℝ} {γ : ℝ} (hw : Continuous weight)
    (hwp : ∀ t, 0 < weight t) (hγ : 0 ≤ γ) (hm : Measurable mirror) (hH : Measurable threshold)
    (L σ D v β η : ℝ) (x0 : E) (call : ℕ)
    {state : S → ℝ × E × E} {seed : S → ℝ × Fin (estimatorDepth v β + 1)} {ξ : S → ℕ → Ω}
    (hs : Measurable state) (hseed : Measurable seed) (hξ : Measurable ξ) :
    Measurable (fun s => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (ξ s)
      (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 (seed s) (state s)) call) := by
  let τ := fun s => (state s).1 + max 0 (seed s).1
  let Y := fun s => accelerationFlow weight γ (state s).1 (τ s) (state s).2.1 (state s).2.2
  have ht : Measurable τ := hs.fst.add (measurable_const.max hseed.fst)
  have hY : Measurable Y := (continuous_acceleration_flow hw hwp hγ).measurable.comp
    ((hs.fst.prodMk ht).prodMk (hs.snd.fst.prodMk hs.snd.snd))
  have hj := measurable_acceleration_jump_parameters hP hg L σ D v β x0 call
    hY hs.snd.snd (measurable_const (a := η)) (hm.comp ht) (hH.comp ht) hseed.snd hξ
  simp only [sampled_acceleration_advance]
  exact ht.prodMk hj

lemma measurable_acceleration_advance_call {S : Type*} [MeasurableSpace S]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : E → E} {g : E → Ω → E} (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    {weight mirror threshold : ℝ → ℝ} {γ : ℝ} (hw : Continuous weight)
    (hwp : ∀ t, 0 < weight t) (hγ : 0 ≤ γ) (hm : Measurable mirror) (hH : Measurable threshold)
    (L σ D v β η : ℝ) (x0 : E)
    {state : S → ℝ × E × E} {seed : S → ℝ × Fin (estimatorDepth v β + 1)} {ξ : S → ℕ → Ω}
    {call : S → ℕ} (hs : Measurable state) (hseed : Measurable seed) (hξ : Measurable ξ)
    (hcall : Measurable call) :
    Measurable (fun s => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (ξ s)
      (accelerationAdvancePlan weight mirror threshold γ L σ D v β η x0 (seed s) (state s)) (call s)) := by
  have ht : Measurable (fun s => fun j => ξ s (call s + j)) :=
    (LongTails.Proofs.StochasticEnvelopeFreshness.measurable_seed_shift hcall).comp
      (measurable_id.prodMk hξ)
  have hh := measurable_acceleration_advance_parameters hP hg hw hwp hγ hm hH
    L σ D v β η x0 0 hs hseed ht
  convert hh using 1
  funext s
  exact StochasticCohypomonotone.sampledEval_shift _ _ _ _

lemma measurable_acceleration_run_parameters {S : Type*} [MeasurableSpace S]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : E → E} {g : E → Ω → E} (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    {weight mirror threshold : ℝ → ℝ} {γ : ℝ} (hw : Continuous weight)
    (hwp : ∀ t, 0 < weight t) (hγ : 0 ≤ γ) (hm : Measurable mirror) (hH : Measurable threshold)
    (L σ D v β η : ℝ) (x0 : E) (k slot : ℕ)
    {state : S → ℝ × E × E} {seeds : S → ℕ → ℝ × Fin (estimatorDepth v β + 1)} {ξ : S → ℕ → Ω}
    {call : S → ℕ} (hs : Measurable state) (hseeds : Measurable seeds) (hξ : Measurable ξ)
    (hcall : Measurable call) :
    Measurable (fun s => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (ξ s)
      (accelerationRunPlan weight mirror threshold γ L σ D v β η x0 (seeds s) k slot (state s)) (call s)) := by
  induction k generalizing slot state call with
  | zero => exact hs
  | succ k ih =>
      have hseed := (measurable_pi_apply slot).comp hseeds
      have hnext := measurable_acceleration_advance_call hP hg hw hwp hγ hm hH L σ D v β η x0
        hs hseed hξ hcall
      have hcost : Measurable (fun s => accelerationJumpCalls L σ D v β (seeds s slot).2.val) :=
        (measurable_of_finite (fun j : Fin (estimatorDepth v β + 1) =>
          accelerationJumpCalls L σ D v β j.val)).comp hseed.snd
      simp only [sampled_acceleration_run_succ]
      exact ih (slot + 1) hnext (hcall.add hcost)

end OracleTemplate.StochasticQuasar
