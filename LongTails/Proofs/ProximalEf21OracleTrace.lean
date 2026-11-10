import LongTails.Proofs.ProximalEf21Regularity
import LongTails.Proofs.ProximalEf21BudgetBridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

noncomputable section

namespace LongTails.Proofs.ProximalEf21OracleTrace

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21Regularity
open LongTails.Proofs.ProximalEf21SetupGeometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21ConditionalBatch

variable {p : Params} {I : Instance p}
variable (O : Oracle (Query p) (Reply p) 4)

abbrev Prefix (k : ℕ) := InitialMemories p × ((j : Fin k) → O.Seed j.val)

noncomputable def prefix (k : ℕ) (ω : Randomness p O) : Prefix O k :=
  (ω.1, fun j => ω.2 j.val)

noncomputable def defaultTape : Tape O :=
  Classical.choice (nonempty_of_isProbabilityMeasure (O.law : Measure _))

noncomputable def truncatedTape (k : ℕ) (ω : Randomness p O) : Tape O :=
  fun j => if j < k then ω.2 j else defaultTape O j

lemma prefix_measurable (k : ℕ) :
    @Measurable _ _ (pastSpace p O k) inferInstance (prefix O k) := measurable_comap

lemma past_le (k : ℕ) : pastSpace p O k ≤ inferInstance := by
  change Measurable (prefix O k)
  exact measurable_fst.prodMk (measurable_pi_lambda _ (fun j => (measurable_pi_apply j.val).comp measurable_snd))

lemma past_mono {k l : ℕ} (hkl : k ≤ l) : pastSpace p O k ≤ pastSpace p O l := by
  change @Measurable _ _ (pastSpace p O l) inferInstance (prefix O k)
  let restrict : Prefix O l → Prefix O k := fun a =>
    (a.1, fun j => a.2 ⟨j.val, lt_of_lt_of_le j.isLt hkl⟩)
  have hr : Measurable restrict := by
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp measurable_snd))
  exact hr.comp (prefix_measurable O l)

lemma measurable_enlarge {A : Type*} [MeasurableSpace A]
    {k l : ℕ} (hkl : k ≤ l) {f : Randomness p O → A}
    (hf : @Measurable _ _ (pastSpace p O k) inferInstance f) :
    @Measurable _ _ (pastSpace p O l) inferInstance f := hf.mono (past_mono O hkl) le_rfl

lemma measurable_global {A : Type*} [MeasurableSpace A]
    {k : ℕ} {f : Randomness p O → A}
    (hf : @Measurable _ _ (pastSpace p O k) inferInstance f) : Measurable f :=
  hf.mono (past_le O k) le_rfl

lemma seed_predictable {k j : ℕ} (hj : j < k) :
    @Measurable _ _ (pastSpace p O k) inferInstance (fun ω : Randomness p O => ω.2 j) := by
  exact ((measurable_pi_apply (⟨j, hj⟩ : Fin k)).comp measurable_snd).comp (prefix_measurable O k)

lemma truncated_predictable (k : ℕ) :
    @Measurable _ _ (pastSpace p O k) inferInstance (truncatedTape O k) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < k
  · simpa only [truncatedTape, if_pos hj] using seed_predictable O hj
  · simpa only [truncatedTape, if_neg hj] using
      (measurable_const : @Measurable _ _ (pastSpace p O k) inferInstance
        (fun _ : Randomness p O => defaultTape O j))

lemma response_predictable (ho : OracleAssumptions p I O)
    {k : ℕ} (h : Randomness p O → History p)
    (q : Randomness p O → Fin 4 × Query p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hq : @Measurable _ _ (pastSpace p O k) inferInstance q)
    (hlen : ∀ ω, (h ω).length = k) :
    @Measurable _ _ (pastSpace p O (k + 1)) inferInstance
      (fun ω => response O (h ω) (q ω) ω.2) := by
  have hm := ho.jointMeasurability.comp
    (((measurable_enlarge O (Nat.le_succ k) hh).prodMk
      (measurable_enlarge O (Nat.le_succ k) hq)).prodMk (truncated_predictable O (k + 1)))
  have he : (fun ω => response O (h ω) (q ω) (truncatedTape O (k + 1) ω)) =
      (fun ω => response O (h ω) (q ω) ω.2) := by
    funext ω
    unfold response
    congr 1
    simp [truncatedTape, hlen ω]
  rwa [he] at hm

noncomputable def appendReply (h : History p) (q : Fin 4 × Query p) (a : Reply p) :
    History p := h ++ [(q, a)]

lemma appendReply_length (h : History p) (q : Fin 4 × Query p) (a : Reply p) :
    (appendReply h q a).length = h.length + 1 := by simp [appendReply]

lemma appendReply_predictable (ho : OracleAssumptions p I O)
    {k : ℕ} (h : Randomness p O → History p)
    (q : Randomness p O → Fin 4 × Query p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hq : @Measurable _ _ (pastSpace p O k) inferInstance q)
    (hlen : ∀ ω, (h ω).length = k) :
    @Measurable _ _ (pastSpace p O (k + 1)) inferInstance
      (fun ω => appendReply (h ω) (q ω) (response O (h ω) (q ω) ω.2)) := by
  have hr := response_predictable O ho h q hh hq hlen
  have hh' := measurable_enlarge O (Nat.le_succ k) hh
  have hq' := measurable_enlarge O (Nat.le_succ k) hq
  unfold appendReply
  exact hh'.append ((hq'.prodMk hr).list_singleton)

noncomputable def batchHistory (h : Randomness p O → History p)
    (x : Randomness p O → Point p) : ℕ → Randomness p O → History p
  | 0 => h
  | j + 1 => fun ω => appendReply (batchHistory h x j ω) (0, (x ω, 0))
      (response O (batchHistory h x j ω) (0, (x ω, 0)) ω.2)

noncomputable def rawSample (h : Randomness p O → History p)
    (x : Randomness p O → Point p) (j : ℕ) (i : Fin p.workers)
    (ω : Randomness p O) : Point p :=
  (response O (batchHistory O h x j ω) (0, (x ω, 0)) ω.2).2 i

noncomputable def batchError (h : Randomness p O → History p)
    (x : Randomness p O → Point p) (B : ℕ) (i : Fin p.workers)
    (ω : Randomness p O) : Point p :=
  (B : ℝ)⁻¹ • ∑ j : Fin B, (rawSample O h x j.val i ω - gradient (I.f i) (x ω))

lemma batch_history_length {k : ℕ} (h : Randomness p O → History p)
    (x : Randomness p O → Point p) (hlen : ∀ ω, (h ω).length = k) (j : ℕ) :
    ∀ ω, (batchHistory O h x j ω).length = k + j := by
  induction j with
  | zero => simpa [batchHistory] using hlen
  | succ j ih =>
      intro ω
      simp [batchHistory, appendReply_length, ih ω, Nat.add_assoc]

lemma batch_history_predictable (ho : OracleAssumptions p I O)
    {k : ℕ} (h : Randomness p O → History p) (x : Randomness p O → Point p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hx : @Measurable _ _ (pastSpace p O k) inferInstance x)
    (hlen : ∀ ω, (h ω).length = k) (j : ℕ) :
    @Measurable _ _ (pastSpace p O (k + j)) inferInstance (batchHistory O h x j) := by
  induction j with
  | zero => simpa [batchHistory] using hh
  | succ j ih =>
      have hq : @Measurable _ _ (pastSpace p O (k + j)) inferInstance
          (fun ω : Randomness p O => ((0 : Fin 4), (x ω, (0 : WorkerVectors p)))) :=
        measurable_const.prodMk ((measurable_enlarge O (Nat.le_add_right k j) hx).prodMk measurable_const)
      simpa [batchHistory, Nat.add_assoc] using appendReply_predictable O ho
        (batchHistory O h x j) _ ih hq (batch_history_length O h x hlen j)

lemma raw_sample_predictable (ho : OracleAssumptions p I O)
    {k : ℕ} (h : Randomness p O → History p) (x : Randomness p O → Point p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hx : @Measurable _ _ (pastSpace p O k) inferInstance x)
    (hlen : ∀ ω, (h ω).length = k) (j : ℕ) (i : Fin p.workers) :
    @Measurable _ _ (pastSpace p O (k + j + 1)) inferInstance (rawSample O h x j i) := by
  have hj := batch_history_predictable O ho h x hh hx hlen j
  have hq : @Measurable _ _ (pastSpace p O (k + j)) inferInstance
      (fun ω : Randomness p O => ((0 : Fin 4), (x ω, (0 : WorkerVectors p)))) :=
    measurable_const.prodMk ((measurable_enlarge O (Nat.le_add_right k j) hx).prodMk measurable_const)
  exact (measurable_pi_apply i).comp
    (response_predictable O ho _ _ hj hq (batch_history_length O h x hlen j)).snd

lemma raw_sample_moments (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) {k : ℕ}
    (h : Randomness p O → History p) (x : Randomness p O → Point p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hx : @Measurable _ _ (pastSpace p O k) inferInstance x)
    (hlen : ∀ ω, (h ω).length = k)
    (hxl : MemLp x 2 (executionMeasure p O)) (j : ℕ) (i : Fin p.workers) :
    MemLp (rawSample O h x j i) 2 (executionMeasure p O) ∧
    MemLp (fun ω => rawSample O h x j i ω - gradient (I.f i) (x ω)) 2
      (executionMeasure p O) ∧
    (condExp (pastSpace p O (k + j)) (executionMeasure p O)
      (fun ω => rawSample O h x j i ω - gradient (I.f i) (x ω)) =ᵐ[executionMeasure p O]
      (fun _ => 0)) ∧
    (∀ᵐ ω ∂(executionMeasure p O),
      condExp (pastSpace p O (k + j)) (executionMeasure p O)
        (fun ω' => ‖rawSample O h x j i ω' - gradient (I.f i) (x ω')‖ ^ 2) ω ≤ p.σ ^ 2) := by
  let P := executionMeasure p O
  have hhj := batch_history_predictable O ho h x hh hx hlen j
  have hxj := measurable_enlarge O (Nat.le_add_right k j) hx
  have ha := ho.conditionalGradient (k + j) (batchHistory O h x j) x hhj hxj
    (batch_history_length O h x hlen j) (norm_square_integrable P hxl) i
  have hm := measurable_global O (raw_sample_predictable O ho h x hh hx hlen j i)
  have hgm := (gradient_continuous hg i).measurable.comp (measurable_global O hx)
  have he : MemLp (fun ω => rawSample O h x j i ω - gradient (I.f i) (x ω)) 2 P :=
    memLp_of_integrable_square P (hm.sub hgm).aestronglyMeasurable ha.2.1
  have hgl := gradient_memLp P hg i hxl
  have hs : MemLp (rawSample O h x j i) 2 P := by
    simpa only [sub_add_cancel] using he.add hgl
  refine ⟨hs, he, ?_, ha.2.2.2⟩
  have hc := condExp_sub (hs.integrable (by norm_num)) (hgl.integrable (by norm_num))
    (pastSpace p O (k + j))
  have hgfix := condExp_of_aestronglyMeasurable' (past_le O (k + j))
    ((gradient_continuous hg i).measurable.comp hxj).aestronglyMeasurable
    (hgl.integrable (by norm_num))
  filter_upwards [hc, ha.2.2.1, hgfix] with ω hc ha hgfix
  simpa only [ha, hgfix, sub_self] using hc

lemma batch_error_moments (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) {k B : ℕ} (hB : 0 < B)
    (h : Randomness p O → History p) (x : Randomness p O → Point p)
    (hh : @Measurable _ _ (pastSpace p O k) inferInstance h)
    (hx : @Measurable _ _ (pastSpace p O k) inferInstance x)
    (hlen : ∀ ω, (h ω).length = k)
    (hxl : MemLp x 2 (executionMeasure p O)) (i : Fin p.workers) :
    MemLp (batchError O (I := I) h x B i) 2 (executionMeasure p O) ∧
    (condExp (pastSpace p O k) (executionMeasure p O) (batchError O (I := I) h x B i)
      =ᵐ[executionMeasure p O] (fun _ => 0)) ∧
    (∀ᵐ ω ∂(executionMeasure p O), condExp (pastSpace p O k) (executionMeasure p O)
      (fun ω' => ‖batchError O (I := I) h x B i ω'‖ ^ 2) ω ≤ p.σ ^ 2 / B) := by
  let P := executionMeasure p O
  let ζ : Fin B → Randomness p O → Point p := fun j ω =>
    rawSample O h x j.val i ω - gradient (I.f i) (x ω)
  let ℱ : Fin B → MeasurableSpace (Randomness p O) := fun j => pastSpace p O (k + j.val)
  have hζ (j : Fin B) := raw_sample_moments O hp hg ho h x hh hx hlen hxl j.val i
  have hpred (a b : Fin B) (hab : a < b) :
      AEStronglyMeasurable[ℱ b] (ζ a) P := by
    have hraw := raw_sample_predictable O ho h x hh hx hlen a.val i
    have hraw' := measurable_enlarge O (show k + a.val + 1 ≤ k + b.val by omega) hraw
    have hx' := measurable_enlarge O (Nat.le_add_right k b.val) hx
    exact (hraw'.sub ((gradient_continuous hg i).measurable.comp hx')).aestronglyMeasurable
  have hl : MemLp (fun ω => (B : ℝ)⁻¹ • ∑ j, ζ j ω) 2 P :=
    (MemLp.finset_sum _ (fun j _ => (hζ j).2.1)).const_smul _
  refine ⟨hl, ?_, ?_⟩
  · exact conditional_batch_mean P (pastSpace p O k) ℱ
      (fun j => past_mono O (Nat.le_add_right k j.val))
      (fun j => past_le O (k + j.val)) ζ
      (fun j => (hζ j).2.1) (fun j => (hζ j).2.2.1)
  · exact conditional_batch_variance hB P (pastSpace p O k) ℱ
      (fun j => past_mono O (Nat.le_add_right k j.val))
      (fun j => past_le O (k + j.val)) ζ p.σ
      (fun j => (hζ j).2.1) hpred (fun j => (hζ j).2.2.1)
      (fun j => (hζ j).2.2.2)

end LongTails.Proofs.ProximalEf21OracleTrace
