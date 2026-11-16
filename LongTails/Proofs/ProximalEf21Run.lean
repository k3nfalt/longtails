import LongTails.Algorithms.ProximalEf21Homotopy
import LongTails.Proofs.ProximalEf21Bound
import LongTails.Proofs.ProximalEf21Moments
import LongTails.Proofs.ProximalEf21Step
import LongTails.Proofs.ProximalEf21Tuning
import LongTails.Template
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

section OracleTrace

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

instance executionMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (executionMeasure p O) := by
  unfold executionMeasure
  infer_instance

abbrev Prefix (k : ℕ) := InitialMemories p × ((j : Fin k) → O.Seed j.val)

noncomputable def observedPrefix (k : ℕ) (ω : Randomness p O) : Prefix O k :=
  (ω.1, fun j => ω.2 j.val)

noncomputable def defaultTape : Tape O :=
  Classical.choice (nonempty_of_isProbabilityMeasure (O.law : Measure _))

noncomputable def truncatedTape (k : ℕ) (ω : Randomness p O) : Tape O :=
  fun j => if j < k then ω.2 j else defaultTape O j

lemma prefix_measurable (k : ℕ) :
    @Measurable _ _ (pastSpace p O k) inferInstance (observedPrefix O k) :=
  comap_measurable (observedPrefix O k)

lemma past_le (k : ℕ) :
    pastSpace p O k ≤ (inferInstance : MeasurableSpace (Randomness p O)) := by
  have hm : Measurable (observedPrefix O k) :=
    measurable_fst.prodMk
      (Measurable.of_eval (fun j => (measurable_pi_apply j.val).comp measurable_snd))
  exact hm.comap_le

lemma past_mono {k l : ℕ} (hkl : k ≤ l) : pastSpace p O k ≤ pastSpace p O l := by
  let restrict : Prefix O l → Prefix O k := fun a =>
    (a.1, fun j => a.2 ⟨j.val, lt_of_lt_of_le j.isLt hkl⟩)
  have hr : Measurable restrict :=
    measurable_fst.prodMk
      (Measurable.of_eval (fun j => (measurable_pi_apply _).comp measurable_snd))
  have hm : @Measurable _ _ (pastSpace p O l) inferInstance (observedPrefix O k) :=
    hr.comp (prefix_measurable O l)
  exact hm.comap_le

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
  letI : MeasurableSpace (Randomness p O) := pastSpace p O k
  change Measurable (truncatedTape O k)
  apply Measurable.of_eval
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
  have hm : @Measurable _ _ (pastSpace p O (k + 1)) inferInstance
      (fun ω => response O (h ω) (q ω) (truncatedTape O (k + 1) ω)) :=
    ho.jointMeasurability.comp
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
  have hc : Continuous
      (fun z : (((Fin 4 × Query p) × Reply p) × History p) =>
        z.2.insertIdx k z.1) := List.continuous_insertIdx
  have hinsert : Measurable
      (fun z : (((Fin 4 × Query p) × Reply p) × History p) =>
        z.2.insertIdx k z.1) := hc.measurable
  have hm : @Measurable _ _ (pastSpace p O (k + 1)) inferInstance
      (fun ω => (h ω).insertIdx k (q ω, response O (h ω) (q ω) ω.2)) :=
    hinsert.comp ((hq'.prodMk hr).prodMk hh')
  have he :
      (fun ω => (h ω).insertIdx k (q ω, response O (h ω) (q ω) ω.2)) =
      (fun ω => appendReply (h ω) (q ω) (response O (h ω) (q ω) ω.2)) := by
    funext ω
    rw [← hlen ω, List.insertIdx_length_self]
    rfl
  rwa [he] at hm

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
    have hsum := he.add hgl
    have hfun :
        ((fun ω : Randomness p O => rawSample O h x j i ω - gradient (I.f i) (x ω)) +
          (fun ω : Randomness p O => gradient (I.f i) (x ω))) = rawSample O h x j i := by
      funext ω
      exact sub_add_cancel _ _
    rw [hfun] at hsum
    exact hsum
  refine ⟨hs, he, ?_, ha.2.2.2⟩
  have hc := condExp_sub (μ := P)
    (f := rawSample O h x j i) (g := fun ω => gradient (I.f i) (x ω))
    (hs.integrable (by norm_num)) (hgl.integrable (by norm_num))
    (pastSpace p O (k + j))
  have hsub :
      (rawSample O h x j i - (fun ω => gradient (I.f i) (x ω))) =
        (fun ω => rawSample O h x j i ω - gradient (I.f i) (x ω)) := rfl
  rw [hsub] at hc
  have hraw : condExp (pastSpace p O (k + j)) P (rawSample O h x j i)
      =ᵐ[P] (fun ω => gradient (I.f i) (x ω)) := ha.2.2.1
  have hgfix : condExp (pastSpace p O (k + j)) P
      (fun ω => gradient (I.f i) (x ω)) =ᵐ[P]
        (fun ω => gradient (I.f i) (x ω)) :=
    condExp_of_aestronglyMeasurable' (μ := P) (past_le O (k + j))
      ((gradient_continuous hg i).measurable.comp hxj).aestronglyMeasurable
      (hgl.integrable (by norm_num))
  filter_upwards [hc, hraw, hgfix] with ω hc hraw hgfix
  change condExp (pastSpace p O (k + j)) P
      (fun ω => rawSample O h x j i ω - gradient (I.f i) (x ω)) ω =
    condExp (pastSpace p O (k + j)) P (rawSample O h x j i) ω -
      condExp (pastSpace p O (k + j)) P
        (fun ω => gradient (I.f i) (x ω)) ω at hc
  rw [hraw, hgfix, sub_self] at hc
  exact hc

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
  let P : Measure (Randomness p O) := executionMeasure p O
  let ζ : Fin B → Randomness p O → Point p := fun j ω =>
    rawSample O h x j.val i ω - gradient (I.f i) (x ω)
  let ℱ : Fin B → MeasurableSpace (Randomness p O) := fun j => pastSpace p O (k + j.val)
  have hmom (j : Fin B) :
      MemLp (ζ j) 2 P ∧
      (condExp (ℱ j) P (ζ j) =ᵐ[P] (fun _ => 0)) ∧
      (∀ᵐ ω ∂P, condExp (ℱ j) P (fun ω' => ‖ζ j ω'‖ ^ 2) ω ≤ p.σ ^ 2) :=
    (raw_sample_moments O hp hg ho h x hh hx hlen hxl j.val i).2
  have hζ : ∀ j : Fin B, MemLp (ζ j) 2 P := fun j => (hmom j).1
  have hzero : ∀ j : Fin B, condExp (ℱ j) P (ζ j) =ᵐ[P] (fun _ => 0) :=
    fun j => (hmom j).2.1
  have hvar : ∀ j : Fin B, ∀ᵐ ω ∂P,
      condExp (ℱ j) P (fun ω' => ‖ζ j ω'‖ ^ 2) ω ≤ p.σ ^ 2 :=
    fun j => (hmom j).2.2
  have hsmall : ∀ j : Fin B, pastSpace p O k ≤ ℱ j :=
    fun j => past_mono O (Nat.le_add_right k j.val)
  have hambient : ∀ j : Fin B,
      ℱ j ≤ (inferInstance : MeasurableSpace (Randomness p O)) :=
    fun j => past_le O (k + j.val)
  have hpred (a b : Fin B) (hab : a < b) :
      AEStronglyMeasurable[ℱ b] (ζ a) P := by
    have hraw : @Measurable _ _ (pastSpace p O (k + a.val + 1)) inferInstance
        (rawSample O h x a.val i) :=
      raw_sample_predictable O ho h x hh hx hlen a.val i
    have hraw' : @Measurable _ _ (ℱ b) inferInstance (rawSample O h x a.val i) :=
      measurable_enlarge O (k := k + a.val + 1) (l := k + b.val) (by omega) hraw
    have hx' : @Measurable _ _ (ℱ b) inferInstance x :=
      measurable_enlarge O (k := k) (l := k + b.val) (Nat.le_add_right k b.val) hx
    exact (hraw'.sub ((gradient_continuous hg i).measurable.comp hx')).aestronglyMeasurable
  change MemLp (fun ω => (B : ℝ)⁻¹ • ∑ j : Fin B, ζ j ω) 2 P ∧
    (condExp (pastSpace p O k) P (fun ω => (B : ℝ)⁻¹ • ∑ j : Fin B, ζ j ω)
      =ᵐ[P] (fun _ => 0)) ∧
    (∀ᵐ ω ∂P, condExp (pastSpace p O k) P
      (fun ω' => ‖(B : ℝ)⁻¹ • ∑ j : Fin B, ζ j ω'‖ ^ 2) ω ≤ p.σ ^ 2 / B)
  refine ⟨?_, ?_, ?_⟩
  · exact (memLp_finsetSum (Finset.univ : Finset (Fin B)) (f := ζ)
      (fun j _ => hζ j)).const_smul ((B : ℝ)⁻¹)
  · exact conditional_batch_mean (mΩ := inferInstance) (E := Point p) (B := B)
      P (pastSpace p O k) ℱ hsmall hambient ζ hζ hzero
  · exact conditional_batch_variance (mΩ := inferInstance) (E := Point p) (B := B)
      hB P (pastSpace p O k) ℱ hsmall hambient ζ p.σ hζ hpred hzero hvar

end LongTails.Proofs.ProximalEf21OracleTrace

end

end OracleTrace


section ConstructedTrajectory_construction

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

noncomputable section

namespace LongTails.Proofs.ProximalEf21ConstructedTrajectory

open LongTails.Proofs.ProximalEf21AverageMoments

open LongTails.Proofs.ProximalEf21Averages

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21SetupGeometry
open LongTails.Proofs.ProximalEf21Regularity
open LongTails.Proofs.ProximalEf21OracleTrace
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21CountedBudget
open LongTails.Proofs.ProximalEf21Regularization
open LongTails.Proofs.ProximalEf21InnerTrajectory
open LongTails.Proofs.ProximalEf21HomotopyTrajectory

variable {p : Params} {I : Instance p}
variable (O : Oracle (Query p) (Reply p) 4)

structure Node (p : Params) where
  x : Point p
  m : WorkerVectors p
  v : WorkerVectors p
  history : History p

abbrev NodePath := Randomness p O → Node p

noncomputable def initialNode : NodePath O := fun ω =>
  ⟨p.x0, ω.1.1, ω.1.2, []⟩

noncomputable def proxQuery (r : NodePath O) (ω : Randomness p O) : Fin 4 × Query p :=
  (2, ((r ω).x - executionStep p • workerMean (r ω).v, 0))

noncomputable def proxReply (r : NodePath O) (ω : Randomness p O) : Reply p :=
  response O (r ω).history (proxQuery O r ω) ω.2

noncomputable def nextX (r : NodePath O) (ω : Randomness p O) : Point p := (proxReply O r ω).1

noncomputable def afterProx (r : NodePath O) (ω : Randomness p O) : History p :=
  appendReply (r ω).history (proxQuery O r ω) (proxReply O r ω)

noncomputable def afterBatch (s : ℕ) (r : NodePath O) : Randomness p O → History p :=
  batchHistory O (afterProx O r) (nextX O r) (batchSize p s)

noncomputable def nextM (s : ℕ) (r : NodePath O) (i : Fin p.workers)
    (ω : Randomness p O) : Point p :=
  (1 - momentum p s) • (r ω).m i + momentum p s •
    ((batchSize p s : ℝ)⁻¹ • (∑ j : Fin (batchSize p s),
      rawSample O (afterProx O r) (nextX O r) j.val i ω) +
        regularization p s • (nextX O r ω - p.x0))

noncomputable def compressQuery (s : ℕ) (r : NodePath O) (ω : Randomness p O) :
    Fin 4 × Query p :=
  (1, (nextX O r ω, fun i => nextM O s r i ω - (r ω).v i))

noncomputable def compressReply (s : ℕ) (r : NodePath O) (ω : Randomness p O) : Reply p :=
  response O (afterBatch O s r ω) (compressQuery O s r ω) ω.2

noncomputable def step (s : ℕ) (r : NodePath O) : NodePath O := fun ω =>
  ⟨nextX O r ω, fun i => nextM O s r i ω,
    fun i => (r ω).v i + (compressReply O s r ω).2 i,
    appendReply (afterBatch O s r ω) (compressQuery O s r ω) (compressReply O s r ω)⟩

noncomputable def iterate (s : ℕ) (r : NodePath O) : ℕ → NodePath O
  | 0 => r
  | t + 1 => step O s (iterate s r t)

noncomputable def stageStart : ℕ → NodePath O
  | 0 => initialNode O
  | s + 1 => iterate O s (stageStart s) (stageLength p s)

noncomputable def stageRun (s t : ℕ) : NodePath O := iterate O s (stageStart O s) t

noncomputable def stageOffset (p : Params) (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, stageLength p j * (batchSize p j + 2)

noncomputable def clock (p : Params) (s t : ℕ) : ℕ :=
  stageOffset p s + t * (batchSize p s + 2)

lemma step_positive (hp : spec.valid p) : 0 < executionStep p := by
  unfold executionStep
  exact div_pos hp.2.2.2.2.1 (by have hL := hp.2.1; positivity)

lemma regularization_positive (hp : spec.valid p) (s : ℕ) : 0 < regularization p s := by
  exact mu_positive hp.2.1 s

lemma batch_positive (s : ℕ) : 0 < batchSize p s := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma stage_length_positive (hp : spec.valid p) (s : ℕ) : 0 < stageLength p s := by
  have hγ := step_positive hp
  have hμ := regularization_positive hp s
  have hR : 0 < p.R := hp.2.2.1
  have hH : 0 ≤ p.H := hp.2.2.2.2.2.2.2.2
  unfold stageLength
  split_ifs with hs
  · apply Nat.ceil_pos.mpr
    have hn : 0 ≤ 2 * p.H / (8192 * regularization p 0 * p.R ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) hH)
        (by have hμ0 := regularization_positive hp 0; positivity)
    have ha : (1 : ℝ) < 2 + 2 * p.H / (8192 * regularization p 0 * p.R ^ 2) := by
      linarith only [hn]
    exact mul_pos (div_pos (by norm_num) (mul_pos (regularization_positive hp 0) hγ))
      (Real.log_pos ha)
  · exact Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (mul_pos hμ hγ))

lemma nextX_eq (ho : OracleAssumptions p I O) (r : NodePath O) (ω : Randomness p O) :
    nextX O r ω = I.prox (executionStep p)
      ((r ω).x - executionStep p • workerMean (r ω).v) := by
  exact ho.exactProximal (r ω).history _ (ω.2 (r ω).history.length)

lemma step_history_length {k : ℕ} (s : ℕ) (r : NodePath O)
    (hr : ∀ ω, (r ω).history.length = k) :
    ∀ ω, (step O s r ω).history.length = k + (batchSize p s + 2) := by
  have hh : ∀ ω, (afterProx O r ω).length = k + 1 := by
    intro ω
    simp [afterProx, appendReply_length, hr ω]
  have hb := batch_history_length O (afterProx O r) (nextX O r) hh (batchSize p s)
  intro ω
  simp only [step, appendReply_length, afterBatch, hb ω]
  omega

structure Regular (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (k : ℕ) (r : NodePath O) : Prop where
  history_length : ∀ ω, (r ω).history.length = k
  history_measurable : @Measurable _ _ (pastSpace p O k) inferInstance (fun ω => (r ω).history)
  x_measurable : @Measurable _ _ (pastSpace p O k) inferInstance (fun ω => (r ω).x)
  m_measurable : ∀ i, @Measurable _ _ (pastSpace p O k) inferInstance (fun ω => (r ω).m i)
  v_measurable : ∀ i, @Measurable _ _ (pastSpace p O k) inferInstance (fun ω => (r ω).v i)
  x_memLp : MemLp (fun ω => (r ω).x) 2 (executionMeasure p O)
  m_memLp : ∀ i, MemLp (fun ω => (r ω).m i) 2 (executionMeasure p O)
  v_memLp : ∀ i, MemLp (fun ω => (r ω).v i) 2 (executionMeasure p O)
  feasible : ∀ ω, (r ω).x ∈ domain I
  regularizer_integrable : Integrable (fun ω => psiValue I (r ω).x) (executionMeasure p O)

lemma initial_regular (hp : spec.valid p) (hg : ProblemAssumptions p I) :
    Regular O hp hg 0 (initialNode O) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; rfl
  · exact measurable_const
  · exact measurable_const
  · intro i
    exact (measurable_pi_apply i).comp ((prefix_measurable O 0).fst.fst)
  · intro i
    exact (measurable_pi_apply i).comp ((prefix_measurable O 0).fst.snd)
  · change MemLp (fun _ : Randomness p O => p.x0) 2 (executionMeasure p O)
    exact memLp_const p.x0
  · exact initial_momentum_memLp hg O
  · exact initial_compressed_memLp hg O
  · intro ω; exact hg.initialFinite
  · change Integrable (fun _ : Randomness p O => psiValue I p.x0)
      (executionMeasure p O)
    exact integrable_const (psiValue I p.x0)

namespace Regular

variable {O} {hp : spec.valid p} {hg : ProblemAssumptions p I}
variable {k : ℕ} {r : NodePath O} (hr : Regular O hp hg k r)
variable (ho : OracleAssumptions p I O)

include hr

lemma m_mean_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance
      (fun ω => workerMean (r ω).m) := by
  have hsum : @Measurable _ _ (pastSpace p O k) inferInstance
      (fun ω => ∑ i : Fin p.workers, (r ω).m i) :=
    Finset.measurable_sum Finset.univ (fun i _ => hr.m_measurable i)
  exact hsum.const_smul ((p.workers : ℝ)⁻¹)

lemma v_mean_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance
      (fun ω => workerMean (r ω).v) := by
  have hsum : @Measurable _ _ (pastSpace p O k) inferInstance
      (fun ω => ∑ i : Fin p.workers, (r ω).v i) :=
    Finset.measurable_sum Finset.univ (fun i _ => hr.v_measurable i)
  exact hsum.const_smul ((p.workers : ℝ)⁻¹)

include ho in
lemma next_x_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance (nextX O r) := by
  have hm := (hg.proximalMeasurable (executionStep p) (step_positive hp)).comp
    (hr.x_measurable.sub (hr.v_mean_measurable.const_smul (executionStep p)))
  have hnext : nextX O r = (fun ω => I.prox (executionStep p)
      ((r ω).x - executionStep p • workerMean (r ω).v)) := by
    funext ω
    exact nextX_eq O ho r ω
  rw [hnext]
  exact hm

include ho in
lemma next_x_memLp : MemLp (nextX O r) 2 (executionMeasure p O) := by
  have hv := workerMean_memLp (executionMeasure p O) (fun i ω => (r ω).v i) hr.v_memLp
  have hm := prox_memLp (executionMeasure p O) hp hg (step_positive hp)
    (hr.x_memLp.sub (hv.const_smul (executionStep p)))
  have hnext : nextX O r = (fun ω => I.prox (executionStep p)
      ((r ω).x - executionStep p • workerMean (r ω).v)) := by
    funext ω
    exact nextX_eq O ho r ω
  rw [hnext]
  exact hm

lemma after_prox_length : ∀ ω, (afterProx O r ω).length = k + 1 := by
  intro ω
  simp [afterProx, appendReply_length, hr.history_length ω]

lemma prox_query_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance (proxQuery O r) := by
  unfold proxQuery
  exact measurable_const.prodMk
    ((hr.x_measurable.sub
      (hr.v_mean_measurable.const_smul (executionStep p))).prodMk measurable_const)

include ho in
lemma after_prox_measurable :
    @Measurable _ _ (pastSpace p O (k + 1)) inferInstance (afterProx O r) := by
  exact appendReply_predictable O ho _ _ hr.history_measurable hr.prox_query_measurable hr.history_length

include ho in
lemma after_batch_measurable (s : ℕ) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (afterBatch O s r) := by
  exact batch_history_predictable O ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length (batchSize p s)

lemma after_batch_length (s : ℕ) : ∀ ω, (afterBatch O s r ω).length = k + 1 + batchSize p s :=
  batch_history_length O _ _ hr.after_prox_length (batchSize p s)

include ho in
lemma raw_measurable (s : ℕ) (j : Fin (batchSize p s)) (i : Fin p.workers) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (rawSample O (afterProx O r) (nextX O r) j.val i) := by
  have hm := raw_sample_predictable O ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length j.val i
  exact measurable_enlarge O (k := k + 1 + j.val + 1)
    (l := k + 1 + batchSize p s) (by omega) hm

include ho in
lemma raw_memLp (s : ℕ) (j : Fin (batchSize p s)) (i : Fin p.workers) :
    MemLp (rawSample O (afterProx O r) (nextX O r) j.val i) 2 (executionMeasure p O) := by
  exact (raw_sample_moments O hp hg ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length (hr.next_x_memLp ho) j.val i).1

include ho in
lemma next_m_measurable (s : ℕ) (i : Fin p.workers) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (nextM O s r i) := by
  unfold nextM
  have hm : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (fun ω => (r ω).m i) :=
    measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
      (hr.m_measurable i)
  have hx : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (nextX O r) :=
    measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
      (hr.next_x_measurable ho)
  have hsum : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (fun ω => ∑ j : Fin (batchSize p s),
        rawSample O (afterProx O r) (nextX O r) j.val i ω) :=
    Finset.measurable_sum Finset.univ (fun j _ => hr.raw_measurable ho s j i)
  exact (hm.const_smul (1 - momentum p s)).add
    (((hsum.const_smul ((batchSize p s : ℝ)⁻¹)).add
      ((hx.sub measurable_const).const_smul (regularization p s))).const_smul (momentum p s))

include ho in
lemma next_m_memLp (s : ℕ) (i : Fin p.workers) :
    MemLp (nextM O s r i) 2 (executionMeasure p O) := by
  have hsum : MemLp
      (fun ω => ∑ j : Fin (batchSize p s),
        rawSample O (afterProx O r) (nextX O r) j.val i ω) 2 (executionMeasure p O) :=
    memLp_finsetSum Finset.univ (fun j _ => hr.raw_memLp ho s j i)
  have hbatch := hsum.const_smul ((batchSize p s : ℝ)⁻¹)
  have hreg := ((hr.next_x_memLp ho).sub (memLp_const p.x0)).const_smul
    (regularization p s)
  exact ((hr.m_memLp i).const_smul (1 - momentum p s)).add
    ((hbatch.add hreg).const_smul (momentum p s))

include ho in
lemma compression_query_measurable (s : ℕ) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (compressQuery O s r) := by
  have hx : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (nextX O r) :=
    measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
      (hr.next_x_measurable ho)
  have hz : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (fun ω i => nextM O s r i ω - (r ω).v i) := by
    letI : MeasurableSpace (Randomness p O) := pastSpace p O (k + 1 + batchSize p s)
    apply Measurable.of_eval
    intro i
    exact (hr.next_m_measurable ho s i).sub
      (measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
        (hr.v_measurable i))
  exact measurable_const.prodMk (hx.prodMk hz)

include ho in
lemma compression_error_moments (s : ℕ) (i : Fin p.workers) :
    MemLp (fun ω => (compressReply O s r ω).2 i - (nextM O s r i ω - (r ω).v i)) 2
      (executionMeasure p O) ∧
    (∀ᵐ ω ∂(executionMeasure p O),
      condExp (pastSpace p O (k + 1 + batchSize p s)) (executionMeasure p O)
        (fun ω' => ‖(compressReply O s r ω').2 i -
          (nextM O s r i ω' - (r ω').v i)‖ ^ 2) ω ≤
        (1 - p.δ) * ‖nextM O s r i ω - (r ω).v i‖ ^ 2) := by
  have hm : @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (fun ω i => nextM O s r i ω - (r ω).v i) := by
    letI : MeasurableSpace (Randomness p O) := pastSpace p O (k + 1 + batchSize p s)
    apply Measurable.of_eval
    intro i
    exact (hr.next_m_measurable ho s i).sub
      (measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
        (hr.v_measurable i))
  have hq := hr.compression_query_measurable ho s
  have ha := ho.conditionalCompression (k + 1 + batchSize p s) (afterBatch O s r)
    (nextX O r) (fun ω i => nextM O s r i ω - (r ω).v i)
    (hr.after_batch_measurable ho s)
    (measurable_enlarge O (k := k) (l := k + 1 + batchSize p s) (by omega)
      (hr.next_x_measurable ho)) hm
    (hr.after_batch_length s)
    (fun i => norm_square_integrable _ ((hr.next_m_memLp ho s i).sub (hr.v_memLp i))) i
  have hreply := response_predictable O ho _ _ (hr.after_batch_measurable ho s)
    hq (hr.after_batch_length s)
  have hc := (measurable_pi_apply i).comp (measurable_global O hreply).snd
  have hz := measurable_global O ((measurable_pi_apply i).comp hm)
  refine ⟨?_, ha.2⟩
  exact memLp_of_integrable_square _ (hc.sub hz).aestronglyMeasurable ha.1

include ho in
lemma step_regular (s : ℕ) :
    Regular O hp hg (k + (batchSize p s + 2)) (step O s r) := by
  have hreply := response_predictable O ho _ _ (hr.after_batch_measurable ho s)
    (hr.compression_query_measurable ho s) (hr.after_batch_length s)
  have hhist := appendReply_predictable O ho _ _ (hr.after_batch_measurable ho s)
    (hr.compression_query_measurable ho s) (hr.after_batch_length s)
  have hclock : k + 1 + batchSize p s + 1 = k + (batchSize p s + 2) := by omega
  rw [hclock] at hreply hhist
  refine ⟨step_history_length O s r hr.history_length, ?_, ?_, ?_, ?_,
    hr.next_x_memLp ho, hr.next_m_memLp ho s, ?_, ?_, ?_⟩
  · exact hhist
  · exact measurable_enlarge O (k := k) (l := k + (batchSize p s + 2))
      (by omega) (hr.next_x_measurable ho)
  · intro i
    exact measurable_enlarge O (k := k + 1 + batchSize p s)
      (l := k + (batchSize p s + 2)) (by omega) (hr.next_m_measurable ho s i)
  · intro i
    exact (measurable_enlarge O (k := k) (l := k + (batchSize p s + 2))
      (by omega) (hr.v_measurable i)).add
      ((measurable_pi_apply i).comp hreply.snd)
  · intro i
    have he := (hr.compression_error_moments ho s i).1
    have hid : (fun ω => (step O s r ω).v i) =
        (fun ω => nextM O s r i ω + ((compressReply O s r ω).2 i -
          (nextM O s r i ω - (r ω).v i))) := by
      funext ω
      simp only [step]
      abel
    rw [hid]
    exact (hr.next_m_memLp ho s i).add he
  · intro ω
    change I.ψ (nextX O r ω) ≠ ⊤
    rw [nextX_eq O ho]
    exact hg.proximalFinite _ (step_positive hp) _
  · have hv := workerMean_memLp (executionMeasure p O) (fun i ω => (r ω).v i) hr.v_memLp
    have hi := regularizer_at_prox_integrable (executionMeasure p O) hp hg (step_positive hp)
      (hr.x_memLp.sub (hv.const_smul (executionStep p)))
    apply hi.congr
    filter_upwards [] with ω
    change psiValue I (I.prox (executionStep p)
        ((r ω).x - executionStep p • workerMean (r ω).v)) =
      psiValue I (nextX O r ω)
    rw [nextX_eq O ho]

include ho in
lemma batch_moments (s : ℕ) (i : Fin p.workers) :
    MemLp (batchError O (I := I) (afterProx O r) (nextX O r) (batchSize p s) i)
      2 (executionMeasure p O) ∧
    (condExp (pastSpace p O (k + 1)) (executionMeasure p O)
      (batchError O (I := I) (afterProx O r) (nextX O r) (batchSize p s) i)
      =ᵐ[executionMeasure p O] (fun _ => 0)) ∧
    (∀ᵐ ω ∂(executionMeasure p O), condExp (pastSpace p O (k + 1))
      (executionMeasure p O)
      (fun ω' => ‖batchError O (I := I) (afterProx O r) (nextX O r)
        (batchSize p s) i ω'‖ ^ 2) ω ≤ p.σ ^ 2 / (batchSize p s : ℝ)) := by
  exact batch_error_moments O hp hg ho (batch_positive s) _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length (hr.next_x_memLp ho) i

end Regular

lemma iterate_regular (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) {k : ℕ} {r : NodePath O}
    (hr : Regular O hp hg k r) (s t : ℕ) :
    Regular O hp hg (k + t * (batchSize p s + 2)) (iterate O s r t) := by
  induction t with
  | zero => simpa only [iterate, Nat.zero_mul, Nat.add_zero] using hr
  | succ t ih =>
      have hs := ih.step_regular ho s
      simpa only [iterate, Nat.succ_mul, Nat.add_assoc] using hs

lemma stage_offset_succ (s : ℕ) :
    stageOffset p (s + 1) = stageOffset p s + stageLength p s * (batchSize p s + 2) := by
  simp only [stageOffset, Finset.sum_range_succ]

lemma stage_start_regular (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) (s : ℕ) :
    Regular O hp hg (stageOffset p s) (stageStart O s) := by
  induction s with
  | zero => simpa [stageStart, stageOffset] using initial_regular O hp hg
  | succ s ih =>
      rw [stageStart, stage_offset_succ]
      exact iterate_regular O hp hg ho ih s (stageLength p s)

lemma stage_regular (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) (s t : ℕ) :
    Regular O hp hg (clock p s t) (stageRun O s t) :=
  iterate_regular O hp hg ho (stage_start_regular O hp hg ho s) s t

lemma batch_mean_identity (s : ℕ) (r : NodePath O) (i : Fin p.workers)
    (ω : Randomness p O) :
    (batchSize p s : ℝ)⁻¹ • ∑ j : Fin (batchSize p s),
        rawSample O (afterProx O r) (nextX O r) j.val i ω =
      gradient (I.f i) (nextX O r ω) +
        batchError O (I := I) (afterProx O r) (nextX O r) (batchSize p s) i ω := by
  change workerMean (fun j : Fin (batchSize p s) =>
      rawSample O (afterProx O r) (nextX O r) j.val i ω) =
    gradient (I.f i) (nextX O r ω) +
      workerMean (fun j : Fin (batchSize p s) =>
        rawSample O (afterProx O r) (nextX O r) j.val i ω -
          gradient (I.f i) (nextX O r ω))
  rw [workerMean_sub, workerMean_const (batch_positive s)]
  abel

noncomputable def innerTrajectory (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) (s : ℕ) :
    Trajectory (executionMeasure p O) (stageGeometry (geometry hp hg) s)
      (1 / (12288 * p.L)) (gamma p.L p.δ) p.δ
      (p.σ ^ 2 / (batches p.L p.R p.σ p.δ s : ℝ))
      ((mu p.L s) • (I.xstar - p.x0)) where
  x t ω := (stageRun O s t ω).x
  m t i ω := (stageRun O s t ω).m i
  v t i ω := (stageRun O s t ω).v i
  noise t i := batchError O (I := I) (afterProx O (stageRun O s t))
    (nextX O (stageRun O s t)) (batchSize p s) i
  correction t i ω := (compressReply O s (stageRun O s t) ω).2 i
  beforeSample t := pastSpace p O (clock p s t + 1)
  beforeCompress t := pastSpace p O (clock p s t + 1 + batchSize p s)
  beforeSample_le t := past_le O _
  beforeCompress_le t := past_le O _
  sample_before_compress t := past_mono O (Nat.le_add_right _ _)
  feasible t := Filter.Eventually.of_forall (stage_regular O hp hg ho s t).feasible
  proximal_update t := by
    filter_upwards [] with ω
    exact nextX_eq O ho (stageRun O s t) ω
  momentum_update t i := by
    filter_upwards [] with ω
    change nextM O s (stageRun O s t) i ω = _
    unfold nextM
    rw [batch_mean_identity O (I := I)]
    change
      (1 - momentum p s) • (stageRun O s t ω).m i +
        momentum p s •
          (gradient (I.f i) (nextX O (stageRun O s t) ω) +
            batchError O (I := I) (afterProx O (stageRun O s t))
              (nextX O (stageRun O s t)) (batchSize p s) i ω +
            regularization p s • (nextX O (stageRun O s t) ω - p.x0)) =
      (1 - momentum p s) • (stageRun O s t ω).m i +
        momentum p s •
          ((gradient (I.f i) (nextX O (stageRun O s t) ω) +
              regularization p s • (nextX O (stageRun O s t) ω - I.xstar)) +
            regularization p s • (I.xstar - p.x0) +
            batchError O (I := I) (afterProx O (stageRun O s t))
              (nextX O (stageRun O s t)) (batchSize p s) i ω)
    apply congrArg (fun u : Point p =>
      (1 - momentum p s) • (stageRun O s t ω).m i + momentum p s • u)
    simp only [smul_sub]
    abel
  compression_update t i := by filter_upwards [] with ω; rfl
  centered_noise t i := ((stage_regular O hp hg ho s t).batch_moments ho s i).2.1
  variance_bound t i := ((stage_regular O hp hg ho s t).batch_moments ho s i).2.2
  contractive_compression t i := (stage_regular O hp hg ho s t).compression_error_moments ho s i |>.2
  x_lp t := (stage_regular O hp hg ho s t).x_memLp
  m_lp t i := (stage_regular O hp hg ho s t).m_memLp i
  v_lp t i := (stage_regular O hp hg ho s t).v_memLp i
  noise_lp t i := ((stage_regular O hp hg ho s t).batch_moments ho s i).1
  gradient_lp t i := regularized_gradient_memLp (executionMeasure p O) hp hg
    (mu_positive hp.2.1 s) (mu_le_initial hp.2.1 s) i
    (stage_regular O hp hg ho s (t + 1)).x_memLp
  auxiliary_lp t := auxiliary_memLp (executionMeasure p O) hp hg
    (τ := 1 / (12288 * p.L)) (by have hL := hp.2.1; positivity)
    (stage_regular O hp hg ho s t).x_memLp (stage_regular O hp hg ho s t).m_memLp
  gap_integrable t := regularized_gap_integrable (executionMeasure p O) hp hg
    (mu_positive hp.2.1 s) (mu_le_initial hp.2.1 s)
    (stage_regular O hp hg ho s t).x_memLp
    (stage_regular O hp hg ho s t).regularizer_integrable
  regularizer_integrable t := (stage_regular O hp hg ho s t).regularizer_integrable
  auxiliary_regularizer_integrable t := by
    have hr := stage_regular O hp hg ho s t
    have hτ : 0 < (1 : ℝ) / (12288 * p.L) := by
      have hL : 0 < p.L := hp.2.1
      positivity
    have hm : MemLp (fun ω => workerMean (stageRun O s t ω).m) 2
        (executionMeasure p O) :=
      workerMean_memLp (executionMeasure p O)
        (fun i ω => (stageRun O s t ω).m i) hr.m_memLp
    exact regularizer_at_prox_integrable (executionMeasure p O) hp hg
      (τ := 1 / (12288 * p.L)) hτ
      (hr.x_memLp.sub (hm.const_smul (1 / (12288 * p.L))))
  x_predictable t := (measurable_enlarge O (Nat.le_succ _) (stage_regular O hp hg ho s t).x_measurable).aestronglyMeasurable
  next_x_predictable t := (measurable_enlarge O (Nat.le_succ _)
    ((stage_regular O hp hg ho s t).next_x_measurable ho)).aestronglyMeasurable
  m_predictable t i := (measurable_enlarge O (Nat.le_succ _)
    ((stage_regular O hp hg ho s t).m_measurable i)).aestronglyMeasurable
  v_predictable t i := (measurable_enlarge O (Nat.le_succ _)
    ((stage_regular O hp hg ho s t).v_measurable i)).aestronglyMeasurable
  gradient_predictable t i := by
    have hx := measurable_enlarge O (Nat.le_succ _)
      ((stage_regular O hp hg ho s t).next_x_measurable ho)
    exact (((gradient_continuous hg i).measurable.comp hx).add
      ((hx.sub measurable_const).const_smul (mu p.L s))).aestronglyMeasurable
  auxiliary_predictable t := by
    have hr := stage_regular O hp hg ho s t
    have hτ : 0 < (1 : ℝ) / (12288 * p.L) := by
      have hL : 0 < p.L := hp.2.1
      positivity
    have hm : @Measurable _ _ (pastSpace p O (clock p s t + 1)) inferInstance
        (fun ω => workerMean (stageRun O s t ω).m) :=
      measurable_enlarge O (Nat.le_succ (clock p s t)) hr.m_mean_measurable
    have hx : @Measurable _ _ (pastSpace p O (clock p s t + 1)) inferInstance
        (fun ω => (stageRun O s t ω).x) :=
      measurable_enlarge O (Nat.le_succ (clock p s t)) hr.x_measurable
    exact ((hg.proximalMeasurable (1 / (12288 * p.L)) hτ).comp
      (hx.sub (hm.const_smul (1 / (12288 * p.L))))).aestronglyMeasurable

noncomputable def homotopyTrajectory (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) :
    HomotopyTrajectory (executionMeasure p O) (geometry hp hg) p.x0 p.R p.σ p.δ p.H where
  run := innerTrajectory O hp hg ho
  initial_point := Filter.Eventually.of_forall (fun _ => rfl)
  transfer_x s := Filter.Eventually.of_forall (fun _ => rfl)
  transfer_m s i := Filter.Eventually.of_forall (fun _ => rfl)
  transfer_v s i := Filter.Eventually.of_forall (fun _ => rfl)

lemma initial_error_integrals (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) :
    (p.workers : ℝ)⁻¹ * ∑ i,
        ∫ ω, ‖((homotopyTrajectory O hp hg ho).run 0).v 0 i ω -
          ((homotopyTrajectory O hp hg ho).run 0).m 0 i ω‖ ^ 2 ∂(executionMeasure p O) =
      initialCompressionError p ∧
    (p.workers : ℝ)⁻¹ * ∑ i,
        ∫ ω, ‖((homotopyTrajectory O hp hg ho).run 0).m 0 i ω -
          gradient (I.f i) p.x0‖ ^ 2 ∂(executionMeasure p O) = initialMomentumError I := by
  constructor
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change (∫ ω : Randomness p O, ‖ω.1.2 i - ω.1.1 i‖ ^ 2
      ∂((p.initialLaw : Measure _).prod (O.law : Measure _))) = _
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := (p.initialLaw : Measure (InitialMemories p)))
        (ν := (O.law : Measure (Tape O)))
        (fun z : InitialMemories p => ‖z.2 i - z.1 i‖ ^ 2))
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change (∫ ω : Randomness p O, ‖ω.1.1 i - gradient (I.f i) p.x0‖ ^ 2
      ∂((p.initialLaw : Measure _).prod (O.law : Measure _))) = _
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := (p.initialLaw : Measure (InitialMemories p)))
        (ν := (O.law : Measure (Tape O)))
        (fun z : InitialMemories p => ‖z.1 i - gradient (I.f i) p.x0‖ ^ 2))

end LongTails.Proofs.ProximalEf21ConstructedTrajectory

end

end ConstructedTrajectory_construction


section StateMachine_simulation

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21StateMachine

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21OracleTrace
open LongTails.Proofs.ProximalEf21ConstructedTrajectory
open LongTails.Proofs.ProximalEf21WeightedErrors

variable {p : Params}
variable (O : Oracle (Query p) (Reply p) 4)

abbrev Machine (p : Params) := State p × History p

lemma state_eq_of_fields {a b : State p}
    (hstage : a.stage = b.stage) (hiteration : a.iteration = b.iteration)
    (hphase : a.phase = b.phase) (hdraws : a.batchDraws = b.batchDraws)
    (hx : a.x = b.x) (hm : a.m = b.m) (hv : a.v = b.v)
    (hacc : a.accumulator = b.accumulator) (hsamples : a.samples = b.samples)
    (hrounds : a.rounds = b.rounds) (hprox : a.proxCalls = b.proxCalls) : a = b := by
  cases a
  cases b
  simp_all

noncomputable def microStep (ξ : Tape O) (a : Machine p) : Machine p :=
  let q := methodQuery p a.1
  let reply := response O a.2 q ξ
  (methodUpdate p a.1 reply, appendReply a.2 q reply)

noncomputable def advance (ξ : Tape O) (a : Machine p) : ℕ → Machine p
  | 0 => a
  | k + 1 => microStep O ξ (advance ξ a k)

lemma advance_add (ξ : Tape O) (a : Machine p) (k l : ℕ) :
    advance O ξ a (k + l) = advance O ξ (advance O ξ a k) l := by
  induction l with
  | zero => simp only [Nat.add_zero, advance]
  | succ l ih =>
      change microStep O ξ (advance O ξ a (k + l)) =
        microStep O ξ (advance O ξ (advance O ξ a k) l)
      exact congrArg (microStep O ξ) ih

noncomputable def sampleOffset (p : Params) (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, batchSize p j * stageLength p j

noncomputable def roundOffset (p : Params) (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, stageLength p j

noncomputable def stateAt (s t : ℕ) (ω : Randomness p O) : State p where
  stage := s
  iteration := t
  phase := 0
  batchDraws := 0
  x := (stageRun O s t ω).x
  m := (stageRun O s t ω).m
  v := (stageRun O s t ω).v
  accumulator := 0
  samples := sampleOffset p s + t * batchSize p s
  rounds := roundOffset p s + t
  proxCalls := roundOffset p s + t

noncomputable def machineAt (s t : ℕ) (ω : Randomness p O) : Machine p :=
  (stateAt O s t ω, (stageRun O s t ω).history)

noncomputable def batchSum (s t j : ℕ) (i : Fin p.workers) (ω : Randomness p O) : Point p :=
  ∑ a ∈ Finset.range j, rawSample O (afterProx O (stageRun O s t))
    (nextX O (stageRun O s t)) a i ω

noncomputable def batchState (s t j : ℕ) (ω : Randomness p O) : State p :=
  if j < batchSize p s then
    { stateAt O s t ω with
      x := nextX O (stageRun O s t) ω
      phase := 1
      batchDraws := j
      accumulator := fun i => batchSum O s t j i ω
      samples := sampleOffset p s + t * batchSize p s + j
      proxCalls := roundOffset p s + t + 1 }
  else
    { stateAt O s t ω with
      x := nextX O (stageRun O s t) ω
      m := fun i => nextM O s (stageRun O s t) i ω
      phase := 2
      batchDraws := 0
      accumulator := 0
      samples := sampleOffset p s + t * batchSize p s + batchSize p s
      proxCalls := roundOffset p s + t + 1 }

noncomputable def batchMachine (s t j : ℕ) (ω : Randomness p O) : Machine p :=
  (batchState O s t j ω,
    batchHistory O (afterProx O (stageRun O s t)) (nextX O (stageRun O s t)) j ω)

lemma batch_sum_zero (s t : ℕ) (ω : Randomness p O) :
    (fun i => batchSum O s t 0 i ω) = 0 := by
  funext i
  simp [batchSum]

lemma batch_sum_succ (s t j : ℕ) (i : Fin p.workers) (ω : Randomness p O) :
    batchSum O s t (j + 1) i ω = batchSum O s t j i ω +
      rawSample O (afterProx O (stageRun O s t)) (nextX O (stageRun O s t)) j i ω := by
  simp only [batchSum, Finset.sum_range_succ]

lemma batch_sum_fin (s t : ℕ) (i : Fin p.workers) (ω : Randomness p O) :
    batchSum O s t (batchSize p s) i ω =
      ∑ j : Fin (batchSize p s), rawSample O (afterProx O (stageRun O s t))
        (nextX O (stageRun O s t)) j.val i ω := by
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma initial_machine (ω : Randomness p O) :
    machineAt O 0 0 ω = (initialState p ω.1, []) := by
  simp only [machineAt, stateAt, stageRun, iterate, stageStart, initialNode,
    initialState, sampleOffset, roundOffset, Finset.sum_range_zero,
    Nat.zero_mul, Nat.add_zero]

lemma proximal_microstep (s t : ℕ) (hs : s ≤ finalStage p) (ω : Randomness p O) :
    microStep O ω.2 (machineAt O s t ω) = batchMachine O s t 0 ω := by
  have hstop : ¬s > finalStage p := not_lt.mpr hs
  have hB : 0 < batchSize p s := batch_positive s
  simp only [microStep, machineAt, stateAt, methodQuery, methodUpdate,
    hstop, if_false, if_pos rfl, batchMachine, batchState, hB, if_true,
    batch_sum_zero, Nat.add_zero, proxQuery, proxReply, nextX, afterProx]
  rfl

lemma sample_microstep (s t j : ℕ) (hs : s ≤ finalStage p)
    (hj : j < batchSize p s) (ω : Randomness p O) :
    microStep O ω.2 (batchMachine O s t j ω) = batchMachine O s t (j + 1) ω := by
  have hstop : ¬s > finalStage p := not_lt.mpr hs
  have hsum (i : Fin p.workers) := batch_sum_succ O s t j i ω
  by_cases hjnext : j + 1 < batchSize p s
  · simp only [microStep, batchMachine, batchState, hj, hjnext, if_pos,
      methodQuery, methodUpdate, stateAt, hstop, if_false, if_true,
      show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) = 1 by rfl,
      batchHistory, rawSample, Nat.add_assoc]
    congr 2
    funext i
    exact (hsum i).symm
  · have heq : j + 1 = batchSize p s := by omega
    have hfin (i : Fin p.workers) :
        batchSum O s t j i ω +
          rawSample O (afterProx O (stageRun O s t)) (nextX O (stageRun O s t)) j i ω =
        ∑ a : Fin (batchSize p s), rawSample O (afterProx O (stageRun O s t))
          (nextX O (stageRun O s t)) a.val i ω := by
      rw [← hsum i, heq]
      exact batch_sum_fin O s t i ω
    have hm :
        (fun i : Fin p.workers =>
          (1 - momentum p s) • (stageRun O s t ω).m i + momentum p s •
            ((batchSize p s : ℝ)⁻¹ •
              (batchSum O s t j i ω +
                rawSample O (afterProx O (stageRun O s t))
                  (nextX O (stageRun O s t)) j i ω) +
              regularization p s • (nextX O (stageRun O s t) ω - p.x0))) =
          (fun i => nextM O s (stageRun O s t) i ω) := by
      funext i
      unfold nextM
      rw [hfin i]
    have hsamples :
        sampleOffset p s + t * batchSize p s + j + 1 =
          sampleOffset p s + t * batchSize p s + batchSize p s := by
      omega
    simp only [microStep, batchMachine, batchState, hj, hjnext, if_pos, if_neg,
      methodQuery, methodUpdate, stateAt, hstop, if_false, if_true,
      show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) = 1 by rfl,
      batchHistory, rawSample]
    apply Prod.ext
    · exact state_eq_of_fields rfl rfl rfl rfl rfl hm rfl rfl hsamples rfl rfl
    · rfl

lemma batch_execution (s t : ℕ) (hs : s ≤ finalStage p)
    (ω : Randomness p O) (j : ℕ) (hj : j ≤ batchSize p s) :
    advance O ω.2 (machineAt O s t ω) (1 + j) = batchMachine O s t j ω := by
  induction j with
  | zero => simpa only [Nat.add_zero, advance] using proximal_microstep O s t hs ω
  | succ j ih =>
      have hj0 : j ≤ batchSize p s := by omega
      have hjlt : j < batchSize p s := by omega
      rw [Nat.add_succ, advance, ih hj0]
      exact sample_microstep O s t j hs hjlt ω

lemma compression_microstep (s t : ℕ) (hs : s ≤ finalStage p)
    (ht : t < stageLength p s) (ω : Randomness p O) :
    microStep O ω.2 (batchMachine O s t (batchSize p s) ω) =
      if t + 1 < stageLength p s then machineAt O s (t + 1) ω
      else machineAt O (s + 1) 0 ω := by
  have hstop : ¬s > finalStage p := not_lt.mpr hs
  have hB : ¬batchSize p s < batchSize p s := lt_irrefl _
  by_cases hnext : t + 1 < stageLength p s
  · simp only [microStep, batchMachine, batchState, hB, if_neg,
      methodQuery, methodUpdate, stateAt, hstop, if_false,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      hnext, if_true, machineAt, stageRun, iterate, step, nextX,
      compressReply, compressQuery, afterBatch, Nat.add_assoc, Nat.succ_mul]
  · have hlast : t + 1 = stageLength p s := by omega
    have hnode : stageRun O (s + 1) 0 = step O s (stageRun O s t) := by
      simp only [stageRun, iterate, stageStart, ← hlast]
    have hn : sampleOffset p (s + 1) = sampleOffset p s + batchSize p s * stageLength p s := by
      simp only [sampleOffset, Finset.sum_range_succ]
    have hr : roundOffset p (s + 1) = roundOffset p s + stageLength p s := by
      simp only [roundOffset, Finset.sum_range_succ]
    have hsamples :
        sampleOffset p s + t * batchSize p s + batchSize p s =
          sampleOffset p (s + 1) := by
      rw [hn, ← hlast]
      ring
    have hrounds : roundOffset p s + t + 1 = roundOffset p (s + 1) := by
      rw [hr]
      omega
    simp only [microStep, batchMachine, batchState, hB, if_neg,
      methodQuery, methodUpdate, stateAt, hstop, if_false,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      hnext, machineAt, hnode, step, compressReply, compressQuery,
      afterBatch, Nat.zero_mul, Nat.add_zero]
    apply Prod.ext
    · exact state_eq_of_fields rfl rfl rfl rfl rfl rfl rfl rfl
        hsamples hrounds hrounds
    · rfl

lemma iteration_execution (s t : ℕ) (hs : s ≤ finalStage p)
    (ht : t < stageLength p s) (ω : Randomness p O) :
    advance O ω.2 (machineAt O s t ω) (batchSize p s + 2) =
      if t + 1 < stageLength p s then machineAt O s (t + 1) ω
      else machineAt O (s + 1) 0 ω := by
  rw [show batchSize p s + 2 = (1 + batchSize p s) + 1 by omega,
    advance, batch_execution O s t hs ω (batchSize p s) le_rfl]
  exact compression_microstep O s t hs ht ω

lemma stage_execution_prefix (hp : spec.valid p) (s : ℕ) (hs : s ≤ finalStage p)
    (ω : Randomness p O) (t : ℕ) (ht : t ≤ stageLength p s) :
    advance O ω.2 (machineAt O s 0 ω) (t * (batchSize p s + 2)) =
      if t < stageLength p s then machineAt O s t ω else machineAt O (s + 1) 0 ω := by
  induction t with
  | zero => simp [advance, stage_length_positive hp s]
  | succ t ih =>
      have hlt : t < stageLength p s := by omega
      have hle : t ≤ stageLength p s := by omega
      rw [Nat.succ_mul, advance_add, ih hle, if_pos hlt]
      exact iteration_execution O s t hs hlt ω

lemma stage_execution (hp : spec.valid p) (s : ℕ) (hs : s ≤ finalStage p)
    (ω : Randomness p O) :
    advance O ω.2 (machineAt O s 0 ω)
      (stageLength p s * (batchSize p s + 2)) = machineAt O (s + 1) 0 ω := by
  simpa only [lt_irrefl, if_false] using
    stage_execution_prefix O hp s hs ω (stageLength p s) le_rfl

lemma whole_execution_prefix (hp : spec.valid p) (ω : Randomness p O)
    (s : ℕ) (hs : s ≤ finalStage p + 1) :
    advance O ω.2 (initialState p ω.1, []) (stageOffset p s) = machineAt O s 0 ω := by
  induction s with
  | zero => simp only [stageOffset, Finset.sum_range_zero, advance, initial_machine]
  | succ s ih =>
      have hs0 : s ≤ finalStage p := by omega
      rw [stage_offset_succ, advance_add, ih (by omega)]
      exact stage_execution O hp s hs0 ω

noncomputable def traceOutput (ω : Randomness p O) : Output p :=
  methodOutput (advance O ω.2 (initialState p ω.1, []) (stageOffset p (finalStage p + 1))).1

lemma trace_output_eq (hp : spec.valid p) (ω : Randomness p O) :
    traceOutput O ω =
      ((stageRun O (finalStage p) (stageLength p (finalStage p)) ω).x,
        (samplesPerWorker p, (iterationCount p, iterationCount p))) := by
  unfold traceOutput
  rw [whole_execution_prefix O hp ω (finalStage p + 1) le_rfl]
  simp only [machineAt, stateAt, methodOutput, Nat.zero_mul, Nat.add_zero,
    sampleOffset, roundOffset, samplesPerWorker, iterationCount, stageRun, iterate, stageStart]

lemma terminal_channel (ω : Randomness p O) :
    (methodQuery p (stateAt O (finalStage p + 1) 0 ω)).1 = 3 := by
  simp [methodQuery, stateAt]

lemma call_count_identity :
    stageOffset p (finalStage p + 1) = samplesPerWorker p + 2 * iterationCount p := by
  unfold stageOffset samplesPerWorker iterationCount
  calc
    (∑ s ∈ Finset.range (finalStage p + 1),
        stageLength p s * (batchSize p s + 2)) =
        ∑ s ∈ Finset.range (finalStage p + 1),
          (batchSize p s * stageLength p s + 2 * stageLength p s) := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = (∑ s ∈ Finset.range (finalStage p + 1),
          batchSize p s * stageLength p s) +
        2 * (∑ s ∈ Finset.range (finalStage p + 1), stageLength p s) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end LongTails.Proofs.ProximalEf21StateMachine

end

end StateMachine_simulation


section ProtocolBudget_accounting

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21ProtocolBudget

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21ConstructedTrajectory
open LongTails.Proofs.ProximalEf21StateMachine
open LongTails.Proofs.ProximalEf21BudgetBridge

variable {p : Params}
variable (O : Oracle (Query p) (Reply p) 4)

noncomputable def callsUsed (s : State p) (i : Fin 4) : ℕ :=
  if i = 0 then s.samples else if i = 1 then s.rounds else if i = 2 then s.proxCalls else 0

lemma sample_prefix_le {s : ℕ} (hs : s ≤ finalStage p) :
    sampleOffset p s + batchSize p s * stageLength p s ≤ samplesPerWorker p := by
  have hsum : (∑ j ∈ Finset.range (s + 1), batchSize p j * stageLength p j) ≤
      ∑ j ∈ Finset.range (finalStage p + 1), batchSize p j * stageLength p j := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ hs)
  simpa only [Finset.sum_range_succ, sampleOffset, samplesPerWorker] using hsum

lemma round_prefix_le {s : ℕ} (hs : s ≤ finalStage p) :
    roundOffset p s + stageLength p s ≤ iterationCount p := by
  have hsum : (∑ j ∈ Finset.range (s + 1), stageLength p j) ≤
      ∑ j ∈ Finset.range (finalStage p + 1), stageLength p j := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ hs)
  simpa only [Finset.sum_range_succ, roundOffset, iterationCount] using hsum

lemma proximal_call_available (hp : spec.valid p) (s t : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s) (ω : Randomness p O) :
    callsUsed (stateAt O s t ω) (methodQuery p (stateAt O s t ω)).1 <
      budget p (methodQuery p (stateAt O s t ω)).1 := by
  have hq : (methodQuery p (stateAt O s t ω)).1 = 2 := by
    simp [methodQuery, stateAt, not_lt.mpr hs]
  rw [hq]
  have hcost := round_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).2.2.1
  change roundOffset p s + t < budget p 2
  omega

lemma sample_call_available (hp : spec.valid p) (s t j : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s)
    (hj : j < batchSize p s) (ω : Randomness p O) :
    callsUsed (batchState O s t j ω) (methodQuery p (batchState O s t j ω)).1 <
      budget p (methodQuery p (batchState O s t j ω)).1 := by
  have hq : (methodQuery p (batchState O s t j ω)).1 = 0 := by
    simp [methodQuery, batchState, stateAt, hj, not_lt.mpr hs]
  rw [hq]
  have hcost := sample_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).1
  have hprod : (t + 1) * batchSize p s ≤ stageLength p s * batchSize p s :=
    Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr ht)
  simp only [Nat.add_mul, one_mul] at hprod
  simp only [callsUsed, batchState, hj, if_true, stateAt]
  have hcomm : batchSize p s * stageLength p s = stageLength p s * batchSize p s :=
    Nat.mul_comm _ _
  omega

lemma compression_call_available (hp : spec.valid p) (s t : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s) (ω : Randomness p O) :
    callsUsed (batchState O s t (batchSize p s) ω)
        (methodQuery p (batchState O s t (batchSize p s) ω)).1 <
      budget p (methodQuery p (batchState O s t (batchSize p s) ω)).1 := by
  have hq : (methodQuery p (batchState O s t (batchSize p s) ω)).1 = 1 := by
    simp [methodQuery, batchState, stateAt, not_lt.mpr hs]
  rw [hq]
  have hcost := round_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).2.1
  simp only [callsUsed, batchState, lt_irrefl, if_false, stateAt]
  norm_num only [show (1 : Fin 4) ≠ 0 by decide, if_false, if_true]
  omega

lemma terminal_call_unavailable (ω : Randomness p O) :
    budget p (methodQuery p (stateAt O (finalStage p + 1) 0 ω)).1 = 0 := by
  rw [terminal_channel]
  simp [budget]

end LongTails.Proofs.ProximalEf21ProtocolBudget

end

end ProtocolBudget_accounting


section Execution_evaluation

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21Execution

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21OracleTrace
open LongTails.Proofs.ProximalEf21ConstructedTrajectory
open LongTails.Proofs.ProximalEf21StateMachine
open LongTails.Proofs.ProximalEf21BudgetBridge
open LongTails.Proofs.ProximalEf21ProtocolBudget

universe uQ uR uO

def runWithBudget
    {Q : Type uQ} {R : Type uR} {Out : Type uO} {n : ℕ}
    (answer : List ((Fin n × Q) × R) → (Fin n × Q) → R)
    (A : Algorithm Q R Out n) :
    ℕ → List ((Fin n × Q) × R) → (Fin n → ℕ) → A.State →
      Out × List ((Fin n × Q) × R)
  | 0, history, _, state => (A.output state, history)
  | k + 1, history, remaining, state =>
      let query := A.query state
      if remaining query.1 = 0 then (A.output state, history)
      else
        let reply := answer history query
        let remaining := Function.update remaining query.1 (remaining query.1 - 1)
        runWithBudget answer A k (history ++ [(query, reply)]) remaining (A.update state reply)

lemma executeWithTrace_eq_runWithBudget
    {Q : Type uQ} {R : Type uR} {Out : Type uO} {n : ℕ}
    (O : Oracle Q R n) (A : Algorithm Q R Out n)
    (b : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) :
    executeWithTrace O A b seed ξ =
      runWithBudget (fun h q => O.answer h q (ξ h.length))
        A (∑ i, b i) [] b (A.initial seed) := by
  unfold executeWithTrace
  generalize (∑ i, b i) = fuel
  generalize ([] : List ((Fin n × Q) × R)) = history
  generalize b = remaining
  generalize A.initial seed = state
  induction fuel generalizing history remaining state with
  | zero => rfl
  | succ fuel ih =>
      change
        (if remaining (A.query state).1 = 0 then (A.output state, history)
          else _) =
        (if remaining (A.query state).1 = 0 then (A.output state, history)
          else _)
      by_cases hstop : remaining (A.query state).1 = 0
      · simp only [hstop, ite_true]
      · simpa only [hstop, ite_false] using
          ih (history ++ [(A.query state,
                O.answer history (A.query state) (ξ history.length))])
            (Function.update remaining (A.query state).1
              (remaining (A.query state).1 - 1))
            (A.update state (O.answer history (A.query state) (ξ history.length)))

variable {p : Params}
variable (O : Oracle (Query p) (Reply p) 4)

noncomputable def replay (ω : Randomness p O) (k : ℕ) : Machine p :=
  advance O ω.2 (initialState p ω.1, []) k

lemma replay_zero (ω : Randomness p O) :
    replay O ω 0 = (initialState p ω.1, []) := rfl

lemma replay_succ (ω : Randomness p O) (k : ℕ) :
    replay O ω (k + 1) = microStep O ω.2 (replay O ω k) := rfl

lemma initial_calls_used (seed : InitialMemories p) :
    callsUsed (initialState p seed) = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [callsUsed, initialState]

lemma calls_used_update (s : State p) (a : Reply p)
    (hs : s.stage ≤ finalStage p) :
    callsUsed (methodUpdate p s a) =
      Function.update (callsUsed s) (methodQuery p s).1
        (callsUsed s (methodQuery p s).1 + 1) := by
  classical
  have hstop : ¬s.stage > finalStage p := not_lt.mpr hs
  by_cases hphase0 : s.phase = 0
  · funext i
    fin_cases i <;>
      simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0]
  · by_cases hphase1 : s.phase = 1
    · by_cases hbatch : s.batchDraws + 1 < batchSize p s.stage
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hbatch]
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hbatch]
    · by_cases hiteration : s.iteration + 1 < stageLength p s.stage
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hiteration]
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hiteration]

lemma remaining_update (s : State p) (a : Reply p) (b : Fin 4 → ℕ)
    (hs : s.stage ≤ finalStage p) :
    Function.update (fun i => b i - callsUsed s i) (methodQuery p s).1
        ((b (methodQuery p s).1 - callsUsed s (methodQuery p s).1) - 1) =
      (fun i => b i - callsUsed (methodUpdate p s a) i) := by
  classical
  rw [calls_used_update s a hs]
  funext i
  by_cases hi : i = (methodQuery p s).1
  · subst i
    simp [Nat.sub_sub]
  · simp [Function.update, hi, Ne.symm hi]

lemma iteration_prefix_available (hp : spec.valid p) (s t j : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s)
    (hj : j < batchSize p s + 2) (ω : Randomness p O) :
    let a := advance O ω.2 (machineAt O s t ω) j
    a.1.stage ≤ finalStage p ∧
      callsUsed a.1 (methodQuery p a.1).1 < budget p (methodQuery p a.1).1 := by
  dsimp only
  by_cases hjzero : j = 0
  · subst j
    change s ≤ finalStage p ∧
      callsUsed (stateAt O s t ω) (methodQuery p (stateAt O s t ω)).1 <
        budget p (methodQuery p (stateAt O s t ω)).1
    exact ⟨hs, proximal_call_available O hp s t hs ht ω⟩
  · have hrewrite : j = 1 + (j - 1) := by omega
    have hle : j - 1 ≤ batchSize p s := by omega
    rw [hrewrite, batch_execution O s t hs ω (j - 1) hle]
    by_cases hsample : j - 1 < batchSize p s
    · refine ⟨?_, ?_⟩
      · simpa only [batchMachine, batchState, if_pos hsample, stateAt] using hs
      · exact sample_call_available O hp s t (j - 1) hs ht hsample ω
    · have hlast : j - 1 = batchSize p s := by omega
      rw [hlast]
      refine ⟨?_, compression_call_available O hp s t hs ht ω⟩
      simpa only [batchMachine, batchState, lt_irrefl, if_false, stateAt] using hs

lemma stage_prefix_available (hp : spec.valid p) (s k : ℕ)
    (hs : s ≤ finalStage p)
    (hk : k < stageLength p s * (batchSize p s + 2))
    (ω : Randomness p O) :
    let a := advance O ω.2 (machineAt O s 0 ω) k
    a.1.stage ≤ finalStage p ∧
      callsUsed a.1 (methodQuery p a.1).1 < budget p (methodQuery p a.1).1 := by
  dsimp only
  let t := k / (batchSize p s + 2)
  let j := k % (batchSize p s + 2)
  have hj : j < batchSize p s + 2 := Nat.mod_lt _ (by omega)
  have ht : t < stageLength p s := by
    have hdiv : t * (batchSize p s + 2) ≤ k := Nat.div_mul_le_self _ _
    by_contra hnot
    have hle : stageLength p s ≤ t := by omega
    have hmul := Nat.mul_le_mul_right (batchSize p s + 2) hle
    omega
  have hdecomp : k = t * (batchSize p s + 2) + j := by
    dsimp [t, j]
    have h := Nat.mod_add_div k (batchSize p s + 2)
    simpa only [Nat.mul_comm, Nat.add_comm] using h.symm
  rw [hdecomp, advance_add,
    stage_execution_prefix O hp s hs ω t (Nat.le_of_lt ht), if_pos ht]
  exact iteration_prefix_available O hp s t j hs ht hj ω

lemma whole_prefix_available (hp : spec.valid p) (ω : Randomness p O)
    (s : ℕ) (hs : s ≤ finalStage p + 1) :
    ∀ k < stageOffset p s,
      (replay O ω k).1.stage ≤ finalStage p ∧
        callsUsed (replay O ω k).1 (methodQuery p (replay O ω k).1).1 <
          budget p (methodQuery p (replay O ω k).1).1 := by
  revert hs
  induction s with
  | zero =>
      intro hs k hk
      have : stageOffset p 0 = 0 := by simp [stageOffset]
      omega
  | succ s ih =>
      intro hs k hk
      have hs0 : s ≤ finalStage p := by omega
      by_cases hprevious : k < stageOffset p s
      · exact ih (by omega) k hprevious
      · have hoffset : stageOffset p s ≤ k := by omega
        have hlocal : k - stageOffset p s < stageLength p s * (batchSize p s + 2) := by
          rw [stage_offset_succ] at hk
          omega
        have hdecomp : k = stageOffset p s + (k - stageOffset p s) := by omega
        unfold replay
        rw [hdecomp, advance_add, whole_execution_prefix O hp ω s (by omega)]
        exact stage_prefix_available O hp s (k - stageOffset p s) hs0 hlocal ω

lemma replay_terminal (hp : spec.valid p) (ω : Randomness p O) :
    replay O ω (stageOffset p (finalStage p + 1)) =
      machineAt O (finalStage p + 1) 0 ω := by
  exact whole_execution_prefix O hp ω (finalStage p + 1) le_rfl

lemma replay_terminal_budget (hp : spec.valid p) (ω : Randomness p O) :
    budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 = 0 := by
  rw [replay_terminal O hp ω]
  exact terminal_call_unavailable O ω

lemma total_fuel_sufficient (hp : spec.valid p) :
    stageOffset p (finalStage p + 1) ≤ ∑ i : Fin 4, budget p i := by
  obtain ⟨hsamples, hrounds, hprox, hstop⟩ := oracle_budget_sufficient p hp
  have hsum : (∑ i : Fin 4, budget p i) =
      budget p 0 + budget p 1 + budget p 2 + budget p 3 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [call_count_identity, hsum]
  omega

lemma run_from_prefix (hp : spec.valid p) (ω : Randomness p O)
    (steps : ℕ) :
    ∀ (t fuel : ℕ), t + steps = stageOffset p (finalStage p + 1) → steps ≤ fuel →
      runWithBudget (fun h q => response O h q ω.2) (method p) fuel
        (replay O ω t).2
        (fun i => budget p i - callsUsed (replay O ω t).1 i)
        (replay O ω t).1 =
      (traceOutput O ω, (replay O ω (stageOffset p (finalStage p + 1))).2) := by
  induction steps with
  | zero =>
      intro t fuel hfinish hfuel
      have ht : t = stageOffset p (finalStage p + 1) := by omega
      subst t
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hstop :
              (budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 -
                callsUsed (replay O ω (stageOffset p (finalStage p + 1))).1
                  (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1) = 0 := by
            rw [replay_terminal_budget O hp ω]
            exact Nat.zero_sub _
          change (if (budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 -
                callsUsed (replay O ω (stageOffset p (finalStage p + 1))).1
                  (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1) = 0
              then (methodOutput (replay O ω (stageOffset p (finalStage p + 1))).1,
                (replay O ω (stageOffset p (finalStage p + 1))).2)
              else _) = _
          rw [if_pos hstop]
          rfl
  | succ steps ih =>
      intro t fuel hfinish hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ht : t < stageOffset p (finalStage p + 1) := by omega
          obtain ⟨hstage, havailable⟩ :=
            whole_prefix_available O hp ω (finalStage p + 1) le_rfl t ht
          have hnonzero :
              budget p (methodQuery p (replay O ω t).1).1 -
                callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1 ≠ 0 := by
            omega
          have hremain := remaining_update (replay O ω t).1
            (response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2)
            (budget p) hstage
          change (if budget p (methodQuery p (replay O ω t).1).1 -
                callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1 = 0
              then (methodOutput (replay O ω t).1, (replay O ω t).2)
              else runWithBudget (fun h q => response O h q ω.2) (method p) fuel
                ((replay O ω t).2 ++ [(methodQuery p (replay O ω t).1,
                  response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2)])
                (Function.update (fun i => budget p i - callsUsed (replay O ω t).1 i)
                  (methodQuery p (replay O ω t).1).1
                  ((budget p (methodQuery p (replay O ω t).1).1 -
                    callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1) - 1))
                (methodUpdate p (replay O ω t).1
                  (response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2))) = _
          rw [if_neg hnonzero, hremain]
          change runWithBudget (fun h q => response O h q ω.2) (method p) fuel
            (replay O ω (t + 1)).2
            (fun i => budget p i - callsUsed (replay O ω (t + 1)).1 i)
            (replay O ω (t + 1)).1 = _
          exact ih (t + 1) fuel (by omega) (by omega)

lemma executeWithTrace_eq_replay (hp : spec.valid p) (ω : Randomness p O) :
    executeWithTrace O (method p) (budget p) ω.1 ω.2 =
      (traceOutput O ω, (replay O ω (stageOffset p (finalStage p + 1))).2) := by
  have hrun := run_from_prefix O hp ω (stageOffset p (finalStage p + 1))
    0 (∑ i : Fin 4, budget p i) (by omega) (total_fuel_sufficient (p := p) hp)
  have hremaining :
      (fun i => budget p i - callsUsed (replay O ω 0).1 i) = budget p := by
    rw [replay_zero, initial_calls_used]
    funext i
    simp
  have hstart := congrArg
    (fun remaining : Fin 4 → ℕ =>
      runWithBudget (fun h q => response O h q ω.2) (method p)
        (∑ i : Fin 4, budget p i) [] remaining (initialState p ω.1))
    hremaining.symm
  exact (executeWithTrace_eq_runWithBudget O (method p) (budget p)
    (show (method p).Seed from ω.1) ω.2).trans (hstart.trans hrun)

lemma execute_eq_traceOutput (hp : spec.valid p) (ω : Randomness p O) :
    execute O (method p) (budget p) ω.1 ω.2 = traceOutput O ω := by
  exact congrArg Prod.fst (executeWithTrace_eq_replay O hp ω)

lemma outputWithCounts_eq_traceOutput (hp : spec.valid p) (ω : Randomness p O) :
    LongTails.Algorithms.ProximalEf21Homotopy.outputWithCounts
      p O (budget p) ω.1 ω.2 = traceOutput O ω := by
  exact execute_eq_traceOutput O hp ω

end LongTails.Proofs.ProximalEf21Execution

end

end Execution_evaluation
