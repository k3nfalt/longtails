import LongTails.Proofs.ProximalEf21OracleTrace
import LongTails.Proofs.ProximalEf21HomotopyTrajectory

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

noncomputable section

namespace LongTails.Proofs.ProximalEf21ConstructedTrajectory

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
    have ha : (1 : ℝ) < 2 + 2 * p.H / (8192 * regularization p 0 * p.R ^ 2) := by positivity
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
  · exact memLp_const p.x0
  · exact initial_momentum_memLp hg O
  · exact initial_compressed_memLp hg O
  · intro ω; exact hg.initialFinite
  · exact integrable_const _

namespace Regular

variable {O} {hp : spec.valid p} {hg : ProblemAssumptions p I}
variable {k : ℕ} {r : NodePath O} (hr : Regular O hp hg k r)
variable (ho : OracleAssumptions p I O)

lemma next_x_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance (nextX O r) := by
  have hv := measurable_pi_lambda _ hr.v_measurable
  have havg : @Measurable _ _ (pastSpace p O k) inferInstance
      (fun ω => workerMean (r ω).v) := by
    unfold workerMean
    exact (Finset.measurable_sum _ (fun i _ => hr.v_measurable i)).const_smul _
  have hm := (hg.proximalMeasurable _ (step_positive hp)).comp
    (hr.x_measurable.sub (havg.const_smul (executionStep p)))
  simpa only [nextX_eq O ho r] using hm

lemma next_x_memLp : MemLp (nextX O r) 2 (executionMeasure p O) := by
  have hv := workerMean_memLp (executionMeasure p O) (fun i ω => (r ω).v i) hr.v_memLp
  have hm := prox_memLp (executionMeasure p O) hp hg (step_positive hp)
    (hr.x_memLp.sub (hv.const_smul (executionStep p)))
  simpa only [nextX_eq O ho r] using hm

lemma after_prox_length : ∀ ω, (afterProx O r ω).length = k + 1 := by
  intro ω
  simp [afterProx, appendReply_length, hr.history_length ω]

lemma prox_query_measurable :
    @Measurable _ _ (pastSpace p O k) inferInstance (proxQuery O r) := by
  unfold proxQuery workerMean
  exact measurable_const.prodMk ((hr.x_measurable.sub
    ((Finset.measurable_sum _ (fun i _ => hr.v_measurable i)).const_smul _).const_smul _).prodMk
      measurable_const)

lemma after_prox_measurable :
    @Measurable _ _ (pastSpace p O (k + 1)) inferInstance (afterProx O r) := by
  exact appendReply_predictable O ho _ _ hr.history_measurable hr.prox_query_measurable hr.history_length

lemma after_batch_measurable (s : ℕ) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (afterBatch O s r) := by
  exact batch_history_predictable O ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length (batchSize p s)

lemma after_batch_length (s : ℕ) : ∀ ω, (afterBatch O s r ω).length = k + 1 + batchSize p s :=
  batch_history_length O _ _ hr.after_prox_length (batchSize p s)

lemma raw_measurable (s : ℕ) (j : Fin (batchSize p s)) (i : Fin p.workers) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance
      (rawSample O (afterProx O r) (nextX O r) j.val i) := by
  have hm := raw_sample_predictable O ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length j.val i
  exact measurable_enlarge O (by omega) hm

lemma raw_memLp (s : ℕ) (j : Fin (batchSize p s)) (i : Fin p.workers) :
    MemLp (rawSample O (afterProx O r) (nextX O r) j.val i) 2 (executionMeasure p O) := by
  exact (raw_sample_moments O hp hg ho _ _ (hr.after_prox_measurable ho)
    (measurable_enlarge O (Nat.le_succ k) (hr.next_x_measurable ho))
    hr.after_prox_length (hr.next_x_memLp ho) j.val i).1

lemma next_m_measurable (s : ℕ) (i : Fin p.workers) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (nextM O s r i) := by
  unfold nextM
  exact ((measurable_enlarge O (by omega) (hr.m_measurable i)).const_smul _).add
    (((Finset.measurable_sum _ (fun j _ => hr.raw_measurable ho s j i)).const_smul _).add
      (((measurable_enlarge O (by omega) (hr.next_x_measurable ho)).sub measurable_const).const_smul _)).const_smul _

lemma next_m_memLp (s : ℕ) (i : Fin p.workers) :
    MemLp (nextM O s r i) 2 (executionMeasure p O) := by
  exact ((hr.m_memLp i).const_smul _).add
    ((((MemLp.finset_sum _ (fun j _ => hr.raw_memLp ho s j i)).const_smul _).add
      (((hr.next_x_memLp ho).sub (memLp_const _)).const_smul _)).const_smul _)

lemma compression_query_measurable (s : ℕ) :
    @Measurable _ _ (pastSpace p O (k + 1 + batchSize p s)) inferInstance (compressQuery O s r) := by
  exact measurable_const.prodMk
    ((measurable_enlarge O (by omega) (hr.next_x_measurable ho)).prodMk
      (measurable_pi_lambda _ (fun i => (hr.next_m_measurable ho s i).sub
        (measurable_enlarge O (by omega) (hr.v_measurable i)))))

lemma compression_error_moments (s : ℕ) (i : Fin p.workers) :
    MemLp (fun ω => (compressReply O s r ω).2 i - (nextM O s r i ω - (r ω).v i)) 2
      (executionMeasure p O) ∧
    (∀ᵐ ω ∂(executionMeasure p O),
      condExp (pastSpace p O (k + 1 + batchSize p s)) (executionMeasure p O)
        (fun ω' => ‖(compressReply O s r ω').2 i -
          (nextM O s r i ω' - (r ω').v i)‖ ^ 2) ω ≤
        (1 - p.δ) * ‖nextM O s r i ω - (r ω).v i‖ ^ 2) := by
  have hm := measurable_pi_lambda _ (fun i => (hr.next_m_measurable ho s i).sub
    (measurable_enlarge O (by omega) (hr.v_measurable i)))
  have hq := hr.compression_query_measurable ho s
  have ha := ho.conditionalCompression (k + 1 + batchSize p s) (afterBatch O s r)
    (nextX O r) (fun ω i => nextM O s r i ω - (r ω).v i)
    (hr.after_batch_measurable ho s)
    (measurable_enlarge O (by omega) (hr.next_x_measurable ho)) hm
    (hr.after_batch_length s)
    (fun i => norm_square_integrable _ ((hr.next_m_memLp ho s i).sub (hr.v_memLp i))) i
  have hreply := response_predictable O ho _ _ (hr.after_batch_measurable ho s)
    hq (hr.after_batch_length s)
  have hc := (measurable_pi_apply i).comp (measurable_global O hreply).snd
  have hz := measurable_global O ((measurable_pi_apply i).comp hm)
  refine ⟨?_, ha.2⟩
  exact memLp_of_integrable_square _ (hc.sub hz).aestronglyMeasurable ha.1

lemma step_regular (s : ℕ) :
    Regular O hp hg (k + (batchSize p s + 2)) (step O s r) := by
  have hreply := response_predictable O ho _ _ (hr.after_batch_measurable ho s)
    (hr.compression_query_measurable ho s) (hr.after_batch_length s)
  have hhist := appendReply_predictable O ho _ _ (hr.after_batch_measurable ho s)
    (hr.compression_query_measurable ho s) (hr.after_batch_length s)
  refine ⟨step_history_length O s r hr.history_length, ?_, ?_, ?_, ?_,
    hr.next_x_memLp ho, hr.next_m_memLp ho s, ?_, ?_, ?_⟩
  · simpa only [step, Nat.add_assoc, Nat.add_comm 1 (batchSize p s)] using hhist
  · exact measurable_enlarge O (by omega) (hr.next_x_measurable ho)
  · intro i
    exact measurable_enlarge O (by omega) (hr.next_m_measurable ho s i)
  · intro i
    exact (measurable_enlarge O (by omega) (hr.v_measurable i)).add
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 (batchSize p s)] using
        (measurable_pi_apply i).comp hreply.snd)
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
      (hr.x_memLp.sub (hv.const_smul _))
    simpa only [step, nextX_eq O ho] using hi

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
  have hB : (batchSize p s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (batch_positive s)
  unfold batchError
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sub_smul, smul_sub, smul_smul]
  rw [inv_mul_cancel₀ hB, one_smul]
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
    change (1 - regularization p s * executionStep p) • _ +
      (regularization p s * executionStep p) • (_ + _ + regularization p s • (_ - p.x0)) = _
    simp only [stageGeometry, ConvexCompositeGeometry.regularized, geometry, mu, gamma,
      regularization, executionStep]
    module
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
  auxiliary_lp t := auxiliary_memLp (executionMeasure p O) hp hg (by have hL := hp.2.1; positivity)
    (stage_regular O hp hg ho s t).x_memLp (stage_regular O hp hg ho s t).m_memLp
  gap_integrable t := regularized_gap_integrable (executionMeasure p O) hp hg
    (mu_positive hp.2.1 s) (mu_le_initial hp.2.1 s)
    (stage_regular O hp hg ho s t).x_memLp
    (stage_regular O hp hg ho s t).regularizer_integrable
  regularizer_integrable t := (stage_regular O hp hg ho s t).regularizer_integrable
  auxiliary_regularizer_integrable t := by
    have hr := stage_regular O hp hg ho s t
    exact regularizer_at_prox_integrable (executionMeasure p O) hp hg (by have hL := hp.2.1; positivity)
      (hr.x_memLp.sub ((workerMean_memLp _ _ hr.m_memLp).const_smul _))
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
    have hm : @Measurable _ _ (pastSpace p O (clock p s t + 1)) inferInstance
        (fun ω => workerMean (stageRun O s t ω).m) := by
      unfold workerMean
      exact (Finset.measurable_sum _ (fun i _ =>
        measurable_enlarge O (Nat.le_succ _) (hr.m_measurable i))).const_smul _
    exact ((hg.proximalMeasurable _ (by have hL := hp.2.1; positivity)).comp
      ((measurable_enlarge O (Nat.le_succ _) hr.x_measurable).sub (hm.const_smul _))).aestronglyMeasurable

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
    rw [integral_prod (hg.compressionInitiallyIntegrable i).comp_fst]
    simp
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change (∫ ω : Randomness p O, ‖ω.1.1 i - gradient (I.f i) p.x0‖ ^ 2
      ∂((p.initialLaw : Measure _).prod (O.law : Measure _))) = _
    rw [integral_prod (hg.momentumInitiallyIntegrable i).comp_fst]
    simp

lemma constructed_accuracy (hp : spec.valid p) (hg : ProblemAssumptions p I)
    (ho : OracleAssumptions p I O) :
    Measurable (fun ω => (stageRun O (finalStage p) (stageLength p (finalStage p)) ω).x) ∧
    (∀ ω, I.ψ ((stageRun O (finalStage p) (stageLength p (finalStage p)) ω).x) ≠ ⊤) ∧
    Integrable (fun ω => finiteObjective I ((stageRun O (finalStage p)
      (stageLength p (finalStage p)) ω).x) - finiteObjective I I.xstar) (executionMeasure p O) ∧
    (∫ ω, finiteObjective I ((stageRun O (finalStage p)
      (stageLength p (finalStage p)) ω).x) - finiteObjective I I.xstar ∂(executionMeasure p O)) ≤ p.ε := by
  rcases hp with ⟨hn, hL, hR, hσ, hδ, hδ1, hε, hεL, hH⟩
  have hp : spec.valid p := ⟨hn, hL, hR, hσ, hδ, hδ1, hε, hεL, hH⟩
  let r := homotopyTrajectory O hp hg ho
  have he := initial_error_integrals O hp hg ho
  have hinit : 8192 * ((geometry hp hg).gap p.x0 + p.L * p.R ^ 2 +
      ((p.workers : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).v 0 i ω - (r.run 0).m 0 i ω‖ ^ 2 ∂(executionMeasure p O)) +
        (p.workers : ℝ)⁻¹ * (∑ i, ∫ ω, ‖(r.run 0).m 0 i ω - (geometry hp hg).grad i p.x0‖ ^ 2
          ∂(executionMeasure p O))) / p.L) ≤ p.H := by
    rw [he.1, he.2, geometry_gap]
    exact hg.initializationBound
  have ha := r.expected_accuracy (executionMeasure p O) (geometry hp hg) p.x0 hg.initialFinite
    hR hδ hδ1 hH hε hεL hg.distance hinit
  have hr := stage_regular O hp hg ho (finalStage p) (stageLength p (finalStage p))
  refine ⟨measurable_global O hr.x_measurable, hr.feasible, ?_, ?_⟩
  · simpa only [HomotopyTrajectory.output, homotopyTrajectory, innerTrajectory, geometry_gap,
      finalStage, stageLength, lastStage, ProximalEf21CountedBudget.length, regularization,
      executionStep, mu, gamma] using ha.1
  · simpa only [HomotopyTrajectory.output, homotopyTrajectory, innerTrajectory, geometry_gap,
      finalStage, stageLength, lastStage, ProximalEf21CountedBudget.length, regularization,
      executionStep, mu, gamma] using ha.2

end LongTails.Proofs.ProximalEf21ConstructedTrajectory
