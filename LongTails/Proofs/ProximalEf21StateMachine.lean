import LongTails.Proofs.ProximalEf21ConstructedTrajectory

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
  | succ l ih => simpa only [Nat.add_succ, advance, ih]

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
  rfl

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
    exact hsum i
  · have heq : j + 1 = batchSize p s := by omega
    have hfin (i : Fin p.workers) :
        batchSum O s t j i ω +
          rawSample O (afterProx O (stageRun O s t)) (nextX O (stageRun O s t)) j i ω =
        ∑ a : Fin (batchSize p s), rawSample O (afterProx O (stageRun O s t))
          (nextX O (stageRun O s t)) a.val i ω := by
      rw [← hsum i, heq]
      exact batch_sum_fin O s t i ω
    simp only [microStep, batchMachine, batchState, hj, hjnext, if_pos, if_neg,
      methodQuery, methodUpdate, stateAt, hstop, if_false, if_true,
      show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) = 1 by rfl,
      batchHistory, rawSample, Nat.add_assoc]
    apply Prod.ext
    · apply state_eq_of_fields <;> try rfl
      · funext i
        simp only [nextM, hfin, momentum, regularization, executionStep]
      · omega
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
    rfl
  · have hlast : t + 1 = stageLength p s := by omega
    have hnode : stageRun O (s + 1) 0 = step O s (stageRun O s t) := by
      simp only [stageRun, iterate, stageStart, ← hlast]
    have hn : sampleOffset p (s + 1) = sampleOffset p s + batchSize p s * stageLength p s := by
      simp only [sampleOffset, Finset.sum_range_succ]
    have hr : roundOffset p (s + 1) = roundOffset p s + stageLength p s := by
      simp only [roundOffset, Finset.sum_range_succ]
    simp only [microStep, batchMachine, batchState, hB, if_neg,
      methodQuery, methodUpdate, stateAt, hstop, if_false,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      hnext, machineAt, hnode, step, compressReply, compressQuery,
      afterBatch, hn, hr, Nat.zero_mul, Nat.add_zero]
    apply Prod.ext
    · apply state_eq_of_fields <;> try rfl
      · rw [← hlast]
        omega
      · omega
      · omega
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
  simp only [Nat.mul_add, Finset.sum_add_distrib, Nat.mul_comm, Finset.mul_sum]
  omega

lemma trace_success (hp : spec.valid p) {I : Instance p}
    (hg : ProblemAssumptions p I) (ho : OracleAssumptions p I O) :
    spec.successful p I (traceOutput O)
      ((p.initialLaw).prod O.law) := by
  have ha := constructed_accuracy O hp hg ho
  have he := funext (trace_output_eq O hp)
  rw [he]
  refine ⟨ha.1.prodMk measurable_const, Filter.Eventually.of_forall ha.2.1,
    ha.2.2.1, ha.2.2.2, ?_⟩
  exact Filter.Eventually.of_forall (fun _ => ⟨rfl, rfl, rfl⟩)

end LongTails.Proofs.ProximalEf21StateMachine
