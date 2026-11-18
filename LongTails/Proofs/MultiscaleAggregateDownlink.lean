import LongTails.Proofs.MultiscaleAggregateBroadcast

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

lemma received_broadcast_facts (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle)) :
    (c.workers 0).iteration < (rounds p) ∧ (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧
      i ∉ (c.workers 0).targets ∧
      (c.workers i.succ).samples = (batch p i) ∧ (c.workers i.succ).pending = false ∧
      (c.workers i.succ).sent = true ∧ c.time = roundStart p (c.workers 0).iteration ∧
      bits = rootBits p g samples (c.workers i.succ).iteration ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish p T g P c htimely 0 i.succ bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_zero, Fin.cases_succ] at hm
  split_ifs at hm with hvalid
  obtain ⟨hi, hr, hnot⟩ := hvalid
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  obtain ⟨hcount, hsent⟩ := hp.behind i hbefore
  have hpending := (sent_worker p T g P samples selected c hp i hsent).2.2
  obtain ⟨ht, hb⟩ := Prod.mk.inj (Option.some.inj hm)
  have hk : (c.workers 0).iteration - 1 = (c.workers i.succ).iteration := by omega
  exact ⟨hi, hr, hnot, hcount, hpending, hsent, ht.symm, by simpa only [hk] using hb.symm⟩

lemma broadcast_worker_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hk : (c.workers 0).iteration < (rounds p)) (hqueued : i ∉ (c.workers 0).targets)
    (hr : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration)
    (hcount : (c.workers i.succ).samples = (batch p i))
    (htime : c.time = roundStart p (c.workers 0).iteration) :
    let x := trajectory p g samples (c.workers 0).iteration
    let state := { c.workers i.succ with
      model := x
      iteration := (c.workers 0).iteration
      accumulator := 0
      samples := 0
      pending := true
      sent := false }
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := (Function.update c.oracle.computation i.succ
            { c.oracle.computation i.succ with pending := some (c.time + p.h i, x.point) })
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages 0
              (Function.update (c.oracle.communication.messages 0) i.succ none)) } } } := by
  classical
  intro x state
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have he := (hc.arrived_current i hm).1
    omega
  refine {
    root := by simpa only [Function.update_of_ne hz] using hc.root
    workers := ?_
    seeds := ?_
    used := ?_
    root_limit := by simpa only [Function.update_of_ne hz] using hc.root_limit
    arrived_incomplete := by simpa only [Function.update_of_ne hz] using hc.arrived_incomplete
    targets_nodup := by simpa only [Function.update_of_ne hz] using hc.targets_nodup
    targets_queued := ?_
    targets_active := by simpa only [Function.update_of_ne hz] using hc.targets_active
    targets_ready := by simpa only [Function.update_of_ne hz] using hc.targets_ready
    outbox := by simpa only [Function.update_of_ne hz] using hc.outbox
    broadcast_time := by simpa only [Function.update_of_ne hz] using hc.broadcast_time
    synchronized := ?_
    behind := ?_
    control := ?_
    root_pending := by simpa only [Function.update_of_ne hz] using hc.root_pending
    pending := ?_
    arrived_current := ?_
    arrived_time := by simpa only [Function.update_of_ne hz] using hc.arrived_time
    links := ?_ }
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      refine ⟨rfl, Nat.zero_le _, ?_⟩
      simp only [state, Finset.range_zero, Finset.sum_empty]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.workers j
  · intro j
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hc.seeds i
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.seeds j
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      change (c.oracle.computation i.succ).used = (c.workers 0).iteration * (batch p i) + 0
      simp only [hc.used i, hcount, ← hr, Nat.add_mul, Nat.one_mul, Nat.add_zero]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.used j
  · intro j hj
    simp only [Function.update_of_ne hz] at hj
    have hne : j ≠ i := fun he => hqueued (he ▸ hj)
    simpa only [Function.update_of_ne hz,
      Function.update_of_ne (fun he => hne (Fin.succ_inj.mp he))] using hc.targets_queued j hj
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, state]
      exact ⟨le_rfl, Nat.le_succ _⟩
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hc.synchronized j
  · intro j hb
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, state, lt_self_iff_false] at hb
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [Function.update_of_ne hne, Function.update_of_ne hz] at hb ⊢
      exact hc.behind j hb
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, WorkerControl, state]
      exact Or.inr (Or.inl ⟨hk, (MultiscaleAggregateBudget.batch_pos (p := p) i), trivial, trivial⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.control j
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, state, htime, Nat.cast_zero, zero_add, one_mul, ite_true]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.pending j
  · intro j hj
    simp only [Function.update_of_ne hz] at hj
    by_cases he : j = i
    · subst j; exact (hnot hj).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hc.arrived_current j hj
  · intro source target
    simp only [Function.update_of_ne hz]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero => simp only [Function.update_of_ne hz]; exact hc.links 0 0
        | succ j =>
            by_cases he : j = i
            · subst j
              have hn : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
              simp only [Function.update_self, Fin.cases_succ, state, hn, false_and, and_false, ite_false]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hc.links]
              simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne hne]
    | succ j =>
        rw [Function.update_of_ne (Fin.succ_ne_zero j), hc.links]
        simp only [Fin.cases_succ]
        by_cases he : j = i
        · subst j
          have hn : (c.workers i.succ).iteration ≠ (c.workers 0).iteration := by omega
          simp only [Function.update_self, state, hn, false_and, and_false, ite_false, Bool.false_eq_true]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simp only [Function.update_of_ne hne]

lemma worker_receive (p : Params) (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading) (bits : List Bool) :
    (algorithm p T).update i.succ s clock (.received (.received 0 bits)) = receive p s bits := by
  simp only [algorithm, Fin.cases_succ, ite_true]

lemma received_broadcast_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  obtain ⟨hk, hr, hqueued, hcount, hpending, hsent, ht, hb⟩ :=
    received_broadcast_facts p T g P samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p T g P c htimely 0 i.succ bits oracle he
  subst bits
  subst oracle
  let x := trajectory p g samples (c.workers 0).iteration
  let updated : State p := { c.workers i.succ with
    model := x
    iteration := (c.workers 0).iteration
    accumulator := 0
    samples := 0
    pending := false
    sent := false }
  have hdecode : advance p (c.workers i.succ).model (c.workers i.succ).iteration
      (readPacket p (c.workers i.succ).iteration (rootBits p g samples (c.workers i.succ).iteration ++ List.replicate clockBits false)) = x := by
    rw [(hc.workers i).model, root_frame]
    dsimp only [x]
    rw [← hr]
    rfl
  have hup : (algorithm p T).update i.succ (c.workers i.succ) 0
      (.received (.received 0 (rootBits p g samples (c.workers i.succ).iteration ++
        List.replicate clockBits false))) = updated := by
    rw [worker_receive]
    unfold receive
    rw [hdecode, hr]
  have hq := worker_query_compute p T updated i 0 hk rfl (MultiscaleAggregateBudget.batch_pos (p := p) i)
  have hfree : (c.oracle.computation i.succ).pending = none := by
    rw [hc.pending i, hpending]
    rfl
  have hsubmit : (system p g P).computation.submit i.succ (c.oracle.computation i.succ)
      c.time (.evaluate x.point) = { c.oracle.computation i.succ with pending := some (c.time + p.h i, x.point) } :=
    DistributedExecution.computation_submit_idle ⟨p.h, p.l, p.b⟩
      (fun j y (ξ : Samples p) k => g j y (ξ j k)) i (c.oracle.computation i.succ) c.time x.point hfree
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    have hclock : (algorithm p T).clock c.time = 0 := rfl
    simp only [hclock, hup, hq] at hstep
    change some { c with
      workers := Function.update c.workers i.succ { updated with pending := true }
      wakeTime := Function.update c.wakeTime i.succ c.time
      turn := i.succ.val + 1
      oracle := { c.oracle with
        computation := Function.update c.oracle.computation i.succ
          ((system p g P).computation.submit i.succ (c.oracle.computation i.succ) c.time (.evaluate x.point))
        communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ none)) } } } = some next at hstep
    rw [hsubmit] at hstep
    have hn := Option.some.inj hstep
    subst next
    exact broadcast_worker_pipeline p T g P samples selected c hc i hk hqueued hr hcount ht

lemma wake_idle_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T)) (hp : Pipeline p T g P samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p g P)) (target : ClockReading) (state : State p)
    (he : event (system p g P) (algorithm p T) c c.time = some ((v, .wake), oracle))
    (hq : (algorithm p T).query v (c.workers v) ((algorithm p T).clock c.time) = (.advance target, state))
    (hs : step (system p g P) (algorithm p T) c = some next) : Pipeline p T g P samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p g P) (algorithm p T) c c.time v oracle he).1
  subst oracle
  have hup : (algorithm p T).update v (c.workers v) ((algorithm p T).clock c.time) .wake = c.workers v := rfl
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate, he, hup, hq, Function.update_idem, Option.some.injEq] at hs
    subst next
    exact idle_pipeline p T g P samples selected c hp v ((algorithm p T).clock c.time) target state hq

lemma wake_start_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T)) (hp : Pipeline p T g P samples selected c)
    (i : Fin p.n) (oracle : OracleState (system p g P))
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0)
    (he : event (system p g P) (algorithm p T) c c.time = some ((i.succ, .wake), oracle))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p g P) (algorithm p T) c c.time i.succ oracle he).1
  subst oracle
  have hk : (c.workers i.succ).iteration < (rounds p) := by
    rw [hinit.1]
    exact (rounds_pos p)
  have hj : (c.workers i.succ).samples < (batch p i) := by rw [hinit.2.1]; exact (MultiscaleAggregateBudget.batch_pos (p := p) i)
  have hnone : (c.oracle.computation i.succ).pending = none := by
    rw [hp.pending, hinit.2.2.1]
    rfl
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    simp only [algorithm, Fin.cases_succ, hk, hj, hinit.2.2.1, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system, LongTails.Setups.StarNetwork.computation,
      Fin.cases_succ, hnone, Option.some.injEq] at hstep
    subst next
    exact start_worker_pipeline p T g P samples selected c hp i hinit

lemma wake_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time = some ((v, .wake), oracle))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  have hidle (hq : (algorithm p T).query v (c.workers v) ((algorithm p T).clock c.time) =
      (.advance 0, c.workers v)) : Pipeline p T g P samples selected next :=
    wake_idle_pipeline p T g P samples selected c next hc v oracle _ _ he hq hstep
  induction v using Fin.cases with
  | zero =>
      have ho := (DistributedExecution.wake_event (system p g P) (algorithm p T) c c.time 0 oracle he).1
      subst oracle
      apply root_event_pipeline p T g P samples selected c next .wake c.oracle he _ hstep
      simpa only [show (algorithm p T).update 0 (c.workers 0) 0 .wake = c.workers 0 from rfl,
        Function.update_eq_self] using root_ready_pipeline p T g P samples selected c hc
  | succ i =>
      rcases hc.control i with hinit | hcompute | hsent
      · exact wake_start_pipeline p T g P samples selected c next hc i oracle hinit he hstep
      · apply hidle
        simp [algorithm, hcompute.2.2.1]
      · apply hidle
        simp [algorithm, hsent.2.1, hsent.2.2.2]


end LongTails.Proofs.MultiscaleAggregateExecution
