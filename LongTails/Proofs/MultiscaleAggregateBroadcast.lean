import LongTails.Proofs.MultiscaleAggregateCollection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

lemma root_complete_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (htime : c.time = roundStart p (c.workers 0).iteration + (batch p i) * p.h i +
      (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ))) :
    let aggregate := (c.workers 0).total + readPacket p (c.workers 0).iteration
      (workerBits p g samples (c.workers 0).iteration i)
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers 0 (finish p (c.workers 0) aggregate)
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages i.succ
            (Function.update (c.oracle.communication.messages i.succ) 0 none)) } } } := by
  classical
  intro aggregate
  have hall := complete_workers p T g P samples selected c hc i hr hs hcomplete
  have hm := complete_messages p T g P samples selected c hc i hr hs hcomplete
  have ht := last_arrival_time p T g P samples selected c hc i hcomplete htime
  have hk : (c.workers 0).iteration < (rounds p) := by
    rw [← hr]
    exact (sent_worker p T g P samples selected c hc i hs).1
  have he : aggregate = totalCode p g samples (c.workers 0).iteration :=
    completed_aggregate p g samples selected (c.workers 0) i hc.root hnot hcomplete
  have hroot := finish_root_data p g samples selected _ aggregate hc.root.toRootPoints he
  have hnext : (finish p (c.workers 0) aggregate).targets ≠ [] →
      (c.workers 0).iteration + 1 < (rounds p) := by
    dsimp only [finish]
    split_ifs with h
    · exact fun _ => h
    · simp
  rw [hm]
  refine {
    root := by simpa only [Function.update_self] using hroot
    workers := ?_
    seeds := hc.seeds
    used := ?_
    root_limit := ?_
    arrived_incomplete := ?_
    targets_nodup := ?_
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    synchronized := ?_
    behind := ?_
    control := ?_
    root_pending := hc.root_pending
    pending := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.workers j
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.used j
  · simpa only [Function.update_self, finish] using Nat.succ_le_of_lt hk
  · change (∅ : Finset (Fin p.n)) ≠ Finset.univ
    intro hempty
    have hj := Finset.mem_univ (0 : Fin p.n)
    rw [← hempty] at hj
    exact Finset.notMem_empty _ hj
  · simp only [Function.update_self, finish]
    split_ifs
    · exact List.nodup_finRange _
    · exact List.nodup_nil
  · intro j _
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), finish] using
      congrArg (fun k => k + 1) (hall j).1
  · simpa only [Function.update_self, finish] using hnext
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro _
    simp only [Function.update_self, finish, Nat.add_sub_cancel]
    rw [he]
    rfl
  · intro htargets
    have hnew := hnext (by simpa only [Function.update_self] using htargets)
    simp only [Function.update_self, finish, Nat.add_sub_cancel]
    rw [roundStart_succ, ht]
    simp only [roundTime, ite_eq_left hnew]
    ring
  · intro j
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), finish, (hall j).1]
    omega
  · intro j _
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using ⟨(hall j).2.1, (hall j).2.2.1⟩
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.pending j
  · simp only [Function.update_self, finish, Finset.notMem_empty, false_implies, implies_true]
  · simp only [Function.update_self, finish, Finset.notMem_empty, false_implies, implies_true]
  · intro source target
    simp only [Function.update_self, finish]
    induction source using Fin.cases with
    | zero =>
        induction target using Fin.cases with
        | zero => rfl
        | succ j =>
            simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
            split_ifs <;> simp_all
    | succ j =>
        have hne : (c.workers 0).iteration ≠ (c.workers 0).iteration + 1 := by omega
        simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j), (hall j).1, hne,
          false_and, and_false, ite_false]

lemma root_query_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) :
    match (algorithm p T).query 0 (c.workers 0) 0 with
    | (.compute _, _) => False
    | (.communicate (target, bits), state) =>
        Pipeline p T g P samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 c.time
            turn := 1
            oracle := { c.oracle with communication := ((system p g P).communication.submit
              c.oracle.communication c.time 0 (target, bits ++ List.replicate clockBits false)) } }
    | (.advance target, state) =>
        Pipeline p T g P samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 (max c.time ((algorithm p T).timer target))
            turn := 1 } := by
  classical
  cases ht : (c.workers 0).targets with
  | nil =>
      have hq : (algorithm p T).query 0 (c.workers 0) 0 = (.advance 0, c.workers 0) := by
        simp [algorithm, ht]
      rw [hq]
      exact idle_pipeline p T g P samples selected c hc 0 0 0 _ hq
  | cons i rest =>
      let bits := rootBits p g samples ((c.workers 0).iteration - 1)
      have hnonempty : (c.workers 0).targets ≠ [] := by simp only [ht, List.cons_ne_nil, ne_eq, not_false_eq_true]
      have ho : (c.workers 0).outbox = bits := hc.outbox hnonempty
      have hq : (algorithm p T).query 0 (c.workers 0) 0 =
          (.communicate (i.succ, bits), { c.workers 0 with targets := rest }) := by
        simp only [algorithm, Fin.cases_zero, ht, ho]
      rw [hq]
      dsimp only
      have hfree : c.oracle.communication.messages 0 i.succ = none := by
        simp only [hc.links, Fin.cases_zero, Fin.cases_succ, ht, List.mem_cons_self,
          not_true_eq_false, and_false, ite_false]
      have hsubmit : (system p g P).communication.submit c.oracle.communication c.time 0
          (i.succ, bits ++ List.replicate clockBits false) =
          { c.oracle.communication with messages := (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (c.time + (p.l + p.b * (payload p ((c.workers 0).iteration - 1) + clockBits : ℕ)),
                bits ++ List.replicate clockBits false)))) } := by
        change (LongTails.Setups.StarNetwork.communication (Seed := Samples p) ⟨p.h, p.l, p.b⟩).submit
          c.oracle.communication c.time 0 (i.succ, bits ++ List.replicate clockBits false) = _
        rw [DistributedExecution.communication_submit_free (Seed := Samples p) ⟨p.h, p.l, p.b⟩
          c.oracle.communication c.time 0 i.succ (bits ++ List.replicate clockBits false)
          (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩) hfree]
        have hlength : bits.length = payload p ((c.workers 0).iteration - 1) :=
          MultiscaleAggregateCodec.packet_length p _ _
        simp only [List.length_append, List.length_replicate, hlength]
        congr 1
        funext source target
        by_cases hs : source = 0
        · subst source
          simp only [Function.update_self, Function.update_apply]
          (split_ifs; congr 2) <;> ring_nf
        · simp only [Function.update_of_ne hs]
      rw [hsubmit, hc.broadcast_time hnonempty]
      exact broadcast_send_pipeline p T g P samples selected c hc i rest ht

lemma root_event_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (notification : Event (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeReply p) (LongTails.Setups.DistributedAggregateSmoothNonconvex.CommReply p)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time = some ((0, notification), oracle))
    (hp : Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers 0 ((algorithm p T).update 0 (c.workers 0) 0 notification)
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := oracle })
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  have h := root_query_pipeline p T g P samples selected _ hp
  simp only [Function.update_self, Function.update_idem] at h
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    have hclock : (algorithm p T).clock c.time = 0 := rfl
    rw [hclock] at hstep
    cases hq : (algorithm p T).query 0 ((algorithm p T).update 0 (c.workers 0) 0 notification) 0 with
    | mk action state =>
        simp only [hq] at h hstep
        cases action with
        | compute query => exact h.elim
        | communicate query =>
            rcases query with ⟨target, bits⟩
            simp only [Fin.val_zero, Nat.zero_add, Option.some.injEq] at hstep
            subst next
            exact h
        | advance target =>
            simp only [Fin.val_zero, Nat.zero_add, Function.update_idem, Option.some.injEq] at hstep
            subst next
            exact h

lemma root_ready_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) :
    Pipeline p T g P samples selected { c with wakeTime := Function.update c.wakeTime 0 c.time, turn := 1 } := by
  refine { hc with targets_ready := ?_, control := ?_ }
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j

lemma accept_partial (p : Params) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < (rounds p)) (hp : insert i s.arrived ≠ Finset.univ) :
    accept p s i.succ bits = { s with
      total := s.total + readPacket p s.iteration bits
      arrived := insert i s.arrived } := by
  simp only [accept, Fin.cases_succ, hnot, not_false_eq_true, hk, and_self, ite_true, hp, ite_false]

lemma accept_complete (p : Params) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < (rounds p)) (hp : insert i s.arrived = Finset.univ) :
    accept p s i.succ bits = finish p s
      (s.total + readPacket p s.iteration bits) := by
  simp only [accept, Fin.cases_succ, hnot, not_false_eq_true, hk, and_self, ite_true, hp]

lemma root_receive (p : Params) (T : Time)
    (s : State p) (clock : ClockReading) (source : Fin (p.n + 1)) (bits : List Bool) :
    (algorithm p T).update 0 s clock (.received (.received source bits)) = accept p s source bits := rfl

lemma received_partial_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hpartial : insert i (c.workers 0).arrived ≠ Finset.univ)
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  obtain ⟨hr, hs, hnot, ht, hb⟩ := received_worker_facts p T g P samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p T g P c htimely i.succ 0 bits oracle he
  have hk : (c.workers 0).iteration < (rounds p) := by
    rw [← hr]
    exact (sent_worker p T g P samples selected c hc i hs).1
  apply root_event_pipeline p T g P samples selected c next _ oracle he _ hstep
  rw [root_receive, accept_partial p (c.workers 0) i bits hnot hk hpartial, hb,
    worker_frame, ho]
  exact
    root_partial_pipeline p T g P samples selected c hc i hr hs hnot hpartial ht

lemma received_complete_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  obtain ⟨hr, hs, hnot, ht, hb⟩ := received_worker_facts p T g P samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p T g P c htimely i.succ 0 bits oracle he
  have hk : (c.workers 0).iteration < (rounds p) := by
    rw [← hr]
    exact (sent_worker p T g P samples selected c hc i hs).1
  apply root_event_pipeline p T g P samples selected c next _ oracle he _ hstep
  rw [root_receive, accept_complete p (c.workers 0) i bits hnot hk hcomplete, hb,
    worker_frame, ho]
  exact root_complete_pipeline p T g P samples selected c hc i hr hs hnot hcomplete ht


end LongTails.Proofs.MultiscaleAggregateExecution
