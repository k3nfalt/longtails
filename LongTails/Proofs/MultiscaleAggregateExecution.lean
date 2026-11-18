import LongTails.Proofs.MultiscaleAggregateDownlink

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

lemma step_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  cases he : event (system p g P) (algorithm p T) c c.time with
  | none =>
      unfold step at hstep
      by_cases hlate : c.deadline < c.time
      · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
      · simp only [ite_eq_right hlate, he] at hstep
        by_cases hdone : c.time = c.deadline
        · simp only [ite_eq_left hdone, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdone, Option.some.injEq] at hstep
          subst next
          exact jump_pipeline p T g P samples selected c hp he
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      cases notification with
      | wake => exact wake_pipeline p T g P samples selected c next hp v oracle he hstep
      | computed reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p g P)
            (algorithm p T) c c.time v reply oracle he
          cases reply with
          | computed input value =>
              induction v using Fin.cases with
              | zero =>
                  simp only [system, LongTails.Setups.StarNetwork.system,
                    LongTails.Setups.StarNetwork.computation,
                    Fin.cases_zero, reduceCtorEq] at ha
              | succ i =>
                  by_cases hmore : (c.workers i.succ).samples + 1 < (batch p i)
                  · exact computed_continue_pipeline p T g P samples selected c next hp htimely
                      i input value oracle he hmore hstep
                  · have hpend := (computed_worker_facts p T g P samples selected c hp htimely
                      i input value oracle he).1
                    have hcount := (pending_worker p T g P samples selected c hp i hpend).2.1
                    exact computed_finish_pipeline p T g P samples selected c next hp htimely
                      i input value oracle he (by omega) hstep
      | received reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p g P)
            (algorithm p T) c c.time v reply oracle he
          cases reply with
          | received source bits =>
              have hm := (received_at_finish p T g P c htimely source v bits oracle he).1
              induction source using Fin.cases with
              | zero =>
                  induction v using Fin.cases with
                  | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
                  | succ i =>
                      exact received_broadcast_pipeline p T g P samples selected
                        c next hp htimely i bits oracle he hstep
              | succ i =>
                  induction v using Fin.cases with
                  | zero =>
                      by_cases hcomplete : insert i (c.workers 0).arrived = Finset.univ
                      · exact received_complete_pipeline p T g P samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                      · exact received_partial_pipeline p T g P samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                  | succ j =>
                      simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                        ite_false, reduceCtorEq] at hm

lemma run_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (deadline : Time) (k : ℕ) :
    Pipeline p T g P samples selected (run (system p g P) (algorithm p T) k
      (DistributedTemplate.initial (system p g P) (algorithm p T) deadline (selected, samples))) := by
  have hrun : ∀ j (c : ExecutionState (system p g P) (algorithm p T)),
      Pipeline p T g P samples selected c → Timely p T g P c →
      Pipeline p T g P samples selected (run (system p g P) (algorithm p T) j c) := by
    intro j
    induction j with
    | zero => intro c hp _; exact hp
    | succ j ih =>
        intro c hp ht
        cases hs : step (system p g P) (algorithm p T) c with
        | none => simpa only [run, hs] using hp
        | some next =>
            simpa only [run, hs] using ih next (step_pipeline p T g P samples selected c next hp ht hs)
              (step_timely p T g P c next ht hs)
  exact hrun k _ (initial_pipeline p T g P samples selected deadline)
    (initial_timely p T g P deadline (selected, samples))

lemma unfinished_round_time (p : Params) (r : ℕ) (hr : r < (rounds p)) :
    roundStart p r + computeTime p +
      (p.l + p.b * (payload p r + clockBits : ℕ)) ≤ executionTime p := by
  calc
    _ = roundStart p r + (computeTime p + p.l +
        p.b * (payload p r + clockBits : ℕ)) := by ring
    _ ≤ roundStart p r + roundTime p r := by
      unfold roundTime
      exact add_le_add le_rfl (le_add_of_nonneg_right (by exact zero_le))
    _ = roundStart p (r + 1) := (roundStart_succ p r).symm
    _ ≤ roundStart p (rounds p) := roundStart_mono p (Nat.succ_le_of_lt hr)
    _ = executionTime p := rfl

lemma quiet_pipeline_complete (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (htime : executionTime p ≤ c.time)
    (hquiet : event (system p g P) (algorithm p T) c c.time = none) :
    (c.workers 0).iteration = (rounds p) := by
  classical
  have htargets := quiet_targets_empty p T g P samples selected c hc hquiet
  by_contra hdone
  have hr : (c.workers 0).iteration < (rounds p) := lt_of_le_of_ne hc.root_limit hdone
  obtain ⟨hcompute, hcomm, hwake⟩ := quiet_future p T g P c hquiet
  have hall (i : Fin p.n) : i ∈ (c.workers 0).arrived := by
    obtain ⟨hle, hnear⟩ := hc.synchronized i
    have hsame : (c.workers i.succ).iteration = (c.workers 0).iteration := by
      by_contra hne
      have hbehind : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration := by omega
      have hlink := hc.links 0 i.succ
      simp only [Fin.cases_zero, Fin.cases_succ, hr, hbehind, htargets, List.not_mem_nil] at hlink
      have hfuture := hcomm 0 i.succ _ _ hlink
      have hb : roundStart p (c.workers 0).iteration ≤ executionTime p :=
        roundStart_mono p hc.root_limit
      exact (not_lt_of_ge (hb.trans htime)) hfuture
    rcases hc.control i with hinit | hworking | hwaiting
    · have ht := hwake i.succ
      rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at ht
      exact (lt_irrefl _ ht).elim
    · have hlink := hc.pending i
      simp only [hworking.2.2.1, ite_true] at hlink
      have hfuture := hcompute i _ _ hlink
      have hsample := computation_finish_le p (c.workers 0).iteration
        ((c.workers i.succ).samples + 1) i (Nat.succ_le_of_lt hworking.2.1)
      push_cast at hsample
      have hlimit := unfinished_round_time p (c.workers 0).iteration hr
      rw [hsame] at hfuture
      exfalso
      exact (not_lt_of_ge (hsample.trans ((le_add_of_nonneg_right (by positivity)).trans
        (hlimit.trans htime)))) hfuture
    · by_contra hnot
      have hlink := hc.links i.succ 0
      simp only [Fin.cases_succ, hsame, hwaiting.2.2.2, hnot, not_false_eq_true,
        and_self, ite_true] at hlink
      have hfuture := hcomm i.succ 0 _ _ hlink
      have hworker := computation_finish_le p (c.workers 0).iteration (batch p i) i le_rfl
      have hlimit := unfinished_round_time p (c.workers 0).iteration hr
      exact (not_lt_of_ge ((add_le_add hworker le_rfl).trans (hlimit.trans htime))) hfuture
  apply hc.arrived_incomplete
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact hall i

lemma terminal_pipeline_output (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (htime : c.time ≤ c.deadline) (hbudget : executionTime p ≤ c.deadline)
    (hterminal : step (system p g P) (algorithm p T) c = none) :
    (algorithm p T).output (c.workers 0) = output p g (selected, samples) := by
  obtain ⟨ht, hquiet⟩ := (DistributedExecution.step_terminal_iff
    (system p g P) (algorithm p T) c htime).mp hterminal
  have hdone := quiet_pipeline_complete p T g P samples selected c hc
    (by simpa only [ht] using hbudget) hquiet
  exact completed_output p T g P samples selected c hc hdone

lemma query_worker_progress_or_idle (p : Params) (T : Time)
    (i : Fin p.n) (s : State p) (clock : ClockReading) :
    workerProgress p i.succ s < workerProgress p i.succ ((algorithm p T).query i.succ s clock).2 ∨
      (algorithm p T).query i.succ s clock = (.advance 0, s) := by
  classical
  simp only [algorithm, Fin.cases_succ]
  split_ifs with hready hcount hsent
  · left
    have hp : s.pending = false := by simpa using hready.2
    simp [workerProgress, hp]
  · left
    have hs : s.sent = false := by simpa using hsent
    simp [workerProgress, hs]
  · exact Or.inr rfl
  · exact Or.inr rfl

lemma receive_progress (p : Params)
    (i : Fin p.n) (s : State p) (bits : List Bool)
    (hcount : s.samples ≤ (batch p i)) (hp : s.pending = false) (hs : s.sent = true) :
    workerProgress p i.succ s < workerProgress p i.succ (receive p s bits) := by
  simp only [workerProgress, Fin.cases_succ, receive, hp, hs, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_add, Nat.mul_one]
  omega

lemma computed_progress (p : Params) (i : Fin p.n) (s : State p) (value : Point p) :
    workerProgress p i.succ s < workerProgress p i.succ
      { s with accumulator := s.accumulator + value, samples := s.samples + 1, pending := false } := by
  cases hp : s.pending <;> simp only [workerProgress, Fin.cases_succ, hp, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_add, Nat.mul_one] <;> omega

lemma accept_progress (p : Params) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < (rounds p)) :
    workerProgress p 0 s < workerProgress p 0 (accept p s i.succ bits) := by
  classical
  have hc : s.arrived.card ≤ p.n := by simpa using Finset.card_le_univ s.arrived
  have htargets := Nat.sub_le p.n s.targets.length
  unfold accept
  simp only [Fin.cases_succ, ite_eq_left (show i ∉ s.arrived ∧ s.iteration < (rounds p) from ⟨hnot, hk⟩)]
  split_ifs <;> simp only [workerProgress, Fin.cases_zero, finish, Finset.card_empty,
    Finset.card_insert_of_notMem hnot, Nat.mul_add, Nat.mul_one] <;> omega

lemma event_progress_or_idle (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (v : Fin (p.n + 1)) (notification : Event (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeReply p) (LongTails.Setups.DistributedAggregateSmoothNonconvex.CommReply p))
    (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time = some ((v, notification), oracle)) :
    workerProgress p v (c.workers v) < workerProgress p v
      ((algorithm p T).query v ((algorithm p T).update v (c.workers v)
        ((algorithm p T).clock c.time) notification) ((algorithm p T).clock c.time)).2 ∨
    (notification = .wake ∧ (algorithm p T).query v (c.workers v) ((algorithm p T).clock c.time) =
      (.advance 0,
        c.workers v)) := by
  classical
  cases notification with
  | wake =>
      induction v using Fin.cases with
      | zero =>
          cases ht : (c.workers 0).targets with
          | nil =>
              right
              exact ⟨rfl, by simp [algorithm, ht]⟩
          | cons i rest =>
              left
              have hlength : rest.length + 1 ≤ p.n := by
                simpa only [ht, List.length_cons, Fintype.card_fin] using hp.targets_nodup.length_le_card
              simp only [algorithm, Fin.cases_zero, ht, workerProgress, List.length_cons]
              omega
      | succ i =>
          rcases query_worker_progress_or_idle p T i (c.workers i.succ) 0 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨rfl, h⟩
  | computed reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p g P)
        (algorithm p T) c c.time v reply oracle he
      cases reply with
      | computed input value =>
          induction v using Fin.cases with
          | zero =>
              simp only [system, LongTails.Setups.StarNetwork.system,
                LongTails.Setups.StarNetwork.computation,
                Fin.cases_zero, reduceCtorEq] at ha
          | succ i =>
              left
              have h := (computed_progress p i (c.workers i.succ) value).trans_le
                (query_progress p T i.succ _ 0)
              simpa only [compute_update, show (algorithm p T).clock c.time = 0 from rfl] using h
  | received reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p g P)
        (algorithm p T) c c.time v reply oracle he
      cases reply with
      | received source bits =>
          have hm := (received_at_finish p T g P c htimely source v bits oracle he).1
          induction source using Fin.cases with
          | zero =>
              induction v using Fin.cases with
              | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
              | succ i =>
                  left
                  obtain ⟨_, _, _, hcount, hpend, hsent, _⟩ :=
                    received_broadcast_facts p T g P samples selected c hp htimely i bits oracle he
                  have h := (receive_progress p i (c.workers i.succ) bits hcount.le hpend hsent).trans_le
                    (query_progress p T i.succ _ 0)
                  simpa only [worker_receive, show (algorithm p T).clock c.time = 0 from rfl] using h
          | succ i =>
              induction v using Fin.cases with
              | zero =>
                  left
                  obtain ⟨hr, hs, hnot, _⟩ := received_worker_facts p T g P samples selected
                    c hp htimely i bits oracle he
                  have hk : (c.workers 0).iteration < (rounds p) := by
                    rw [← hr]
                    exact (sent_worker p T g P samples selected c hp i hs).1
                  have h := (accept_progress p (c.workers 0) i bits hnot hk).trans_le
                    (query_progress p T 0 _ 0)
                  simpa only [root_receive, show (algorithm p T).clock c.time = 0 from rfl] using h
              | succ j =>
                  simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                    ite_false, reduceCtorEq] at hm

noncomputable def workerProgressBound (p : Params) (v : Fin (p.n + 1)) : ℕ :=
  Fin.cases ((3 * p.n + 1) * (((rounds p) : ℕ) + 1))
    (fun i => (2 * (batch p i) + 2) * (((rounds p) : ℕ) + 1)) v

lemma worker_progress_le (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (v : Fin (p.n + 1)) :
    workerProgress p v (c.workers v) ≤ workerProgressBound p v := by
  classical
  induction v using Fin.cases with
  | zero =>
      have hcard : (c.workers 0).arrived.card ≤ p.n := by simpa using Finset.card_le_univ (c.workers 0).arrived
      have hm := Nat.mul_le_mul_left (3 * p.n + 1) hc.root_limit
      have ht := Nat.sub_le p.n (c.workers 0).targets.length
      simp only [workerProgress, workerProgressBound, Fin.cases_zero, Nat.mul_add, Nat.mul_one]
      omega
  | succ i =>
      have hk : (c.workers i.succ).iteration ≤ (rounds p) := (hc.synchronized i).1.trans hc.root_limit
      have hm := Nat.mul_le_mul_left (2 * (batch p i) + 2) hk
      have hcount := (hc.workers i).count
      have hpend : (c.workers i.succ).pending.toNat ≤ 1 := by cases (c.workers i.succ).pending <;> decide
      have hsent : (c.workers i.succ).sent.toNat ≤ 1 := by cases (c.workers i.succ).sent <;> decide
      simp only [workerProgress, workerProgressBound, Fin.cases_succ, Nat.mul_add, Nat.mul_one]
      omega

noncomputable def workerRank (p : Params) (T : Time) (v : Fin (p.n + 1))
    (s : State p) (wake : Time) : ℕ :=
  2 * (workerProgressBound p v - workerProgress p v s) + if wake ≤ T then 1 else 0

lemma workerRank_decrease (p : Params) (T : Time) (v : Fin (p.n + 1))
    (old next : State p) (oldWake newWake : Time)
    (hbound : workerProgress p v next ≤ workerProgressBound p v)
    (hprogress : workerProgress p v old < workerProgress p v next) :
    workerRank p T v next newWake < workerRank p T v old oldWake := by
  unfold workerRank
  split_ifs <;> omega

lemma event_rank_decrease (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ T) (v : Fin (p.n + 1))
    (notification : Event (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeReply p) (LongTails.Setups.DistributedAggregateSmoothNonconvex.CommReply p)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time = some ((v, notification), oracle))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    (∑ j, workerRank p c.deadline j (next.workers j) (next.wakeTime j)) <
      ∑ j, workerRank p c.deadline j (c.workers j) (c.wakeTime j) := by
  classical
  generalize hquery : (algorithm p T).query v ((algorithm p T).update v (c.workers v)
    ((algorithm p T).clock c.time) notification) ((algorithm p T).clock c.time) = pair
  obtain ⟨action, state⟩ := pair
  obtain ⟨hworkers, hwakes⟩ := DistributedExecution.step_event_state (system p g P)
    (algorithm p T) c next v notification oracle action state he hquery hstep
  have hstrict : workerRank p c.deadline v (next.workers v) (next.wakeTime v) <
      workerRank p c.deadline v (c.workers v) (c.wakeTime v) := by
    rcases event_progress_or_idle p T g P samples selected c hp htimely v notification oracle he with
      hprogress | ⟨hn, hidle⟩
    · have hbound := worker_progress_le p T g P samples selected next
        (step_pipeline p T g P samples selected c next hp htimely hstep) v
      simp only [hquery] at hprogress
      simp only [hworkers, Function.update_self] at hbound ⊢
      exact workerRank_decrease p c.deadline v (c.workers v) state (c.wakeTime v)
        (next.wakeTime v) hbound hprogress
    · subst notification
      change (algorithm p T).query v (c.workers v) ((algorithm p T).clock c.time) = (action, state) at hquery
      rw [hidle] at hquery
      cases hquery
      have hw := (DistributedExecution.wake_event (system p g P) (algorithm p T)
        c c.time v oracle he).2
      simp only [hworkers, hwakes, Function.update_self, workerRank]
      have hready : c.wakeTime v ≤ c.deadline := hw.trans htime
      have hafter : ¬ max c.time ((algorithm p T).timer 0) ≤ c.deadline := by
        apply not_le.mpr
        exact (hbudget.trans_lt (lt_add_of_pos_right _ zero_lt_one)).trans_le (le_max_right _ _)
      simp only [ite_eq_left hready, ite_eq_right hafter, Nat.add_zero]
      exact Nat.lt_succ_self _
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = v
    · subst j; exact hstrict.le
    · simp only [hworkers, hwakes, Function.update_of_ne hj]
      exact le_rfl
  · exact ⟨v, Finset.mem_univ _, hstrict⟩

noncomputable def executionRank (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p T)) : ℕ :=
  2 * (∑ v, workerRank p c.deadline v (c.workers v) (c.wakeTime v)) +
    if c.time = c.deadline ∨ (event (system p g P) (algorithm p T) c c.time).isSome then 0 else 1

lemma step_rank_decrease (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ T)
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    executionRank p T g P next < executionRank p T g P c := by
  classical
  cases he : event (system p g P) (algorithm p T) c c.time with
  | none =>
      have hdone : c.time ≠ c.deadline := by
        intro h
        have hn := (DistributedExecution.step_terminal_iff (system p g P) (algorithm p T) c htime).mpr ⟨h, he⟩
        rw [hn] at hstep
        cases hstep
      simp only [step, ite_eq_right (not_lt.mpr htime), he, ite_eq_right hdone, Option.some.injEq] at hstep
      subst next
      have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
        (fun i x (samples : Samples p) k => g i x (samples i k)) P (algorithm p T) c htime
      have hn := (DistributedExecution.nextTime_spec (event (system p g P) (algorithm p T) c)
        c.time c.deadline hex).1.2.2
      have hready :
          (nextTime (event (system p g P) (algorithm p T) c) c.time c.deadline = c.deadline ∨
          (event (system p g P) (algorithm p T)
            { c with time := nextTime (event (system p g P) (algorithm p T) c) c.time c.deadline }
            (nextTime (event (system p g P) (algorithm p T) c) c.time c.deadline)).isSome) := hn
      simp only [executionRank, hready, ite_true, he, Option.isSome_none, Bool.false_eq_true,
        or_false, hdone, ite_false, Nat.add_zero]
      exact Nat.lt_succ_self _
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      have hr := event_rank_decrease p T g P samples selected c next hp htimely htime hbudget v notification oracle he hstep
      have hd := DistributedExecution.step_deadline (system p g P) (algorithm p T) c next hstep
      unfold executionRank
      rw [hd]
      split_ifs <;> omega

lemma finiteEvents (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p)) :
    FiniteEvents (system p g P) (algorithm p T) T (selected, samples) := by
  intro deadline hdeadline
  apply DistributedExecution.termination_of_rank (system p g P) (algorithm p T)
    (fun c => Pipeline p T g P samples selected c ∧ Timely p T g P c ∧
      c.time ≤ c.deadline ∧ c.deadline ≤ T)
    (executionRank p T g P)
  · intro c next hc hs
    refine ⟨⟨step_pipeline p T g P samples selected c next hc.1 hc.2.1 hs,
      step_timely p T g P c next hc.2.1 hs,
      DistributedExecution.step_time_le_deadline (system p g P) (algorithm p T) c next hc.2.2.1 hs,
      by simpa only [DistributedExecution.step_deadline _ _ _ _ hs] using hc.2.2.2⟩, ?_⟩
    exact step_rank_decrease p T g P samples selected c next hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hs
  · exact ⟨initial_pipeline p T g P samples selected deadline,
      initial_timely p T g P deadline (selected, samples), by exact zero_le, hdeadline⟩

lemma execute_output (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (hbudget : executionTime p ≤ T) :
    execute (system p g P) (algorithm p T) T selected samples =
      output p g (selected, samples) := by
  have hfinite := finiteEvents p T g P samples selected
  obtain ⟨k, hk⟩ := hfinite T le_rfl
  rw [DistributedExecution.execute_eq_terminal (system p g P) (algorithm p T)
    T (selected, samples) k hk]
  apply terminal_pipeline_output p T g P samples selected _
    (run_pipeline p T g P samples selected T k)
  · exact DistributedExecution.run_time_le_deadline (system p g P) (algorithm p T) _ k (by exact zero_le)
  · simpa only [DistributedExecution.run_deadline, DistributedTemplate.initial] using hbudget
  · exact hk


end LongTails.Proofs.MultiscaleAggregateExecution
