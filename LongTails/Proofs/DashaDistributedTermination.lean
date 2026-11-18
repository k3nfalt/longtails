import LongTails.Proofs.DashaDistributedInvariant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedTermination

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedInvariant
open LongTails.Proofs.DashaDistributedWake
open LongTails.Proofs.DashaDistributedBroadcast

variable {p : Params}

def progressCap (cfg : Config p) : ℕ :=
  (2 * p.n + 1) * cfg.iterations + 2 * p.n + p.n * (4 * cfg.iterations + 3)

noncomputable def totalProgress (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : ℕ :=
  ∑ v, workerProgress v (c.workers v)

noncomputable def wakes (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : Finset (Fin (p.n + 1)) :=
  Finset.univ.filter fun v => c.wakeTime v ≤ c.deadline

noncomputable def phase (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : ℕ :=
  if c.time = c.deadline ∨ (event (system p f) (algorithm p cfg) c c.time).isSome then 0 else 1

noncomputable def rank (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : ℕ :=
  4 * (progressCap cfg - totalProgress cfg f c) + 2 * (wakes cfg f c).card + phase cfg f c

lemma totalProgress_le (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) : totalProgress cfg f c ≤ progressCap cfg := by
  classical
  obtain ⟨hr, hw⟩ := progress_bounded cfg f seed selected c hp
  have hs : (∑ i : Fin p.n, workerProgress i.succ (c.workers i.succ)) ≤ p.n * (4 * cfg.iterations + 3) := by
    calc
      _ ≤ ∑ _ : Fin p.n, (4 * (cfg.iterations : ℕ) + 3) := Finset.sum_le_sum (fun i _ => hw i)
      _ = _ := by simp
  simpa only [totalProgress, Fin.sum_univ_succ, progressCap] using Nat.add_le_add hr hs

lemma phase_le (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : phase cfg f c ≤ 1 := by
  unfold phase
  split_ifs <;> omega

lemma totalProgress_update_strict (cfg : Config p) (f : Functions p)
    (c next : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1)) (state : State p)
    (hw : next.workers = Function.update c.workers v state)
    (hstrict : workerProgress v (c.workers v) < workerProgress v state) :
    totalProgress cfg f c < totalProgress cfg f next := by
  classical
  apply Finset.sum_lt_sum
  · intro w _
    rw [hw]
    by_cases he : w = v
    · subst w
      simpa only [Function.update_self] using hstrict.le
    · simp only [Function.update_of_ne he, le_refl]
  · refine ⟨v, Finset.mem_univ v, ?_⟩
    simpa only [hw, Function.update_self] using hstrict

lemma wakes_update_le (cfg : Config p) (f : Functions p)
    (c next : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1)) (time : Time)
    (hw : next.wakeTime = Function.update c.wakeTime v time) (hd : next.deadline = c.deadline) :
    (wakes cfg f next).card ≤ (wakes cfg f c).card + 1 := by
  classical
  apply (Finset.card_le_card (show wakes cfg f next ⊆ insert v (wakes cfg f c) from ?_)).trans
    (Finset.card_insert_le _ _)
  intro w hwake
  by_cases he : w = v
  · subst w
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    simpa only [wakes, Finset.mem_filter, Finset.mem_univ, true_and, hw, hd,
      Function.update_of_ne he] using hwake

lemma wakes_idle (cfg : Config p) (f : Functions p)
    (c next : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1)) (time : Time)
    (hw : next.wakeTime = Function.update c.wakeTime v time) (hd : next.deadline = c.deadline)
    (hold : c.wakeTime v ≤ c.deadline) (hnew : c.deadline < time) :
    (wakes cfg f next).card + 1 = (wakes cfg f c).card := by
  classical
  have heq : wakes cfg f next = (wakes cfg f c).erase v := by
    ext w
    by_cases he : w = v
    · subst w
      simp [wakes, hw, hd, not_le.mpr hnew]
    · simp [wakes, hw, hd, he]
  rw [heq]
  exact Finset.card_erase_add_one (by simp [wakes, hold])

lemma rank_progress (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hn : Pipeline cfg f seed selected next)
    (hprogress : totalProgress cfg f c < totalProgress cfg f next)
    (hw : (wakes cfg f next).card ≤ (wakes cfg f c).card + 1) :
    rank cfg f next < rank cfg f c := by
  have hc := totalProgress_le cfg f seed selected c hp
  have hd := totalProgress_le cfg f seed selected next hn
  have hf := phase_le cfg f next
  unfold rank
  omega

lemma rank_idle (cfg : Config p) (f : Functions p)
    (c next : ExecutionState (system p f) (algorithm p cfg))
    (hprogress : totalProgress cfg f c = totalProgress cfg f next)
    (hw : (wakes cfg f next).card + 1 = (wakes cfg f c).card) :
    rank cfg f next < rank cfg f c := by
  have hf := phase_le cfg f next
  unfold rank
  omega

lemma rank_jump (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg))
    (hc : c.time ≤ c.deadline) (hquiet : event (system p f) (algorithm p cfg) c c.time = none)
    (hne : c.time ≠ c.deadline) :
    rank cfg f { c with time := nextTime (event (system p f) (algorithm p cfg) c) c.time c.deadline } < rank cfg f c := by
  have hex := nextTime_exists cfg f c hc
  have hr := (DistributedExecution.nextTime_spec (event (system p f) (algorithm p cfg) c) c.time c.deadline hex).1.2.2
  have hold : phase cfg f c = 1 := by simp [phase, hquiet, hne]
  have hnew : phase cfg f { c with time := nextTime (event (system p f) (algorithm p cfg) c) c.time c.deadline } = 0 := by
    unfold phase
    apply ite_eq_left
    simpa only [event] using hr
  simp only [rank, totalProgress, wakes, hold, hnew]
  omega

lemma rank_of_update_progress (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, notification), oracle))
    (hstep : step (system p f) (algorithm p cfg) c = some next)
    (hstrict : workerProgress v (c.workers v) < workerProgress v
      ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) notification)) :
    rank cfg f next < rank cfg f c := by
  have hn := step_pipeline cfg f seed selected c next hp hexact hpos htimely hstep
  cases hq : (algorithm p cfg).query v
      ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) notification)
      ((algorithm p cfg).clock c.time) with
  | mk action state =>
      have hfields := DistributedExecution.step_event_state (system p f) (algorithm p cfg)
        c next v notification oracle action state hevent hq hstep
      have hstrict' : workerProgress v (c.workers v) < workerProgress v state := by
        simpa only [hq] using hstrict.trans_le (query_progress cfg v _ ((algorithm p cfg).clock c.time))
      exact rank_progress cfg f seed selected c next hp hn
        (totalProgress_update_strict cfg f c next v state hfields.1 hstrict')
        (wakes_update_le cfg f c next v _ hfields.2
          (DistributedExecution.step_deadline (system p f) (algorithm p cfg) c next hstep))

lemma computed_update_progress (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (v : Fin (p.n + 1)) (reply : ComputeReply p) (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .computed reply), oracle)) :
    workerProgress v (c.workers v) < workerProgress v
      ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) (.computed reply)) := by
  cases reply with
  | computed input value =>
      induction v using Fin.cases with
      | zero =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p f) (algorithm p cfg)
            c c.time 0 (.computed input value) oracle hevent
          simp [system, LongTails.Setups.StarNetwork.computation] at ha
      | succ i =>
          obtain ⟨hflag, hs, _, _, _, _⟩ := computed_facts cfg f seed selected c hp htimely i input value oracle hevent
          exact computed_progress cfg i _ value hflag (hp.workers i).outbox hs

lemma received_update_progress (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (v : Fin (p.n + 1)) (reply : CommReply p) (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .received reply), oracle)) :
    workerProgress v (c.workers v) < workerProgress v
      ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) (.received reply)) := by
  cases reply with
  | received source bits =>
      induction v using Fin.cases with
      | zero =>
          induction source using Fin.cases with
          | zero =>
              have hm := (received_at_finish cfg f c htimely 0 0 bits oracle hevent).1
              rw [hp.links 0 0] at hm
              simp only [Fin.cases_zero, reduceCtorEq] at hm
          | succ i =>
              obtain ⟨_, _, hi, _, _⟩ := received_worker_facts cfg f seed selected c hp htimely i bits oracle hevent
              change workerProgress 0 (c.workers 0) < workerProgress 0 (accept p cfg (c.workers 0) i.succ bits)
              exact accept_progress cfg _ i bits hi
      | succ i =>
          induction source using Fin.cases with
          | zero =>
              obtain ⟨_, _, hs, _, _⟩ := received_broadcast_facts cfg f seed selected c hp htimely i bits oracle hevent
              have hflag : (c.workers i.succ).pending = false := by
                rcases hp.control i with h | h | h | h
                · exact h.2.1
                · simp [hs] at h
                · exact h.2.1
                · exact h.2.1
              simp only [algorithm, Fin.succ_ne_zero, ite_false, ite_true]
              exact advance_progress cfg i _ _ hflag (hp.workers i).outbox hs
          | succ j =>
              have hm := (received_at_finish cfg f c htimely j.succ i.succ bits oracle hevent).1
              rw [hp.links j.succ i.succ] at hm
              simp only [Fin.cases_succ, Fin.succ_ne_zero, false_and, ite_false, reduceCtorEq] at hm

lemma rank_of_total_progress (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, notification), oracle))
    (hstep : step (system p f) (algorithm p cfg) c = some next)
    (hstrict : totalProgress cfg f c < totalProgress cfg f next) : rank cfg f next < rank cfg f c := by
  have hn := step_pipeline cfg f seed selected c next hp hexact hpos htimely hstep
  cases hq : (algorithm p cfg).query v
      ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) notification)
      ((algorithm p cfg).clock c.time) with
  | mk action state =>
      have hfields := DistributedExecution.step_event_state (system p f) (algorithm p cfg)
        c next v notification oracle action state hevent hq hstep
      exact rank_progress cfg f seed selected c next hp hn hstrict
        (wakes_update_le cfg f c next v _ hfields.2
          (DistributedExecution.step_deadline (system p f) (algorithm p cfg) c next hstep))

lemma idle_rank_event (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1))
    (hdeadline : c.time ≤ c.deadline) (hbudget : c.deadline ≤ timeBudget p cfg)
    (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .wake), oracle)) :
    rank cfg f (afterIdle cfg f c v) < rank cfg f c := by
  have hold := ((DistributedExecution.wake_event (system p f) (algorithm p cfg) c c.time v oracle hevent).2).trans hdeadline
  apply rank_idle cfg f c (afterIdle cfg f c v) rfl
  apply wakes_idle cfg f c (afterIdle cfg f c v) v _ rfl rfl hold
  exact lt_of_lt_of_le (lt_of_le_of_lt hbudget (lt_add_of_pos_right _ (by norm_num))) (le_max_right _ _)

lemma wake_rank (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c)
    (hdeadline : c.time ≤ c.deadline) (hbudget : c.deadline ≤ timeBudget p cfg)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .wake), oracle))
    (hstep : step (system p f) (algorithm p cfg) c = some next) : rank cfg f next < rank cfg f c := by
  induction v using Fin.cases with
  | zero =>
      cases ht : (c.workers 0).targets with
      | nil =>
          have ho : (c.workers 0).outbox = none := by simpa only [ht, ite_true] using hp.outbox.message
          have hq : (algorithm p cfg).query 0 (c.workers 0) 0 = (.advance 0, c.workers 0) := by simp [algorithm, ho, ht]
          have hn := idle_step_eq cfg f c 0 oracle hdeadline hevent hq
          have heq : next = afterIdle cfg f c 0 := Option.some.inj (hstep.symm.trans hn)
          rw [heq]
          exact idle_rank_event cfg f c 0 hdeadline hbudget oracle hevent
      | cons i rest =>
          have hn := send_step_eq cfg f seed selected c hp hdeadline i rest ht oracle hevent
          have heq : next = afterSend cfg f seed c i rest := Option.some.inj (hstep.symm.trans hn)
          apply rank_of_total_progress cfg f seed selected c next hp hexact hpos htimely 0 .wake oracle hevent hstep
          rw [heq]
          apply totalProgress_update_strict cfg f c _ 0 _ rfl
          simpa only [afterSend, Function.update_self] using send_progress_strict cfg f seed selected c hp i rest ht
  | succ i =>
      by_cases hr : (c.workers i.succ).iteration < cfg.iterations ∧
          (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false
      · have hn := start_step_eq cfg f seed selected c hp hdeadline i oracle hevent hr.1 hr.2.1 hr.2.2
        have heq : next = afterStart cfg f c i := Option.some.inj (hstep.symm.trans hn)
        apply rank_of_total_progress cfg f seed selected c next hp hexact hpos htimely i.succ .wake oracle hevent hstep
        rw [heq]
        apply totalProgress_update_strict cfg f c _ i.succ _ rfl
        simpa only [afterStart, Function.update_self] using start_progress_strict cfg f c i hr.2.1
      · have hr' : ¬ ((c.workers i.succ).iteration < cfg.iterations ∧
            (!(c.workers i.succ).pending) = true ∧ (!(c.workers i.succ).sent) = true) := by simpa using hr
        have hq : (algorithm p cfg).query i.succ (c.workers i.succ) 0 = (.advance 0, c.workers i.succ) := by
          simp only [algorithm, Fin.cases_succ, ite_eq_right hr']
        have hn := idle_step_eq cfg f c i.succ oracle hdeadline hevent hq
        have heq : next = afterIdle cfg f c i.succ := Option.some.inj (hstep.symm.trans hn)
        rw [heq]
        exact idle_rank_event cfg f c i.succ hdeadline hbudget oracle hevent

lemma step_rank (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c next : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) (htimely : Timely cfg f c)
    (hdeadline : c.time ≤ c.deadline) (hbudget : c.deadline ≤ timeBudget p cfg)
    (hstep : step (system p f) (algorithm p cfg) c = some next) : rank cfg f next < rank cfg f c := by
  cases he : event (system p f) (algorithm p cfg) c c.time with
  | none =>
      simp only [step, ite_eq_right (not_lt.mpr hdeadline), he] at hstep
      split_ifs at hstep with ht
      have hn := Option.some.inj hstep
      subst next
      exact rank_jump cfg f c hdeadline he ht
  | some value =>
      rcases value with ⟨⟨v, notification⟩, oracle⟩
      cases notification with
      | wake => exact wake_rank cfg f seed selected c next hp hexact hpos htimely hdeadline hbudget v oracle he hstep
      | computed reply =>
          exact rank_of_update_progress cfg f seed selected c next hp hexact hpos htimely v (.computed reply) oracle he hstep
            (computed_update_progress cfg f seed selected c hp htimely v reply oracle he)
      | received reply =>
          exact rank_of_update_progress cfg f seed selected c next hp hexact hpos htimely v (.received reply) oracle he hstep
            (received_update_progress cfg f seed selected c hp htimely v reply oracle he)

lemma finiteEvents (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) :
    FiniteEvents (system p f) (algorithm p cfg) (timeBudget p cfg) ((selected, seed), ()) := by
  intro T hT
  let Inv := fun c : ExecutionState (system p f) (algorithm p cfg) =>
    Pipeline cfg f seed selected c ∧ Timely cfg f c ∧ c.time ≤ c.deadline ∧ c.deadline ≤ timeBudget p cfg
  apply DistributedExecution.termination_of_rank (system p f) (algorithm p cfg) Inv (rank cfg f)
  · intro c next hc hs
    rcases hc with ⟨hp, ht, hd, hb⟩
    refine ⟨⟨step_pipeline cfg f seed selected c next hp hexact hpos ht hs,
      step_timely cfg f c next ht hs,
      DistributedExecution.step_time_le_deadline (system p f) (algorithm p cfg) c next hd hs, ?_⟩,
      step_rank cfg f seed selected c next hp hexact hpos ht hd hb hs⟩
    simpa only [DistributedExecution.step_deadline (system p f) (algorithm p cfg) c next hs] using hb
  · exact ⟨initial_pipeline cfg f seed selected T, initial_timely cfg f T ((selected, seed), ()),
      by simp [initial], hT⟩

lemma execute_eq_ideal (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (hpos : ∀ i, 0 < p.h i) :
    execute (system p f) (algorithm p cfg) (timeBudget p cfg) (selected, seed) () = idealOutput p cfg f (selected, seed) :=
  execute_eq_ideal_of_finite cfg f seed selected hexact hpos (finiteEvents cfg f seed selected hexact hpos)

end LongTails.Proofs.DashaDistributedTermination
