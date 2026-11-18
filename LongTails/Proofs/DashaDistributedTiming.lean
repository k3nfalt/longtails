import LongTails.Algorithms.DashaDistributed
import LongTails.Proofs.DistributedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedTiming

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed

variable {p : Params}

lemma event_thresholds (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) :
    ∃ times : Finset Time, ∀ time,
      (event (system p f) (algorithm p cfg) c time).isSome ↔ ∃ finish ∈ times, finish ≤ time := by
  classical
  choose times htimes using fun v => DistributedExecution.computation_thresholds ⟨p.h, p.l, p.b⟩
    (fun i x (_ : Unit) _ => gradient (f i) x) v (c.oracle.computation v)
  obtain ⟨comm, hcomm⟩ := DistributedExecution.communication_thresholds (Seed := Unit)
    ⟨p.h, p.l, p.b⟩ c.oracle.communication
  refine ⟨(Finset.univ.biUnion times) ∪ comm ∪ (Finset.univ.image c.wakeTime), ?_⟩
  intro time
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready]
  change ((∃ v, ((LongTails.Setups.StarNetwork.computation ⟨p.h, p.l, p.b⟩
    (fun i x (_ : Unit) _ => gradient (f i) x)).answer v (c.oracle.computation v) time).isSome) ∨
    ((LongTails.Setups.StarNetwork.communication (Seed := Unit) ⟨p.h, p.l, p.b⟩).answer c.oracle.communication time).isSome) ∨
    (∃ v, c.wakeTime v ≤ time) ↔ _
  simp only [htimes, hcomm, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  aesop

lemma nextTime_exists (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (hc : c.time ≤ c.deadline) :
    ∃ t, IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧
      (t = c.deadline ∨ (event (system p f) (algorithm p cfg) c t).isSome)} t := by
  obtain ⟨times, htimes⟩ := event_thresholds cfg f c
  exact DistributedExecution.nextTime_exists_of_thresholds (event (system p f) (algorithm p cfg) c)
    times c.time c.deadline hc htimes

lemma communication_submit_timely
    (s : LongTails.Setups.StarNetwork.CommunicationState p.n) (time : Time)
    (source : Fin (p.n + 1)) (query : Fin (p.n + 1) × List Bool)
    (hs : ∀ v w finish bits, s.messages v w = some (finish, bits) → time ≤ finish) :
    ∀ v w finish bits, ((communication p).submit s time source query).messages v w = some (finish, bits) → time ≤ finish := by
  unfold communication
  dsimp only
  split_ifs
  · exact DistributedExecution.communication_submit_timely (Seed := Unit) ⟨p.h, 0, 0⟩ s time source query hs
  · exact DistributedExecution.communication_submit_timely (Seed := Unit) ⟨p.h, p.l, p.b⟩ s time source query hs

def Timely (cfg : Config p) (f : Functions p)

    (c : ExecutionState (system p f) (algorithm p cfg)) : Prop :=
  (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time ≤ finish) ∧
  (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
    c.time ≤ finish) ∧ ∀ v, c.time ≤ c.wakeTime v

lemma initial_timely (cfg : Config p) (f : Functions p)
 (T : Time)
    (seed : (algorithm p cfg).Seed × (system p f).Seed) :
    Timely cfg f (initial (system p f) (algorithm p cfg) T seed) := by
  simp [Timely, initial, system, communication, Oracle.initial,
    LongTails.Setups.StarNetwork.computation, LongTails.Setups.StarNetwork.communication]

lemma jump_timely (cfg : Config p) (f : Functions p)

    (c : ExecutionState (system p f) (algorithm p cfg))
    (hc : c.time ≤ c.deadline) (htimely : Timely cfg f c) :
    Timely cfg f { c with time := nextTime (event (system p f) (algorithm p cfg) c) c.time c.deadline } := by
  let O := system p f
  let A := algorithm p cfg
  have hex := nextTime_exists cfg f c hc
  rcases htimely with ⟨hcompute, hcomm, hwake⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i finish input hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcompute i finish input hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inl
    refine ⟨i.succ, ?_⟩
    exact (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
      (fun i x (_ : Unit) _ => gradient (f i) x) i
      (c.oracle.computation i.succ) finish).mpr ⟨finish, input, hpending, le_rfl⟩
  · intro source target finish bits hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcomm source target finish bits hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inr
    exact (DistributedExecution.communication_ready (Seed := Unit) ⟨p.h, p.l, p.b⟩
      c.oracle.communication finish).mpr ⟨source, target, finish, bits, hpending, le_rfl⟩
  · intro v
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline (c.wakeTime v) hex (hwake v)
    exact (DistributedExecution.event_ready O A c (c.wakeTime v)).mpr (Or.inr ⟨v, le_rfl⟩)

lemma event_timely (cfg : Config p) (f : Functions p)

    (c : ExecutionState (system p f) (algorithm p cfg)) (htimely : Timely cfg f c)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, notification), next)) :
    Timely cfg f { c with oracle := next } := by
  classical
  rcases DistributedExecution.event_cases (system p f) (algorithm p cfg)
    c c.time v notification next hevent with horacle | ⟨_, hnext, _⟩
  · rcases htimely with ⟨hcompute, hcomm, hwake⟩
    rcases DistributedExecution.oracle_answer_cases (system p f) c.oracle next c.time v notification horacle with
      ⟨reply, state, _, ha, rfl⟩ | ⟨reply, state, _, ha, rfl⟩
    · refine ⟨?_, hcomm, hwake⟩
      intro i finish input hpending
      by_cases hv : i.succ = v
      · have hp : state.pending = some (finish, input) := by simpa [hv] using hpending
        rcases DistributedExecution.computation_answer_pending ⟨p.h, p.l, p.b⟩
          (fun i x (_ : Unit) _ => gradient (f i) x) v
          (c.oracle.computation v) state c.time reply ha with hnone | hold
        · simp [hnone] at hp
        · apply hcompute i finish input
          simpa [hv, ← hold] using hp
      · apply hcompute i finish input
        simpa [hv] using hpending
    · refine ⟨hcompute, ?_, hwake⟩
      intro source target finish bits hpending
      rcases DistributedExecution.communication_answer_pending (Seed := Unit) ⟨p.h, p.l, p.b⟩
        c.oracle.communication state c.time v reply ha source target with hnone | hold
      · simp [hnone] at hpending
      · exact hcomm source target finish bits (hold ▸ hpending)
  · simpa only [hnext] using htimely

lemma step_timely (cfg : Config p) (f : Functions p)

    (c next : ExecutionState (system p f) (algorithm p cfg))
    (htimely : Timely cfg f c)
    (hstep : step (system p f) (algorithm p cfg) c = some next) : Timely cfg f next := by
  classical
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate] at hstep
    have hc : c.time ≤ c.deadline := le_of_not_gt hlate
    cases he : event (system p f) (algorithm p cfg) c c.time with
    | none =>
        rw [he] at hstep
        by_cases hdeadline : c.time = c.deadline
        · simp only [ite_eq_left hdeadline, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdeadline] at hstep
          have hn := Option.some.inj hstep
          subst next
          exact jump_timely cfg f c hc htimely
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        have ho := event_timely cfg f c htimely v notification oracle he
        rcases ho with ⟨hcompute, hcomm, hwake⟩
        rw [he] at hstep
        cases hq : (algorithm p cfg).query v
            ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) notification)
            ((algorithm p cfg).clock c.time) with
        | mk action state =>
            simp only [hq] at hstep
            cases action with
            | compute query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨?_, hcomm, ?_⟩
                · intro i finish input hpending
                  by_cases hv : i.succ = v
                  · have hp : ((system p f).computation.submit i.succ
                        (oracle.computation i.succ) c.time query).pending = some (finish, input) := by
                      simpa [← hv] using hpending
                    exact DistributedExecution.computation_submit_timely ⟨p.h, p.l, p.b⟩
                      (fun i x (_ : Unit) _ => gradient (f i) x) i
                      (oracle.computation i.succ) c.time query (hcompute i) finish input hp
                  · apply hcompute i finish input
                    simpa [hv] using hpending
                · intro w
                  by_cases hw : w = v
                  · simp [hw]
                  · simpa [hw] using hwake w
            | communicate query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨hcompute, ?_, ?_⟩
                · exact communication_submit_timely oracle.communication c.time v
                    (query.1, query.2 ++ List.replicate clockBits false) hcomm
                · intro w
                  by_cases hw : w = v
                  · simp [hw]
                  · simpa [hw] using hwake w
            | advance target =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨hcompute, hcomm, ?_⟩
                intro w
                by_cases hw : w = v
                · simp [hw]
                · simpa [hw] using hwake w

lemma run_timely (cfg : Config p) (f : Functions p)
 (T : Time)
    (seed : (algorithm p cfg).Seed × (system p f).Seed) (k : ℕ) :
    Timely cfg f (run (system p f) (algorithm p cfg) k
      (initial (system p f) (algorithm p cfg) T seed)) := by
  have hrun : ∀ j (c : ExecutionState (system p f) (algorithm p cfg)),
      Timely cfg f c → Timely cfg f (run (system p f) (algorithm p cfg) j c) := by
    intro j
    induction j with
    | zero => intro c hc; exact hc
    | succ j ih =>
        intro c hc
        cases hs : step (system p f) (algorithm p cfg) c with
        | none => simpa only [run, hs] using hc
        | some next =>
            simpa only [run, hs] using ih next (step_timely cfg f c next hc hs)
  exact hrun k _ (initial_timely cfg f T seed)

lemma computed_at_finish (cfg : Config p) (f : Functions p)

    (c : ExecutionState (system p f) (algorithm p cfg)) (htimely : Timely cfg f c)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.oracle.computation i.succ).pending = some (c.time, input) ∧
      value = gradient (f i) input ∧
      next = { c.oracle with computation := (Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := none, used := (c.oracle.computation i.succ).used + 1 }) } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.computed_event (system p f) (algorithm p cfg)
    c c.time i.succ (.computed input value) next hevent
  obtain ⟨finish, hp, ht, hv, hs⟩ := DistributedExecution.computation_completed_data ⟨p.h, p.l, p.b⟩
    (fun i x (_ : Unit) _ => gradient (f i) x) i
    (c.oracle.computation i.succ) state c.time input value ha
  have hf : finish = c.time := le_antisymm ht (htimely.1 i finish input hp)
  subst finish
  exact ⟨hp, hv, by simpa only [hs] using hn⟩

lemma received_at_finish (cfg : Config p) (f : Functions p)

    (c : ExecutionState (system p f) (algorithm p cfg)) (htimely : Timely cfg f c)
    (source target : Fin (p.n + 1)) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((target, .received (.received source bits)), next)) :
    c.oracle.communication.messages source target = some (c.time, bits) ∧
      next = { c.oracle with communication := { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages source
          (Function.update (c.oracle.communication.messages source) target none)) } } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.received_event (system p f) (algorithm p cfg)
    c c.time target (.received source bits) next hevent
  obtain ⟨finish, hp, ht, hs⟩ := DistributedExecution.communication_received_data (Seed := Unit)
    ⟨p.h, p.l, p.b⟩ c.oracle.communication state c.time source target bits ha
  have hf : finish = c.time := le_antisymm ht (htimely.2.1 source target finish bits hp)
  subst finish
  exact ⟨hp, by simpa only [hs] using hn⟩

lemma quiet_wake_future (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg))
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none) (v : Fin (p.n + 1)) :
    c.time < c.wakeTime v := by
  apply lt_of_not_ge
  intro hw
  have he := (DistributedExecution.event_ready (system p f) (algorithm p cfg) c c.time).mpr
    (Or.inr ⟨v, hw⟩)
  simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he

lemma quiet_computation_future (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg))
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none)
    (i : Fin p.n) (finish : Time) (input : Point p)
    (hp : (c.oracle.computation i.succ).pending = some (finish, input)) : c.time < finish := by
  apply lt_of_not_ge
  intro hf
  have hc := (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
    (fun i x (_ : Unit) _ => gradient (f i) x) i (c.oracle.computation i.succ) c.time).mpr
      ⟨finish, input, hp, hf⟩
  have ho := (DistributedExecution.oracle_ready (system p f) c.oracle c.time).mpr (Or.inl ⟨i.succ, hc⟩)
  have he := (DistributedExecution.event_ready (system p f) (algorithm p cfg) c c.time).mpr (Or.inl ho)
  simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he

lemma quiet_message_future (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg))
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none)
    (source target : Fin (p.n + 1)) (finish : Time) (bits : List Bool)
    (hp : c.oracle.communication.messages source target = some (finish, bits)) : c.time < finish := by
  apply lt_of_not_ge
  intro hf
  have hc := (DistributedExecution.communication_ready (Seed := Unit) ⟨p.h, p.l, p.b⟩
    c.oracle.communication c.time).mpr ⟨source, target, finish, bits, hp, hf⟩
  have ho := (DistributedExecution.oracle_ready (system p f) c.oracle c.time).mpr (Or.inr hc)
  have he := (DistributedExecution.event_ready (system p f) (algorithm p cfg) c c.time).mpr (Or.inl ho)
  simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he

end LongTails.Proofs.DashaDistributedTiming
