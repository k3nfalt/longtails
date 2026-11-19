import LongTails.Algorithms.MultiscaleAggregateProtocol
import LongTails.Proofs.DistributedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

def Timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget)) : Prop :=
  (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time ≤ finish) ∧
  (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
    c.time ≤ finish) ∧ ∀ v, c.time ≤ c.wakeTime v

lemma initial_timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (seed : (algorithm p budget).Seed × (system p g P).Seed) :
    Timely p budget g P (DistributedTemplate.initial (system p g P) (algorithm p budget) T seed) := by
  simp [Timely, DistributedTemplate.initial, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
    LongTails.Setups.StarNetwork.computation, LongTails.Setups.StarNetwork.communication]

lemma jump_timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget))
    (hc : c.time ≤ c.deadline) (htimely : Timely p budget g P c) :
    Timely p budget g P { c with time := nextTime (event (system p g P) (algorithm p budget) c) c.time c.deadline } := by
  let O := system p g P
  let A := algorithm p budget
  have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p) k => g i x (samples i k)) P A c hc
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
      (fun i x (samples : Samples p) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) finish).mpr ⟨finish, input, hpending, le_rfl⟩
  · intro source target finish bits hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcomm source target finish bits hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inr
    exact (DistributedExecution.communication_ready (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication finish).mpr ⟨source, target, finish, bits, hpending, le_rfl⟩
  · intro v
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline (c.wakeTime v) hex (hwake v)
    exact (DistributedExecution.event_ready O A c (c.wakeTime v)).mpr (Or.inr ⟨v, le_rfl⟩)

lemma event_timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget)) (htimely : Timely p budget g P c)
    (v : Fin (p.n + 1)) (notification : Event (LongTails.Setups.DistributedAggregateSmoothNonconvex.ComputeReply p) (LongTails.Setups.DistributedAggregateSmoothNonconvex.CommReply p))
    (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p budget) c c.time = some ((v, notification), next)) :
    Timely p budget g P { c with oracle := next } := by
  classical
  rcases DistributedExecution.event_cases (system p g P) (algorithm p budget)
    c c.time v notification next hevent with horacle | ⟨_, hnext, _⟩
  · rcases htimely with ⟨hcompute, hcomm, hwake⟩
    rcases DistributedExecution.oracle_answer_cases (system p g P) c.oracle next c.time v notification horacle with
      ⟨reply, state, _, ha, rfl⟩ | ⟨reply, state, _, ha, rfl⟩
    · refine ⟨?_, hcomm, hwake⟩
      intro i finish input hpending
      by_cases hv : i.succ = v
      · have hp : state.pending = some (finish, input) := by simpa [hv] using hpending
        rcases DistributedExecution.computation_answer_pending ⟨p.h, p.l, p.b⟩
          (fun i x (samples : Samples p) k => g i x (samples i k)) v
          (c.oracle.computation v) state c.time reply ha with hnone | hold
        · simp [hnone] at hp
        · apply hcompute i finish input
          simpa [hv, ← hold] using hp
      · apply hcompute i finish input
        simpa [hv] using hpending
    · refine ⟨hcompute, ?_, hwake⟩
      intro source target finish bits hpending
      rcases DistributedExecution.communication_answer_pending (Seed := Samples p) ⟨p.h, p.l, p.b⟩
        c.oracle.communication state c.time v reply ha source target with hnone | hold
      · simp [hnone] at hpending
      · exact hcomm source target finish bits (hold ▸ hpending)
  · simpa only [hnext] using htimely

lemma step_timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c next : ExecutionState (system p g P) (algorithm p budget))
    (htimely : Timely p budget g P c)
    (hstep : step (system p g P) (algorithm p budget) c = some next) : Timely p budget g P next := by
  classical
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate] at hstep
    have hc : c.time ≤ c.deadline := le_of_not_gt hlate
    cases he : event (system p g P) (algorithm p budget) c c.time with
    | none =>
        rw [he] at hstep
        by_cases hdeadline : c.time = c.deadline
        · simp only [ite_eq_left hdeadline, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdeadline] at hstep
          have hn := Option.some.inj hstep
          subst next
          exact jump_timely p budget g P c hc htimely
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        have ho := event_timely p budget g P c htimely v notification oracle he
        rcases ho with ⟨hcompute, hcomm, hwake⟩
        rw [he] at hstep
        cases hq : (algorithm p budget).query v
            ((algorithm p budget).update v (c.workers v) ((algorithm p budget).clock c.time) notification)
            ((algorithm p budget).clock c.time) with
        | mk action state =>
            simp only [hq] at hstep
            cases action with
            | compute query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨?_, hcomm, ?_⟩
                · intro i finish input hpending
                  by_cases hv : i.succ = v
                  · have hp : ((system p g P).computation.submit i.succ
                        (oracle.computation i.succ) c.time query).pending = some (finish, input) := by
                      simpa [← hv] using hpending
                    exact DistributedExecution.computation_submit_timely ⟨p.h, p.l, p.b⟩
                      (fun i x (samples : Samples p) k => g i x (samples i k)) i
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
                · exact DistributedExecution.communication_submit_timely (Seed := Samples p)
                    ⟨p.h, p.l, p.b⟩ oracle.communication c.time v
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

lemma run_timely (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (seed : (algorithm p budget).Seed × (system p g P).Seed) (k : ℕ) :
    Timely p budget g P (run (system p g P) (algorithm p budget) k
      (DistributedTemplate.initial (system p g P) (algorithm p budget) T seed)) := by
  have hrun : ∀ j (c : ExecutionState (system p g P) (algorithm p budget)),
      Timely p budget g P c → Timely p budget g P (run (system p g P) (algorithm p budget) j c) := by
    intro j
    induction j with
    | zero => intro c hc; exact hc
    | succ j ih =>
        intro c hc
        cases hs : step (system p g P) (algorithm p budget) c with
        | none => simpa only [run, hs] using hc
        | some next =>
            simpa only [run, hs] using ih next (step_timely p budget g P c next hc hs)
  exact hrun k _ (initial_timely p budget g P T seed)

lemma computed_at_finish (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget)) (htimely : Timely p budget g P c)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p budget) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.oracle.computation i.succ).pending = some (c.time, input) ∧
      value = g i input ((c.oracle.computation i.succ).seed i (c.oracle.computation i.succ).used) ∧
      next = { c.oracle with computation := (Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := none, used := (c.oracle.computation i.succ).used + 1 }) } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.computed_event (system p g P) (algorithm p budget)
    c c.time i.succ (.computed input value) next hevent
  obtain ⟨finish, hp, ht, hv, hs⟩ := DistributedExecution.computation_completed_data ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p) k => g i x (samples i k)) i
    (c.oracle.computation i.succ) state c.time input value ha
  have hf : finish = c.time := le_antisymm ht (htimely.1 i finish input hp)
  subst finish
  exact ⟨hp, hv, by simpa only [hs] using hn⟩

lemma received_at_finish (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget)) (htimely : Timely p budget g P c)
    (source target : Fin (p.n + 1)) (bits : List Bool) (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p budget) c c.time =
      some ((target, .received (.received source bits)), next)) :
    c.oracle.communication.messages source target = some (c.time, bits) ∧
      next = { c.oracle with communication := { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages source
          (Function.update (c.oracle.communication.messages source) target none)) } } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.received_event (system p g P) (algorithm p budget)
    c c.time target (.received source bits) next hevent
  obtain ⟨finish, hp, ht, hs⟩ := DistributedExecution.communication_received_data (Seed := Samples p)
    ⟨p.h, p.l, p.b⟩ c.oracle.communication state c.time source target bits ha
  have hf : finish = c.time := le_antisymm ht (htimely.2.1 source target finish bits hp)
  subst finish
  exact ⟨hp, by simpa only [hs] using hn⟩

lemma quiet_future (p : Params) (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p budget))
    (hquiet : event (system p g P) (algorithm p budget) c c.time = none) :
    (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time < finish) ∧
    (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
      c.time < finish) ∧ ∀ v, c.time < c.wakeTime v := by
  have hnot : ¬ (event (system p g P) (algorithm p budget) c c.time).isSome := by simp [hquiet]
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready] at hnot
  refine ⟨?_, ?_, ?_⟩
  · intro i finish input hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inl ⟨i.succ, ?_⟩)
    exact (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
      (fun i x (samples : Samples p) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) c.time).mpr ⟨finish, input, hp, ht⟩
  · intro source target finish bits hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inr ?_)
    exact (DistributedExecution.communication_ready (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time).mpr ⟨source, target, finish, bits, hp, ht⟩
  · intro v
    exact lt_of_not_ge (fun ht => hnot (Or.inr ⟨v, ht⟩))

end LongTails.Proofs.MultiscaleAggregateExecution
