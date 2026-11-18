import LongTails.Proofs.DashaDistributedBroadcast

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedReceive

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedWake
open LongTails.Proofs.DashaDistributedBroadcast

variable {p : Params}

noncomputable def afterPartial (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers 0 { c.workers 0 with
      accumulator := (c.workers 0).accumulator + wireIncrement cfg f seed (c.workers 0).iteration i
      arrived := insert i (c.workers 0).arrived }
    wakeTime := Function.update c.wakeTime 0 c.time
    turn := 1
    oracle := { c.oracle with communication := {
      messages := Function.update c.oracle.communication.messages i.succ
        (Function.update (c.oracle.communication.messages i.succ) 0 none) } } }

lemma partial_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (hi : i ∉ (c.workers 0).arrived)
    (hall : insert i (c.workers 0).arrived ≠ Finset.univ)
    (haligned : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + p.h i +
      uploadTime p cfg (c.workers 0).iteration) :
    Pipeline cfg f seed selected (afterPartial cfg f seed c i) := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  refine {
    root := ?_, workers := ?_, root_limit := ?_, outbox := ?_, arrived_incomplete := ?_
    rounds := ?_, behind := ?_, control := ?_, root_pending := ?_, pending := ?_
    arrived_current := ?_, arrived_time := ?_, links := ?_ }
  · simp only [afterPartial, Function.update_self]
    have hr := hp.root
    exact ⟨⟨hr.points.point, hr.points.index, hr.points.selected_point⟩, hr.randomness, hr.code,
      accumulated_insert cfg f seed selected _ hr i hi⟩
  · intro j
    simpa only [afterPartial, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simpa only [afterPartial, Function.update_self] using hp.root_limit
  · constructor
    · simpa only [afterPartial, Function.update_self] using hp.outbox.message
    · simpa only [afterPartial, Function.update_self] using hp.outbox.nodup
    · intro j
      simpa only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.outbox.queued j
    · simp [afterPartial]
    · simpa only [afterPartial, Function.update_self] using hp.outbox.finish
  · simpa only [afterPartial, Function.update_self] using hall
  · intro j
    simpa only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.rounds j
  · intro j
    simpa only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.behind j
  · intro j
    simpa only [afterPartial, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [afterPartial, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · intro j hj
    simp only [afterPartial, Function.update_self, Finset.mem_insert] at hj
    simp only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)]
    rcases hj with rfl | hj
    · exact ⟨haligned, hs⟩
    · exact hp.arrived_current j hj
  · intro j hj
    simp only [afterPartial, Function.update_self, Finset.mem_insert] at hj
    simp only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)]
    rcases hj with rfl | hj
    · simpa only [haligned] using htime.ge
    · exact hp.arrived_time j hj
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterPartial, Function.update_self, Function.update_of_ne hz, Fin.cases_zero] using hp.links 0 0
      · simpa only [afterPartial, Function.update_self, Function.update_of_ne hz,
          Function.update_of_ne (Fin.succ_ne_zero j), Fin.cases_zero, Fin.cases_succ] using hp.links 0 j.succ
    · by_cases hj : j = i
      · subst j
        by_cases ht : target = 0
        · subst target
          simp [afterPartial]
        · have hold := hp.links i.succ target
          simp only [Fin.cases_succ, ht, false_and, ite_false] at hold
          simp [afterPartial, ht, hold]
      · simpa only [afterPartial, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j),
          Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he)), Fin.cases_succ,
          Finset.mem_insert, hj, false_or] using hp.links j.succ target

lemma partial_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (hpos : 0 < p.h i) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next))
    (hall : insert i (c.workers 0).arrived ≠ Finset.univ) :
    step (system p f) (algorithm p cfg) c = some (afterIdle cfg f (afterPartial cfg f seed c i) 0) := by
  classical
  obtain ⟨haligned, hs, hi, _, hb⟩ := received_worker_facts cfg f seed selected c hp htimely i bits next hevent
  have hn := (received_at_finish cfg f c htimely i.succ 0 bits next hevent).2
  have ht := received_upload_targets_empty cfg f seed selected c hp htimely i hpos bits next hevent
  have ho : (c.workers 0).outbox = none := by simpa only [ht, ite_true] using hp.outbox.message
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← haligned]
    exact sent_iteration_lt cfg f seed selected c hp i hs
  have hw := hexact.worker _ hk i (List.replicate clockBits false)
  have ha : accept p cfg (c.workers 0) i.succ bits =
      { c.workers 0 with
        accumulator := (c.workers 0).accumulator + wireIncrement cfg f seed (c.workers 0).iteration i
        arrived := insert i (c.workers 0).arrived } := by
    simp only [accept, Fin.cases_succ, ite_eq_left hi, hp.root.randomness, hb, haligned, hw, ite_eq_right hall]
  have hq : (algorithm p cfg).query 0
      ((algorithm p cfg).update 0 (c.workers 0) ((algorithm p cfg).clock c.time)
        (.received (.received i.succ bits))) ((algorithm p cfg).clock c.time) =
      (.advance 0, accept p cfg (c.workers 0) i.succ bits) := by
    change (algorithm p cfg).query 0 (accept p cfg (c.workers 0) i.succ bits) 0 = _
    rw [ha]
    simp [algorithm, ho, ht]
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn, ha]
  simp only [afterIdle, afterPartial, algorithm, Function.update_idem]

lemma partial_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (hpos : 0 < p.h i) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next))
    (hall : insert i (c.workers 0).arrived ≠ Finset.univ) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  obtain ⟨haligned, hs, hi, htime, _⟩ := received_worker_facts cfg f seed selected c hp htimely i bits next hevent
  have ht := received_upload_targets_empty cfg f seed selected c hp htimely i hpos bits next hevent
  have hpartial := partial_pipeline cfg f seed selected c hp i hi hall haligned hs (by simpa only [haligned] using htime)
  refine ⟨_, partial_step_eq cfg f seed selected c hp hexact htimely hdeadline i hpos bits next hevent hall,
    idle_pipeline cfg f seed selected _ hpartial 0 ?_ (fun j hj => False.elim (Fin.succ_ne_zero j hj))⟩
  intro _
  simpa only [afterPartial, Function.update_self] using ht

end LongTails.Proofs.DashaDistributedReceive
