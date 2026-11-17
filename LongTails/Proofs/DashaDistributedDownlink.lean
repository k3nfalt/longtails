import LongTails.Proofs.DashaDistributedComplete

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedDownlink

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedWake
open LongTails.Proofs.DashaDistributedBroadcast
open LongTails.Proofs.DashaDistributedComplete

variable {p : Params}

noncomputable def downlinkState (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (s : State p) : State p :=
  { advance p cfg s (fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j) with
    pending := decide (s.iteration + 1 < cfg.iterations) }

noncomputable def afterDownlink (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers i.succ (downlinkState cfg f seed (c.workers i.succ))
    wakeTime := Function.update c.wakeTime i.succ
      (if (c.workers i.succ).iteration + 1 < cfg.iterations then c.time else max c.time (timeBudget p cfg + 1))
    turn := i.succ.val + 1
    oracle := {
      computation := Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := (
          if (c.workers i.succ).iteration + 1 < cfg.iterations then
            some (c.time + p.h i, (downlinkState cfg f seed (c.workers i.succ)).point) else none) }
      communication := { messages := (Function.update c.oracle.communication.messages 0
        (Function.update (c.oracle.communication.messages 0) i.succ none)) } } }

lemma downlink_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (hi : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration)
    (hnot : i ∉ (c.workers 0).targets) (hs : (c.workers i.succ).sent = true)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration) :
    Pipeline cfg f seed selected (afterDownlink cfg f seed c i) := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hlimit : (c.workers i.succ).iteration + 1 ≤ cfg.iterations := hi ▸ hp.root_limit
  have hna : i ∉ (c.workers 0).arrived := by
    intro ha
    have he := (hp.arrived_current i ha).1
    omega
  have hne : (c.workers i.succ).iteration ≠ (c.workers 0).iteration := by omega
  refine {
    root := ?_, workers := ?_, root_limit := ?_, outbox := ?_, arrived_incomplete := ?_
    rounds := ?_, behind := ?_, control := ?_, root_pending := ?_, pending := ?_
    arrived_current := ?_, arrived_time := ?_, links := ?_ }
  · simpa only [afterDownlink, Function.update_of_ne hz] using hp.root
  · intro j
    by_cases hj : j = i
    · subst j
      have hw := advance_worker_data cfg f seed selected i _ _ (hp.workers i) hs
      simp only [afterDownlink, Function.update_self]
      exact ⟨⟨hw.points.point, hw.points.index, hw.points.selected_point⟩,
        hw.randomness, hw.code, hw.gradient, hw.used, hw.outbox⟩
    · simpa only [afterDownlink, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.workers j
  · simpa only [afterDownlink, Function.update_of_ne hz] using hp.root_limit
  · exact broadcast_update_worker cfg f seed c hp.outbox i _ _ _ _ (fun h => False.elim (hnot h))
  · simpa only [afterDownlink, Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j
    by_cases hj : j = i
    · subst j
      simp [afterDownlink, Function.update_of_ne hz, downlinkState, advance, hi]
    · simpa only [afterDownlink, Function.update_of_ne hz,
        Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.rounds j
  · intro j
    by_cases hj : j = i
    · subst j
      simp [afterDownlink, Function.update_of_ne hz, downlinkState, advance, hi]
    · simpa only [afterDownlink, Function.update_of_ne hz,
        Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.behind j
  · intro j
    by_cases hj : j = i
    · subst j
      by_cases hk : (c.workers i.succ).iteration + 1 < cfg.iterations
      · simp only [afterDownlink, Function.update_self, downlinkState, advance, WorkerControl,
          decide_eq_true hk]
        exact Or.inr (Or.inl ⟨hk, trivial, trivial⟩)
      · have he : (c.workers i.succ).iteration + 1 = cfg.iterations := by omega
        simp only [afterDownlink, Function.update_self, downlinkState, advance, WorkerControl,
          decide_eq_false hk]
        exact Or.inr (Or.inr (Or.inr ⟨he, trivial, trivial⟩))
    · simpa only [afterDownlink, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.control j
  · simpa only [afterDownlink, Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [afterDownlink, downlinkState, advance, hi, htime]
    · simpa only [afterDownlink, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.pending j
  · intro j hj
    simp only [afterDownlink, Function.update_of_ne hz] at hj ⊢
    have hji : j ≠ i := fun he => hna (he ▸ hj)
    simpa only [Function.update_of_ne (fun he => hji (Fin.succ_inj.mp he))] using hp.arrived_current j hj
  · intro j hj
    simp only [afterDownlink, Function.update_of_ne hz] at hj ⊢
    have hji : j ≠ i := fun he => hna (he ▸ hj)
    simpa only [Function.update_of_ne (fun he => hji (Fin.succ_inj.mp he))] using hp.arrived_time j hj
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterDownlink, Function.update_self, Function.update_of_ne hz, Fin.cases_zero] using hp.links 0 0
      · by_cases hj : j = i
        · subst j
          simp [afterDownlink, Function.update_of_ne hz, downlinkState, advance, hi]
        · simpa only [afterDownlink, Function.update_self, Function.update_of_ne hz,
            Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he)), Fin.cases_zero, Fin.cases_succ] using hp.links 0 j.succ
    · by_cases hj : j = i
      · subst j
        have hold := hp.links i.succ target
        simp only [Fin.cases_succ, hne, and_false, false_and, ite_false] at hold
        simp [afterDownlink, Function.update_of_ne hz, downlinkState, advance, hold]
      · simpa only [afterDownlink, Function.update_of_ne (Fin.succ_ne_zero j), Function.update_of_ne hz,
          Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he)), Fin.cases_succ] using hp.links j.succ target

lemma downlink_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .received (.received 0 bits)), next)) :
    step (system p f) (algorithm p cfg) c = some (afterDownlink cfg f seed c i) := by
  classical
  obtain ⟨_, _, hs, _, hb⟩ := received_broadcast_facts cfg f seed selected c hp htimely i bits next hevent
  have hn := (received_at_finish cfg f c htimely 0 i.succ bits next hevent).2
  have hk := sent_iteration_lt cfg f seed selected c hp i hs
  have hflag : (c.workers i.succ).pending = false := by
    rcases hp.control i with h | h | h | h
    · exact h.2.1
    · simp [hs] at h
    · exact h.2.1
    · exact h.2.1
  have hpend : (c.oracle.computation i.succ).pending = none := by
    simpa only [hflag, Bool.false_eq_true, ite_false] using hp.pending i
  have hdecode : LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth bits =
      fun j => ∑ a, (idealTrajectory p cfg f seed (c.workers i.succ).iteration).localCode a j := by
    rw [hb]
    exact hexact.broadcast _ hk _
  have hu : (algorithm p cfg).update i.succ (c.workers i.succ) ((algorithm p cfg).clock c.time)
      (.received (.received 0 bits)) =
      advance p cfg (c.workers i.succ)
        (fun j => ∑ a, (idealTrajectory p cfg f seed (c.workers i.succ).iteration).localCode a j) := by
    simp [algorithm, hdecode]
  by_cases hnext : (c.workers i.succ).iteration + 1 < cfg.iterations
  · have hq : (algorithm p cfg).query i.succ
        ((algorithm p cfg).update i.succ (c.workers i.succ) ((algorithm p cfg).clock c.time)
          (.received (.received 0 bits))) ((algorithm p cfg).clock c.time) =
        (.compute (.evaluate (downlinkState cfg f seed (c.workers i.succ)).point),
          downlinkState cfg f seed (c.workers i.succ)) := by
      rw [hu]
      simp [algorithm, advance, downlinkState, hnext]
    simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn]
    simp only [afterDownlink, hnext, ite_true, system, LongTails.Setups.StarNetwork.computation,
      Fin.cases_succ, hpend]
  · have hq : (algorithm p cfg).query i.succ
        ((algorithm p cfg).update i.succ (c.workers i.succ) ((algorithm p cfg).clock c.time)
          (.received (.received 0 bits))) ((algorithm p cfg).clock c.time) =
        (.advance 0, downlinkState cfg f seed (c.workers i.succ)) := by
      rw [hu]
      simp [algorithm, advance, downlinkState, hnext]
    have horacle : { c.oracle.computation i.succ with pending := none } = c.oracle.computation i.succ := by
      cases he : c.oracle.computation i.succ
      simp_all
    simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn]
    simp only [afterDownlink, hnext, ite_false, horacle, Function.update_eq_self, Function.update_idem, algorithm]

lemma downlink_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .received (.received 0 bits)), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  obtain ⟨hi, hnot, hs, ht, _⟩ := received_broadcast_facts cfg f seed selected c hp htimely i bits next hevent
  exact ⟨_, downlink_step_eq cfg f seed selected c hp hexact htimely hdeadline i bits next hevent,
    downlink_pipeline cfg f seed selected c hp i hi hnot hs ht⟩

end LongTails.Proofs.DashaDistributedDownlink
