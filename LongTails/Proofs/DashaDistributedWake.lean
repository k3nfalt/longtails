import LongTails.Proofs.DashaDistributedPipeline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedWake

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline

variable {p : Params}

noncomputable def afterIdle (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1)) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with wakeTime := Function.update c.wakeTime v (max c.time (timeBudget p cfg + 1)), turn := v.val + 1 }

lemma idle_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (v : Fin (p.n + 1))
    (htargets : v = 0 → (c.workers 0).targets = [])
    (hworker : ∀ i : Fin p.n, i.succ = v →
      (c.workers i.succ).pending = true ∨ (c.workers i.succ).sent = true ∨
      (c.workers i.succ).iteration = cfg.iterations) :
    Pipeline cfg f seed selected (afterIdle cfg f c v) := by
  classical
  refine { hp with outbox := ?_, control := ?_ }
  · refine { hp.outbox with ready := ?_ }
    intro ht
    have hv : (0 : Fin (p.n + 1)) ≠ v := fun he => ht (htargets he.symm)
    simpa only [afterIdle, Function.update_of_ne hv] using hp.outbox.ready ht
  · intro i
    by_cases hi : i.succ = v
    · rcases hp.control i with h | h | h | h
      · rcases hworker i hi with hb | hb | hb
        · simp [h.2.1] at hb
        · simp [h.2.2.1] at hb
        · have hk := cfg.iterations.pos
          omega
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · simpa only [afterIdle, Function.update_of_ne hi] using hp.control i

lemma idle_step_eq (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1))
    (next : OracleState (system p f)) (hdeadline : c.time ≤ c.deadline)
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .wake), next))
    (hq : (algorithm p cfg).query v (c.workers v) 0 = (.advance 0, c.workers v)) :
    step (system p f) (algorithm p cfg) c = some (afterIdle cfg f c v) := by
  have hn := (DistributedExecution.wake_event (system p f) (algorithm p cfg) c c.time v next hevent).1
  change (algorithm p cfg).query v
    ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) .wake)
    ((algorithm p cfg).clock c.time) = _ at hq
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn]
  simp only [afterIdle, algorithm, Function.update_eq_self, Function.update_idem]

noncomputable def afterStart (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers i.succ { c.workers i.succ with pending := true }
    wakeTime := Function.update c.wakeTime i.succ c.time
    turn := i.succ.val + 1
    oracle := { c.oracle with computation := (Function.update c.oracle.computation i.succ
      { c.oracle.computation i.succ with pending := some (c.time + p.h i, (c.workers i.succ).point) }) } }

lemma start_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (hk : (c.workers i.succ).iteration < cfg.iterations)
    (hflag : (c.workers i.succ).pending = false) (hs : (c.workers i.succ).sent = false) :
    Pipeline cfg f seed selected (afterStart cfg f c i) := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hi : (c.workers i.succ).iteration = 0 ∧ c.time = 0 := by
    rcases hp.control i with h | h | h | h
    · exact ⟨h.1, h.2.2.2.1⟩
    · simp [hflag] at h
    · simp [hs] at h
    · omega
  refine {
    root := ?_, workers := ?_, root_limit := ?_, outbox := ?_, arrived_incomplete := ?_
    rounds := ?_, behind := ?_, control := ?_, root_pending := ?_, pending := ?_
    arrived_current := ?_, arrived_time := ?_, links := ?_ }
  · simpa only [afterStart, Function.update_of_ne hz] using hp.root
  · intro j
    by_cases hj : j = i
    · subst j
      have hw := hp.workers i
      simp only [afterStart, Function.update_self]
      exact ⟨⟨hw.points.point, hw.points.index, hw.points.selected_point⟩,
        hw.randomness, hw.code, hw.gradient, hw.used, hw.outbox⟩
    · simpa only [afterStart, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.workers j
  · simpa only [afterStart, Function.update_of_ne hz] using hp.root_limit
  · exact broadcast_update_worker cfg f seed c hp.outbox i _ _ _ _ (fun _ => rfl)
  · simpa only [afterStart, Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [afterStart, Function.update_self, Function.update_of_ne hz] using hp.rounds i
    · simpa only [afterStart, Function.update_of_ne hz,
        Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.rounds j
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [afterStart, Function.update_self, Function.update_of_ne hz] using hp.behind i
    · simpa only [afterStart, Function.update_of_ne hz,
        Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.behind j
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [afterStart, Function.update_self, WorkerControl]
      exact Or.inr (Or.inl ⟨hk, trivial, hs⟩)
    · simpa only [afterStart, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.control j
  · simpa only [afterStart, Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [afterStart, hi.1, hi.2, roundStart]
    · simpa only [afterStart, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.pending j
  · intro j hj
    simp only [afterStart, Function.update_of_ne hz] at hj ⊢
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hp.arrived_current i hj
    · simpa only [Function.update_of_ne (fun h => he (Fin.succ_inj.mp h))] using hp.arrived_current j hj
  · intro j hj
    simp only [afterStart, Function.update_of_ne hz] at hj ⊢
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hp.arrived_time i hj
    · simpa only [Function.update_of_ne (fun h => he (Fin.succ_inj.mp h))] using hp.arrived_time j hj
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterStart, Function.update_of_ne hz, Fin.cases_zero] using hp.links 0 0
      · by_cases hj : j = i
        · subst j
          simpa only [afterStart, Function.update_of_ne hz, Function.update_self, Fin.cases_zero,
            Fin.cases_succ] using hp.links 0 i.succ
        · simpa only [afterStart, Function.update_of_ne hz, Fin.cases_zero, Fin.cases_succ,
            Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.links 0 j.succ
    · by_cases hj : j = i
      · subst j
        simpa only [afterStart, Function.update_of_ne hz, Function.update_self, Fin.cases_succ] using hp.links i.succ target
      · simpa only [afterStart, Function.update_of_ne hz, Fin.cases_succ,
          Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he))] using hp.links j.succ target

lemma start_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((i.succ, .wake), next))
    (hk : (c.workers i.succ).iteration < cfg.iterations)
    (hflag : (c.workers i.succ).pending = false) (hs : (c.workers i.succ).sent = false) :
    step (system p f) (algorithm p cfg) c = some (afterStart cfg f c i) := by
  have hn := (DistributedExecution.wake_event (system p f) (algorithm p cfg) c c.time i.succ next hevent).1
  have ho := (hp.workers i).outbox
  have hc := hp.pending i
  simp only [hflag, Bool.false_eq_true, ite_false] at hc
  have hq : (algorithm p cfg).query i.succ (c.workers i.succ) 0 =
      (.compute (.evaluate (c.workers i.succ).point), { c.workers i.succ with pending := true }) := by
    simp [algorithm, hk, hflag, hs, ho]
  change (algorithm p cfg).query i.succ
    ((algorithm p cfg).update i.succ (c.workers i.succ) ((algorithm p cfg).clock c.time) .wake)
    ((algorithm p cfg).clock c.time) = _ at hq
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn]
  simp only [afterStart, system, LongTails.Setups.StarNetwork.computation, Fin.cases_succ, hc]

lemma worker_wake_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((i.succ, .wake), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  by_cases hr : (c.workers i.succ).iteration < cfg.iterations ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false
  · exact ⟨_, start_step_eq cfg f seed selected c hp hdeadline i next hevent hr.1 hr.2.1 hr.2.2,
      start_pipeline cfg f seed selected c hp i hr.1 hr.2.1 hr.2.2⟩
  · have hq : (algorithm p cfg).query i.succ (c.workers i.succ) 0 = (.advance 0, c.workers i.succ) := by
      have hr' : ¬ ((c.workers i.succ).iteration < cfg.iterations ∧
          (!(c.workers i.succ).pending) = true ∧ (!(c.workers i.succ).sent) = true) := by simpa using hr
      simp only [algorithm, Fin.cases_succ, ite_eq_right hr']
    refine ⟨_, idle_step_eq cfg f c i.succ next hdeadline hevent hq,
      idle_pipeline cfg f seed selected c hp i.succ (fun h => False.elim (Fin.succ_ne_zero i h)) ?_⟩
    intro j hj
    have he : j = i := Fin.succ_inj.mp hj
    subst j
    rcases hp.control i with h | h | h | h
    · exact False.elim (hr ⟨by rw [h.1]; exact cfg.iterations.pos, h.2.1, h.2.2.1⟩)
    · exact Or.inl h.2.1
    · exact Or.inr (Or.inl h.2.2)
    · exact Or.inr (Or.inr h.1)

lemma root_idle_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((0, .wake), next))
    (ht : (c.workers 0).targets = []) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  have ho : (c.workers 0).outbox = none := by simpa only [ht, ite_true] using hp.outbox.message
  have hq : (algorithm p cfg).query 0 (c.workers 0) 0 = (.advance 0, c.workers 0) := by
    simp [algorithm, ho, ht]
  exact ⟨_, idle_step_eq cfg f c 0 next hdeadline hevent hq,
    idle_pipeline cfg f seed selected c hp 0 (fun _ => ht)
      (fun i hi => False.elim (Fin.succ_ne_zero i hi))⟩

lemma start_progress_strict (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n)
    (hflag : (c.workers i.succ).pending = false) :
    workerProgress i.succ (c.workers i.succ) <
      workerProgress i.succ ((afterStart cfg f c i).workers i.succ) := by
  simp [workerProgress, afterStart, hflag]

end LongTails.Proofs.DashaDistributedWake
