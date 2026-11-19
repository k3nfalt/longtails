import LongTails.Proofs.MultiscaleAggregatePipeline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

noncomputable abbrev localPacket (p : Params) (k : ℕ) (v : Point p) := packet p k (localCode p v)

lemma completed_output (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (hk : (c.workers 0).iteration = (rounds p)) :
    (algorithm p T).output (c.workers (algorithm p T).root) =
      output p g (selected, samples) :=
  by
  change (c.workers 0).selected = _
  rw [hc.root.selected_point, ite_eq_left (by rw [hk]; exact selected.isLt.le)]
  rfl

lemma broadcast_arrived_empty (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (hh : ∀ i, 0 < p.h i)
    (htargets : (c.workers 0).targets ≠ []) : (c.workers 0).arrived = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have ha := hc.arrived_time i hi
  have ht := hc.broadcast_time htargets
  have hp : (0 : Time) < ((batch p i) : Time) * p.h i :=
    mul_pos (by exact_mod_cast (MultiscaleAggregateBudget.batch_pos (p := p) i)) (hh i)
  have hstart : c.time ≤ roundStart p (c.workers 0).iteration := by
    rw [← ht]
    exact le_add_of_nonneg_right (by positivity)
  have hbefore : roundStart p (c.workers 0).iteration + (batch p i) * p.h i ≤ c.time :=
    (le_add_of_nonneg_right (by positivity)).trans ha
  have hlt : roundStart p (c.workers 0).iteration <
      roundStart p (c.workers 0).iteration + (batch p i) * p.h i := by
    exact lt_add_of_pos_right _ hp
  exact (not_lt_of_ge (hbefore.trans hstart)) hlt

lemma quiet_targets_empty (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (hquiet : event (system p g P) (algorithm p T) c c.time = none) :
    (c.workers 0).targets = [] := by
  by_contra ht
  exact (not_lt_of_ge (hc.targets_ready ht)) ((quiet_future p T g P c hquiet).2.2 0)

lemma jump_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (hquiet : event (system p g P) (algorithm p T) c c.time = none) :
    Pipeline p T g P samples selected
      { c with time := nextTime (event (system p g P) (algorithm p T) c) c.time c.deadline } := by
  have ht := quiet_targets_empty p T g P samples selected c hc hquiet
  refine { hc with targets_ready := ?_, broadcast_time := ?_, control := ?_, arrived_time := ?_ }
  · simp only [ht, ne_eq, not_true_eq_false, false_implies]
  · simp only [ht, ne_eq, not_true_eq_false, false_implies]
  · intro i
    rcases hc.control i with hinit | hworking | hwaiting
    · have hw := (quiet_future p T g P c hquiet).2.2 i.succ
      rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at hw
      exact (lt_irrefl _ hw).elim
    · exact Or.inr (Or.inl hworking)
    · exact Or.inr (Or.inr hwaiting)
  · intro i hi
    exact (hc.arrived_time i hi).trans (DistributedExecution.nextTime_ge _ _ _)

lemma worker_query_compute (p : Params) (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading)
    (hk : s.iteration < (rounds p)) (hp : s.pending = false) (hj : s.samples < (batch p i)) :
    (algorithm p T).query i.succ s clock = (.compute (.evaluate s.model.point), { s with pending := true }) := by
  simp [algorithm, hk, hp, hj]

lemma worker_query_send (p : Params) (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading)
    (hk : s.iteration < (rounds p)) (hp : s.pending = false) (hj : s.samples = (batch p i))
    (hs : s.sent = false) :
    (algorithm p T).query i.succ s clock =
      (.communicate (0, localPacket p s.iteration (((batch p i) : ℝ)⁻¹ • s.accumulator)),
        { s with sent := true }) := by
  simp [algorithm, hk, hp, hj, hs]

lemma query_advance_state (p : Params) (T : Time)
    (s next : State p) (v : Fin (p.n + 1)) (clock target : ClockReading)
    (hq : (algorithm p T).query v s clock = (.advance target, next)) : next = s := by
  induction v using Fin.cases with
  | zero =>
      cases ht : s.targets <;> simp_all [algorithm]
  | succ i =>
      simp only [algorithm, Fin.cases_succ] at hq
      split_ifs at hq <;> simp_all

lemma idle_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c)
    (v : Fin (p.n + 1)) (clock target : ClockReading) (next : State p)
    (hq : (algorithm p T).query v (c.workers v) clock = (.advance target, next)) :
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers v next
        wakeTime := Function.update c.wakeTime v (max c.time ((algorithm p T).timer target))
        turn := v.val + 1 } := by
  classical
  have hn := query_advance_state p T (c.workers v) next v clock target hq
  subst next
  rw [Function.update_eq_self]
  refine { hc with targets_ready := ?_, control := ?_ }
  · intro ht
    by_cases hv : (0 : Fin (p.n + 1)) = v
    · subst v
      cases hs : (c.workers 0).targets with
      | nil => exact (ht hs).elim
      | cons i rest => simp [algorithm, hs] at hq
    · simpa only [Function.update_of_ne hv] using hc.targets_ready ht
  · intro i
    by_cases hv : i.succ = v
    · rcases hc.control i with hinit | hworking | hwaiting
      · have hk : (c.workers i.succ).iteration < (rounds p) := by
          rw [hinit.1]
          exact (rounds_pos p)
        have hj : (c.workers i.succ).samples < (batch p i) := by
          rw [hinit.2.1]
          exact (MultiscaleAggregateBudget.batch_pos (p := p) i)
        have hcompute := worker_query_compute p T (c.workers i.succ) i clock hk hinit.2.2.1 hj
        rw [← hv, hcompute] at hq
        cases congrArg Prod.fst hq
      · exact Or.inr (Or.inl hworking)
      · exact Or.inr (Or.inr hwaiting)
    · simpa only [Function.update_of_ne hv] using hc.control i

lemma start_worker_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0) :
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers i.succ { c.workers i.succ with pending := true }
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with computation := (Function.update c.oracle.computation i.succ
          { c.oracle.computation i.succ with pending := some (c.time + p.h i, (c.workers i.succ).model.point) }) } } := by
  classical
  have hw : Function.update c.workers i.succ { c.workers i.succ with pending := true } =
      fun v => { c.workers v with pending := if v = i.succ then true else (c.workers v).pending } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have ho : Function.update c.oracle.computation i.succ
      { c.oracle.computation i.succ with pending := some (c.time + p.h i, (c.workers i.succ).model.point) } =
      fun v => { c.oracle.computation v with pending := (if v = i.succ then
        some (c.time + p.h i, (c.workers i.succ).model.point) else (c.oracle.computation v).pending) } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have hwake : Function.update c.wakeTime i.succ c.time = c.wakeTime := by
    rw [hinit.2.2.2.2.1.trans hinit.2.2.2.2.2.symm, Function.update_eq_self]
  rw [hw, ho, hwake]
  refine { hc with
    root := ⟨⟨hc.root.model, hc.root.index, hc.root.selected_point⟩, hc.root.total⟩
    workers := fun j => ⟨(hc.workers j).model,
      (hc.workers j).count, (hc.workers j).accumulator⟩
    control := ?_
    root_pending := ?_
    pending := ?_ }
  · intro j
    by_cases hj : j = i
    · subst j
      apply Or.inr
      apply Or.inl
      refine ⟨?_, ?_, by simp, hinit.2.2.2.1⟩
      · simpa only [hinit.1] using (rounds_pos p)
      · simpa only [hinit.2.1] using (MultiscaleAggregateBudget.batch_pos (p := p) i)
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [WorkerControl, ite_eq_right hs] using hc.control j
  · have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [hinit.1, hinit.2.1, hinit.2.2.2.2.1, roundStart_zero]
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [ite_eq_right hs] using hc.pending j

lemma pending_worker (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true) :
    (c.workers i.succ).iteration < (rounds p) ∧ (c.workers i.succ).samples < (batch p i) ∧
      (c.workers i.succ).sent = false ∧ (c.workers i.succ).iteration = (c.workers 0).iteration := by
  have hcontrol := hc.control i
  simp only [WorkerControl, hpending, Bool.true_eq_false, false_and, and_false, false_or,
    true_and, or_false] at hcontrol
  obtain ⟨hk, hj, hs⟩ := hcontrol
  refine ⟨hk, hj, hs, ?_⟩
  have hle := (hc.synchronized i).1
  by_contra hne
  have hbehind := (hc.behind i (lt_of_le_of_ne hle hne)).2
  rw [hs] at hbehind
  cases hbehind

lemma computed_worker_facts (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T)) (hp : Pipeline p T g P samples selected c)
    (htimely : Timely p T g P c) (i : Fin p.n) (input value : Point p)
    (next : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.workers i.succ).pending = true ∧ input = (c.workers i.succ).model.point ∧
      c.time = roundStart p (c.workers i.succ).iteration +
        ((c.workers i.succ).samples + 1) * p.h i ∧
      value = g i (c.workers i.succ).model.point
        (samples i ((c.workers i.succ).iteration * (batch p i) + (c.workers i.succ).samples)) := by
  obtain ⟨hready, hv, _⟩ := computed_at_finish p T g P c htimely i input value next he
  rw [hp.pending i] at hready
  cases hb : (c.workers i.succ).pending with
  | false => simp [hb] at hready
  | true =>
      simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at hready
      obtain ⟨ht, hx⟩ := hready
      refine ⟨rfl, hx.symm, ht.symm, ?_⟩
      rw [← hx, hp.seeds i, hp.used i] at hv
      exact hv

lemma continue_worker_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true)
    (hmore : (c.workers i.succ).samples + 1 < (batch p i))
    (htime : c.time = roundStart p (c.workers i.succ).iteration +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let value := g i (c.workers i.succ).model.point
      (samples i ((c.workers i.succ).iteration * (batch p i) + (c.workers i.succ).samples))
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + value
      samples := (c.workers i.succ).samples + 1 }
    let localState := { c.oracle.computation i.succ with
      pending := some (c.time + p.h i, (c.workers i.succ).model.point)
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with computation := Function.update c.oracle.computation i.succ localState } } := by
  classical
  intro value state localState
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hk, hj, hs, hr⟩ := pending_worker p T g P samples selected c hc i hpending
  have hw : Function.update c.workers i.succ state = fun v => { c.workers v with
      accumulator := if v = i.succ then (c.workers v).accumulator + value else (c.workers v).accumulator
      samples := if v = i.succ then (c.workers v).samples + 1 else (c.workers v).samples } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have ho : Function.update c.oracle.computation i.succ localState = fun v => { c.oracle.computation v with
      pending := if v = i.succ then localState.pending else (c.oracle.computation v).pending
      used := if v = i.succ then (c.oracle.computation v).used + 1 else (c.oracle.computation v).used } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw, ho]
  refine { hc with
    root := ?_
    workers := ?_
    used := ?_
    targets_ready := ?_
    behind := ?_
    control := ?_
    root_pending := ?_
    pending := ?_ }
  · simp only [ite_eq_right hz]
    exact ⟨⟨hc.root.model, hc.root.index, hc.root.selected_point⟩, hc.root.total⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      refine ⟨(hc.workers i).model, hmore.le, ?_⟩
      change (c.workers i.succ).accumulator + value = _
      rw [Finset.sum_range_succ, ← (hc.workers i).accumulator]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [ite_eq_right hne]
      exact ⟨(hc.workers j).model, (hc.workers j).count, (hc.workers j).accumulator⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      rw [hc.used i, Nat.add_assoc]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.used j
  · simpa only [Function.update_of_ne hz] using hc.targets_ready
  · intro j hb
    by_cases he : j = i
    · subst j
      exact (lt_irrefl _ (hr ▸ hb)).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.behind j hb
  · intro j
    by_cases he : j = i
    · subst j
      exact Or.inr (Or.inl ⟨hk, by simpa only [ite_true] using hmore, hpending, hs⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [WorkerControl, ite_eq_right hne, Function.update_of_ne hne] using hc.control j
  · simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true, hpending]
      change some (c.time + p.h i, (c.workers i.succ).model.point) = _
      congr 2
      rw [htime]
      push_cast
      ring
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.pending j

end LongTails.Proofs.MultiscaleAggregateExecution
