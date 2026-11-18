import LongTails.Proofs.MultiscaleAggregateCompute

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

lemma finish_worker_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true)
    (hlast : (c.workers i.succ).samples + 1 = (batch p i))
    (htime : c.time = roundStart p (c.workers i.succ).iteration +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let value := g i (c.workers i.succ).model.point
      (samples i ((c.workers i.succ).iteration * (batch p i) + (c.workers i.succ).samples))
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + value
      samples := (c.workers i.succ).samples + 1
      pending := false
      sent := true }
    let localState := { c.oracle.computation i.succ with
      pending := none
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := Function.update c.oracle.computation i.succ localState
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages i.succ
              (Function.update (c.oracle.communication.messages i.succ) 0
                (some (c.time + (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)),
                  workerBits p g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } } } := by
  classical
  intro value state localState
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hk, hj, hs, hr⟩ := pending_worker p T g P samples selected c hc i hpending
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have hf := (hc.arrived_current i hm).2
    rw [hs] at hf
    cases hf
  have hw : Function.update c.workers i.succ state = fun v => { c.workers v with
      accumulator := if v = i.succ then (c.workers v).accumulator + value else (c.workers v).accumulator
      samples := if v = i.succ then (c.workers v).samples + 1 else (c.workers v).samples
      pending := if v = i.succ then false else (c.workers v).pending
      sent := if v = i.succ then true else (c.workers v).sent } := by
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
    pending := ?_
    arrived_current := ?_
    links := ?_ }
  · simp only [ite_eq_right hz]
    exact ⟨⟨hc.root.model, hc.root.index, hc.root.selected_point⟩, hc.root.total⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      refine ⟨(hc.workers i).model, hlast.le, ?_⟩
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
      exact Or.inr (Or.inr ⟨hk, by simpa only [ite_true] using hlast, by simp, by simp⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [WorkerControl, ite_eq_right hne, Function.update_of_ne hne] using hc.control j
  · simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rfl
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.pending j
  · intro j hmem
    by_cases he : j = i
    · subst j
      exact (hnot hmem).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.arrived_current j hmem
  · intro source target
    induction source using Fin.cases with
    | zero =>
        simpa only [Function.update_of_ne hz, Fin.cases_zero] using hc.links 0 target
    | succ j =>
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Fin.cases_succ, ite_true]
          by_cases ht : target = 0
          · subst target
            simp only [Function.update_self, hr, hnot, and_self, ite_true, not_false_eq_true]
            congr 2
            rw [htime]
            have hb : (((c.workers i.succ).samples : Time) + 1) = ((batch p i) : Time) := by
              exact_mod_cast hlast
            rw [hb, hr]
          · rw [Function.update_of_ne ht, hc.links i.succ target]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simpa only [Function.update_of_ne hne, Fin.cases_succ, ite_eq_right hne] using
            hc.links j.succ target

lemma compute_update (p : Params) (T : Time)
    (s : State p) (v : Fin (p.n + 1)) (clock : ClockReading) (input value : Point p) :
    (algorithm p T).update v s clock (.computed (.computed input value)) =
      { s with accumulator := s.accumulator + value, samples := s.samples + 1, pending := false } := rfl

lemma computed_continue_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hmore : (c.workers i.succ).samples + 1 < (batch p i))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts p T g P samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish p T g P c htimely i input value oracle he
  obtain ⟨hk, _, _, _⟩ := pending_worker p T g P samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hk, hmore, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system,
      LongTails.Setups.StarNetwork.computation, Function.update_self, Fin.cases_succ,
      Function.update_idem, Option.some.injEq] at hstep
    subst next
    have h := continue_worker_pipeline p T g P samples selected c hp i hpending hmore ht
    simpa only [hpending] using h

lemma computed_finish_pipeline (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c next : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hlast : (c.workers i.succ).samples + 1 = (batch p i))
    (hstep : step (system p g P) (algorithm p T) c = some next) :
    Pipeline p T g P samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts p T g P samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish p T g P c htimely i input value oracle he
  obtain ⟨hk, _, hs, hr⟩ := pending_worker p T g P samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  have hbits : localPacket p (c.workers i.succ).iteration
      (((batch p i) : ℝ)⁻¹ • ((c.workers i.succ).accumulator + g i (c.workers i.succ).model.point
        (samples i ((c.workers i.succ).iteration * (batch p i) + (c.workers i.succ).samples)))) =
      workerBits p g samples (c.workers i.succ).iteration i := by
    simp only [workerBits, workerMessage, localPacket, ← (hp.workers i).model, batchMean]
    congr 2
    rw [show Finset.range ((batch p i)) = Finset.range ((c.workers i.succ).samples + 1) by rw [hlast],
      Finset.sum_range_succ, ← (hp.workers i).accumulator]
  have hfree : c.oracle.communication.messages i.succ 0 = none := by
    rw [hp.links]
    simp only [Fin.cases_succ, hs, Bool.false_eq_true, false_and, and_false, ite_false]
  have hsubmit : (system p g P).communication.submit c.oracle.communication c.time i.succ
      ⟨0, workerBits p g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ =
      { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages i.succ
          (Function.update (c.oracle.communication.messages i.succ) 0
            (some (c.time + (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)),
              workerBits p g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } := by
    change (LongTails.Setups.StarNetwork.communication (Seed := Samples p) ⟨p.h, p.l, p.b⟩).submit
      c.oracle.communication c.time i.succ
      ⟨0, workerBits p g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ = _
    rw [DistributedExecution.communication_submit_free (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time i.succ 0
      (workerBits p g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)
      (Or.inr ⟨Fin.succ_ne_zero i, rfl⟩) hfree]
    simp only [List.length_append, List.length_replicate, workerBits, workerMessage, MultiscaleAggregateCodec.packet_length, payload]
    congr 1
    funext source target
    by_cases hv : source = i.succ
    · subst source
      simp only [Function.update_self, Function.update_apply]
      (split_ifs; congr 2) <;> ring_nf; rw [hr]
    · simp only [Function.update_of_ne hv]
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hk, not_lt.mpr hlast.ge, hs, Bool.not_false,
      and_self, ite_true, ite_false, hbits] at hstep
    rw [hsubmit] at hstep
    simp only [Option.some.injEq] at hstep
    subst next
    exact finish_worker_pipeline p T g P samples selected c hp i hpending hlast ht


end LongTails.Proofs.MultiscaleAggregateExecution
