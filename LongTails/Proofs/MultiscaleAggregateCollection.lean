import LongTails.Proofs.MultiscaleAggregateUplink

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

lemma broadcast_send_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n) (rest : List (Fin p.n))
    (htargets : (c.workers 0).targets = i :: rest) :
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers 0 { c.workers 0 with targets := rest }
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (roundStart p (c.workers 0).iteration,
                rootBits p g samples ((c.workers 0).iteration - 1) ++
                  List.replicate clockBits false)))) } } } := by
  classical
  have hnonempty : (c.workers 0).targets ≠ [] := by simp only [htargets, ne_eq, List.cons_ne_nil, not_false_eq_true]
  have hnodup : (i :: rest).Nodup := htargets ▸ hc.targets_nodup
  have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
  have hround : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration :=
    hc.targets_queued i (by simp only [htargets, List.mem_cons, true_or])
  have hactive := hc.targets_active hnonempty
  have hw : Function.update c.workers 0 { c.workers 0 with targets := rest } =
      fun v => { c.workers v with targets := if v = 0 then rest else (c.workers v).targets } := by
    funext v
    by_cases hv : v = 0
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw]
  refine { hc with
    root := ⟨⟨hc.root.model, hc.root.index, hc.root.selected_point⟩, hc.root.total⟩
    workers := fun j => ⟨(hc.workers j).model,
      (hc.workers j).count, (hc.workers j).accumulator⟩
    targets_nodup := ?_
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    control := ?_
    links := ?_ }
  · simpa only [ite_true] using (List.nodup_cons.mp hnodup).2
  · intro j hj
    apply hc.targets_queued j
    simp only [ite_true] at hj
    simp only [htargets, List.mem_cons]
    exact Or.inr hj
  · intro _
    exact hactive
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro _
    exact hc.outbox hnonempty
  · intro _
    exact hc.broadcast_time hnonempty
  · intro j
    simpa only [WorkerControl, Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro source target
    simp only [ite_true]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero =>
            simpa only [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.cases_zero] using hc.links 0 0
        | succ j =>
            by_cases he : j = i
            · subst j
              simp only [Function.update_self, Fin.cases_succ, hactive, hround, hnot,
                not_false_eq_true, and_self, ite_true]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hc.links 0 j.succ]
              simp only [Fin.cases_zero, Fin.cases_succ, htargets, List.mem_cons, he, false_or]
    | succ j =>
        simpa only [Function.update_of_ne (Fin.succ_ne_zero j), Fin.cases_succ] using hc.links j.succ target

lemma root_partial_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hpartial : insert i (c.workers 0).arrived ≠ Finset.univ)
    (htime : c.time = roundStart p (c.workers 0).iteration + (batch p i) * p.h i +
      (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ))) :
    let value := readPacket p (c.workers 0).iteration
      (workerBits p g samples (c.workers 0).iteration i)
    let state := { c.workers 0 with
      total := (c.workers 0).total + value
      arrived := insert i (c.workers 0).arrived }
    Pipeline p T g P samples selected
      { c with
        workers := Function.update c.workers 0 state
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages i.succ
            (Function.update (c.oracle.communication.messages i.succ) 0 none)) } } } := by
  classical
  intro value state
  have hw : Function.update c.workers 0 state = fun v => { c.workers v with
      total := if v = 0 then (c.workers v).total + value else (c.workers v).total
      arrived := if v = 0 then insert i (c.workers v).arrived else (c.workers v).arrived } := by
    funext v
    by_cases hv : v = 0
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw]
  refine { hc with
    root := ?_
    workers := ?_
    arrived_incomplete := ?_
    targets_ready := ?_
    control := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · refine ⟨⟨hc.root.model, hc.root.index, hc.root.selected_point⟩, ?_⟩
    simp only [ite_true]
    rw [Finset.sum_insert hnot, hc.root.total]
    dsimp only [value]
    abel
  · intro j
    simp only [ite_eq_right (Fin.succ_ne_zero j)]
    exact ⟨(hc.workers j).model, (hc.workers j).count, (hc.workers j).accumulator⟩
  · simpa only [ite_true] using hpartial
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro j
    simpa only [WorkerControl, Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro j hj
    simp only [ite_true, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hc.arrived_current j hj
  · intro j hj
    simp only [ite_true, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact htime.ge
    · exact hc.arrived_time j hj
  · intro source target
    simp only [ite_true]
    induction source using Fin.cases with
    | zero =>
        simpa only [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.cases_zero] using hc.links 0 target
    | succ j =>
        simp only [Fin.cases_succ]
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, not_true_eq_false, and_false, ite_false]
          by_cases ht : target = 0
          · subst target; simp only [Function.update_self]
          · rw [Function.update_of_ne ht, hc.links i.succ target]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simpa only [Function.update_of_ne hne, Fin.cases_succ, Finset.mem_insert, he, false_or] using
            hc.links j.succ target

lemma received_worker_facts (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hp : Pipeline p T g P samples selected c) (htimely : Timely p T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle)) :
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧
      (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived ∧
      c.time = roundStart p (c.workers 0).iteration + (batch p i) * p.h i +
        (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)) ∧
      bits = workerBits p g samples (c.workers 0).iteration i ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish p T g P c htimely i.succ 0 bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_succ, true_and] at hm
  split_ifs at hm with hvalid
  · obtain ⟨hr, hs, hnot⟩ := hvalid
    have heq := Option.some.inj hm
    obtain ⟨ht, hb⟩ := Prod.mk.inj heq
    exact ⟨hr, hs, hnot, by simpa only [hr] using ht.symm,
      by simpa only [hr] using hb.symm⟩

lemma sent_worker (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hsent : (c.workers i.succ).sent = true) :
    (c.workers i.succ).iteration < (rounds p) ∧ (c.workers i.succ).samples = (batch p i) ∧
      (c.workers i.succ).pending = false := by
  have hcontrol := hc.control i
  simpa only [WorkerControl, hsent, Bool.true_eq_false, false_and, and_false,
    false_or, true_and, and_true] using hcontrol

lemma last_arrival_time (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (htime : c.time = roundStart p (c.workers 0).iteration + (batch p i) * p.h i +
      (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ))) :
    c.time = roundStart p (c.workers 0).iteration + computeTime p +
      (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)) := by
  have hmax : computeTime p = (batch p i : Time) * p.h i := by
    apply le_antisymm _ (Finset.le_sup (f := fun j : Fin p.n => (batch p j : Time) * p.h j) (Finset.mem_univ i))
    apply Finset.sup_le
    intro j hj
    rw [← hcomplete, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact le_rfl
    · have hbefore := hc.arrived_time j hj
      rw [htime] at hbefore
      exact le_of_add_le_add_left (le_of_add_le_add_right hbefore)
  rw [hmax]
  exact htime

lemma complete_workers (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ) :
    ∀ j : Fin p.n, (c.workers j.succ).iteration = (c.workers 0).iteration ∧
      (c.workers j.succ).samples = (batch p j) ∧ (c.workers j.succ).sent = true ∧
      (c.workers j.succ).pending = false := by
  intro j
  have hj : j ∈ insert i (c.workers 0).arrived := by rw [hcomplete]; exact Finset.mem_univ j
  have hf : (c.workers j.succ).iteration = (c.workers 0).iteration ∧ (c.workers j.succ).sent = true := by
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hc.arrived_current j hj
  have hw := sent_worker p T g P samples selected c hc j hf.2
  exact ⟨hf.1, hw.2.1, hf.2, hw.2.2⟩

lemma complete_messages (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T))
    (hc : Pipeline p T g P samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ) :
    Function.update c.oracle.communication.messages i.succ
      (Function.update (c.oracle.communication.messages i.succ) 0 none) = fun _ _ => none := by
  classical
  have hall := complete_workers p T g P samples selected c hc i hr hs hcomplete
  funext source target
  induction source using Fin.cases with
  | zero =>
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, hc.links]
      induction target using Fin.cases with
      | zero => rfl
      | succ j =>
          have hne : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
          simp only [Fin.cases_zero, Fin.cases_succ, (hall j).1, hne, false_and,
            and_false, ite_false]
  | succ j =>
      by_cases he : j = i
      · subst j
        rw [Function.update_self]
        by_cases ht : target = 0
        · subst target; exact Function.update_self ..
        · rw [Function.update_of_ne ht, hc.links]
          simp only [Fin.cases_succ, ht, false_and, ite_false]
      · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
        have hj : j ∈ (c.workers 0).arrived := by
          have hm : j ∈ insert i (c.workers 0).arrived := by rw [hcomplete]; exact Finset.mem_univ j
          exact (Finset.mem_insert.mp hm).resolve_left he
        rw [Function.update_of_ne hne, hc.links]
        simp only [Fin.cases_succ, hj, not_true_eq_false, and_false, ite_false]


end LongTails.Proofs.MultiscaleAggregateExecution
