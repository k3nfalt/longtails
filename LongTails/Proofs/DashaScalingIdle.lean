import LongTails.Algorithms.DashaScaling
import LongTails.Proofs.DistributedExecution

namespace LongTails.Proofs.DashaScalingIdle

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

lemma initial_answer_none (f : Functions p) (seed : (system p f).Seed) (time : Time) :
    (system p f).answer ((system p f).initial seed) time = none := by
  have hc (v : Fin (p.n + 1)) :
      (system p f).computation.answer v
        (((system p f).initial seed).computation v) time = none := by
    refine Fin.cases ?_ (fun i => ?_) v <;>
      simp [system, Oracle.initial, LongTails.Setups.StarNetwork.computation]
  unfold Oracle.answer
  have hf : (List.finRange (p.n + 1)).findSome? (fun v =>
      ((system p f).computation.answer v (((system p f).initial seed).computation v) time).map
        (fun (reply, state) => ((v, Event.computed (CommReply := CommReply p) reply),
          { (system p f).initial seed with
            computation := Function.update ((system p f).initial seed).computation v state }))) = none := by
    simp [hc]
  rw [hf]
  have hflat (l : List (Fin (p.n + 1))) :
      l.flatMap (fun _ => ([] : List (Time × Fin (p.n + 1) × Fin (p.n + 1) × List Bool))) = [] := by
    rw [List.flatMap_eq_nil_iff]
    simp
  simp [system, Oracle.initial, communication, LongTails.Setups.StarNetwork.communication, hflat]

lemma idle_termination
    (O : Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1))
    (seed : O.Seed) (ho : ∀ time, O.answer (O.initial seed) time = none) :
    ∃ k, step O (idle p) (run O (idle p) k (initial O (idle p) 0 ((), seed))) = none := by
  classical
  let Inv := fun c : ExecutionState O (idle p) =>
    c.time = 0 ∧ c.deadline = 0 ∧ ∀ time, O.answer c.oracle time = none
  let ready := fun c : ExecutionState O (idle p) =>
    Finset.univ.filter (fun v => c.wakeTime v = 0)
  refine DistributedExecution.termination_of_rank O (idle p) Inv (fun c => (ready c).card) ?_
    (initial O (idle p) 0 ((), seed)) ⟨rfl, rfl, ho⟩
  · intro c next hc hstep
    rcases hc with ⟨ht, hT, hnone⟩
    have hlate : ¬ c.deadline < c.time := by simp [ht, hT]
    cases he : event O (idle p) c c.time with
    | none =>
      simp only [step, ite_eq_right hlate, he] at hstep
      simp [ht, hT] at hstep
    | some z =>
      rcases z with ⟨⟨v, notification⟩, oracle⟩
      rcases DistributedExecution.event_cases O (idle p) c c.time v notification oracle he with
        horacle | ⟨hn, horacle, hv⟩
      · rw [hnone] at horacle
        contradiction
      · subst notification
        subst oracle
        simp only [step, ite_eq_right hlate, he] at hstep
        have hn : next = { c with
            workers := Function.update c.workers v ()
            wakeTime := Function.update c.wakeTime v 1
            turn := v.val + 1 } := by
          apply Option.some.inj
          simpa [idle, ht, Function.update_idem] using hstep.symm
        subst next
        refine ⟨⟨ht, hT, hnone⟩, ?_⟩
        have hv0 : c.wakeTime v = 0 := le_antisymm (by simpa [ht] using hv) (by positivity)
        have hr : ready { c with
            workers := Function.update c.workers v ()
            wakeTime := Function.update c.wakeTime v 1
            turn := v.val + 1 } = (ready c).erase v := by
          ext j
          by_cases hj : j = v
          · subst j
            simp [ready]
          · simp [ready, hj]
        rw [hr]
        exact Finset.card_erase_lt_of_mem (by simp [ready, hv0])

lemma idle_finiteEvents (f : Functions p) (seed : (idle p).Seed × (system p f).Seed) :
    FiniteEvents (system p f) (idle p) 0 seed := by
  intro T hT
  have hz : T = 0 := le_antisymm hT (by positivity)
  subst T
  rcases seed with ⟨u, v⟩
  cases u
  exact idle_termination (system p f) v (initial_answer_none f v)

lemma idle_execute (f : Functions p) (seed : (idle p).Seed) (oracleSeed : (system p f).Seed) :
    execute (system p f) (idle p) 0 seed oracleSeed = p.x0 := rfl

end LongTails.Proofs.DashaScalingIdle
