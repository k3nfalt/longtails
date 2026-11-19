import LongTails.Proofs.MultilevelCoordinator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultilevelWorker

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions
open MultilevelDeadline MultilevelBookkeeping MultilevelActions MultilevelCoordinator

variable {p : Params}

lemma receive_worker (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c)
    (i : Fin p.n) (bits : Bits) (o : OracleState u.O)
    (he : event u.O u.A c c.time = some ((i.succ,.received (.received 0 bits)),o))
    (hs : step u.O u.A c = some d) : Move u b c d := by
  obtain ⟨hm,ho⟩ := MultilevelClock.received_at_finish (Network p) (evalPair u.g) u.P u.A c hc.timely _ _ _ _ he
  rw [hc.oracle] at hm ho
  change MultilevelWireState.Phase.downlink u.t u.out (b.pending i) = some (c.time,bits) at hm
  cases hp : b.pending i with
  | idle | work | up => simp [hp,MultilevelWireState.Phase.downlink] at hm
  | down j τ =>
    simp [hp,MultilevelWireState.Phase.downlink] at hm
    obtain ⟨rfl,rfl⟩ := hm
    let bs := payload u.t u.out j
    let z := startWork b i j (c.time+2*p.h i) bs
    have hroot : root z u.seed u.out = root b u.seed u.out := by
      apply root_same (b := b) (out := u.out) z u.seed rfl rfl
      intro a
      by_cases h : a = i <;> simp [z,startWork,h,hp,Phase.job]
    have hq : u.A.query i.succ (u.A.update i.succ (c.workers i.succ) (u.A.clock c.time)
          (.received (.received 0 (frame bs)))) (u.A.clock c.time) =
        (.compute (.evaluate (u.t.decode bs)),worker z u.seed i) := by
      rw [hc.workers]
      simp [Context.A,algorithm,nodes,update,worker,z,startWork,unframe_frame]
    have hd := step_action u c d _ _ _ _ _ he hq hs
    have hw : d.workers = nodes z u.seed u.out := by
      rw [hd]
      change Function.update c.workers i.succ (worker z u.seed i) = _
      rw [hc.workers]
      exact nodes_worker_update _ _ hroot (fun a ha => by simp [z,startWork,ha])
    have hcomp := DistributedExecution.computation_submit_idle (Network p) (evalPair u.g) i
      (unitState u.t u.out b u.xs i) c.time (u.t.decode bs) (by simp [unitState,MultilevelWireState.Phase.computing,hp])
    have hor : d.oracle = machine u.t u.g u.P u.xs z := by
      rw [hd,ho]
      apply congrArg₂ OracleState.mk
      · change Function.update ((machine u.t u.g u.P u.xs b).computation) i.succ
          ((StarNetwork.computation (Network p) (evalPair u.g)).submit i.succ
          (unitState u.t u.out b u.xs i) c.time (.evaluate (u.t.decode bs))) = _
        rw [hcomp]
        exact (succ_update (p := p) _ _ _ _ (units_work (t := u.t) (out := u.out) hp _ bs u.xs)).symm
      · exact (down_work (t := u.t) (out := u.out) hp _ bs).symm
    have htime : d.time = c.time := hd ▸ rfl
    refine ⟨z, make_good u c d b z hc hs htime (valid_work u b _ (Good.local hc) i j hp) hw hor ?_,
      .job (phase_decreases _ _ _ i (.work j _) rfl rfl (by simp [hp,Phase.remaining]))⟩
    rw [hroot,hd]
    simpa only [applyAction,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))] using hc.runnable

lemma computed_worker (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c)
    (i : Fin p.n) (q value : Query p) (o : OracleState u.O)
    (he : event u.O u.A c c.time = some ((i.succ,.computed (.computed q value)),o))
    (hs : step u.O u.A c = some d) : Move u b c d := by
  obtain ⟨hm,hv,ho⟩ := MultilevelClock.computed_at_finish (Network p) (evalPair u.g) u.P u.A c hc.timely _ _ _ _ he
  rw [hc.oracle] at hm hv ho
  change MultilevelWireState.Phase.computing u.t u.out (b.pending i) = some (c.time,q) at hm
  cases hp : b.pending i with
  | idle | down | up => simp [hp,MultilevelWireState.Phase.computing] at hm
  | work j τ =>
    simp [hp,MultilevelWireState.Phase.computing] at hm
    obtain ⟨rfl,rfl⟩ := hm
    let z := startReply b i j (c.time+wire p (u.out j))
    have hj : (b.pending i).job = some j := by simp [hp,Phase.job]
    obtain ⟨_,hwk,_,hcount⟩ := hc.valid.2.2.1 _ _ hj
    have hused : (unitState u.t u.out b u.xs i).used = ordinal u.t j := by simp [unitState,hp,Phase.unused,hcount]
    change value = evalPair u.g i (u.t.decode (payload u.t u.out j)) u.xs (unitState u.t u.out b u.xs i).used at hv
    have hout : u.t.encode (b.memory i) value = u.out j := by
      rw [hc.memory i j c.time hp,hv,hused,← hwk]
      exact (reply_eq _ _ _ _).symm
    have hroot : root z u.seed u.out = root b u.seed u.out := by
      apply root_same (b := b) (out := u.out) z u.seed rfl rfl
      intro a
      by_cases h : a = i <;> simp [z,startReply,h,hp,Phase.job]
    have hq : u.A.query i.succ (u.A.update i.succ (c.workers i.succ) (u.A.clock c.time)
          (.computed (.computed (u.t.decode (payload u.t u.out j)) value))) (u.A.clock c.time) =
        (.communicate (0,u.out j),worker z u.seed i) := by
      rw [hc.workers]
      simp [Context.A,algorithm,nodes,update,worker,z,startReply,hout]
    have hd := step_action u c d _ _ _ _ _ he hq hs
    have hw : d.workers = nodes z u.seed u.out := by
      rw [hd]
      change Function.update c.workers i.succ (worker z u.seed i) = _
      rw [hc.workers]
      exact nodes_worker_update _ _ hroot (fun _ _ => rfl)
    have hsend := DistributedExecution.communication_submit_free (Seed := Samples p) (Network p)
      (wires u.t u.out b) c.time i.succ 0 (frame (u.out j)) (Or.inr ⟨Fin.succ_ne_zero _,rfl⟩)
      (by rw [wires_up,hp]; rfl)
    have hprice : c.time + (Network p).timePerBit * (frame (u.out j)).length + (Network p).latency =
        c.time + wire p (u.out j) := by simp [frame,wire,add_assoc]
    rw [hprice] at hsend
    have hor : d.oracle = machine u.t u.g u.P u.xs z := by
      rw [hd,ho]
      apply congrArg₂ OracleState.mk
      · exact (succ_update (p := p) _ _ _ _ (units_reply (out := u.out) hc.valid hp _ u.xs)).symm
      · exact hsend.trans (up_reply (t := u.t) (out := u.out) hp _).symm
    refine ⟨z,make_good u c d b z hc hs (hd ▸ rfl) (valid_reply u b _ (Good.local hc) i j hp) hw hor ?_,
      .job (phase_decreases _ _ _ i (.up j _) rfl rfl (by simp [hp,Phase.remaining]))⟩
    rw [hroot,hd]
    simpa only [applyAction,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))] using hc.runnable

lemma event_move (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c)
    (sc : Timetable p u.t u.T) (v : Fin (p.n+1)) (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState u.O)
    (he : event u.O u.A c c.time = some ((v,ev),o)) (hs : step u.O u.A c = some d) : Move u b c d := by
  cases ev with
  | wake =>
    induction v using Fin.cases with
    | zero => exact wake_root u b c d hc sc o he hs
    | succ i => exact wake_worker u b c d hc i o he hs
  | computed reply =>
    cases reply with
    | computed x y =>
      induction v using Fin.cases with
      | zero =>
        obtain ⟨s,ha,_⟩ := DistributedExecution.computed_event _ _ _ _ _ _ _ he
        simp [Context.O,system,StarNetwork.system,StarNetwork.computation] at ha
      | succ i => exact computed_worker u b c d hc i x y o he hs
  | received msg =>
    cases msg with
    | received source bits =>
      have info := (MultilevelClock.received_at_finish (Network p) (evalPair u.g) u.P u.A c hc.timely _ _ _ _ he).1
      rw [hc.oracle] at info
      induction v using Fin.cases with
      | zero =>
        induction source using Fin.cases with
        | zero => contradiction
        | succ i => exact receive_root u b c d hc sc i bits o he hs
      | succ i =>
        induction source using Fin.cases with
        | zero => exact receive_worker u b c d hc i bits o he hs
        | succ j => contradiction

end LongTails.Proofs.MultilevelWorker
