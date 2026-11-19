import LongTails.Proofs.MultilevelBookkeeping

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultilevelActions

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions
open MultilevelDeadline MultilevelBookkeeping

variable {p : Params}

noncomputable def applyAction (u : Context p) (c : u.Exec) (v : Fin (p.n+1)) (o : OracleState u.O)
    (s : State p) (action : Action (ComputeQuery p) (p.n+1)) : u.Exec :=
  let d := {c with workers := Function.update c.workers v s, wakeTime := Function.update c.wakeTime v c.time,
                   turn := v.val+1, oracle := o}
  match action with
  | .compute q => {d with oracle := {o with computation := Function.update o.computation v (u.O.computation.submit v (o.computation v) c.time q)}}
  | .communicate (w,bs) =>
    let comm := u.O.communication.submit o.communication c.time v (w,frame bs)
    {d with oracle := {o with communication := comm}}
  | .advance τ => {d with wakeTime := Function.update c.wakeTime v (max c.time (u.A.timer τ))}

lemma step_action (u : Context p) (c next : u.Exec) (v : Fin (p.n+1))
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState u.O)
    (action : Action (ComputeQuery p) (p.n+1)) (s : State p)
    (h : event u.O u.A c c.time = some ((v,ev),o))
    (hq : u.A.query v (u.A.update v (c.workers v) (u.A.clock c.time) ev) (u.A.clock c.time) = (action,s))
    (hs : step u.O u.A c = some next) : next = applyAction u c v o s action := by
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp [hlate] at hs
  simp only [ite_eq_right hlate, h, hq] at hs
  cases action <;> simp only [Option.some.injEq, Function.update_idem] at hs <;> subst next <;> rfl

inductive Progress (u : Context p) (b : Book p) (c : u.Exec) (b' : Book p) (d : u.Exec) : Prop
  | job : workLeft u.t b' < workLeft u.t b → Progress u b c b' d
  | idle (v : Fin (p.n+1)) : b' = b → c.wakeTime v ≤ c.time →
      d.wakeTime = Function.update c.wakeTime v (max c.time (u.T+1)) → Progress u b c b' d

lemma proto_launch (u : Context p) (c : u.Exec) (b : Book p)
    (hr : ready u.t (root b u.seed u.out)) (hw : ∀ i : Fin p.n, c.workers i.succ = worker b u.seed i) :
    let j := b.issued
    let i := u.t.worker j
    let bs := payload u.t u.out j
    let d := c.time + wire p bs
    let b' := launch u.t b d
    let next := applyAction u c 0 (machine u.t u.g u.P u.xs b) (root b' u.seed u.out) (.communicate (i.succ,bs))
    next.workers = nodes b' u.seed u.out ∧ next.oracle = machine u.t u.g u.P u.xs b' ∧
      next.wakeTime = Function.update c.wakeTime 0 c.time := by
  intro j i bs d b' next
  have hid : b.pending i = .idle := phase_idle hr.2.1
  have hsend := DistributedExecution.communication_submit_free (Seed := Samples p) (Network p)
    (wires u.t u.out b) c.time 0 i.succ (frame bs)
    (Or.inl ⟨rfl,Fin.succ_ne_zero _⟩) (by rw [wires_down,hid]; rfl)
  have hd : c.time + (Network p).timePerBit * (frame bs).length + (Network p).latency = d := by
    simp [d,wire,frame,add_assoc]
  change (StarNetwork.communication (Seed := Samples p) (Network p)).submit _ _ _ _ = _ at hsend
  rw [hd] at hsend
  refine ⟨?_, ?_, rfl⟩
  · funext v
    induction v using Fin.cases with
    | zero => simp [next,applyAction,nodes]
    | succ a => simpa [next,applyAction,nodes,b',launch,worker] using hw a
  · change OracleState.mk _ _ = OracleState.mk _ _
    apply congrArg₂ OracleState.mk
    · have he := units_launch (xs := u.xs) (t := u.t) (out := u.out) d hid
      exact congrArg (fun f => Fin.cases (motive := fun _ : Fin (p.n+1) => StarNetwork.ComputationState (Query p) (Samples p)) ⟨none,u.xs,0⟩ f) he.symm
    · exact hsend.trans (down_launch (t := u.t) (out := u.out) d hid).symm

lemma server_action (u : Context p) (c : u.Exec) (b : Book p) (sc : Timetable p u.t u.T)
    (hl : Local u b c.time) (hw : ∀ i : Fin p.n, c.workers i.succ = worker b u.seed i) :
    let o := machine u.t u.g u.P u.xs b
    let s := root b u.seed u.out
    let a := dispatch u.t s
    let next := applyAction u c 0 o a.2 a.1
    ∃ b', Local u b' c.time ∧ next.workers = nodes b' u.seed u.out ∧
      next.oracle = machine u.t u.g u.P u.xs b' ∧
      (ready u.t (root b' u.seed u.out) → next.wakeTime 0 ≤ c.time) ∧
      (workLeft u.t b' < workLeft u.t b ∨
        b' = b ∧ next.wakeTime = Function.update c.wakeTime 0 (max c.time (u.T+1))) := by
  dsimp only
  by_cases hr : ready u.t (root b u.seed u.out)
  · let d := c.time + wire p (payload u.t u.out b.issued)
    rw [dispatch_yes b u.seed u.out d hr]
    have ht := proto_launch u c b hr hw
    exact ⟨launch u.t b d, valid_launch u b c.time hl sc hr, ht.1, ht.2.1,
      fun _ => by rw [ht.2.2,Function.update_self], Or.inl (launch_decreases u b d hr)⟩
  · rw [dispatch_no b u.seed u.out hr]
    refine ⟨b, hl, ?_, rfl, fun h => (hr h).elim, Or.inr ⟨rfl,rfl⟩⟩
    funext v
    induction v using Fin.cases with
    | zero => simp [applyAction,nodes]
    | succ i => simpa [applyAction,nodes] using hw i

end LongTails.Proofs.MultilevelActions
