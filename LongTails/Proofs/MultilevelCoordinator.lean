import LongTails.Proofs.MultilevelActions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultilevelCoordinator

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions
open MultilevelDeadline MultilevelBookkeeping MultilevelActions

variable {p : Params}

def Move (u : Context p) (b : Book p) (c d : u.Exec) : Prop :=
  ∃ b', Good u b' d ∧ Progress u b c b' d

lemma apply_time (u : Context p) (c : u.Exec) (v : Fin (p.n+1)) (o : OracleState u.O)
    (s : State p) (act : Action (ComputeQuery p) (p.n+1)) : (applyAction u c v o s act).time = c.time := by
  cases act <;> rfl

lemma make_good (u : Context p) (c d : u.Exec) (b z : Book p)
    (hc : Good u b c) (hstep : step u.O u.A c = some d) (ht : d.time = c.time)
    (hl : Local u z c.time) (hw : d.workers = nodes z u.seed u.out)
    (ho : d.oracle = machine u.t u.g u.P u.xs z) (hr : ready u.t (root z u.seed u.out) → d.wakeTime 0 ≤ c.time) :
    Good u z d :=
  ⟨hl.valid,hl.memory,hl.forecast,hw,ho,MultilevelClock.step_timely _ _ _ _ _ _ hc.timely hstep,
    ht ▸ hl.frontier,ht ▸ hr⟩

lemma server_event (u : Context p) (b z : Book p) (c d : u.Exec) (hc : Good u b c)
    (sc : Timetable p u.t u.T) (hs : step u.O u.A c = some d)
    (ev : Event (ComputeReply p) (CommReply p))
    (he : event u.O u.A c c.time = some ((0,ev),machine u.t u.g u.P u.xs z))
    (hu : u.A.update 0 (c.workers 0) (u.A.clock c.time) ev = root z u.seed u.out)
    (hw : ∀ i : Fin p.n, c.workers i.succ = worker z u.seed i)
    (hl : Local u z c.time)
    (hpre : workLeft u.t z < workLeft u.t b ∨ z = b ∧ c.wakeTime 0 ≤ c.time) : Move u b c d := by
  let a := dispatch u.t (root z u.seed u.out)
  have hq : u.A.query 0 (u.A.update 0 (c.workers 0) (u.A.clock c.time) ev) (u.A.clock c.time) = (a.1,a.2) := by
    rw [hu]; simp [Context.A,algorithm,a]
  have hd := step_action u c d _ _ _ _ _ he hq hs
  have ht : d.time = c.time := hd ▸ apply_time u c _ _ _ _
  obtain ⟨b',hl',hw',ho',hr',hp⟩ := server_action u c z sc hl hw
  refine ⟨b',make_good u c d b b' hc hs ht hl' (hd ▸ hw') (hd ▸ ho') (hd ▸ hr'),?_⟩
  rcases hp with hp | ⟨rfl,hidle⟩
  · exact .job (hp.trans_le (hpre.elim LT.lt.le (fun h => h.1 ▸ le_rfl)))
  · rcases hpre with h | ⟨rfl,h⟩
    · exact .job h
    · exact .idle 0 rfl h (hd ▸ hidle)

lemma wake_root (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c) (sc : Timetable p u.t u.T)
    (o : OracleState u.O) (he : event u.O u.A c c.time = some ((0,.wake),o))
    (hs : step u.O u.A c = some d) : Move u b c d := by
  obtain ⟨rfl,hready⟩ := DistributedExecution.wake_event u.O u.A c c.time 0 o he
  rw [hc.oracle] at he
  apply server_event u b b c d hc sc hs _ he
  · rw [hc.workers]; rfl
  · intro i; rw [hc.workers]; rfl
  · exact Good.local hc
  · exact Or.inr ⟨rfl,hready⟩

lemma wake_worker (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c)
    (i : Fin p.n) (o : OracleState u.O) (he : event u.O u.A c c.time = some ((i.succ,.wake),o))
    (hs : step u.O u.A c = some d) : Move u b c d := by
  obtain ⟨rfl,hr⟩ := DistributedExecution.wake_event u.O u.A c c.time i.succ o he
  have hq : u.A.query i.succ (u.A.update i.succ (c.workers i.succ) (u.A.clock c.time) .wake) (u.A.clock c.time) =
      (.advance 0, worker b u.seed i) := by
    rw [hc.workers]
    simp [Context.A,algorithm,update,nodes,worker]
  have hd := step_action u c d _ _ _ _ _ he hq hs
  have ht : d.time = c.time := hd ▸ rfl
  have hw : d.workers = nodes b u.seed u.out := by
    rw [hd]
    change Function.update c.workers i.succ (worker b u.seed i) = _
    rw [hc.workers]
    exact nodes_worker_update b u.seed rfl (fun _ _ => rfl)
  have ho : d.oracle = machine u.t u.g u.P u.xs b := by rw [hd]; exact hc.oracle
  have htime : d.wakeTime = Function.update c.wakeTime i.succ (max c.time (u.T+1)) := hd ▸ rfl
  refine ⟨b,make_good u c d b b hc hs ht (Good.local hc) hw ho ?_,.idle i.succ rfl hr htime⟩
  simpa [htime,Ne.symm (Fin.succ_ne_zero i)] using hc.runnable

lemma receive_root (u : Context p) (b : Book p) (c d : u.Exec) (hc : Good u b c) (sc : Timetable p u.t u.T)
    (i : Fin p.n) (bits : Bits) (o : OracleState u.O) (he : event u.O u.A c c.time = some ((0,.received (.received i.succ bits)),o))
    (hs : step u.O u.A c = some d) : Move u b c d := by
  obtain ⟨hm,ho⟩ := MultilevelClock.received_at_finish (Network p) (evalPair u.g) u.P u.A c hc.timely _ _ _ _ he
  rw [hc.oracle] at hm ho
  change MultilevelWireState.Phase.uplink u.out (b.pending i) = some (c.time,bits) at hm
  cases hphase : b.pending i with
  | idle | down | work => simp [hphase,MultilevelWireState.Phase.uplink] at hm
  | up j τ =>
    simp [hphase,MultilevelWireState.Phase.uplink] at hm
    obtain ⟨rfl,rfl⟩ := hm
    have heq : o = machine u.t u.g u.P u.xs (collect b i j) := by
      rw [ho]
      apply congrArg₂ OracleState.mk
      · have h := units_collect (t := u.t) (out := u.out) hphase u.xs
        exact congrArg (fun f => Fin.cases (motive := fun _ : Fin (p.n+1) => StarNetwork.ComputationState (Query p) (Samples p)) ⟨none,u.xs,0⟩ f) h.symm
      · exact (up_collect (t := u.t) (out := u.out) hphase).symm
    rw [heq] at he
    apply server_event u b (collect b i j) c d hc sc hs _ he
    · rw [hc.workers]
      change accept (root b u.seed u.out) i (frame (u.out j)) = _
      exact accepted b u.seed u.out i j (by simp [hphase,Phase.job])
    · intro a; rw [hc.workers]; rfl
    · exact valid_collect u b _ (Good.local hc) i j hphase
    · exact Or.inl (phase_decreases _ _ _ i .idle rfl rfl (by simp [hphase,Phase.remaining]))

end LongTails.Proofs.MultilevelCoordinator
