import LongTails.Proofs.MultirateInteraction

open MeasureTheory

namespace LongTails.Proofs.MultirateReplay

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex LongTails.Setups.StarNetwork
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open LongTails.Algorithms.MultirateTrajectory
open MultirateReservations MultirateMachine MultirateEvents MultirateInteraction

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {D u : Time} {x y : Config p}

lemma oracle_ext {a b : OracleState (systemOf g P)}
    (hc : a.computation = b.computation) (hm : a.communication.messages = b.communication.messages) : a = b := by
  cases a with
  | mk ac am =>
    cases b with
    | mk bc bm =>
      change ac = bc at hc
      subst bc
      cases am; cases bm
      cases hm
      rfl

lemma inbox_same (i : Fin p.n) (v : Cell p) (h : mailbox g s i v = mailbox g s i (x.table i)) :
    inbox g s (revised x i v) = inbox g s x.table := by
  rw [revised, inbox_update, h, show mailbox g s i (x.table i) = inbox g s x.table i from rfl, Function.update_eq_self]

lemma replay {v e os} (h : Move g P s D u x v e os y) (ht : x.now ≤ x.deadline) (hD : x.deadline ≤ D)
    (he : event (systemOf g P) (algorithm p D) (image g P s D x) x.now = some ((v,e),os)) :
    step (systemOf g P) (algorithm p D) (image g P s D x) = some (image g P s D y) := by
  cases h with
  | sleep v _ hs =>
    apply actual_tick g P s D ht he hs (Function.update_eq_self ..) rfl (wake_sleep D (ht.trans hD))
  | post i bits next e hp hf _ hb =>
    let cell := Cell.down (p := p) ⟨e,bits,u⟩ (x.now+packetDelay p)
    have hm := inbox_same (g := g) (s := s) i cell (by rw [hf]; rfl)
    apply actual_tick g P s D ht he (act := .communicate (i.succ,bits))
      (st := ⟨next,inbox g s x.table,.idle,false⟩) _ _ _ rfl
    · change rootQuery p ⟨x.program,inbox g s x.table,.idle,false⟩ = _
      simp [rootQuery,hp]
      rfl
    · rw [← hm]
      exact (workers_mail g s x.table x.program next i cell (by rw [hf]; rfl)).symm
    · apply oracle_ext
      · exact (computation_same g s P x.table i cell (by rw [hf]; rfl)).symm
      · have hfree : messages g s x.table 0 i.succ = none := by simp [messages,hf,downlink]
        have hsend := DistributedExecution.communication_submit_free (Seed := Samples p) (network p)
          ⟨messages g s x.table⟩ x.now 0 i.succ (wire bits) (Or.inl ⟨rfl,Fin.succ_ne_zero _⟩) hfree
        change ((communication (Seed := Samples p) (network p)).submit ⟨messages g s x.table⟩ x.now 0 (i.succ,wire bits)).messages = messages g s (Function.update x.table i cell)
        rw [hsend,messages_down g s x.table i cell (by rw [hf]; rfl)]
        rw [show x.now + (network p).timePerBit * (wire bits).length + (network p).latency = _ from wire_delay hb _]
        rfl
  | take i job next hp hf _ =>
    let cell := Cell.free (p := p) (job.number+1)
    apply actual_tick g P s D ht he (act := .advance 0)
      (st := ⟨next (jobReply g s i job),inbox g s (revised x i cell),.idle,false⟩) _ _ _ (wake_zero D _)
    · change rootQuery p ⟨x.program,inbox g s x.table,.idle,false⟩ = _
      simp [rootQuery,hp, revised, inbox_update, show inbox g s x.table i = some (jobReply g s i job) by simp [inbox,hf,mailbox],cell,mailbox]
      rfl
    · exact (workers_mail g s x.table x.program _ i cell (by rw [hf]; rfl)).symm
    · apply oracle_ext
      · exact (computation_same g s P x.table i cell (by rw [hf]; rfl)).symm
      · exact (messages_same g s x.table i cell (by rw [hf]; rfl) (by rw [hf]; rfl)).symm
  | evaluate i job j t hc _ hj =>
    let cell := Cell.work job j (x.now + p.h i)
    apply actual_tick g P s D ht he (act := .compute (.evaluate (jobInput p job)))
      (st := ⟨.done p.x0,fun _ => none,phaseOf g s i cell,false⟩) _ _ _ rfl
    · change workerQuery p i ⟨.done p.x0, fun _ => none,phaseOf g s i (x.table i),false⟩ = _
      simp [workerQuery,hc,phaseOf,cell,hj]
      rfl
    · exact (workers_leaf g s x.table x.program i cell (by rw [hc]; rfl)).symm
    · apply oracle_ext
      · rw [show revised x i cell = Function.update x.table i cell from rfl, computation_update]
        have hsrc : (oracleOf g P s x.table).computation i.succ = computationOf s i (.dispatch job j t) := by
          change computationOf s i (x.table i) = _
          rw [hc]
        change Function.update (oracleOf g P s x.table).computation i.succ ((computation (network p) (evalAt g)).submit i.succ ((oracleOf g P s x.table).computation i.succ) x.now (.evaluate (jobInput p job))) = _
        rw [hsrc,DistributedExecution.computation_submit_idle _ _ _ _ _ _ rfl]
        rfl
      · exact (messages_same g s x.table i cell (by rw [hc]; rfl) (by rw [hc]; rfl)).symm
  | reply i job t hc _ =>
    let cell := Cell.up job (x.now+packetDelay p)
    let bits := replyPacket p ((batch p i : ℝ)⁻¹ • partialSum g s i job (batch p i))
    apply actual_tick g P s D ht he (act := .communicate (0,bits))
      (st := ⟨.done p.x0,fun _ => none,.idle,false⟩) _ _ _ rfl
    · change workerQuery p i ⟨.done p.x0, fun _ => none,phaseOf g s i (x.table i),false⟩ = _
      simp [workerQuery,hc,phaseOf,bits]
      rfl
    · exact (workers_leaf g s x.table x.program i cell (by rw [hc]; rfl)).symm
    · apply oracle_ext
      · apply (computation_same g s P x.table i cell _).symm
        rw [hc]
        simp [computationOf,cell,Nat.add_mul]
      · have hfree : messages g s x.table i.succ 0 = none := by simp [messages,hc,uplink]
        have hsend := DistributedExecution.communication_submit_free (Seed := Samples p) (network p)
          ⟨messages g s x.table⟩ x.now i.succ 0 (wire bits) (Or.inr ⟨Fin.succ_ne_zero _,rfl⟩) hfree
        change ((communication (Seed := Samples p) (network p)).submit ⟨messages g s x.table⟩ x.now i.succ (0,wire bits)).messages = messages g s (Function.update x.table i cell)
        rw [hsend,messages_up g s x.table i cell (by rw [hc]; rfl)]
        rw [show x.now + (network p).timePerBit * (wire bits).length + (network p).latency = _ from wire_delay (reply_length _) _]
        rfl
  | down i job t hc _ =>
    let cell := Cell.dispatch job 0 t
    apply actual_tick g P s D ht he (act := .advance 0)
      (st := ⟨.done p.x0,fun _ => none,phaseOf g s i cell,false⟩) _ _ _ (wake_zero D _)
    · simp [algorithm,update,workersOf,phaseOf,cell,partialSum,jobInput]
    · exact (workers_leaf g s x.table x.program i cell (by rw [hc]; rfl)).symm
    · apply oracle_ext
      · apply (computation_same g s P x.table i cell _).symm
        simp [hc,cell,computationOf]
      · exact (messages_down g s x.table i cell (by rw [hc]; rfl)).symm
  | up i job t hc _ =>
    let cell := Cell.buffered job
    apply actual_tick g P s D ht he (act := .advance 0)
      (st := ⟨x.program,inbox g s (revised x i cell),.idle,false⟩) _ _ _ (wake_zero D _)
    · simp [algorithm,update,workersOf,revised,inbox_update,mailbox,cell]
    · exact (workers_mail g s x.table x.program _ i cell (by rw [hc]; rfl)).symm
    · apply oracle_ext
      · exact (computation_same g s P x.table i cell (by rw [hc]; rfl)).symm
      · exact (messages_up g s x.table i cell (by rw [hc]; rfl)).symm
  | computed i job j t hc _ =>
    let cell := Cell.dispatch job (j+1) t
    apply actual_tick g P s D ht he (act := .advance 0)
      (st := ⟨.done p.x0,fun _ => none,phaseOf g s i cell,false⟩) _ _ _ (wake_zero D _)
    · simp [algorithm,update,workersOf,hc,phaseOf,cell,partialSum,Finset.sum_range_succ]
    · exact (workers_leaf g s x.table x.program i cell (by rw [hc]; rfl)).symm
    · apply oracle_ext
      · rw [show revised x i cell = Function.update x.table i cell from rfl, computation_update]
        simp [submit,cell,computationOf,Nat.add_assoc]
      · exact (messages_same g s x.table i cell (by rw [hc]; rfl) (by rw [hc]; rfl)).symm

end LongTails.Proofs.MultirateReplay
