import LongTails.Proofs.DistributedJacobianStrongGrowthTimeNotification
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeBroadcast

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeReceive

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeNotification
open DistributedJacobianStrongGrowthTimeBroadcast
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma wakeFits_received (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (message : CommReply p) (next : CommunicationState p)
    (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c) (ht : TimedState p g S idle c)
    (hi : c.time < idle) (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication) (hedges : NetworkEdges p c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (ha : (communication p S).answer c.oracle.communication c.time = some ((v, message), next)) :
    WakeFits p v (update p v (c.workers v) (.received message)) c.time := by
  have hstored := noOverdue_received_time p g S idle c hn message.source v message.bits next ha
  have hadj := hedges message.source v _ hstored
  by_cases hd : v ≠ p.root ∧ message.source = p.parent v
  · have hs : c.oracle.communication.messages (p.parent v) v = some (c.time, message.bits) := by
      simpa only [hd.2] using hstored
    have hsent := down_pending_sent p c.workers c.oracle.communication hh v hd.1 c.time message.bits hs
    have hactive := (hr v).1.2.1 (Or.inr hsent)
    have htime := ht.down v hd.1 c.time message.bits hs
    simpa only [update, ite_eq_left hd] using wakeFits_relay p hp v (c.workers v) _ c.time (hb v) hactive htime
  · have hup : p.parent message.source = v := by
      rcases hadj.2 with hu | hu
      · exact hu
      · exfalso
        apply hd
        refine ⟨?_, hu.symm⟩
        intro hv
        have hh := hp.2.1
        rw [hv, hh] at hu
        exact hadj.1 (hu.symm.trans hv.symm)
    have hsource : message.source ≠ p.root := by
      intro hs
      have hh := hp.2.1
      rw [hs, hh] at hup
      exact hadj.1 (hs.trans hup)
    have hf := wakeFits_up_arrival p g S idle c message.source hsource message.bits hn hpark ht hi hh ho
      (by simpa only [hup] using hstored)
    simpa only [update, ite_eq_right hd, hup, WakeFits, WorkFits, workRemaining] using hf

lemma wakeFits_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c) (ht : TimedState p g S idle c)
    (hi : c.time < idle) (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication) (hedges : NetworkEdges p c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    WakeFits p v (update p v (c.workers v) notification) c.time := by
  cases notification with
  | wake =>
      have hw := (DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time v next he).2
      have heq := le_antisymm hw (hn.wake v)
      simpa only [update, heq] using ht.wake v (by simpa only [heq] using hi)
  | computed value =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value next he
      exact wakeFits_computed p g S idle c v value oracle hn hpark ht (hm v) hi ha
  | received message =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
      exact wakeFits_received p hp g S idle c v message oracle hn hpark ht hi hh ho hedges hr hb ha

lemma queueWork_notification (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hh : Handshake p c.workers c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i))
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next))
    (hq : (update p v (c.workers v) notification).queue ≠ []) :
    DistributedJacobianStrongGrowthTimeWork.WorkFits p (update p v (c.workers v) notification)
      (DistributedJacobianStrongGrowthTimeSchedule.roundStart p (epochIndex p (update p v (c.workers v) notification).phase)) := by
  cases notification with
  | wake => exact ht.queueWork v hq
  | computed value =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value next he
      obtain ⟨finish, point, hpending, _, _, _⟩ :=
        DistributedJacobianStrongGrowthOracle.computation_received_data p g S v (c.oracle.computation v) oracle c.time value ha
      obtain ⟨work, hwork, hquery⟩ := (hm v).2 finish point hpending
      have hbusy : (c.workers v).busy = true := by
        simpa only [hpending, Option.isSome_some] using (hm v).1.symm
      have hqueue : (c.workers v).queue ≠ [] := by
        simpa only [DistributedJacobianStrongGrowthProtocol.update_computed p v (c.workers v) work value hwork hbusy] using hq
      exact queueWork_computed p (c.workers v) v work point value hwork hquery hbusy (ht.queueWork v hqueue)
  | received message =>
      by_cases hd : v ≠ p.root ∧ message.source = p.parent v
      · obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
        obtain ⟨finish, hstored, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
          c.oracle.communication oracle c.time message.source v message.bits ha
        have hsent := down_pending_sent p c.workers c.oracle.communication hh v hd.1 finish message.bits
          (by simpa only [hd.2] using hstored)
        have hactive := (hr v).1.2.1 (Or.inr hsent)
        simpa only [update, ite_eq_left hd, relay, WorkFits, workRemaining] using workFits_finishBroadcast_start p (c.workers v) _ hactive
      · have hqueue : (c.workers v).queue ≠ [] := by simpa only [update, ite_eq_right hd] using hq
        simpa only [update, ite_eq_right hd, WorkFits, workRemaining] using ht.queueWork v hqueue

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeReceive
