import LongTails.Proofs.DistributedJacobianStrongGrowthTimeReceive

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeBookkeeping

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimePackets
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma queueCost_notification (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hh : Handshake p c.workers c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next))
    (packet : Fin p.n × List Bool) (hq : packet ∈ (update p v (c.workers v) notification).queue) :
    p.l + p.β * (packet.2 ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p (update p v (c.workers v) notification).phase - 1) := by
  cases notification with
  | wake => exact ht.queue v packet hq
  | computed value =>
      cases hw : (c.workers v).work with
      | none => simpa only [update, hw] using ht.queue v packet (by simpa only [update, hw] using hq)
      | some work =>
          cases hbusy : (c.workers v).busy <;>
            simpa [update, hw, hbusy] using
              ht.queue v packet (by simpa [update, hw, hbusy] using hq)
  | received message =>
      by_cases hd : v ≠ p.root ∧ message.source = p.parent v
      · obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
        obtain ⟨finish, hstored, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
          c.oracle.communication oracle c.time message.source v message.bits ha
        have hsent := down_pending_sent p c.workers c.oracle.communication hh v hd.1 finish message.bits
          (by simpa only [hd.2] using hstored)
        have hactive := (hr v).1.2.1 (Or.inr hsent)
        have hmem : packet ∈ (relay p v (c.workers v) (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d (downWidth p (c.workers v).phase) message.bits)).queue := by
          simpa only [update, ite_eq_left hd] using hq
        have hcost := relay_packet_time p v (c.workers v) _ packet hmem (hb v) hactive
        simpa only [update, ite_eq_left hd, relay,
          epochIndex_finishBroadcast p (c.workers v) _ (hb v) hactive, Nat.add_sub_cancel] using hcost
      · simpa only [update, ite_eq_right hd] using
          ht.queue v packet (by simpa only [update, ite_eq_right hd] using hq)

lemma pendingTime_notification (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hh : Handshake p c.workers c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i))
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    ∀ i finish point, (next.computation i).pending = some (finish, point) →
      PendingWorkFits p (Function.update c.workers v (update p v (c.workers v) notification) i) finish := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time v next he).1]
      intro i finish point hstored
      by_cases hiv : i = v
      · subst i
        simpa [Function.update, update, algorithm] using ht.computation v finish point hstored
      · simpa [Function.update, update, algorithm, hiv] using ht.computation i finish point hstored
  | computed value =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value next he
      obtain ⟨endTime, x, _, _, _, rfl⟩ := DistributedJacobianStrongGrowthOracle.computation_received_data p g S
        v (c.oracle.computation v) oracle c.time value ha
      intro i finish point hstored
      by_cases hiv : i = v
      · subst i
        simp [Function.update, system] at hstored
      · have hold : (c.oracle.computation i).pending = some (finish, point) := by
          simpa [Function.update, hiv, system] using hstored
        simpa [Function.update, hiv, algorithm] using ht.computation i finish point hold
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
      intro i finish point hstored
      by_cases hiv : i = v
      · subst i
        by_cases hd : v ≠ p.root ∧ message.source = p.parent v
        · obtain ⟨endTime, hpacket, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
            c.oracle.communication oracle c.time message.source v message.bits ha
          have hbusy := down_pending_idle p c.workers c.oracle.communication hh (fun i => (hr i).1.1)
            v hd.1 endTime message.bits (by simpa only [hd.2] using hpacket)
          have hmatch := (hm v).1
          change (c.oracle.computation v).pending = some (finish, point) at hstored
          have hfalse : (true : Bool) = false := by simpa only [hstored, Option.isSome_some, hbusy] using hmatch
          cases hfalse
        · simpa [Function.update, update, hd, PendingWorkFits, workRemaining, algorithm] using
            ht.computation v finish point hstored
      · simpa [Function.update, hiv, algorithm] using ht.computation i finish point hstored

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeBookkeeping
