import LongTails.Proofs.DistributedJacobianStrongGrowthTimeBookkeeping
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeMessages

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeEvent

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeReceive
open DistributedJacobianStrongGrowthTimeBookkeeping
open DistributedJacobianStrongGrowthTimeMessages
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma timedState_event (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c)
    (hi : c.time < idle) (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication) (hedges : NetworkEdges p c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    TimedState p g S idle
      { c with workers := Function.update c.workers v (update p v (c.workers v) notification), oracle := next, wakeTime := Function.update c.wakeTime v c.time } := by
  classical
  have hw := wakeFits_notification p hp g S idle c v notification next hn hpark ht hi hh ho hedges hr hb hm he
  have hmTime := messageTimes_notification p hp g S idle c v notification next ht hh he
  constructor
  · intro i htime
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hw
    · simpa [Function.update, hiv, algorithm] using ht.wake i (by simpa [Function.update, hiv] using htime)
  · exact pendingTime_notification p g S idle c v notification next ht hh hr hm he
  · exact hmTime.1
  · exact hmTime.2
  · intro i hqueue
    by_cases hiv : i = v
    · subst i
      have hq : (update p v (c.workers v) notification).queue ≠ [] := by
        simpa [Function.update, algorithm] using hqueue
      simpa [Function.update, algorithm] using queueWork_notification p g S idle c v notification next ht hh hr hm he hq
    · simpa [Function.update, hiv, algorithm] using ht.queueWork i (by simpa [Function.update, hiv, algorithm] using hqueue)
  · intro i packet hpacket
    by_cases hiv : i = v
    · subst i
      have hq : packet ∈ (update p v (c.workers v) notification).queue := by
        simpa [Function.update, algorithm] using hpacket
      simpa [Function.update, algorithm] using queueCost_notification p g S idle c v notification next ht hh hr hb he packet hq
    · simpa [Function.update, hiv, algorithm] using ht.queue i packet (by simpa [Function.update, hiv, algorithm] using hpacket)

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeEvent
