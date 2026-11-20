import LongTails.Proofs.DistributedJacobianStrongGrowthFallbackContent
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeEvent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTime

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthFallbackState
open DistributedJacobianStrongGrowthFallbackContent
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeNotification
open DistributedJacobianStrongGrowthTimeReceive
open DistributedJacobianStrongGrowthTimeBookkeeping
open DistributedJacobianStrongGrowthTimeMessages
open DistributedJacobianStrongGrowthTimeReplace
open DistributedJacobianStrongGrowthTimeAdvance
open DistributedJacobianStrongGrowthTimeCompute
open DistributedJacobianStrongGrowthTimeQuery
open DistributedJacobianStrongGrowthTimeDispatch
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma fallbackWakeFits_notification (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c)
    (hi : c.time < idle) (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (hmessages : ∀ a b, c.oracle.communication.messages a b = none)
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
      obtain ⟨finish, hstored, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
        c.oracle.communication oracle c.time message.source v message.bits ha
      rw [hmessages message.source v] at hstored
      cases hstored

lemma fallbackTimed_event (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (ht : TimedState p g S idle c) (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c)
    (hi : c.time < idle) (hh : Handshake p c.workers c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (hmessages : ∀ a b, c.oracle.communication.messages a b = none)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    TimedState p g S idle
      { c with workers := Function.update c.workers v (update p v (c.workers v) notification), oracle := next, wakeTime := Function.update c.wakeTime v c.time } := by
  classical
  have hw := fallbackWakeFits_notification p g S idle c v notification next ht hn hpark hi hm hmessages he
  have hmsg := messageTimes_notification p hp g S idle c v notification next ht hh he
  constructor
  · intro i htime
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hw
    · simpa [Function.update, hiv, algorithm] using ht.wake i (by simpa [Function.update, hiv] using htime)
  · exact pendingTime_notification p g S idle c v notification next ht hh hr hm he
  · exact hmsg.1
  · exact hmsg.2
  · intro i hqueue
    by_cases hiv : i = v
    · subst i
      have hq : (update p v (c.workers v) notification).queue ≠ [] := by simpa [Function.update, algorithm] using hqueue
      simpa [Function.update, algorithm] using queueWork_notification p g S idle c v notification next ht hh hr hm he hq
    · simpa [Function.update, hiv, algorithm] using ht.queueWork i (by simpa [Function.update, hiv, algorithm] using hqueue)
  · intro i packet hpacket
    by_cases hiv : i = v
    · subst i
      have hq : packet ∈ (update p v (c.workers v) notification).queue := by simpa [Function.update, algorithm] using hpacket
      simpa [Function.update, algorithm] using queueCost_notification p g S idle c v notification next ht hh hr hb he packet hq
    · simpa [Function.update, hiv, algorithm] using ht.queue i packet (by simpa [Function.update, hiv, algorithm] using hpacket)

lemma fallbackTimed_finishLocal (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (x : Point p)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers p.root) (c.oracle.computation p.root))
    (hq : (c.workers p.root).queue = []) (hb : (c.workers p.root).busy = false)
    (hf : WorkFits p (c.workers p.root) c.time) :
    TimedState p g S idle
      { c with workers := Function.update c.workers p.root (finishLocal p (c.workers p.root) x), wakeTime := Function.update c.wakeTime p.root c.time } := by
  have hnone := pending_none p (c.workers p.root) (c.oracle.computation p.root) hm hb
  have hqueue : (finishLocal p (c.workers p.root) x).queue = [] :=
    (DistributedJacobianStrongGrowthNetworkExecution.finishLocal_queue p (c.workers p.root) x).trans hq
  apply timedState_replace p g S idle c p.root _ c.time ht
  · intro _
    exact wakeFits_finishLocal p p.root (c.workers p.root) c.time x hq hf
  · intro finish point hstored
    rw [hnone] at hstored
    cases hstored
  · intro hroot _
    exact False.elim (hroot rfl)
  · intro hnonempty
    exact False.elim (hnonempty hqueue)
  · intro packet hpacket
    simp only [hqueue, List.not_mem_nil] at hpacket

lemma fallbackTimed_query (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (h : FallbackState p g samples v (c.workers v) (c.oracle.computation v).used)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers v) (c.oracle.computation v))
    (hi : c.time < idle) (hwake : c.wakeTime v = c.time) :
    TimedState p g S idle (queryTransition p g S idle c v (query p v (c.workers v)).1 (query p v (c.workers v)).2) := by
  classical
  have hf : WakeFits p v (c.workers v) c.time := by simpa only [hwake] using ht.wake v (by simpa only [hwake] using hi)
  cases hw : (c.workers v).work with
  | none =>
      simpa [query, h.1, hw, h.2.1, queryTransition, clockBits, max_eq_right hi.le] using timedState_park p g S idle c v ht
  | some work =>
      cases hbusy : (c.workers v).busy with
      | true => simpa [query, h.1, hw, hbusy, queryTransition, clockBits, max_eq_right hi.le] using timedState_park p g S idle c v ht
      | false =>
          cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
          | some point =>
              have hq : query p v (c.workers v) = (.compute point, { c.workers v with busy := true }) := by
                simp [query, h.1, hw, hbusy, hquery]
              simpa only [hq, queryTransition] using timedState_compute p g S idle c v _ point ht hm hi hwake hq
          | none =>
              have hv := (fallbackState_work p g samples v (c.workers v) (c.oracle.computation v).used work h hw).1
              subst v
              have hwork : WorkFits p (c.workers p.root) c.time := by simpa [WakeFits, h.1, hw, hbusy] using hf
              simpa [query, h.1, hw, hbusy, hquery, queryTransition] using
                fallbackTimed_finishLocal p g S idle c (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)
                  ht hm h.1 hbusy hwork

end LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTime
