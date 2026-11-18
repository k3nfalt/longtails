import LongTails.Proofs.DistributedJacobianStrongGrowthTimeSend
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeAdvance
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeCompute

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeDispatch

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeSend
open DistributedJacobianStrongGrowthTimeAdvance
open DistributedJacobianStrongGrowthTimeCompute
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting

noncomputable def queryTransition (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (action : Action (Point p) p.n) (worker : State p) : ExecutionState (system p g S) (algorithm p idle) :=
  match action with
  | .compute x => { c with workers := Function.update c.workers v worker, wakeTime := Function.update c.wakeTime v c.time, oracle := { c.oracle with computation := Function.update c.oracle.computation v ((computation p g S).submit v (c.oracle.computation v) c.time x) } }
  | .communicate packet => { c with workers := Function.update c.workers v worker, wakeTime := Function.update c.wakeTime v c.time, oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time v (packet.1, packet.2 ++ List.replicate clockBits false) } }
  | .advance code => { c with workers := Function.update c.workers v worker, wakeTime := Function.update c.wakeTime v (max c.time (if code = 0 then 0 else idle)) }

lemma timedState_query (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers v) (c.oracle.computation v))
    (hh : Handshake p c.workers c.oracle.communication) (ho : EpochOrdering p c.workers c.oracle.communication)
    (hr : RoutingShape p v (c.workers v)) (hb : PhaseBounds p (c.workers v).phase)
    (hn : (c.workers v).phase ≠ .baseline) (hi : c.time < idle) (hwake : c.wakeTime v = c.time) :
    TimedState p g S idle (queryTransition p g S idle c v (query p v (c.workers v)).1 (query p v (c.workers v)).2) := by
  classical
  have hf : WakeFits p v (c.workers v) c.time := by
    simpa only [hwake] using ht.wake v (by simpa only [hwake] using hi)
  cases hqueue : (c.workers v).queue with
  | cons packet rest =>
      rcases packet with ⟨target, bits⟩
      have hchild := hr.2.2.1.1 (target, bits) (by simp [hqueue])
      have htarget : target ≠ p.root ∧ p.parent target = v := (Finset.mem_filter.mp hchild).2
      have hq : (c.workers (p.parent target)).queue = (target, bits) :: rest := by simpa only [htarget.2] using hqueue
      have hfit : WakeFits p (p.parent target) (c.workers (p.parent target)) c.time := by simpa only [htarget.2] using hf
      simpa only [query, hqueue, queryTransition, htarget.2] using
        timedState_send_down p hp g S idle c target htarget.1 bits rest ht hh ho hq hfit
  | nil =>
      cases hw : (c.workers v).work with
      | some work =>
          cases hbusy : (c.workers v).busy with
          | true =>
              simpa [query, hqueue, hw, hbusy, queryTransition, clockBits, max_eq_right hi.le] using timedState_park p g S idle c v ht
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some x =>
                  have hq : query p v (c.workers v) = (.compute x, { c.workers v with busy := true }) := by
                    simp [query, hqueue, hw, hbusy, hquery]
                  simpa only [hq, queryTransition] using timedState_compute p g S idle c v _ x ht hm hi hwake hq
              | none =>
                  have hwork : WorkFits p (c.workers v) c.time := by simpa [WakeFits, hqueue, hw, hbusy] using hf
                  simpa [query, hqueue, hw, hbusy, hquery, queryTransition] using
                    timedState_finishLocal p g S idle c v (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)
                      ht hm hqueue hbusy hn hwork
      | none =>
          by_cases hready : (c.workers v).ready ∧ ¬ (c.workers v).sent ∧ children p v ⊆ (c.workers v).collector.seen
          · have ha := hr.1.2.1 (Or.inl hready.1)
            by_cases hv : v = p.root
            · subst v
              simpa [query, hqueue, hw, hready, queryTransition] using
                timedState_rootRelay p hp g S idle c
                  (broadcastValues p (c.workers p.root).phase (fun j => (c.workers p.root).own j + (c.workers p.root).collector.total j))
                  ht hm hqueue hw hb ha hf
            · simpa [query, hqueue, hw, hready, hv, queryTransition] using
                timedState_send_up p hp g S idle c v hv (fun j => (c.workers v).own j + (c.workers v).collector.total j)
                  ht hf hb ha hqueue hw
          · simp only [query, hqueue, hw, ite_eq_right hready]
            simpa [queryTransition, clockBits, max_eq_right hi.le] using timedState_park p g S idle c v ht

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeDispatch
