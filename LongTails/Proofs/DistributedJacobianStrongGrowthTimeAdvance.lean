import LongTails.Proofs.DistributedJacobianStrongGrowthTimeReplace
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeBroadcast
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeQuery

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeAdvance

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeReplace
open DistributedJacobianStrongGrowthTimeBroadcast
open DistributedJacobianStrongGrowthTimeQuery
open DistributedJacobianStrongGrowthTimePackets
open DistributedJacobianStrongGrowthQueryAccounting

lemma timedState_park (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (ht : TimedState p g S idle c) :
    TimedState p g S idle { c with workers := Function.update c.workers v (c.workers v), wakeTime := Function.update c.wakeTime v idle } := by
  apply timedState_replace p g S idle c v (c.workers v) idle ht
  · intro hi
    exact False.elim (lt_irrefl idle hi)
  · exact ht.computation v
  · intro _ he
    exact False.elim (he rfl)
  · exact ht.queueWork v
  · exact ht.queue v

lemma timedState_finishLocal (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n) (x : Point p)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers v) (c.oracle.computation v))
    (hq : (c.workers v).queue = []) (hb : (c.workers v).busy = false)
    (hn : (c.workers v).phase ≠ .baseline) (hf : WorkFits p (c.workers v) c.time) :
    TimedState p g S idle
      { c with workers := Function.update c.workers v (finishLocal p (c.workers v) x), wakeTime := Function.update c.wakeTime v c.time } := by
  have hnone := pending_none p (c.workers v) (c.oracle.computation v) hm hb
  have hqueue : (finishLocal p (c.workers v) x).queue = [] := by
    cases hs : (c.workers v).phase <;> simp [finishLocal, hs, startMedian, hq]
  apply timedState_replace p g S idle c v _ c.time ht
  · intro _
    exact wakeFits_finishLocal p v (c.workers v) c.time x hq hf
  · intro finish point hstored
    rw [hnone] at hstored
    cases hstored
  · intro _ he
    exact False.elim (he (epochIndex_finishLocal p (c.workers v) x hn))
  · intro hnonempty
    exact False.elim (hnonempty hqueue)
  · intro packet hpacket
    simp only [hqueue, List.not_mem_nil] at hpacket

lemma timedState_rootRelay (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (values : Fin p.d → ℕ)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers p.root) (c.oracle.computation p.root))
    (hq : (c.workers p.root).queue = []) (hw : (c.workers p.root).work = none)
    (hb : PhaseBounds p (c.workers p.root).phase) (ha : Active (c.workers p.root).phase)
    (hf : WakeFits p p.root (c.workers p.root) c.time) :
    TimedState p g S idle
      { c with workers := Function.update c.workers p.root (relay p p.root (c.workers p.root) values), wakeTime := Function.update c.wakeTime p.root c.time } := by
  have hnone := pending_none p (c.workers p.root) (c.oracle.computation p.root) hm
    (pending_no_work p (c.workers p.root) (c.oracle.computation p.root) hm hw)
  have htime : c.time ≤ upDeadline p (epochIndex p (c.workers p.root).phase) p.root := by
    have hh : Active (c.workers p.root).phase → c.time ≤ upDeadline p (epochIndex p (c.workers p.root).phase) p.root := by
      simpa only [WakeFits, hq, ite_true, hw] using hf
    exact hh ha
  apply timedState_replace p g S idle c p.root _ c.time ht
  · intro _
    exact wakeFits_relay p hp p.root (c.workers p.root) values c.time hb ha
      (htime.trans (upDeadline_le_down p _ p.root))
  · intro finish point hstored
    rw [hnone] at hstored
    cases hstored
  · intro hroot _
    exact False.elim (hroot rfl)
  · intro _
    simpa only [relay, WorkFits, workRemaining] using workFits_finishBroadcast_start p (c.workers p.root) values ha
  · intro packet hpacket
    have hc := relay_packet_time p p.root (c.workers p.root) values packet hpacket hb ha
    simpa only [relay, epochIndex_finishBroadcast p (c.workers p.root) values hb ha, Nat.add_sub_cancel] using hc

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeAdvance
