import LongTails.Proofs.DistributedJacobianStrongGrowthTimeInsert
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeReplace
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeSendCost

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeSend

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeReplace
open DistributedJacobianStrongGrowthTimeQueue
open DistributedJacobianStrongGrowthTimeInsert
open DistributedJacobianStrongGrowthTimeSendCost
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering

lemma timedState_queue_tail (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (packet : Fin p.n × List Bool) (rest : List (Fin p.n × List Bool))
    (ht : TimedState p g S idle c) (hq : (c.workers v).queue = packet :: rest)
    (he : 1 ≤ epochIndex p (c.workers v).phase) (hf : WakeFits p v (c.workers v) c.time) :
    TimedState p g S idle { c with workers := Function.update c.workers v { c.workers v with queue := rest }, wakeTime := Function.update c.wakeTime v c.time } := by
  have hwork := ht.queueWork v (by simp [hq])
  apply timedState_replace p g S idle c v _ c.time ht
  · intro _
    exact wakeFits_queue_tail p hp v (c.workers v) packet rest c.time hq he hf hwork
  · exact ht.computation v
  · intro _ hneq
    exact False.elim (hneq rfl)
  · intro _
    exact hwork
  · intro item hitem
    exact ht.queue v item (by rw [hq]; exact List.mem_cons_of_mem _ hitem)

lemma timedState_sent (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (ht : TimedState p g S idle c) (hf : WakeFits p v (c.workers v) c.time) :
    TimedState p g S idle { c with workers := Function.update c.workers v { c.workers v with sent := true }, wakeTime := Function.update c.wakeTime v c.time } := by
  apply timedState_replace p g S idle c v _ c.time ht
  · intro _
    simpa only [WakeFits, WorkFits, workRemaining] using hf
  · exact ht.computation v
  · intro _ hneq
    exact False.elim (hneq rfl)
  · exact ht.queueWork v
  · exact ht.queue v

lemma timedState_send_up (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n) (hv : v ≠ p.root)
    (values : Fin p.d → ℕ) (ht : TimedState p g S idle c) (hf : WakeFits p v (c.workers v) c.time)
    (hb : PhaseBounds p (c.workers v).phase) (ha : Active (c.workers v).phase)
    (hq : (c.workers v).queue = []) (hw : (c.workers v).work = none) :
    TimedState p g S idle { c with workers := Function.update c.workers v { c.workers v with sent := true }, wakeTime := Function.update c.wakeTime v c.time, oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time v (p.parent v, naturalMessage (upWidth p (c.workers v).phase) values ++ List.replicate clockBits false) } } := by
  classical
  let localState : ExecutionState (system p g S) (algorithm p idle) :=
    { c with workers := Function.update c.workers v { c.workers v with sent := true }, wakeTime := Function.update c.wakeTime v c.time }
  have hl : TimedState p g S idle localState := timedState_sent p g S idle c v ht hf
  have hfinish := up_send_finish p hp v hv (c.workers v) c.time values hb ha hq hw hf
  have hs := timedState_submit_up p hp g S idle localState hl v hv
    (naturalMessage (upWidth p (c.workers v).phase) values ++ List.replicate clockBits false)
    (by simpa [localState, Function.update, algorithm] using hfinish)
  exact hs

lemma timedState_send_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n) (hv : v ≠ p.root)
    (bits : List Bool) (rest : List (Fin p.n × List Bool)) (ht : TimedState p g S idle c)
    (hh : Handshake p c.workers c.oracle.communication) (ho : EpochOrdering p c.workers c.oracle.communication)
    (hq : (c.workers (p.parent v)).queue = (v, bits) :: rest)
    (hf : WakeFits p (p.parent v) (c.workers (p.parent v)) c.time) :
    TimedState p g S idle { c with workers := Function.update c.workers (p.parent v) { c.workers (p.parent v) with queue := rest }, wakeTime := Function.update c.wakeTime (p.parent v) c.time, oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time (p.parent v) (v, bits ++ List.replicate clockBits false) } } := by
  classical
  have he := queued_epoch p c.workers c.oracle.communication hh ho v hv bits rest hq
  let localState : ExecutionState (system p g S) (algorithm p idle) :=
    { c with workers := Function.update c.workers (p.parent v) { c.workers (p.parent v) with queue := rest }, wakeTime := Function.update c.wakeTime (p.parent v) c.time }
  have hl : TimedState p g S idle localState := timedState_queue_tail p hp g S idle c (p.parent v) (v, bits) rest ht hq (by omega) hf
  have hcost := ht.queue (p.parent v) (v, bits) (by simp [hq])
  have hfinish := queued_send_finish p hp c.workers c.oracle.communication hh ho v hv bits rest c.time hq hf hcost
  have hne := Ne.symm (DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv)
  have hs := timedState_submit_down p hp g S idle localState hl v hv (bits ++ List.replicate clockBits false)
    (by simpa [localState, Function.update, hne, algorithm] using hfinish)
  exact hs

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeSend
