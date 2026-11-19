import LongTails.Proofs.DistributedJacobianStrongGrowthTimeQueue

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeNotification

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeQuery

lemma wakeFits_computed (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (value : Point p) (next : ComputationState p)
    (hn : NoOverdue p g S idle c) (hp : Parked p g S idle c) (ht : TimedState p g S idle c)
    (hm : PendingMatches p (c.workers v) (c.oracle.computation v)) (hi : c.time < idle)
    (ha : (computation p g S).answer v (c.oracle.computation v) c.time = some (value, next)) :
    WakeFits p v (update p v (c.workers v) (.computed value)) c.time := by
  obtain ⟨point, hpending⟩ := noOverdue_computed_time p g S idle c hn v value next ha
  obtain ⟨work, hwork, hquery⟩ := hm.2 c.time point hpending
  have hbusy : (c.workers v).busy = true := by
    simpa only [hpending, Option.isSome_some] using hm.1.symm
  by_cases hqueue : (c.workers v).queue = []
  · exact wakeFits_computed_empty p v (c.workers v) work point value c.time hwork hquery
      hqueue hbusy (ht.computation v c.time point hpending)
  · have hwake := active_wake_time p g S idle c v hn hp
      (queued_query_active p v (c.workers v) hqueue)
    have hold := ht.wake v (by simpa only [hwake] using hi)
    rw [hwake] at hold
    rw [DistributedJacobianStrongGrowthProtocol.update_computed p v (c.workers v) work value hwork hbusy]
    simpa only [WakeFits, ite_eq_right hqueue] using hold

lemma queueWork_computed (p : Params) (s : State p) (v : Fin p.n)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (hbusy : s.busy = true)
    (h : WorkFits p s (roundStart p (DistributedJacobianStrongGrowthPhaseProgress.epochIndex p s.phase))) :
    WorkFits p (update p v s (.computed value))
      (roundStart p (DistributedJacobianStrongGrowthPhaseProgress.epochIndex p (update p v s (.computed value)).phase)) := by
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p v s work value hs hbusy]
  exact workFits_mono p _ _ _ (le_add_of_nonneg_right zero_le)
    (workFits_reply p s work point value _ hs hq h)

lemma nonbusy_work_query_active (p : Params) (v : Fin p.n) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (hw : s.work = some work) (hb : s.busy = false) : (query p v s).1 ≠ .advance 1 := by
  cases hqueue : s.queue with
  | cons packet rest => simp [query, hqueue]
  | nil =>
      cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work <;>
        simp [query, hqueue, hw, hb, hq, clockBits]

lemma wakeFits_up_arrival (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (child : Fin p.n) (hc : child ≠ p.root)
    (bits : List Bool) (hn : NoOverdue p g S idle c) (hp : Parked p g S idle c)
    (ht : TimedState p g S idle c) (hi : c.time < idle)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p c.workers c.oracle.communication)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p c.workers c.oracle.communication)
    (hpacket : c.oracle.communication.messages child (p.parent child) = some (c.time, bits)) :
    WakeFits p (p.parent child) (c.workers (p.parent child)) c.time := by
  have he := DistributedJacobianStrongGrowthEpochOrdering.epoch_eq_of_up p c.workers c.oracle.communication
    hh ho child hc (c.time, bits) hpacket
  have htime := ht.up child hc c.time bits hpacket
  rw [← he] at htime
  have hold : (query p (p.parent child) (c.workers (p.parent child))).1 ≠ .advance 1 →
      WakeFits p (p.parent child) (c.workers (p.parent child)) c.time := by
    intro hq
    have hwake := active_wake_time p g S idle c (p.parent child) hn hp hq
    simpa only [hwake] using ht.wake (p.parent child) (by simpa only [hwake] using hi)
  by_cases hqueue : (c.workers (p.parent child)).queue = []
  · cases hw : (c.workers (p.parent child)).work with
    | none =>
        simpa only [WakeFits, hqueue, ite_true, hw] using
          (fun _ : DistributedJacobianStrongGrowthPhases.Active (c.workers (p.parent child)).phase => htime)
    | some work =>
        cases hb : (c.workers (p.parent child)).busy with
        | true => simp [WakeFits, hqueue, hw, hb]
        | false => exact hold (nonbusy_work_query_active p (p.parent child) _ work hw hb)
  · exact hold (queued_query_active p (p.parent child) _ hqueue)

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeNotification
