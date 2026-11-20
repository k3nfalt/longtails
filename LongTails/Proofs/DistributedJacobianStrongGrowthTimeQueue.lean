import LongTails.Proofs.DistributedJacobianStrongGrowthTimeQuery

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeQueue

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeQuery

lemma wakeFits_of_workFits (p : Params) (v : Fin p.n) (s : State p) (time : Time)
    (hq : s.queue = []) (h : WorkFits p s time) : WakeFits p v s time := by
  simp only [WakeFits, hq, ite_true]
  cases hw : s.work with
  | none =>
      intro ha
      exact (workFits_done p s time h).trans (localFinish_le_up p v s.phase ha)
  | some work => exact fun _ => h

lemma wakeFits_queue_tail (p : Params) (hp : valid p) (v : Fin p.n) (s : State p)
    (packet : Fin p.n × List Bool) (rest : List (Fin p.n × List Bool)) (time : Time)
    (hq : s.queue = packet :: rest) (he : 1 ≤ epochIndex p s.phase)
    (h : WakeFits p v s time)
    (hw : WorkFits p s (roundStart p (epochIndex p s.phase))) :
    WakeFits p v { s with queue := rest } time := by
  have ht : time ≤ downDeadline p (epochIndex p s.phase - 1) v := by
    simpa [WakeFits, hq] using h
  by_cases hr : rest = []
  · subst rest
    apply wakeFits_of_workFits p v _ time rfl
    have heq : epochIndex p s.phase - 1 + 1 = epochIndex p s.phase := by omega
    have hstart : time ≤ roundStart p (epochIndex p s.phase) := by
      simpa only [heq] using ht.trans (downDeadline_le_next p hp (epochIndex p s.phase - 1) v)
    exact workFits_mono p s time _ hstart hw
  · simpa [WakeFits, hr] using ht

lemma queueWork_tail (p : Params) (s : State p) (rest : List (Fin p.n × List Bool))
    (h : WorkFits p s (roundStart p (epochIndex p s.phase))) :
    WorkFits p { s with queue := rest } (roundStart p (epochIndex p { s with queue := rest }.phase)) := h

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeQueue
