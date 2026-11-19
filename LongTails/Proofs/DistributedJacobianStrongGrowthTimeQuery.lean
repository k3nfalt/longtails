import LongTails.Proofs.DistributedJacobianStrongGrowthTimeState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeQuery

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState

lemma wakeFits_compute (p : Params) (v : Fin p.n) (s next : State p) (x : Point p) (time : Time)
    (h : WakeFits p v s time) (hq : query p v s = (.compute x, next)) :
    WorkFits p s time ∧ PendingWorkFits p next (time + p.computeTime) ∧ WakeFits p v next time := by
  obtain ⟨work, hqueue, hwork, hbusy, hx, rfl⟩ :=
    DistributedJacobianStrongGrowthProtocol.query_compute_data p v s next x hq
  have hf : WorkFits p s time := by simpa [WakeFits, hqueue, hwork, hbusy] using h
  refine ⟨hf, ?_, ?_⟩
  · exact pendingWorkFits_submit p s work x time hwork hx hf
  · simp [WakeFits, hqueue, hwork]

lemma wakeFits_computed_empty (p : Params) (v : Fin p.n) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (finish : Time) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (hqueue : s.queue = []) (hbusy : s.busy = true) (h : PendingWorkFits p s finish) :
    WakeFits p v (update p v s (.computed value)) finish := by
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p v s work value hs hbusy]
  have hf := pendingWorkFits_reply p s work point value finish hs hq h
  simpa [WakeFits, hqueue] using hf

lemma queued_query_active (p : Params) (v : Fin p.n) (s : State p) (hq : s.queue ≠ []) :
    (query p v s).1 ≠ .advance 1 := by
  cases he : s.queue with
  | nil => exact False.elim (hq he)
  | cons packet rest => simp [query, he]

lemma localFinish_le_up (p : Params) (v : Fin p.n) (phase : Phase)
    (ha : Active phase) :
    localFinish p phase ≤ upDeadline p (epochIndex p phase) v := by
  cases phase with
  | baseline => cases ha
  | warming => cases ha
  | done => cases ha
  | median remaining =>
      change roundStart p (warmWidth p (localDepth p) - remaining) ≤ _
      exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
  | refinement epoch =>
      have hc : roundCompute p (warmWidth p (localDepth p) + epoch) =
          (2 * localDepth p : ℕ) * p.computeTime := ite_eq_right (by omega)
      change roundStart p (warmWidth p (localDepth p) + epoch) +
        (2 * localDepth p : ℕ) * p.computeTime ≤ _
      rw [← hc]
      exact le_add_of_nonneg_right zero_le

lemma wakeFits_finishLocal (p : Params) (v : Fin p.n) (s : State p) (time : Time) (x : Point p)
    (hqueue : s.queue = []) (hf : WorkFits p s time) :
    WakeFits p v (finishLocal p s x) time := by
  have ht := workFits_done p s time hf
  cases hs : s.phase with
  | baseline => simp [WakeFits, finishLocal, hs, hqueue, Active]
  | done => simp [WakeFits, finishLocal, hs, hqueue, Active]
  | warming =>
      have hh : time ≤ upDeadline p 0 v := by
        have hstart : time ≤ roundStart p 0 := by simpa [localFinish, hs, roundStart_zero] using ht
        exact hstart.trans ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le))
      simpa [WakeFits, finishLocal, hs, startMedian, hqueue, Active, epochIndex] using hh
  | median remaining =>
      have hh := ht.trans (localFinish_le_up p v s.phase (by simp [hs, Active]))
      simpa [WakeFits, finishLocal, hs, hqueue, Active] using hh
  | refinement epoch =>
      have hh := ht.trans (localFinish_le_up p v s.phase (by simp [hs, Active]))
      simpa [WakeFits, finishLocal, hs, hqueue, Active] using hh

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeQuery
