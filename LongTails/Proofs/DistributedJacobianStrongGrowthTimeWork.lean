import LongTails.Proofs.DistributedJacobianStrongGrowthTimeSchedule
import LongTails.Proofs.DistributedJacobianStrongGrowthQueryAccounting
import LongTails.Proofs.DistributedJacobianStrongGrowthParked
import LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdue

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeWork

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthQueryAccounting

noncomputable def localFinish (p : Params) : Phase → Time
  | .baseline => (baselineCount p : ℕ) * p.computeTime
  | .warming => (warmCount p (localDepth p) : ℕ) * p.computeTime
  | .median remaining => roundStart p (warmWidth p (localDepth p) - remaining)
  | .refinement epoch => roundStart p (warmWidth p (localDepth p) + epoch) +
      (2 * localDepth p : ℕ) * p.computeTime
  | .done => roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p))

def WorkFits (p : Params) (s : State p) (time : Time) : Prop :=
  time + (workRemaining p s : ℕ) * p.computeTime ≤ localFinish p s.phase

lemma workFits_reply (p : Params) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (time : Time) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (h : WorkFits p s time) :
    WorkFits p { s with work := some (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value), busy := false }
      (time + p.computeTime) := by
  have hd := DistributedJacobianStrongGrowthWorker.reply_decreases p work value point hq
  simp only [WorkFits, workRemaining, hs] at h ⊢
  rw [← hd, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at h
  convert h using 1
  ring

lemma workFits_done (p : Params) (s : State p) (time : Time)
    (h : WorkFits p s time) : time ≤ localFinish p s.phase :=
  (le_add_of_nonneg_right zero_le).trans h

lemma workFits_finish_warming (p : Params) (s : State p) (time : Time) (x : Point p)
    (hs : s.phase = .warming) (h : WorkFits p s time) :
    WorkFits p (finishLocal p s x) time := by
  have ht := workFits_done p s time h
  simpa [WorkFits, finishLocal, hs, startMedian, workRemaining, localFinish,
    roundStart_zero] using ht

lemma workFits_startRefinement (p : Params) (s : State p) (epoch : ℕ) (time : Time)
    (he : epoch ≤ refinementCount p (localDepth p))
    (ht : time ≤ roundStart p (warmWidth p (localDepth p) + epoch)) :
    WorkFits p (startRefinement p epoch s) time := by
  unfold startRefinement
  split_ifs with hk
  · simp only [WorkFits, workRemaining, localFinish,
      LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries]
    exact add_le_add ht le_rfl
  · have heq : epoch = refinementCount p (localDepth p) := by omega
    simpa [WorkFits, workRemaining, localFinish, heq] using ht

lemma active_wake_time (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (hn : DistributedJacobianStrongGrowthNoOverdue.NoOverdue p g S idle c)
    (hp : DistributedJacobianStrongGrowthParked.Parked p g S idle c)
    (hq : (query p v (c.workers v)).1 ≠ .advance 1) : c.wakeTime v = c.time := by
  apply le_antisymm _ (hn.wake v)
  exact le_of_not_gt (fun ht => hq (hp v ht))

lemma workFits_mono (p : Params) (s : State p) (time next : Time)
    (ht : time ≤ next) (h : WorkFits p s next) : WorkFits p s time :=
  (add_le_add ht le_rfl).trans h

def PendingWorkFits (p : Params) (s : State p) (finish : Time) : Prop :=
  finish + ((workRemaining p s - 1 : ℕ) : Time) * p.computeTime ≤ localFinish p s.phase

lemma pendingWorkFits_submit (p : Params) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point : Point p) (time : Time) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (h : WorkFits p s time) : PendingWorkFits p s (time + p.computeTime) := by
  have hn : workRemaining p s ≠ 0 := by
    simp only [workRemaining, hs]
    intro hz
    have hh := (DistributedJacobianStrongGrowthWorker.query_none_iff p work).mpr hz
    rw [hq] at hh
    cases hh
  have he : workRemaining p s = (workRemaining p s - 1) + 1 := by omega
  unfold WorkFits at h
  rw [he, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at h
  unfold PendingWorkFits
  convert h using 1
  ring

lemma pendingWorkFits_reply (p : Params) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (finish : Time) (hs : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (h : PendingWorkFits p s finish) :
    WorkFits p { s with work := some (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value), busy := false } finish := by
  have hd := DistributedJacobianStrongGrowthWorker.reply_decreases p work value point hq
  have hr : LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value) =
      LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries work - 1 := by omega
  simpa only [PendingWorkFits, WorkFits, workRemaining, hs, hr] using h

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeWork
