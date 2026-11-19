import LongTails.Proofs.DistributedJacobianStrongGrowthTimeState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeBroadcast

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState

lemma wakeFits_startMedian_empty (p : Params) (v : Fin p.n) (s : State p) (remaining : ℕ) (time : Time)
    (ht : time ≤ roundStart p (warmWidth p (localDepth p) - remaining)) :
    WakeFits p v { startMedian p remaining s with queue := [] } time := by
  simp only [WakeFits, startMedian, ite_true, Active, epochIndex, true_implies]
  exact ht.trans ((le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le))

lemma wakeFits_startRefinement_empty (p : Params) (v : Fin p.n) (s : State p) (epoch : ℕ) (time : Time)
    (ht : time ≤ roundStart p (warmWidth p (localDepth p) + epoch)) :
    WakeFits p v { startRefinement p epoch s with queue := [] } time := by
  unfold startRefinement
  split_ifs
  · simpa [WakeFits, WorkFits, localFinish, DistributedJacobianStrongGrowthQueryAccounting.workRemaining,
      LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries] using
      add_le_add ht (le_refl ((2 * localDepth p : ℕ) * p.τ))
  · simp [WakeFits, Active]

lemma wakeFits_finishBroadcast_empty (p : Params) (v : Fin p.n) (s : State p)
    (values : Fin p.d → ℕ) (time : Time) (hb : PhaseBounds p s.phase) (ha : Active s.phase)
    (ht : time ≤ roundStart p (epochIndex p s.phase + 1)) :
    WakeFits p v { finishBroadcast p s values with queue := [] } time := by
  cases hs : s.phase with
  | baseline => simp [hs, Active] at ha
  | warming => simp [hs, Active] at ha
  | done => simp [hs, Active] at ha
  | median remaining =>
      have hr : 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) := by simpa [PhaseBounds, hs] using hb
      simp only [finishBroadcast, hs]
      split_ifs with hrem
      · apply wakeFits_startMedian_empty
        have he : warmWidth p (localDepth p) - (remaining - 1) = warmWidth p (localDepth p) - remaining + 1 := by omega
        simpa only [hs, epochIndex, he] using ht
      · apply wakeFits_startRefinement_empty
        have he : warmWidth p (localDepth p) - remaining + 1 = warmWidth p (localDepth p) + 0 := by omega
        simpa only [hs, epochIndex, he] using ht
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      apply wakeFits_startRefinement_empty
      simpa only [hs, epochIndex, Nat.add_assoc] using ht

lemma wakeFits_relay (p : Params) (hp : valid p) (v : Fin p.n) (s : State p)
    (values : Fin p.d → ℕ) (time : Time) (hb : PhaseBounds p s.phase) (ha : Active s.phase)
    (ht : time ≤ downDeadline p (epochIndex p s.phase) v) :
    WakeFits p v (relay p v s values) time := by
  classical
  by_cases hqueue : (relay p v s values).queue = []
  · have hf := wakeFits_finishBroadcast_empty p v s values time hb ha
      (ht.trans (downDeadline_le_next p hp (epochIndex p s.phase) v))
    change (LongTails.Algorithms.DistributedLocalExtragradientTree.children p v).toList.map
      (fun child => (child, LongTails.Algorithms.LocalExtragradientQuantization.naturalMessage (downWidth p s.phase) values)) = [] at hqueue
    simpa only [relay, hqueue] using hf
  · unfold WakeFits
    rw [ite_eq_right hqueue]
    change time ≤ downDeadline p (epochIndex p (finishBroadcast p s values).phase - 1) v
    rw [epochIndex_finishBroadcast p s values hb ha, Nat.add_sub_cancel]
    exact ht

lemma workFits_startMedian_start (p : Params) (s : State p) (remaining : ℕ) :
    WorkFits p (startMedian p remaining s)
      (roundStart p (epochIndex p (startMedian p remaining s).phase)) := by
  simp [WorkFits, startMedian, localFinish, epochIndex,
    DistributedJacobianStrongGrowthQueryAccounting.workRemaining]

lemma workFits_startRefinement_start (p : Params) (s : State p) (epoch : ℕ) :
    WorkFits p (startRefinement p epoch s)
      (roundStart p (epochIndex p (startRefinement p epoch s).phase)) := by
  unfold startRefinement
  split_ifs <;> simp [WorkFits, localFinish, epochIndex,
    DistributedJacobianStrongGrowthQueryAccounting.workRemaining,
    LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries]

lemma workFits_finishBroadcast_start (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (ha : Active s.phase) : WorkFits p (finishBroadcast p s values)
      (roundStart p (epochIndex p (finishBroadcast p s values).phase)) := by
  cases hs : s.phase with
  | baseline => simp [hs, Active] at ha
  | warming => simp [hs, Active] at ha
  | done => simp [hs, Active] at ha
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · exact workFits_startMedian_start p _ _
      · exact workFits_startRefinement_start p _ _
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact workFits_startRefinement_start p _ _

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeBroadcast
