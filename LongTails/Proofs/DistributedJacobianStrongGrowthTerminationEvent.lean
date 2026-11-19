import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationQuery
import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationNotification
import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationClock

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationEvent

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthTerminationRank
open DistributedJacobianStrongGrowthTerminationLocal
open DistributedJacobianStrongGrowthTerminationQuery
open DistributedJacobianStrongGrowthTerminationNotification
open DistributedJacobianStrongGrowthTerminationClock

lemma event_query_progress (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (hh : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hpending : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    let updated := update p i (c.workers i) notification
    stagesRemaining p (query p i updated).2.phase < stagesRemaining p (c.workers i).phase ∨
      stagesRemaining p (query p i updated).2.phase = stagesRemaining p (c.workers i).phase ∧
      workerRank p (query p i updated).2 + notificationCost p notification + actionCost p (query p i updated).1 ≤
        workerRank p (c.workers i) := by
  dsimp only
  have hn := notification_progress p hp g S idle c i notification next hh hedges hroute hbounds hpending he
  have hq := query_progress p i (update p i (c.workers i) notification)
    (phaseBounds_update p i (c.workers i) notification (hbounds i))
    (routingShape_update p i (c.workers i) notification (hroute i))
  rcases hn with hn | ⟨hne, hnr⟩
  · left
    rcases hq with hq | ⟨hqe, _⟩ <;> omega
  · rcases hq with hq | ⟨hqe, hqr⟩
    · left
      omega
    · right
      exact ⟨hqe.trans hne, by omega⟩

lemma mapped_update_balance {n : ℕ} {α : Type} (weight : α → ℕ) (workers : Fin n → α)
    (v : Fin n) (next : α) :
    (∑ i, weight (Function.update workers v next i)) + weight (workers v) =
      (∑ i, weight (workers i)) + weight next := by
  classical
  have he : (fun i => weight (Function.update workers v next i)) =
      Function.update (fun i => weight (workers i)) v (weight next) := by
    funext i
    by_cases hi : i = v <;> simp [Function.update, hi]
  rw [he]
  exact sum_update_balance _ v _

noncomputable def executionStages (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : ℕ :=
  ∑ i, stagesRemaining p (c.workers i).phase

noncomputable def executionRank (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : ℕ :=
  (∑ i, workerRank p (c.workers i)) + (∑ i, if c.wakeTime i ≤ c.deadline then 2 else 0) +
    waitFlag (system p g S) (algorithm p idle) c

lemma time_jump_progress (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none) (ht : c.time < c.deadline) :
    let next := { c with time := nextTime (event (system p g S) (algorithm p idle) c) c.time c.deadline }
    executionStages p g S idle next = executionStages p g S idle c ∧
      executionRank p g S idle next < executionRank p g S idle c := by
  refine ⟨rfl, ?_⟩
  have hbefore := waitFlag_before (system p g S) (algorithm p idle) c he ht
  have hafter := waitFlag_after_jump p g S (algorithm p idle) c ht.le
  simp only [executionRank, hbefore, hafter]
  omega

noncomputable def actionWake (p : Params) (idle time : Time) : Action (Point p) p.n → Time
  | .advance code => max time ((algorithm p idle).timer code)
  | _ => time

lemma event_state_progress (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c final : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (oracle : OracleState (system p g S))
    (hh : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hpending : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hc : c.time ≤ c.deadline) (hidle : c.deadline < idle)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), oracle))
    (hworkers : final.workers = Function.update c.workers i (query p i (update p i (c.workers i) notification)).2)
    (hdeadline : final.deadline = c.deadline)
    (hwake : final.wakeTime = Function.update c.wakeTime i
      (actionWake p idle c.time (query p i (update p i (c.workers i) notification)).1)) :
    executionStages p g S idle final < executionStages p g S idle c ∨
      executionStages p g S idle final = executionStages p g S idle c ∧
      executionRank p g S idle final < executionRank p g S idle c := by
  classical
  let action := (query p i (update p i (c.workers i) notification)).1
  let worker := (query p i (update p i (c.workers i) notification)).2
  have hprogress := event_query_progress p hp g S idle c i notification oracle hh hedges hroute hbounds hpending he
  change stagesRemaining p worker.phase < stagesRemaining p (c.workers i).phase ∨
    stagesRemaining p worker.phase = stagesRemaining p (c.workers i).phase ∧
      workerRank p worker + notificationCost p notification + actionCost p action ≤ workerRank p (c.workers i) at hprogress
  have hstages := mapped_update_balance (fun s : State p => stagesRemaining p s.phase) c.workers i worker
  have hworkers' : final.workers = Function.update c.workers i worker := hworkers
  have hsb : executionStages p g S idle final + stagesRemaining p (c.workers i).phase =
      executionStages p g S idle c + stagesRemaining p worker.phase := by
    simpa [executionStages, hworkers', Function.update, algorithm] using hstages
  rcases hprogress with hdrop | ⟨hstage, hrank⟩
  · left
    omega
  · right
    refine ⟨by omega, ?_⟩
    have hwb0 := mapped_update_balance (workerRank p) c.workers i worker
    have hwb : (∑ v, workerRank p (final.workers v)) + workerRank p (c.workers i) =
        (∑ v, workerRank p (c.workers v)) + workerRank p worker := by
      simpa [hworkers', Function.update, algorithm] using hwb0
    have hw' : final.wakeTime = Function.update c.wakeTime i (actionWake p idle c.time action) := hwake
    have hflag := waitFlag_le_one (system p g S) (algorithm p idle) final
    by_cases hcost : notificationCost p notification + actionCost p action = 0
    · have hn : notification = .wake := by
        cases notification <;> simp_all only [notificationCost] <;> omega
      have ha : action = .advance 1 := by
        by_contra hnot
        simp only [actionCost, ite_eq_right hnot] at hcost
        omega
      have hready := (DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i oracle
        (by simpa only [hn] using he)).2
      have hpark := eligible_wake_park p.n c.wakeTime c.deadline idle c.time i hidle (hready.trans hc)
      have htime : actionWake p idle c.time action = max c.time idle := by simp [ha, actionWake, algorithm, clockBits]
      simp only [executionRank, hw', hdeadline, htime]
      omega
    · have hcost4 : 4 ≤ notificationCost p notification + actionCost p action := by
        unfold actionCost at hcost ⊢
        split_ifs at hcost ⊢ <;> cases notification <;> simp_all [notificationCost]
      have htime := eligible_wake_update p.n c.wakeTime c.deadline i (actionWake p idle c.time action)
      simp only [executionRank, hw', hdeadline]
      omega

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationEvent
