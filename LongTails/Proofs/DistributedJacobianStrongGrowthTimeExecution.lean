import LongTails.Proofs.DistributedJacobianStrongGrowthTimeEvent
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeDispatch
import LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeEvent
open DistributedJacobianStrongGrowthTimeDispatch
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthEpochExecution

lemma timedState_fields (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle)) (ht : TimedState p g S idle c)
    (hw : next.workers = c.workers) (ho : next.oracle = c.oracle) (hwake : next.wakeTime = c.wakeTime) :
    TimedState p g S idle next := by
  constructor
  · simpa only [hw, hwake] using ht.wake
  · simpa only [hw, ho] using ht.computation
  · simpa only [hw, ho] using ht.up
  · simpa only [hw, ho] using ht.down
  · simpa only [hw] using ht.queueWork
  · simpa only [hw] using ht.queue

lemma timedState_step (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (ht : TimedState p g S idle c) (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c)
    (hdeadline : c.deadline < idle) (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication) (hedges : NetworkEdges p c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (hno : ∀ i, (c.workers i).phase ≠ .baseline)
    (hs : step (system p g S) (algorithm p idle) c = some next) : TimedState p g S idle next := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate] at hs
    cases he : event (system p g S) (algorithm p idle) c c.time with
    | none =>
        rw [he] at hs
        by_cases htime : c.time = c.deadline
        · simp only [ite_eq_left htime, reduceCtorEq] at hs
        · rw [ite_eq_right htime] at hs
          have hstate := Option.some.inj hs
          subst next
          exact timedState_time p g S idle c _ ht
    | some result =>
        obtain ⟨⟨v, notification⟩, oracle⟩ := result
        have hi : c.time < idle := (le_of_not_gt hlate).trans_lt hdeadline
        let notified : ExecutionState (system p g S) (algorithm p idle) :=
          { c with workers := Function.update c.workers v (update p v (c.workers v) notification), oracle := oracle, wakeTime := Function.update c.wakeTime v c.time }
        have htimed : TimedState p g S idle notified := timedState_event p hp g S idle c v notification oracle ht hn hpark hi hh ho hedges hr hb hm he
        have hhu := handshake_notification p hp g S idle c v notification oracle hh hedges hr he
        have hou := epochOrdering_notification p hp g S idle c v notification oracle hh ho hb hedges hr he
        have hmu := pending_notification p g S idle c v notification oracle hm he
          (by
            intro message hnotification hparent
            subst notification
            exact parent_event_idle p g S idle c v message oracle hh hr he hparent)
        have hquery := timedState_query p hp g S idle notified v htimed
          (by simpa [notified, Function.update, algorithm] using hmu v) hhu hou
          (by simpa [notified, Function.update, algorithm] using routingShape_update p v (c.workers v) notification (hr v))
          (by simpa [notified, Function.update, algorithm] using phaseBounds_update p v (c.workers v) notification (hb v))
          (by simpa [notified, Function.update, algorithm] using noBaseline_update p v (c.workers v) notification (hno v))
          hi (by simp [notified, Function.update])
        have hw_eq : notified.workers v = update p v (c.workers v) notification := by
          simp [notified, Function.update, algorithm]
        rw [hw_eq] at hquery
        rw [he] at hs
        cases hq : query p v (update p v (c.workers v) notification) with
        | mk action worker =>
            rw [hq] at hquery
            simp only [algorithm, hq] at hs
            cases action with
            | compute x =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                apply timedState_fields p g S idle _ _ hquery
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]
                · rfl
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv]
            | communicate packet =>
                rcases packet with ⟨target, bits⟩
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                apply timedState_fields p g S idle _ _ hquery
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]
                · rfl
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv]
            | advance code =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                apply timedState_fields p g S idle _ _ hquery
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]
                · rfl
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]

lemma timedState_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R)
    (hrich : 64 * (p.L / p.μ) * LongTails.Algorithms.DistributedLocalExtragradientTuning.growth p ≤ (p.n : ℝ))
    (hdeadline : deadline < idle) :
    TimedState p g S idle (run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)) := by
  induction k with
  | zero => exact timedState_initial p g S idle deadline seed
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change TimedState p g S idle (run (system p g S) (algorithm p idle) 1 c)
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using ih
      | some next =>
          have hnetwork := network_initial_run p hp g S idle deadline seed k
          have hd : c.deadline < idle := by
            simpa only [c, DistributedExecution.run_deadline, initial] using hdeadline
          have hn := timedState_step p hp g S idle c next ih
            (DistributedJacobianStrongGrowthNoOverdueExecution.noOverdue_initial_run p g S idle deadline seed k)
            (parked_initial_run p g S idle deadline seed k) hd hnetwork.1
            (epochOrdering_initial_run p hp g S idle deadline seed k hε hrich) hnetwork.2
            (fun v => routingShape_initial_run p g S idle deadline seed k v)
            (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
            (fun v => pending_initial_run p hp g S idle deadline seed k v)
            (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich) hs
          simpa only [run, hs] using hn

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeExecution
