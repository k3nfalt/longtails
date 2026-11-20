import LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTime
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthSampleReference
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeDispatch
import LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthFallbackExecution

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

open DistributedJacobianStrongGrowthFallbackContent
open DistributedJacobianStrongGrowthFallbackTime
open DistributedJacobianStrongGrowthTimeExecution

def FallbackInvariant (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : Prop :=
  FallbackContent p g samples S idle c ∧ TimedState p g S idle c

lemma fallbackInvariant_fields (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle)) (h : FallbackInvariant p g samples S idle c)
    (hw : next.workers = c.workers) (ho : next.oracle = c.oracle) (hwake : next.wakeTime = c.wakeTime) :
    FallbackInvariant p g samples S idle next := by
  refine ⟨?_, timedState_fields p g S idle c next h.2 hw ho hwake⟩
  simpa only [FallbackContent, hw, ho] using h.1

lemma fallbackInvariant_step (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : FallbackInvariant p g samples S idle c) (hn : NoOverdue p g S idle c) (hpark : Parked p g S idle c)
    (hdeadline : c.deadline < idle) (hh : Handshake p c.workers c.oracle.communication)
    (hr : ∀ i, RoutingShape p i (c.workers i)) (hb : ∀ i, PhaseBounds p (c.workers i).phase)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (hsamples : ∀ i, (c.oracle.computation i).samples = samples)
    (hs : step (system p g S) (algorithm p idle) c = some next) : FallbackInvariant p g samples S idle next := by
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
          exact ⟨h.1, timedState_time p g S idle c _ h.2⟩
    | some result =>
        obtain ⟨⟨v, notification⟩, oracle⟩ := result
        have hi : c.time < idle := (le_of_not_gt hlate).trans_lt hdeadline
        let notified : ExecutionState (system p g S) (algorithm p idle) :=
          { c with workers := Function.update c.workers v (update p v (c.workers v) notification), oracle := oracle, wakeTime := Function.update c.wakeTime v c.time }
        have hcontent : FallbackContent p g samples S idle notified :=
          fallbackContent_event p g samples S idle c v notification oracle h.1 hm hsamples he
        have htimed : TimedState p g S idle notified :=
          fallbackTimed_event p hp g S idle c v notification oracle h.2 hn hpark hi hh hr hb hm h.1.2 he
        have hmu := pending_notification p g S idle c v notification oracle hm he
          (by
            intro message hnotification hparent
            subst notification
            exact parent_event_idle p g S idle c v message oracle hh hr he hparent)
        have hquery : FallbackInvariant p g samples S idle
            (queryTransition p g S idle notified v (query p v (notified.workers v)).1 (query p v (notified.workers v)).2) :=
          ⟨fallbackContent_query p g samples S idle notified v hcontent,
            fallbackTimed_query p g samples S idle notified v (hcontent.1 v) htimed
              (by simpa [notified, Function.update, algorithm] using hmu v)
              hi (by simp [notified, Function.update])⟩
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
                apply fallbackInvariant_fields p g samples S idle _ _ hquery
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
                apply fallbackInvariant_fields p g samples S idle _ _ hquery
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]
                · rfl
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv]
            | advance code =>
                dsimp only at hs
                have hstate := Option.some.inj hs
                subst next
                apply fallbackInvariant_fields p g samples S idle _ _ hquery
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]
                · rfl
                · funext i
                  by_cases hiv : i = v <;> simp [notified, queryTransition, Function.update, hiv, algorithm]

lemma fallbackInvariant_initial_run (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R)
    (hrich : ¬ 64 * (p.L / p.μ) * LongTails.Algorithms.DistributedLocalExtragradientTuning.growth p ≤ (p.n : ℝ))
    (hdeadline : deadline < idle) :
    FallbackInvariant p g (fun j => S.sample j seed.2) S idle (run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)) := by
  induction k with
  | zero => exact ⟨fallbackContent_initial p g _ S idle deadline seed hε hrich, timedState_initial p g S idle deadline seed⟩
  | succ k ih =>
      let c := run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)
      erw [DistributedExecution.run_add]
      change FallbackInvariant p g (fun j => S.sample j seed.2) S idle (run (system p g S) (algorithm p idle) 1 c)
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using ih
      | some next =>
          have hnetwork := network_initial_run p hp g S idle deadline seed k
          have hd : c.deadline < idle := by
            simpa only [c, DistributedExecution.run_deadline, initial] using hdeadline
          have hn := fallbackInvariant_step p hp g (fun j => S.sample j seed.2) S idle c next ih
            (DistributedJacobianStrongGrowthNoOverdueExecution.noOverdue_initial_run p g S idle deadline seed k)
            (parked_initial_run p g S idle deadline seed k) hd hnetwork.1
            (fun v => routingShape_initial_run p g S idle deadline seed k v)
            (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
            (fun v => pending_initial_run p hp g S idle deadline seed k v)
            (fun v => DistributedJacobianStrongGrowthSampleReference.samples_initial_run p g S idle deadline seed k v) hs
          simpa only [run, hs] using hn

end LongTails.Proofs.DistributedJacobianStrongGrowthFallbackExecution
