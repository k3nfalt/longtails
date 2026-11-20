import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationEvent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthTerminationRank
open DistributedJacobianStrongGrowthTerminationEvent

lemma step_progress (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c final : ExecutionState (system p g S) (algorithm p idle))
    (hh : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hpending : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hc : c.time ≤ c.deadline) (hidle : c.deadline < idle)
    (hs : step (system p g S) (algorithm p idle) c = some final) :
    executionStages p g S idle final < executionStages p g S idle c ∨
      executionStages p g S idle final = executionStages p g S idle c ∧
      executionRank p g S idle final < executionRank p g S idle c := by
  classical
  unfold step at hs
  rw [ite_eq_right (not_lt.mpr hc)] at hs
  cases he : event (system p g S) (algorithm p idle) c c.time with
  | none =>
      rw [he] at hs
      by_cases ht : c.time = c.deadline
      · simp only [ite_eq_left ht, reduceCtorEq] at hs
      · rw [ite_eq_right ht] at hs
        have hstate := Option.some.inj hs
        subst final
        exact Or.inr (time_jump_progress p g S idle c he (lt_of_le_of_ne hc ht))
  | some result =>
      obtain ⟨⟨i, notification⟩, oracle⟩ := result
      rw [he] at hs
      cases hq : query p i (update p i (c.workers i) notification) with
      | mk action worker =>
          simp only [algorithm, hq] at hs
          cases action <;> dsimp only at hs
          all_goals
            have hstate := Option.some.inj hs
            subst final
            apply event_state_progress p hp g S idle c _ i notification oracle hh hedges hroute hbounds hpending
              hc hidle he
            · simp only [hq]
              rfl
            · rfl
            · funext v
              by_cases hv : v = i <;> simp [hq, actionWake, algorithm, Function.update, hv]

lemma termination_at_deadline (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (hidle : deadline < idle) :
    ∃ k, step (system p g S) (algorithm p idle)
      (run (system p g S) (algorithm p idle) k
        (initial (system p g S) (algorithm p idle) deadline seed)) = none := by
  let start := initial (system p g S) (algorithm p idle) deadline seed
  let Inv := fun c : ExecutionState (system p g S) (algorithm p idle) =>
    ∃ m, c = run (system p g S) (algorithm p idle) m start
  apply termination_of_lex (system p g S) (algorithm p idle) Inv
    (executionStages p g S idle) (executionRank p g S idle) ?_ start ⟨0, rfl⟩
  intro c next hreach hs
  obtain ⟨m, rfl⟩ := hreach
  have hnext : next = run (system p g S) (algorithm p idle) (m + 1) start := by
    erw [DistributedExecution.run_add]
    simp only [run, hs]
  refine ⟨⟨m + 1, hnext⟩, ?_⟩
  apply step_progress p hp g S idle _ next
    (network_initial_run p hp g S idle deadline seed m).1
    (network_initial_run p hp g S idle deadline seed m).2
    (fun v => routingShape_initial_run p g S idle deadline seed m v)
    (fun v => phaseBounds_initial_run p g S idle deadline seed m v)
    (fun v => pending_initial_run p hp g S idle deadline seed m v)
  · exact DistributedExecution.run_time_le_deadline (system p g S) (algorithm p idle) start m (by change (0 : Time) ≤ deadline; exact zero_le)
  · simpa only [DistributedExecution.run_deadline, start, initial] using hidle
  · exact hs

lemma finiteEvents (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle budget : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (hidle : budget < idle) :
    FiniteEvents (system p g S) (algorithm p idle) budget seed := by
  intro deadline hdeadline
  exact termination_at_deadline p hp g S idle deadline seed (hdeadline.trans_lt hidle)

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution
