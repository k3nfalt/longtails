import LongTails.Proofs.DistributedJacobianStrongGrowthTimeExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeFinish
import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeTerminal

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeExecution
open DistributedJacobianStrongGrowthTimeFinish
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthRouting

lemma terminal_initial_run_done (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hidle : deadline < idle)
    (hbudget : roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ≤ deadline)
    (hterminal : step (system p g S) (algorithm p idle)
      (run (system p g S) (algorithm p idle) k (initial (system p g S) (algorithm p idle) deadline seed)) = none) :
    ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers p.root).phase = .done := by
  let c := run (system p g S) (algorithm p idle) k
    (initial (system p g S) (algorithm p idle) deadline seed)
  have ht := timedState_initial_run p hp g S idle deadline seed k hε hrich hidle
  have hnetwork := network_initial_run p hp g S idle deadline seed k
  have hb := fun v => phaseBounds_initial_run p g S idle deadline seed k v
  have hr := fun v => routingShape_initial_run p g S idle deadline seed k v
  apply DistributedJacobianStrongGrowthDeadlockExecution.terminal_initial_run_done_of_deadlines
    p hp g S idle deadline seed k hε hrich hterminal
  · intro v finish point hstored
    exact (timedState_computation_finish p g S idle c ht hb
      (fun v => noBaseline_initial_run p g S idle deadline seed k v hrich) v finish point hstored).trans hbudget
  · intro source target finish bits hstored
    exact (timedState_communication_finish p hp g S idle c ht hnetwork.1 hnetwork.2 hr hb
      source target finish bits hstored).trans hbudget

lemma execute_rich (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hidle : deadline < idle)
    (hbudget : roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ≤ deadline) :
    execute (system p g S) (algorithm p idle) deadline seed.1 seed.2 =
      output p (localDepth p) g (fun j => S.sample j seed.2) := by
  obtain ⟨k, hk⟩ := DistributedJacobianStrongGrowthTerminationExecution.termination_at_deadline
    p hp g S idle deadline seed hidle
  exact DistributedJacobianStrongGrowthRefinementExecution.refinement_execute_of_terminal
    p hp g S idle deadline seed k hε hrich hk
    (terminal_initial_run_done p hp g S idle deadline seed k hε hrich hidle hbudget hk)

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeTerminal
