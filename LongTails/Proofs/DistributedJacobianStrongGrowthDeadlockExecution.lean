import LongTails.Proofs.DistributedJacobianStrongGrowthDeadlock
import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthDeadlockExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthDeadlock
open DistributedJacobianStrongGrowthTerminalWaits
open DistributedJacobianStrongGrowthLiveShape
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNetworkExecution
open DistributedJacobianStrongGrowthEpochExecution
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthPhaseProgress

lemma empty_terminal_initial_run_done (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    let c := run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)
    step (system p g S) (algorithm p idle) c = none →
    (∀ v, (c.oracle.computation v).pending = none) →
    (∀ source target, c.oracle.communication.messages source target = none) →
    (c.workers p.root).phase = .done := by
  intro c hterminal hcompute hnetwork
  have htime := DistributedExecution.run_time_le_deadline (system p g S) (algorithm p idle)
    (initial (system p g S) (algorithm p idle) deadline seed) k zero_le
  have he := ((DistributedExecution.step_terminal_iff (system p g S) (algorithm p idle) c htime).mp hterminal).2
  exact empty_terminal_root_done p hp g S idle c he
    (parked_initial_run p g S idle deadline seed k)
    (liveShape_initial_run p g S idle deadline seed k)
    (fun v => pending_initial_run p hp g S idle deadline seed k v)
    (network_initial_run p hp g S idle deadline seed k).1
    (epochOrdering_initial_run p hp g S idle deadline seed k hε hrich)
    (fun v => routingShape_initial_run p g S idle deadline seed k v)
    (fun v => phaseBounds_initial_run p g S idle deadline seed k v)
    (rootUnsent_initial_run p g S idle deadline seed k) hcompute hnetwork

lemma terminal_initial_run_done_of_deadlines (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    let c := run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)
    step (system p g S) (algorithm p idle) c = none →
    (∀ v finish x, (c.oracle.computation v).pending = some (finish, x) → finish ≤ deadline) →
    (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
      finish ≤ deadline) → (c.workers p.root).phase = .done := by
  classical
  intro c hterminal hcompute hnetwork
  have htime := DistributedExecution.run_time_le_deadline (system p g S) (algorithm p idle)
    (initial (system p g S) (algorithm p idle) deadline seed) k zero_le
  have ht := (DistributedExecution.step_terminal_iff (system p g S) (algorithm p idle) c htime).mp hterminal
  have hdeadline : c.time = deadline := ht.1.trans
    (DistributedExecution.run_deadline (system p g S) (algorithm p idle)
      (initial (system p g S) (algorithm p idle) deadline seed) k)
  apply empty_terminal_initial_run_done p hp g S idle deadline seed k hε hrich hterminal
  · intro v
    cases hs : (c.oracle.computation v).pending with
    | none => rfl
    | some packet =>
        obtain ⟨finish, x⟩ := packet
        have hlate := noEvent_computation p g S idle c ht.2 v finish x hs
        exact False.elim ((hdeadline ▸ hlate).not_ge (hcompute v finish x hs))
  · intro source target
    cases hs : c.oracle.communication.messages source target with
    | none => rfl
    | some packet =>
        obtain ⟨finish, bits⟩ := packet
        have hlate := noEvent_communication p g S idle c ht.2 source target finish bits hs
        exact False.elim ((hdeadline ▸ hlate).not_ge (hnetwork source target finish bits hs))

end LongTails.Proofs.DistributedJacobianStrongGrowthDeadlockExecution
