import LongTails.Proofs.DistributedJacobianStrongGrowthFallbackExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthTerminalWaits

namespace LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTerminal

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthFallbackState
open DistributedJacobianStrongGrowthFallbackExecution
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthTerminalWaits
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthNetworkExecution

lemma terminal_initial_run_current (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ)
    (hε : p.ε < p.R) (hrich : ¬ 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hidle : deadline < idle) (hbudget : (baselineCount p : Time) * p.computeTime ≤ deadline)
    (hterminal : step (system p g S) (algorithm p idle)
      (run (system p g S) (algorithm p idle) k (initial (system p g S) (algorithm p idle) deadline seed)) = none) :
    ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers p.root).current =
      baselineOutput p g (fun j => S.sample j seed.2) := by
  let c := run (system p g S) (algorithm p idle) k
    (initial (system p g S) (algorithm p idle) deadline seed)
  have h := fallbackInvariant_initial_run p hp g S idle deadline seed k hε hrich hidle
  have href : RootReference p g (fun j => S.sample j seed.2)
      (c.workers p.root) (c.oracle.computation p.root).used := by
    simpa [c] using (h.1.1 p.root).2.2.2
  rcases href with hbase | hdone
  · have htime := DistributedExecution.run_time_le_deadline (system p g S) (algorithm p idle)
      (initial (system p g S) (algorithm p idle) deadline seed) k zero_le
    have ht := (DistributedExecution.step_terminal_iff (system p g S) (algorithm p idle) c htime).mp hterminal
    have hdeadline : c.time = deadline := ht.1.trans
      (DistributedExecution.run_deadline (system p g S) (algorithm p idle)
        (initial (system p g S) (algorithm p idle) deadline seed) k)
    have hpark := parked_initial_run p g S idle deadline seed k
    have hbusy := (query_park_data p p.root (c.workers p.root)
      (hpark p.root (noEvent_wake p g S idle c ht.2 p.root))).2.1 _ hbase.2.2
    have hm := pending_initial_run p hp g S idle deadline seed k p.root
    cases hs : (c.oracle.computation p.root).pending with
    | none =>
        have hbad := hm.1
        simp [c, hs, hbusy] at hbad
    | some packet =>
        obtain ⟨finish, point⟩ := packet
        have hf := h.2.computation p.root finish point hs
        have hbound : finish ≤ (baselineCount p : Time) * p.computeTime := by
          have hh : finish ≤ localFinish p (c.workers p.root).phase :=
            (le_add_of_nonneg_right zero_le).trans hf
          simpa only [hbase.1, localFinish] using hh
        have hlate := noEvent_computation p g S idle c ht.2 p.root finish point hs
        exact False.elim ((hdeadline ▸ hlate).not_ge (hbound.trans hbudget))
  · exact hdone.2.2.2

lemma execute_fallback (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed)
    (hε : p.ε < p.R) (hrich : ¬ 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ))
    (hidle : deadline < idle) (hbudget : (baselineCount p : Time) * p.computeTime ≤ deadline) :
    execute (system p g S) (algorithm p idle) deadline seed.1 seed.2 =
      baselineOutput p g (fun j => S.sample j seed.2) := by
  obtain ⟨k, hk⟩ := DistributedJacobianStrongGrowthTerminationExecution.termination_at_deadline
    p hp g S idle deadline seed hidle
  rw [DistributedExecution.execute_eq_terminal (system p g S) (algorithm p idle) deadline seed k hk]
  exact terminal_initial_run_current p hp g S idle deadline seed k hε hrich hidle hbudget hk

end LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTerminal
