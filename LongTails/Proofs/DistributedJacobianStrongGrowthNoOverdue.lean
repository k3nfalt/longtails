import LongTails.Proofs.DistributedJacobianStrongGrowthOracle
import LongTails.Algorithms.DistributedLocalExtragradientProtocol

namespace LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdue

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

structure NoOverdue (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle)) : Prop where
  wake : ∀ v, c.time ≤ c.wakeTime v
  computation : ∀ v finish x, (c.oracle.computation v).pending = some (finish, x) → c.time ≤ finish
  communication : ∀ source target finish bits,
    c.oracle.communication.messages source target = some (finish, bits) → c.time ≤ finish

lemma noOverdue_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) :
    NoOverdue p g S idle (initial (system p g S) (algorithm p idle) deadline seed) := by
  constructor
  · intro v
    exact le_rfl
  · intro v finish x h
    cases h
  · intro source target finish bits h
    cases h

lemma noOverdue_time_jump (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (ht : c.time ≤ c.deadline) :
    NoOverdue p g S idle
      { c with time := nextTime (event (system p g S) (algorithm p idle) c) c.time c.deadline } := by
  have hex := DistributedJacobianStrongGrowthOracle.nextTime_exists p g S (algorithm p idle) c ht
  constructor
  · intro v
    apply DistributedExecution.nextTime_le_ready (event (system p g S) (algorithm p idle) c)
      c.time c.deadline (c.wakeTime v) hex (h.wake v)
    exact (DistributedExecution.event_ready (system p g S) (algorithm p idle) c _).mpr (Or.inr ⟨v, le_rfl⟩)
  · intro v finish x hpending
    apply DistributedExecution.nextTime_le_ready (event (system p g S) (algorithm p idle) c)
      c.time c.deadline finish hex (h.computation v finish x hpending)
    apply (DistributedExecution.event_ready (system p g S) (algorithm p idle) c finish).mpr
    left
    apply (DistributedExecution.oracle_ready (system p g S) c.oracle finish).mpr
    left
    exact ⟨v, (DistributedJacobianStrongGrowthOracle.computation_ready p g S v (c.oracle.computation v) finish).mpr
      ⟨finish, x, hpending, le_rfl⟩⟩
  · intro source target finish bits hpending
    apply DistributedExecution.nextTime_le_ready (event (system p g S) (algorithm p idle) c)
      c.time c.deadline finish hex (h.communication source target finish bits hpending)
    apply (DistributedExecution.event_ready (system p g S) (algorithm p idle) c finish).mpr
    left
    apply (DistributedExecution.oracle_ready (system p g S) c.oracle finish).mpr
    right
    exact (DistributedJacobianStrongGrowthOracle.communication_ready p S c.oracle.communication finish).mpr
      ⟨source, target, finish, bits, hpending, le_rfl⟩

lemma noOverdue_computed_time (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (v : Fin p.n) (value : Point p) (next : ComputationState p)
    (ha : (computation p g S).answer v (c.oracle.computation v) c.time = some (value, next)) :
    ∃ x, (c.oracle.computation v).pending = some (c.time, x) := by
  obtain ⟨finish, x, hs, ht, _, _⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S v (c.oracle.computation v)
      next c.time value ha
  have he := le_antisymm (h.computation v finish x hs) ht
  exact ⟨x, by simpa only [← he] using hs⟩

lemma noOverdue_received_time (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (source target : Fin p.n) (bits : List Bool) (next : CommunicationState p)
    (ha : (communication p S).answer c.oracle.communication c.time = some ((target, ⟨source, bits⟩), next)) :
    c.oracle.communication.messages source target = some (c.time, bits) := by
  obtain ⟨finish, hs, ht, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
    c.oracle.communication next c.time source target bits ha
  have he := le_antisymm (h.communication source target finish bits hs) ht
  simpa only [← he] using hs

end LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdue
