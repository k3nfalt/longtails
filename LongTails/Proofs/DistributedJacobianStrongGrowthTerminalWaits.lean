import LongTails.Proofs.DistributedJacobianStrongGrowthParked
import LongTails.Proofs.DistributedJacobianStrongGrowthExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthOracle

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminalWaits

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthLiveShape
open DistributedJacobianStrongGrowthParked
open DistributedJacobianStrongGrowthExecution

lemma noEvent_wake (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none) (v : Fin p.n) :
    c.time < c.wakeTime v := by
  by_contra hn
  have hr := (DistributedExecution.event_ready (system p g S) (algorithm p idle) c c.time).mpr
    (Or.inr ⟨v, le_of_not_gt hn⟩)
  simp [he] at hr

lemma noEvent_computation (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none)
    (v : Fin p.n) (finish : Time) (x : Point p)
    (hs : (c.oracle.computation v).pending = some (finish, x)) : c.time < finish := by
  by_contra hn
  have hc := (DistributedJacobianStrongGrowthOracle.computation_ready p g S v (c.oracle.computation v) c.time).mpr
    ⟨finish, x, hs, le_of_not_gt hn⟩
  have ho := (DistributedExecution.oracle_ready (system p g S) c.oracle c.time).mpr (Or.inl ⟨v, hc⟩)
  have hr := (DistributedExecution.event_ready (system p g S) (algorithm p idle) c c.time).mpr (Or.inl ho)
  simp [he] at hr

lemma noEvent_communication (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none)
    (source target : Fin p.n) (finish : Time) (bits : List Bool)
    (hs : c.oracle.communication.messages source target = some (finish, bits)) : c.time < finish := by
  by_contra hn
  have hc := (DistributedJacobianStrongGrowthOracle.communication_ready p S c.oracle.communication c.time).mpr
    ⟨source, target, finish, bits, hs, le_of_not_gt hn⟩
  have ho := (DistributedExecution.oracle_ready (system p g S) c.oracle c.time).mpr (Or.inr hc)
  have hr := (DistributedExecution.event_ready (system p g S) (algorithm p idle) c c.time).mpr (Or.inl ho)
  simp [he] at hr

lemma unfinished_parked_waits (p : Params) (v : Fin p.n) (s : State p) (oracle : ComputationState p)
    (hlive : LiveShape p s) (hpark : (query p v s).1 = .advance 1)
    (hmatch : PendingMatches p s oracle) (hn : s.phase ≠ .done) :
    (∃ finish x, oracle.pending = some (finish, x)) ∨ s.sent = true ∨
      ∃ child ∈ children p v, child ∉ s.collector.seen := by
  classical
  have hd := query_park_data p v s hpark
  cases hw : s.work with
  | some work =>
      left
      have hb := hd.2.1 work hw
      have hp := hmatch.1
      rw [hb] at hp
      cases hs : oracle.pending with
      | none => simp [hs] at hp
      | some packet => exact ⟨packet.1, packet.2, rfl⟩
  | none =>
      right
      by_cases hs : s.sent = true
      · exact Or.inl hs
      · right
        have hr := liveShape_unfinished p s hlive hn hw
        have hf : ¬ children p v ⊆ s.collector.seen := by
          intro hf
          exact hd.2.2 hw ⟨hr, hs, hf⟩
        exact Finset.not_subset.mp hf

lemma noEvent_unfinished_waits (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (he : event (system p g S) (algorithm p idle) c c.time = none)
    (hpark : Parked p g S idle c) (hlive : ∀ v, LiveShape p (c.workers v))
    (hmatch : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (v : Fin p.n) (hn : (c.workers v).phase ≠ .done) :
    (∃ finish x, (c.oracle.computation v).pending = some (finish, x)) ∨ (c.workers v).sent = true ∨
      ∃ child ∈ children p v, child ∉ (c.workers v).collector.seen :=
  unfinished_parked_waits p v (c.workers v) (c.oracle.computation v) (hlive v)
    (hpark v (noEvent_wake p g S idle c he v)) (hmatch v) hn

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminalWaits
