import LongTails.Proofs.DistributedJacobianStrongGrowthTimeWork
import LongTails.Proofs.DistributedJacobianStrongGrowthTimePackets

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeState

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork

noncomputable def WakeFits (p : Params) (v : Fin p.n) (s : State p) (time : Time) : Prop :=
  if s.queue = [] then
    match s.work with
    | some _ => s.busy = false → WorkFits p s time
    | none => Active s.phase → time ≤ upDeadline p (epochIndex p s.phase) v
  else time ≤ downDeadline p (epochIndex p s.phase - 1) v

structure TimedState (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : Prop where
  wake : ∀ v, c.wakeTime v < idle → WakeFits p v (c.workers v) (c.wakeTime v)
  computation : ∀ v finish x, (c.oracle.computation v).pending = some (finish, x) →
    PendingWorkFits p (c.workers v) finish
  up : ∀ v, v ≠ p.root → ∀ finish bits,
    c.oracle.communication.messages v (p.parent v) = some (finish, bits) →
      finish ≤ upDeadline p (epochIndex p (c.workers v).phase) (p.parent v)
  down : ∀ v, v ≠ p.root → ∀ finish bits,
    c.oracle.communication.messages (p.parent v) v = some (finish, bits) →
      finish ≤ downDeadline p (epochIndex p (c.workers v).phase) v
  queueWork : ∀ v, (c.workers v).queue ≠ [] →
    WorkFits p (c.workers v) (roundStart p (epochIndex p (c.workers v).phase))
  queue : ∀ v packet, packet ∈ (c.workers v).queue →
    p.latency + p.timePerBit * (packet.2 ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p (c.workers v).phase - 1)

lemma wakeFits_initial (p : Params) (v : Fin p.n) : WakeFits p v (initialState p v) 0 := by
  classical
  unfold initialState
  split_ifs <;> simp [WakeFits, Active, WorkFits,
    DistributedJacobianStrongGrowthQueryAccounting.workRemaining, localFinish,
    LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries]

lemma timedState_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) :
    TimedState p g S idle (initial (system p g S) (algorithm p idle) deadline seed) := by
  constructor
  · intro v _
    exact wakeFits_initial p v
  · intro v finish x h
    cases h
  · intro v hv finish bits h
    cases h
  · intro v hv finish bits h
    cases h
  · intro v h
    exact False.elim (h (DistributedJacobianStrongGrowthHandshake.initial_bookkeeping p v).2.2)
  · intro v packet h
    have he : (initialState p v).queue = [] := by unfold initialState; split_ifs <;> rfl
    change packet ∈ (initialState p v).queue at h
    simp only [he, List.not_mem_nil] at h

lemma timedState_time (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (time : Time)
    (h : TimedState p g S idle c) : TimedState p g S idle { c with time := time } :=
  ⟨h.wake, h.computation, h.up, h.down, h.queueWork, h.queue⟩

lemma localFinish_le_finish (p : Params) (phase : Phase)
    (hb : PhaseBounds p phase) (hn : phase ≠ .baseline) :
    localFinish p phase ≤ roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) := by
  cases phase with
  | baseline => exact False.elim (hn rfl)
  | warming =>
      rw [localFinish, ← roundStart_zero]
      exact roundStart_mono p (Nat.zero_le _)
  | median remaining =>
      exact roundStart_mono p (by omega : warmWidth p (localDepth p) - remaining ≤
        warmWidth p (localDepth p) + refinementCount p (localDepth p))
  | refinement epoch =>
      have he : epoch < refinementCount p (localDepth p) := hb
      have hc : roundCompute p (warmWidth p (localDepth p) + epoch) =
          (2 * localDepth p : ℕ) * p.computeTime := ite_eq_right (by omega)
      change roundStart p (warmWidth p (localDepth p) + epoch) +
        (2 * localDepth p : ℕ) * p.computeTime ≤ _
      rw [← hc]
      calc
        _ ≤ roundStart p (warmWidth p (localDepth p) + epoch + 1) := by
          rw [roundStart_succ]
          exact le_add_of_nonneg_right zero_le
        _ ≤ _ := roundStart_mono p (by omega)
  | done => exact le_rfl

lemma timedState_computation_finish (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (h : TimedState p g S idle c) (hb : ∀ v, PhaseBounds p (c.workers v).phase)
    (hn : ∀ v, (c.workers v).phase ≠ .baseline) (v : Fin p.n) (finish : Time) (x : Point p)
    (hpending : (c.oracle.computation v).pending = some (finish, x)) :
    finish ≤ roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) := by
  have ht := h.computation v finish x hpending
  exact ((le_add_of_nonneg_right zero_le).trans ht).trans
    (localFinish_le_finish p (c.workers v).phase (hb v) (hn v))

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeState
