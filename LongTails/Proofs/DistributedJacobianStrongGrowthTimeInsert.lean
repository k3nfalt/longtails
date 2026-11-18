import LongTails.Proofs.DistributedJacobianStrongGrowthTimeState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeInsert

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeState

lemma timedState_insert_up (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (ht : TimedState p g S idle c)
    (v : Fin p.n) (hv : v ≠ p.root) (finish : Time) (payload : List Bool)
    (hfinish : finish ≤ upDeadline p (epochIndex p (c.workers v).phase) (p.parent v)) :
    TimedState p g S idle { c with oracle := { c.oracle with communication :=
      ⟨Function.update c.oracle.communication.messages v (Function.update (c.oracle.communication.messages v) (p.parent v) (some (finish, payload)))⟩ } } := by
  classical
  constructor
  · exact ht.wake
  · exact ht.computation
  · intro child hc time bits hstored
    by_cases hcv : child = v
    · subst child
      have he : some (finish, payload) = some (time, bits) := by simpa [Function.update] using hstored
      have hf : finish = time := congrArg Prod.fst (Option.some.inj he)
      simpa only [← hf] using hfinish
    · exact ht.up child hc time bits (by simpa [Function.update, hcv] using hstored)
  · intro child hc time bits hstored
    by_cases hpc : p.parent child = v
    · have hcv : child ≠ p.parent v := by
        intro heq
        exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child v hc hv hpc heq.symm
      exact ht.down child hc time bits (by simpa [Function.update, hpc, hcv] using hstored)
    · exact ht.down child hc time bits (by simpa [Function.update, hpc] using hstored)
  · exact ht.queueWork
  · exact ht.queue

lemma timedState_insert_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (ht : TimedState p g S idle c)
    (v : Fin p.n) (hv : v ≠ p.root) (finish : Time) (payload : List Bool)
    (hfinish : finish ≤ downDeadline p (epochIndex p (c.workers v).phase) v) :
    TimedState p g S idle { c with oracle := { c.oracle with communication :=
      ⟨Function.update c.oracle.communication.messages (p.parent v) (Function.update (c.oracle.communication.messages (p.parent v)) v (some (finish, payload)))⟩ } } := by
  classical
  constructor
  · exact ht.wake
  · exact ht.computation
  · intro child hc time bits hstored
    by_cases hcp : child = p.parent v
    · have hpc : p.parent (p.parent v) ≠ v := by
        simpa only [hcp] using
          (DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp v child hv hc hcp.symm)
      exact ht.up child hc time bits (by simpa [Function.update, hcp, hpc] using hstored)
    · exact ht.up child hc time bits (by simpa [Function.update, hcp] using hstored)
  · intro child hc time bits hstored
    by_cases hcv : child = v
    · subst child
      have he : some (finish, payload) = some (time, bits) := by simpa [Function.update] using hstored
      have hf : finish = time := congrArg Prod.fst (Option.some.inj he)
      simpa only [← hf] using hfinish
    · by_cases hpc : p.parent child = p.parent v
      · exact ht.down child hc time bits (by simpa [Function.update, hpc, hcv] using hstored)
      · exact ht.down child hc time bits (by simpa [Function.update, hpc] using hstored)
  · exact ht.queueWork
  · exact ht.queue

lemma timedState_submit_up (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (ht : TimedState p g S idle c)
    (v : Fin p.n) (hv : v ≠ p.root) (payload : List Bool)
    (hfinish : c.time + p.latency + p.timePerBit * payload.length ≤ upDeadline p (epochIndex p (c.workers v).phase) (p.parent v)) :
    TimedState p g S idle { c with oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time v (p.parent v, payload) } } := by
  have hadj := DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl
  cases hstored : c.oracle.communication.messages v (p.parent v) with
  | none =>
      have he := DistributedJacobianStrongGrowthOracle.communication_submit_free p S c.oracle.communication c.time v (p.parent v) payload hadj hstored
      simpa only [he] using timedState_insert_up p hp g S idle c ht v hv _ payload hfinish
  | some packet => simpa [communication, hadj, hstored] using ht

lemma timedState_submit_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (ht : TimedState p g S idle c)
    (v : Fin p.n) (hv : v ≠ p.root) (payload : List Bool)
    (hfinish : c.time + p.latency + p.timePerBit * payload.length ≤ downDeadline p (epochIndex p (c.workers v).phase) v) :
    TimedState p g S idle { c with oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time (p.parent v) (v, payload) } } := by
  have hadj := DistributedJacobianStrongGrowthOracle.adjacent_symm p v (p.parent v)
    (DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl)
  cases hstored : c.oracle.communication.messages (p.parent v) v with
  | none =>
      have he := DistributedJacobianStrongGrowthOracle.communication_submit_free p S c.oracle.communication c.time (p.parent v) v payload hadj hstored
      simpa only [he] using timedState_insert_down p hp g S idle c ht v hv _ payload hfinish
  | some packet => simpa [communication, hadj, hstored] using ht

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeInsert
