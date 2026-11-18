import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationRank

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationClock

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth

noncomputable def waitFlag {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n)
    (A : Algorithm ComputeQuery ComputeReply CommReply Output n) (c : ExecutionState O A) : ℕ :=
  if event O A c c.time = none ∧ c.time < c.deadline then 1 else 0

lemma waitFlag_le_one {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n)
    (A : Algorithm ComputeQuery ComputeReply CommReply Output n) (c : ExecutionState O A) :
    waitFlag O A c ≤ 1 := by
  unfold waitFlag
  split_ifs <;> omega

lemma waitFlag_before {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n)
    (A : Algorithm ComputeQuery ComputeReply CommReply Output n) (c : ExecutionState O A)
    (he : event O A c c.time = none) (ht : c.time < c.deadline) : waitFlag O A c = 1 := by
  simp [waitFlag, he, ht]

lemma waitFlag_after_jump {Result : Type} (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (A : Algorithm (Point p) (Point p) (CommReply p) Result p.n)
    (c : ExecutionState (system p g S) A) (ht : c.time ≤ c.deadline) :
    waitFlag (system p g S) A
      { c with time := nextTime (event (system p g S) A c) c.time c.deadline } = 0 := by
  have hex := DistributedJacobianStrongGrowthOracle.nextTime_exists p g S A c ht
  have hs := (DistributedExecution.nextTime_spec (event (system p g S) A c) c.time c.deadline hex).1.2.2
  unfold waitFlag
  split_ifs with h
  · change event (system p g S) A c
      (nextTime (event (system p g S) A c) c.time c.deadline) = none ∧
      nextTime (event (system p g S) A c) c.time c.deadline < c.deadline at h
    rcases hs with hs | hs
    · exact False.elim (h.2.ne hs)
    · rw [h.1] at hs
      simp at hs
  · rfl

lemma sum_update_balance {n : ℕ} (f : Fin n → ℕ) (v : Fin n) (value : ℕ) :
    (∑ i, Function.update f v value i) + f v = (∑ i, f i) + value := by
  classical
  have hleft := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (Function.update f v value) (Finset.mem_univ v)
  have hright := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f (Finset.mem_univ v)
  have he : (∑ i ∈ (Finset.univ : Finset (Fin n)).erase v, Function.update f v value i) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)).erase v, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Function.update, (Finset.mem_erase.mp hi).1]
  simp only [Function.update_self] at hleft
  rw [he] at hleft
  omega

lemma eligible_wake_update (n : ℕ) (wake : Fin n → Time) (deadline : Time) (v : Fin n) (time : Time) :
    (∑ i, if Function.update wake v time i ≤ deadline then 2 else 0) ≤
      (∑ i, if wake i ≤ deadline then 2 else 0) + 2 := by
  classical
  have he : (fun i => if Function.update wake v time i ≤ deadline then 2 else 0) =
      Function.update (fun i => if wake i ≤ deadline then 2 else 0) v (if time ≤ deadline then 2 else 0) := by
    funext i
    by_cases hi : i = v <;> simp [Function.update, hi]
  rw [he]
  have hb := sum_update_balance (fun i => if wake i ≤ deadline then 2 else 0) v
    (if time ≤ deadline then 2 else 0)
  split_ifs at hb ⊢ <;> omega

lemma eligible_wake_park (n : ℕ) (wake : Fin n → Time) (deadline idle time : Time) (v : Fin n)
    (hi : deadline < idle) (hw : wake v ≤ deadline) :
    (∑ i, if Function.update wake v (max time idle) i ≤ deadline then 2 else 0) + 2 =
      ∑ i, if wake i ≤ deadline then 2 else 0 := by
  classical
  have he : (fun i => if Function.update wake v (max time idle) i ≤ deadline then 2 else 0) =
      Function.update (fun i => if wake i ≤ deadline then 2 else 0) v 0 := by
    funext i
    by_cases hv : i = v
    · subst i
      simp [Function.update, not_le.mpr (hi.trans_le (le_max_right time idle))]
    · simp [Function.update, hv]
  rw [he]
  have hb := sum_update_balance (fun i => if wake i ≤ deadline then 2 else 0) v 0
  simpa [hw] using hb

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationClock
