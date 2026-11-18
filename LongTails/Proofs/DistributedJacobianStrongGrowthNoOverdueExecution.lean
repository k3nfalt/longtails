import LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueTransitions

namespace LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthNoOverdue
open DistributedJacobianStrongGrowthNoOverdueTransitions

lemma noOverdue_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c final : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (hc : c.time ≤ c.deadline)
    (hs : step (system p g S) (algorithm p idle) c = some final) : NoOverdue p g S idle final := by
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
        exact noOverdue_time_jump p g S idle c h hc
  | some result =>
      obtain ⟨⟨i, notification⟩, oracle⟩ := result
      have hn := noOverdue_notification p g S idle c h i notification oracle he
      rw [he] at hs
      cases hq : query p i (update p i (c.workers i) notification) with
      | mk action worker =>
          let base : ExecutionState (system p g S) (algorithm p idle) :=
            { c with workers := Function.update c.workers i worker, wakeTime := Function.update c.wakeTime i c.time, turn := i.val + 1, oracle := oracle }
          have hb : NoOverdue p g S idle base :=
            noOverdue_wake p g S idle _
              (noOverdue_workers p g S idle _ hn (Function.update c.workers i worker) (i.val + 1)) i c.time le_rfl
          simp only [algorithm, hq] at hs
          cases action with
          | compute x =>
              dsimp only at hs
              have hstate := Option.some.inj hs
              subst final
              simpa [base, system, algorithm, Function.update] using noOverdue_compute_submit p g S idle base hb i x
          | communicate packet =>
              rcases packet with ⟨target, bits⟩
              dsimp only at hs
              have hstate := Option.some.inj hs
              subst final
              simpa [base, system, algorithm, Function.update] using noOverdue_communication_submit p g S idle base hb i target
                (bits ++ List.replicate clockBits false)
          | advance code =>
              dsimp only at hs
              have hstate := Option.some.inj hs
              subst final
              simpa only [base, algorithm] using noOverdue_wake p g S idle base hb i
                (max c.time ((algorithm p idle).timer code)) (le_max_left _ _)

lemma noOverdue_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (hc : c.time ≤ c.deadline) :
    NoOverdue p g S idle (run (system p g S) (algorithm p idle) k c) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using h
      | some next =>
          simpa only [run, hs] using ih next (noOverdue_step p g S idle c next h hc hs)
            (DistributedExecution.step_time_le_deadline (system p g S) (algorithm p idle) c next hc hs)

lemma noOverdue_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) :
    NoOverdue p g S idle (run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)) :=
  noOverdue_run p g S idle k _ (noOverdue_initial p g S idle deadline seed) zero_le

end LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueExecution
