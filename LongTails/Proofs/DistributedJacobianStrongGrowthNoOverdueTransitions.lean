import LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdue

namespace LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueTransitions

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthNoOverdue

lemma noOverdue_notification (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (i : Fin p.n) (notification : Event (Point p) (CommReply p))
    (next : OracleState (system p g S))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    NoOverdue p g S idle { c with oracle := next } := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      exact h
  | computed value =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      obtain ⟨finish, x, _, _, _, rfl⟩ :=
        DistributedJacobianStrongGrowthOracle.computation_received_data p g S i (c.oracle.computation i)
          oracle c.time value ha
      constructor
      · exact h.wake
      · intro v finish x hpending
        by_cases hv : v = i
        · subst v
          simp [Function.update, system] at hpending
        · exact h.computation v finish x (by simpa [Function.update, hv, system] using hpending)
      · exact h.communication
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      obtain ⟨finish, _, _, rfl⟩ :=
        DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
          c.time message.source i message.bits ha
      constructor
      · exact h.wake
      · exact h.computation
      · intro source target finish bits hpending
        by_cases hs : source = message.source
        · subst source
          by_cases ht : target = i
          · subst target
            simp [Function.update] at hpending
          · exact h.communication message.source target finish bits
              (by simpa [Function.update, ht, system] using hpending)
        · exact h.communication source target finish bits (by simpa [Function.update, hs, system] using hpending)

lemma noOverdue_workers (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (workers : Fin p.n → State p) (turn : ℕ) :
    NoOverdue p g S idle { c with workers := workers, turn := turn } := ⟨h.wake, h.computation, h.communication⟩

lemma noOverdue_wake (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (i : Fin p.n) (time : Time) (ht : c.time ≤ time) :
    NoOverdue p g S idle { c with wakeTime := Function.update c.wakeTime i time } := by
  classical
  refine ⟨?_, h.computation, h.communication⟩
  intro v
  by_cases hv : v = i
  · subst v
    simpa [Function.update] using ht
  · simpa [Function.update, hv] using h.wake v

lemma noOverdue_compute_submit (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (i : Fin p.n) (x : Point p) :
    NoOverdue p g S idle { c with oracle := { c.oracle with computation := Function.update c.oracle.computation i ((computation p g S).submit i (c.oracle.computation i) c.time x) } } := by
  classical
  refine ⟨h.wake, ?_, h.communication⟩
  intro v finish y hpending
  by_cases hv : v = i
  · subst v
    cases hs : (c.oracle.computation i).pending with
    | none =>
        have he : c.time + p.τ = finish := by
          have hlocal : ((computation p g S).submit i (c.oracle.computation i) c.time x).pending = some (finish, y) := by
            simpa [Function.update, system, algorithm] using hpending
          rw [DistributedJacobianStrongGrowthOracle.computation_submit_idle p g S i _ c.time x hs] at hlocal
          exact congrArg Prod.fst (Option.some.inj hlocal)
        rw [← he]
        exact le_add_of_nonneg_right zero_le
    | some packet =>
        exact h.computation i finish y (by simpa [Function.update, computation, system, hs] using hpending)
  · exact h.computation v finish y (by simpa [Function.update, hv] using hpending)

lemma noOverdue_communication_submit (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : NoOverdue p g S idle c) (i target : Fin p.n) (bits : List Bool) :
    NoOverdue p g S idle { c with oracle := { c.oracle with communication := (communication p S).submit c.oracle.communication c.time i (target, bits) } } := by
  classical
  by_cases ha : adjacent p i target
  · cases hs : c.oracle.communication.messages i target with
    | some packet => simpa [communication, ha, hs] using h
    | none =>
        refine ⟨h.wake, h.computation, ?_⟩
        intro source receiver finish payload hpending
        by_cases hi : source = i
        · subst source
          by_cases ht : receiver = target
          · subst receiver
            have he : c.time + p.l + p.β * bits.length = finish := by
              change ((communication p S).submit c.oracle.communication c.time i (target, bits)).messages i target =
                some (finish, payload) at hpending
              rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S _ c.time i target bits ha hs] at hpending
              simp only [Function.update_self] at hpending
              exact congrArg Prod.fst (Option.some.inj hpending)
            rw [← he]
            exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
          · exact h.communication i receiver finish payload
              (by simpa [communication, ha, hs, Function.update, ht] using hpending)
        · exact h.communication source receiver finish payload
            (by simpa [communication, ha, hs, Function.update, hi] using hpending)
  · simpa [communication, ha] using h

end LongTails.Proofs.DistributedJacobianStrongGrowthNoOverdueTransitions
