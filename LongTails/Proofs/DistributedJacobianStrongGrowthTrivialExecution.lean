import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTrivialExecution

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

def Dormant (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : Prop :=
  (∀ v, c.workers v = { phase := .done, current := p.x0, anchor := p.x0 }) ∧
    (∀ v, (c.oracle.computation v).pending = none) ∧
    (∀ a b, c.oracle.communication.messages a b = none)

lemma dormant_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) (hε : p.R ≤ p.ε) :
    Dormant p g S idle (initial (system p g S) (algorithm p idle) deadline seed) := by
  constructor
  · intro v
    simp [initial, algorithm, initialState, hε]
  · constructor
    · intro v
      rfl
    · intro a b
      rfl

lemma dormant_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (c next : ExecutionState (system p g S) (algorithm p idle))
    (h : Dormant p g S idle c) (hs : step (system p g S) (algorithm p idle) c = some next) :
    Dormant p g S idle next := by
  classical
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate] at hs
    cases he : event (system p g S) (algorithm p idle) c c.time with
    | none =>
        rw [he] at hs
        by_cases ht : c.time = c.deadline
        · simp only [ite_eq_left ht, reduceCtorEq] at hs
        · rw [ite_eq_right ht] at hs
          have hstate := Option.some.inj hs
          subst next
          exact h
    | some result =>
        obtain ⟨⟨v, notification⟩, oracle⟩ := result
        cases notification with
        | wake =>
            have horacle := (DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time v oracle he).1
            rw [he] at hs
            simp only [algorithm, update, h.1 v, query] at hs
            have hstate := Option.some.inj hs
            subst next
            constructor
            · intro i
              by_cases hiv : i = v
              · subst i
                simp [Function.update, algorithm]
              · simpa [Function.update, hiv, algorithm] using h.1 i
            · exact horacle ▸ h.2
        | computed value =>
            obtain ⟨nextOracle, ha, _⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value oracle he
            obtain ⟨finish, point, hstored, _, _, _⟩ := DistributedJacobianStrongGrowthOracle.computation_received_data p g S v
              (c.oracle.computation v) nextOracle c.time value ha
            rw [h.2.1 v] at hstored
            cases hstored
        | received message =>
            obtain ⟨nextOracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message oracle he
            obtain ⟨finish, hstored, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
              c.oracle.communication nextOracle c.time message.source v message.bits ha
            rw [h.2.2 message.source v] at hstored
            cases hstored

lemma dormant_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : Dormant p g S idle c) : Dormant p g S idle (run (system p g S) (algorithm p idle) k c) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using h
      | some next => simpa only [run, hs] using ih next (dormant_step p g S idle c next h hs)

lemma execute_trivial (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (hε : p.R ≤ p.ε) (hidle : deadline < idle) :
    execute (system p g S) (algorithm p idle) deadline seed.1 seed.2 = p.x0 := by
  obtain ⟨k, hk⟩ := DistributedJacobianStrongGrowthTerminationExecution.termination_at_deadline p hp g S idle deadline seed hidle
  rw [DistributedExecution.execute_eq_terminal (system p g S) (algorithm p idle) deadline seed k hk]
  have h := dormant_run p g S idle k _ (dormant_initial p g S idle deadline seed hε)
  change ((run (system p g S) (algorithm p idle) k
    (initial (system p g S) (algorithm p idle) deadline seed)).workers p.root).current = p.x0
  rw [h.1 p.root]

end LongTails.Proofs.DistributedJacobianStrongGrowthTrivialExecution
