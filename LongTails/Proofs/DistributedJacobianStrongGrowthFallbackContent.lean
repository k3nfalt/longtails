import LongTails.Proofs.DistributedJacobianStrongGrowthFallbackState
import LongTails.Proofs.DistributedJacobianStrongGrowthTimeDispatch

namespace LongTails.Proofs.DistributedJacobianStrongGrowthFallbackContent

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthFallbackState
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthTimeDispatch

def FallbackContent (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) : Prop :=
  (∀ v, FallbackState p g samples v (c.workers v) (c.oracle.computation v).used) ∧
    (∀ a b, c.oracle.communication.messages a b = none)

lemma fallbackContent_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (hε : p.ε < p.R)
    (hrich : ¬ 64 * (p.L / p.μ) * LongTails.Algorithms.DistributedLocalExtragradientTuning.growth p ≤ (p.n : ℝ)) :
    FallbackContent p g samples S idle (initial (system p g S) (algorithm p idle) deadline seed) := by
  exact ⟨fun v => fallbackState_initial p g samples v hε hrich, fun _ _ => rfl⟩

lemma fallbackState_computed (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (v : Fin p.n) (s : State p)
    (oracle next : ComputationState p) (time : Time) (value : Point p)
    (h : FallbackState p g samples v s oracle.used) (hm : PendingMatches p s oracle)
    (hsamples : oracle.samples = samples)
    (ha : (computation p g S).answer v oracle time = some (value, next)) :
    FallbackState p g samples v (update p v s (.computed value)) next.used := by
  obtain ⟨finish, point, hpending, _, hvalue, rfl⟩ :=
    DistributedJacobianStrongGrowthOracle.computation_received_data p g S v oracle next time value ha
  obtain ⟨work, hwork, hquery⟩ := hm.2 finish point hpending
  have hbusy : s.busy = true := by simpa only [hpending, Option.isSome_some] using hm.1.symm
  rw [DistributedJacobianStrongGrowthProtocol.update_computed p v s work value hwork hbusy]
  exact fallbackState_reply p g samples v s oracle.used work point value h hwork hquery
    (by simpa only [hsamples] using hvalue)

lemma fallbackContent_event (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : FallbackContent p g samples S idle c)
    (hm : ∀ i, PendingMatches p (c.workers i) (c.oracle.computation i))
    (hsamples : ∀ i, (c.oracle.computation i).samples = samples)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((v, notification), next)) :
    FallbackContent p g samples S idle
      { c with workers := Function.update c.workers v (update p v (c.workers v) notification), oracle := next, wakeTime := Function.update c.wakeTime v c.time } := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time v next he).1]
      constructor
      · intro i
        by_cases hiv : i = v
        · subst i
          simpa [Function.update, update, algorithm] using h.1 v
        · simpa [Function.update, hiv, algorithm] using h.1 i
      · exact h.2
  | computed value =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle) c c.time v value next he
      constructor
      · intro i
        by_cases hiv : i = v
        · subst i
          simpa [Function.update, system, algorithm] using fallbackState_computed p g samples S v (c.workers v)
            (c.oracle.computation v) oracle c.time value (h.1 v) (hm v) (hsamples v) ha
        · simpa [Function.update, hiv, system, algorithm] using h.1 i
      · exact h.2
  | received message =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle) c c.time v message next he
      obtain ⟨finish, hstored, _, _⟩ := DistributedJacobianStrongGrowthOracle.communication_received_data p S
        c.oracle.communication oracle c.time message.source v message.bits ha
      rw [h.2 message.source v] at hstored
      cases hstored

lemma fallbackContent_query (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n)
    (h : FallbackContent p g samples S idle c) :
    FallbackContent p g samples S idle
      (queryTransition p g S idle c v (query p v (c.workers v)).1 (query p v (c.workers v)).2) := by
  classical
  have hlocal := fallbackState_query p g samples v (c.workers v) (c.oracle.computation v).used (h.1 v)
  cases hq : query p v (c.workers v) with
  | mk action worker =>
      rw [hq] at hlocal
      cases action with
      | communicate packet =>
          have hn := fallbackState_no_send p g samples v (c.workers v) (c.oracle.computation v).used (h.1 v) packet
          exact False.elim (hn (congrArg Prod.fst hq))
      | compute point =>
          constructor
          · intro i
            by_cases hiv : i = v
            · subst i
              have hu := computation_submit_used p g S v (c.oracle.computation v) c.time point
              have hl : FallbackState p g samples v worker
                  ((computation p g S).submit v (c.oracle.computation v) c.time point).used := by
                rw [hu]
                exact hlocal
              simpa [queryTransition, Function.update, system, algorithm] using hl
            · simpa [queryTransition, Function.update, hiv, system, algorithm] using h.1 i
          · exact h.2
      | advance code =>
          constructor
          · intro i
            by_cases hiv : i = v
            · subst i
              simpa [queryTransition, Function.update, algorithm] using hlocal
            · simpa [queryTransition, Function.update, hiv, algorithm] using h.1 i
          · exact h.2

end LongTails.Proofs.DistributedJacobianStrongGrowthFallbackContent
