import LongTails.Proofs.DistributedJacobianStrongGrowthTimeQuery

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeCompute

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeQuery

lemma timedState_compute (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n) (next : State p) (x : Point p)
    (ht : TimedState p g S idle c) (hm : PendingMatches p (c.workers v) (c.oracle.computation v))
    (hi : c.time < idle) (hwake : c.wakeTime v = c.time) (hq : query p v (c.workers v) = (.compute x, next)) :
    TimedState p g S idle
      { c with workers := Function.update c.workers v next, oracle := { c.oracle with computation := Function.update c.oracle.computation v ((computation p g S).submit v (c.oracle.computation v) c.time x) }, wakeTime := Function.update c.wakeTime v c.time } := by
  classical
  have hbefore : WakeFits p v (c.workers v) c.time := by
    simpa only [hwake] using ht.wake v (by simpa only [hwake] using hi)
  have hafter := wakeFits_compute p v (c.workers v) next x c.time hbefore hq
  obtain ⟨work, hqueue, hwork, hbusy, _, rfl⟩ :=
    DistributedJacobianStrongGrowthProtocol.query_compute_data p v (c.workers v) next x hq
  have hnone := pending_none p (c.workers v) (c.oracle.computation v) hm hbusy
  have hsubmit := DistributedJacobianStrongGrowthOracle.computation_submit_idle p g S v
    (c.oracle.computation v) c.time x hnone
  constructor
  · intro i htime
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hafter.2.2
    · simpa [Function.update, hiv, algorithm] using ht.wake i (by simpa [Function.update, hiv] using htime)
  · intro i finish point hstored
    by_cases hiv : i = v
    · subst i
      have he : some (c.time + p.computeTime, x) = some (finish, point) := by
        simpa [Function.update, system, hsubmit] using hstored
      have hf : c.time + p.computeTime = finish := congrArg Prod.fst (Option.some.inj he)
      simpa [Function.update, algorithm, ← hf] using hafter.2.1
    · have hold : (c.oracle.computation i).pending = some (finish, point) := by
        simpa [Function.update, hiv, system] using hstored
      simpa [Function.update, hiv, algorithm] using ht.computation i finish point hold
  · intro i hir finish bits hstored
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using ht.up v hir finish bits hstored
    · simpa [Function.update, hiv, algorithm] using ht.up i hir finish bits hstored
  · intro i hir finish bits hstored
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using ht.down v hir finish bits hstored
    · simpa [Function.update, hiv, algorithm] using ht.down i hir finish bits hstored
  · intro i hqueued
    by_cases hiv : i = v
    · subst i
      simp [Function.update, algorithm, hqueue] at hqueued
    · simpa [Function.update, hiv, algorithm] using ht.queueWork i (by simpa [Function.update, hiv, algorithm] using hqueued)
  · intro i packet hpacket
    by_cases hiv : i = v
    · subst i
      simp [Function.update, algorithm, hqueue] at hpacket
    · simpa [Function.update, hiv, algorithm] using ht.queue i packet (by simpa [Function.update, hiv, algorithm] using hpacket)

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeCompute
