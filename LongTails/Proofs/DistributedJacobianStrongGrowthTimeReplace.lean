import LongTails.Proofs.DistributedJacobianStrongGrowthTimeMessages

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeReplace

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeWork
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthTimeMessages

lemma timedState_replace (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (v : Fin p.n) (next : State p) (wake : Time)
    (ht : TimedState p g S idle c) (hwake : wake < idle → WakeFits p v next wake)
    (hcompute : ∀ finish point, (c.oracle.computation v).pending = some (finish, point) → PendingWorkFits p next finish)
    (hchange : v ≠ p.root → epochIndex p next.phase ≠ epochIndex p (c.workers v).phase →
      c.oracle.communication.messages v (p.parent v) = none ∧ c.oracle.communication.messages (p.parent v) v = none)
    (hwork : next.queue ≠ [] → WorkFits p next (roundStart p (epochIndex p next.phase)))
    (hcost : ∀ packet, packet ∈ next.queue →
      p.l + p.β * (packet.2 ++ List.replicate clockBits false).length ≤ roundComm p (epochIndex p next.phase - 1)) :
    TimedState p g S idle { c with workers := Function.update c.workers v next, wakeTime := Function.update c.wakeTime v wake } := by
  classical
  have hm := messageTimes_replace p c.workers (Function.update c.workers v next)
    c.oracle.communication c.oracle.communication ht.up ht.down (fun _ _ _ h => h)
    (by
      intro i hir hneq
      by_cases hiv : i = v
      · subst i
        exact hchange hir (by simpa [Function.update, algorithm] using hneq)
      · exact False.elim (hneq (by simp [Function.update, hiv, algorithm])))
  constructor
  · intro i hi
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hwake (by simpa [Function.update] using hi)
    · simpa [Function.update, hiv, algorithm] using ht.wake i (by simpa [Function.update, hiv] using hi)
  · intro i finish point hstored
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hcompute finish point hstored
    · simpa [Function.update, hiv, algorithm] using ht.computation i finish point hstored
  · exact hm.1
  · exact hm.2
  · intro i hqueue
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hwork (by simpa [Function.update, algorithm] using hqueue)
    · simpa [Function.update, hiv, algorithm] using ht.queueWork i (by simpa [Function.update, hiv, algorithm] using hqueue)
  · intro i packet hpacket
    by_cases hiv : i = v
    · subst i
      simpa [Function.update, algorithm] using hcost packet (by simpa [Function.update, algorithm] using hpacket)
    · simpa [Function.update, hiv, algorithm] using ht.queue i packet (by simpa [Function.update, hiv, algorithm] using hpacket)

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeReplace
