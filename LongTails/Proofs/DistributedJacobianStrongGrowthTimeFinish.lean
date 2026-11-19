import LongTails.Proofs.DistributedJacobianStrongGrowthTimeState
import LongTails.Proofs.DistributedJacobianStrongGrowthDeadlockExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeFinish

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthRouting

lemma timedState_communication_finish (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle))
    (ht : TimedState p g S idle c) (hh : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication) (hr : ∀ v, RoutingShape p v (c.workers v))
    (hb : ∀ v, PhaseBounds p (c.workers v).phase) (source target : Fin p.n) (finish : Time) (bits : List Bool)
    (hpacket : c.oracle.communication.messages source target = some (finish, bits)) :
    finish ≤ roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) := by
  have hadj := hedges source target _ hpacket
  rcases hadj.2 with hu | hd
  · have hc : source ≠ p.root := by
      intro hs
      have he := hp.2.1
      rw [hs, he] at hu
      exact hadj.1 (hs.trans hu)
    have hstored : c.oracle.communication.messages source (p.parent source) = some (finish, bits) := by
      simpa only [hu] using hpacket
    have hsent : (c.workers source).sent = true := by
      cases hs : (c.workers source).sent with
      | true => rfl
      | false =>
          have hn := up_free_of_not_sent p c.workers c.oracle.communication hh source hc hs
          rw [hstored] at hn
          cases hn
    have ha := (hr source).1.2.1 (Or.inr hsent)
    exact (ht.up source hc finish bits hstored).trans
      (deadlines_le_finish p hp _ (p.parent source)
        (DistributedJacobianStrongGrowthDeadlock.active_epoch_lt_final p _ (hb source) ha)).1
  · have hc : target ≠ p.root := by
      intro hs
      have he := hp.2.1
      rw [hs, he] at hd
      exact hadj.1 (hd.symm.trans hs.symm)
    have hstored : c.oracle.communication.messages (p.parent target) target = some (finish, bits) := by
      simpa only [hd] using hpacket
    have hsent := down_pending_sent p c.workers c.oracle.communication hh target hc finish bits hstored
    have ha := (hr target).1.2.1 (Or.inr hsent)
    exact (ht.down target hc finish bits hstored).trans
      (deadlines_le_finish p hp _ target
        (DistributedJacobianStrongGrowthDeadlock.active_epoch_lt_final p _ (hb target) ha)).2

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeFinish
