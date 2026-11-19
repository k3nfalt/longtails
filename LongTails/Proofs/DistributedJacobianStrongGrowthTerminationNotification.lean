import LongTails.Proofs.DistributedJacobianStrongGrowthTerminationLocal

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationNotification

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTree
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthExecution
open DistributedJacobianStrongGrowthTerminationRank
open DistributedJacobianStrongGrowthTerminationLocal

def notificationCost (p : Params) : Event (Point p) (CommReply p) → ℕ
  | .wake => 0
  | _ => 4

lemma notification_progress (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (hh : Handshake p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hpending : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    stagesRemaining p (update p i (c.workers i) notification).phase < stagesRemaining p (c.workers i).phase ∨
      stagesRemaining p (update p i (c.workers i) notification).phase = stagesRemaining p (c.workers i).phase ∧
      workerRank p (update p i (c.workers i) notification) + notificationCost p notification ≤
        workerRank p (c.workers i) := by
  classical
  cases notification with
  | wake => exact Or.inr ⟨rfl, le_rfl⟩
  | computed value =>
      obtain ⟨oracle, hanswer, _⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      obtain ⟨finish, x, hstored, _, _, _⟩ :=
        DistributedJacobianStrongGrowthOracle.computation_received_data p g S i (c.oracle.computation i)
          oracle c.time value hanswer
      obtain ⟨work, hw, hq⟩ := (hpending i).2 finish x hstored
      have hb : (c.workers i).busy = true := by
        simpa only [hstored, Option.isSome_some] using (hpending i).1.symm
      exact Or.inr ⟨stagesRemaining_computed p i (c.workers i) value,
        le_of_eq (workerRank_computed p i (c.workers i) work x value hw hb hq)⟩
  | received message =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      obtain ⟨finish, hstored, _, _⟩ :=
        DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
          c.time message.source i message.bits ha
      have hadj := hedges message.source i _ hstored
      by_cases hd : i ≠ p.root ∧ message.source = p.parent i
      · have hstored' : c.oracle.communication.messages (p.parent i) i = some (finish, message.bits) := by
          simpa only [hd.2] using hstored
        have hsent := down_pending_sent p c.workers c.oracle.communication hh i hd.1 finish message.bits hstored'
        have hactive := (hroute i).1.2.1 (Or.inr hsent)
        have hdrop := stagesRemaining_finishBroadcast p (c.workers i)
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (downWidth p (c.workers i).phase) message.bits) (hbounds i) hactive
        left
        simp only [update, ite_eq_left hd]
        change stagesRemaining p (finishBroadcast p (c.workers i) _).phase < _
        omega
      · have hup : p.parent message.source = i := by
          rcases hadj.2 with hu | hu
          · exact hu
          · exfalso
            apply hd
            refine ⟨?_, hu.symm⟩
            intro hi
            have hroot := hp.2.1
            rw [hi, hroot] at hu
            exact hadj.1 (hu.symm.trans hi.symm)
        have hsource : message.source ≠ p.root := by
          intro hs
          have hroot := hp.2.1
          rw [hs, hroot] at hup
          exact hadj.1 (hs.trans hup)
        have hf := up_pending_unseen p c.workers c.oracle.communication hh message.source hsource finish message.bits
          (by simpa only [hup] using hstored)
        have hc : message.source ∈ children p i := by simp [children, hsource, hup]
        have hdrop := workerRank_accept p (c.workers i) (children p i) message.source
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (upWidth p (c.workers i).phase) message.bits) hc (by simpa only [hup] using hf)
        right
        refine ⟨by simp [update, hd], ?_⟩
        simp only [update, ite_eq_right hd, notificationCost]
        omega

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationNotification
