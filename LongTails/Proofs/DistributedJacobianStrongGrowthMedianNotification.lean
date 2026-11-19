import LongTails.Proofs.DistributedJacobianStrongGrowthMedianQuery

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianNotification

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.LocalExtragradientQuantization
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianLocal
open DistributedJacobianStrongGrowthMedianRelay
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthConservation

lemma medianContent_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : MedianContent p codes c.workers c.oracle.communication)
    (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (hno : ∀ v, (c.workers v).phase ≠ .baseline)
    (hcodes : ∀ v, (c.workers v).phase ≠ .warming →
      (c.workers v).warmCodes = fun j => (codes v j).val)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    MedianContent p codes (Function.update c.workers i (update p i (c.workers i) notification)) next.communication := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      apply medianContent_congr p codes c.workers _ c.oracle.communication h
      all_goals
        intro v
        by_cases hv : v = i <;> simp [Function.update, update, hv, algorithm]
  | computed value =>
      obtain ⟨oracle, _, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      exact medianContent_computed p codes c.workers c.oracle.communication h i value
  | received message =>
      obtain ⟨oracle, ha, rfl⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      obtain ⟨finish, hstored, _, rfl⟩ :=
        DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
          c.time message.source i message.bits ha
      have hadj := hedges message.source i _ hstored
      by_cases hd : i ≠ p.root ∧ message.source = p.parent i
      · have hstored' : c.oracle.communication.messages (p.parent i) i = some (finish, message.bits) := by
          simpa only [hd.2] using hstored
        have hsent := down_pending_sent p c.workers c.oracle.communication hh i hd.1 finish message.bits hstored'
        have hactive := (hroute i).1.2.1 (Or.inr hsent)
        cases hs : (c.workers i).phase <;>
          simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at hactive
        · rename_i remaining
          have hb : 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) := by
            simpa only [hs, PhaseBounds] using hbounds i
          have result := medianContent_receive_down p hp codes c.workers c.oracle.communication h hh i hd.1
            remaining hs (by omega) hb.2 (hcodes i (by simp [hs])) finish message.bits hstored'
          simpa only [← hd.2] using result
        · rename_i epoch
          have hb : epoch < refinementCount p (localDepth p) := by
            simpa only [hs, PhaseBounds] using hbounds i
          have herase := medianContent_erase p codes c.workers c.oracle.communication h (p.parent i) i
          have result := medianContent_relay_refinement p codes c.workers _ herase i epoch hs hb
            (receiveNaturals p.d (downWidth p (c.workers i).phase) message.bits)
          simpa [update, hd, hd.2] using result
      · have hup : p.parent message.source = i := by
          rcases hadj.2 with hu | hu
          · exact hu
          · exfalso
            apply hd
            refine ⟨?_, hu.symm⟩
            intro hi
            have hh := hp.2.1
            rw [hi, hh] at hu
            exact hadj.1 (hu.symm.trans hi.symm)
        have hsource : message.source ≠ p.root := by
          intro hs
          have hh := hp.2.1
          rw [hs, hh] at hup
          exact hadj.1 (hs.trans hup)
        have result := medianContent_receive_up p hp codes c.workers c.oracle.communication h hh ho
          message.source hsource finish message.bits (by simpa only [hup] using hstored)
          (by simpa only [hup] using hno i)
        simpa only [hup] using result

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianNotification
