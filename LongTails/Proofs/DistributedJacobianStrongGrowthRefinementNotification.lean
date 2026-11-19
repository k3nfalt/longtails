import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementQuery
import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReceive

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementNotification

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementReceive
open DistributedJacobianStrongGrowthRefinementDown
open DistributedJacobianStrongGrowthRefinementMedian
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting
open DistributedJacobianStrongGrowthConservation
open DistributedJacobianStrongGrowthQueryAccounting
open DistributedJacobianStrongGrowthExecution

lemma refinementContent_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (samples : ℕ → p.Ω) (idle : Time)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : RefinementContent p g samples c.workers c.oracle.communication)
    (hm : MedianContent p codes c.workers c.oracle.communication)
    (hcenter : projectBall p p.x0 p.R
      (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) = refinementPoint p g samples 0)
    (hanchor : ∀ v epoch, (c.workers v).phase = .refinement epoch →
      (c.workers v).anchor = warmCenter p (warmCount p (localDepth p))
        (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples)
    (haccount : ∀ v, Accounted p (c.workers v) (c.oracle.computation v).used)
    (hpending : ∀ v, PendingMatches p (c.workers v) (c.oracle.computation v))
    (hsamples : ∀ v, (c.oracle.computation v).samples = samples)
    (hh : Handshake p c.workers c.oracle.communication)
    (ho : EpochOrdering p c.workers c.oracle.communication)
    (hedges : NetworkEdges p c.oracle.communication)
    (hroute : ∀ v, RoutingShape p v (c.workers v))
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    RefinementContent p g samples (Function.update c.workers i (update p i (c.workers i) notification))
      next.communication := by
  classical
  cases notification with
  | wake =>
      rw [(DistributedExecution.wake_event (system p g S) (algorithm p idle) c c.time i next he).1]
      apply refinementContent_congr p g samples c.workers _ c.oracle.communication h
      · intro v
        by_cases hv : v = i
        · subst v
          simpa [Function.update, update, algorithm] using h.states i
        · simpa [Function.update, hv] using h.states v
      all_goals
        intro v
        by_cases hv : v = i <;> simp [Function.update, update, hv, algorithm]
  | computed value =>
      obtain ⟨oracle, hanswer, rfl⟩ := DistributedExecution.computed_event (system p g S) (algorithm p idle)
        c c.time i value next he
      exact refinementContent_computed p g samples S c.workers c.oracle.communication h i
        (c.oracle.computation i) oracle c.time value (haccount i) (hpending i) (hsamples i) hanswer
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
          have result := refinementContent_median_down p hp g samples codes c.workers c.oracle.communication h hm hh hcenter i hd.1
            remaining hs (by omega) hb.2 finish message.bits hstored'
          simpa only [← hd.2] using result
        · rename_i epoch
          have hb : epoch < refinementCount p (localDepth p) := by
            simpa only [hs, PhaseBounds] using hbounds i
          have result := refinementContent_receive_down p hp g samples c.workers c.oracle.communication
            h hh i hd.1 epoch hs hb (hanchor i epoch hs) finish message.bits hstored'
          simpa only [← hd.2] using result
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
        have result := refinementContent_receive_up p hp g samples c.workers c.oracle.communication h hh ho
          hbounds (fun v => (hroute v).1.2.1)
          message.source hsource finish message.bits (by simpa only [hup] using hstored)
        simpa only [hup] using result

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementNotification
