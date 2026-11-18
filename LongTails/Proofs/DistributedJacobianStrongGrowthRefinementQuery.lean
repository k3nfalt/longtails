import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementSend
import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementDown
import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementMedian

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementQuery

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementLocal
open DistributedJacobianStrongGrowthRefinementSend
open DistributedJacobianStrongGrowthRefinementDown
open DistributedJacobianStrongGrowthRefinementMedian
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting

lemma refinementContent_query (p : Params) (hp : valid p) (S : Sampling p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hm : MedianContent p codes workers network)
    (hcenter : projectBall p p.x0 p.R
      (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) = refinementPoint p g samples 0)
    (hanchor : ∀ v epoch, (workers v).phase = .refinement epoch →
      (workers v).anchor = warmCenter p (warmCount p (localDepth p))
        (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples)
    (hh : Handshake p workers network)
    (ho : EpochOrdering p workers network) (hroute : ∀ v, RoutingShape p v (workers v))
    (hbounds : ∀ v, PhaseBounds p (workers v).phase)
    (i : Fin p.n) (time : Time) (hn : (workers i).phase ≠ .baseline) :
    RefinementContent p g samples (Function.update workers i (query p i (workers i)).2)
      (match (query p i (workers i)).1 with
       | .communicate packet => (communication p S).submit network time i
           (packet.1, packet.2 ++ List.replicate clockBits false)
       | _ => network) := by
  classical
  cases hqueue : (workers i).queue with
  | cons packet rest =>
      rcases packet with ⟨target, bits⟩
      have hchild := (hroute i).2.2.1.1 (target, bits) (by simp [hqueue])
      have ht : target ≠ p.root ∧ p.parent target = i := (Finset.mem_filter.mp hchild).2
      have hq : (workers (p.parent target)).queue = (target, bits) :: rest := by simpa only [ht.2] using hqueue
      simpa only [query, hqueue, ht.2, clockBits] using
        refinementContent_send_queued p hp S g samples workers network h hh ho target ht.1 time bits rest hq
  | nil =>
      cases hw : (workers i).work with
      | some work =>
          cases hb : (workers i).busy with
          | true => simpa [query, hqueue, hw, hb] using h
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  simpa [query, hqueue, hw, hb, hquery] using refinementContent_finishLocal p g samples workers network h i work hn hw hquery
              | some x =>
                  simpa [query, hqueue, hw, hb, hquery] using refinementContent_busy p g samples workers network h i
      | none =>
          by_cases hr : (workers i).ready ∧ ¬ (workers i).sent ∧ children p i ⊆ (workers i).collector.seen
          · have ha := (hroute i).1.2.1 (Or.inl hr.1)
            by_cases hi : i = p.root
            · subst i
              cases hs : (workers p.root).phase <;>
                simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
              · rename_i remaining
                have hb : 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) := by
                  simpa only [hs, PhaseBounds] using hbounds p.root
                simpa [query, hqueue, hw, hr] using refinementContent_median_root p hp g samples codes workers network h hm hcenter
                  remaining hs (by omega) hb.2 hr.2.2
              · rename_i epoch
                have hb : epoch < refinementCount p (localDepth p) := by
                  simpa only [hs, PhaseBounds] using hbounds p.root
                simpa [query, hqueue, hw, hr] using refinementContent_relay_root p hp g samples workers network h
                  epoch hs hb (hanchor p.root epoch hs) hw hr.2.2
            · simpa [query, hqueue, hw, hr, hi, clockBits] using
                refinementContent_send_totals p hp S g samples workers network h i hi time hw hr.2.2
          · simp only [query, hqueue, hw, ite_eq_right hr]
            simpa only [Function.update_eq_self] using h

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementQuery
