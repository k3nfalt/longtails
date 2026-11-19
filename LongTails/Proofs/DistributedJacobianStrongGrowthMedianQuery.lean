import LongTails.Proofs.DistributedJacobianStrongGrowthMedianSend
import LongTails.Proofs.DistributedJacobianStrongGrowthMedianRelay

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianQuery

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianLocal
open DistributedJacobianStrongGrowthMedianSend
open DistributedJacobianStrongGrowthMedianRelay
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering
open DistributedJacobianStrongGrowthRouting

lemma medianContent_query (p : Params) (hp : valid p) (S : Sampling p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (hh : Handshake p workers network)
    (ho : EpochOrdering p workers network) (hroute : ∀ v, RoutingShape p v (workers v))
    (hbounds : ∀ v, PhaseBounds p (workers v).phase)
    (i : Fin p.n) (time : Time) (hn : (workers i).phase ≠ .baseline)
    (hcodes : (workers i).phase ≠ .warming → (workers i).warmCodes = fun j => (codes i j).val)
    (hfinish : ∀ work, (workers i).work = some work →
      LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none →
      (workers i).phase = .warming →
      (finishLocal p (workers i) (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)).warmCodes =
        fun j => (codes i j).val) :
    MedianContent p codes (Function.update workers i (query p i (workers i)).2)
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
        medianContent_send_queued p hp S codes workers network h hh ho target ht.1 time bits rest hq
  | nil =>
      cases hw : (workers i).work with
      | some work =>
          cases hb : (workers i).busy with
          | true => simpa [query, hqueue, hw, hb] using h
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none =>
                  simpa [query, hqueue, hw, hb, hquery] using medianContent_finishLocal p codes workers network h i
                    (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hn (hfinish work hw hquery)
              | some x =>
                  simpa [query, hqueue, hw, hb, hquery] using medianContent_busy p codes workers network h i
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
                simpa [query, hqueue, hw, hr] using medianContent_relay_root p hp codes workers network h
                  remaining hs (by omega) hb.2 (hcodes (by simp [hs])) hr.2.2
              · rename_i epoch
                have hb : epoch < refinementCount p (localDepth p) := by
                  simpa only [hs, PhaseBounds] using hbounds p.root
                simpa [query, hqueue, hw, hr] using medianContent_relay_refinement p codes workers network h
                  p.root epoch hs hb
                  (broadcastValues p (workers p.root).phase
                    (fun j => (workers p.root).own j + (workers p.root).collector.total j))
            · simpa [query, hqueue, hw, hr, hi, clockBits] using
                medianContent_send_totals p hp S codes workers network h i hi time ha hr.2.2
          · simp only [query, hqueue, hw, ite_eq_right hr]
            simpa only [Function.update_eq_self] using h

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianQuery
