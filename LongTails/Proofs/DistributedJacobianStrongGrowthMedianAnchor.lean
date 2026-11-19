import LongTails.Proofs.DistributedJacobianStrongGrowthMedianRelay

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianAnchor

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPayload
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianState
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianRelay

lemma median_final_center (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (v : Fin p.n) (s : State p) (hs : s.phase = .median 1)
    (hstate : MedianState p codes v s) :
    (finishBroadcast p s (medianDecision p codes (epochIndex p s.phase))).current =
      projectBall p p.x0 p.R (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) := by
  rw [medianDecision_broadcast p hp codes v s 1 hs (by omega) (warmWidth_pos p) hstate]
  simpa using median_final_reference p s hs codes (hstate 1 hs).1

lemma median_final_anchor (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (v : Fin p.n) (s : State p) (hs : s.phase = .median 1)
    (hstate : MedianState p codes v s) :
    (finishBroadcast p s (medianDecision p codes (epochIndex p s.phase))).anchor =
      projectBall p p.x0 p.R (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) := by
  have he : ∀ values, (finishBroadcast p s values).anchor = (finishBroadcast p s values).current := by
    intro values
    simp [finishBroadcast, hs, DistributedJacobianStrongGrowthProtocol.startRefinement_anchor,
      DistributedJacobianStrongGrowthProtocol.startRefinement_current]
  rw [he]
  exact median_final_center p hp codes v s hs hstate

lemma median_root_anchor (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hs : (workers p.root).phase = .median 1)
    (hfull : LongTails.Algorithms.DistributedLocalExtragradientTree.children p p.root ⊆
      (workers p.root).collector.seen) :
    (relay p p.root (workers p.root) (broadcastValues p (workers p.root).phase
      (fun j => (workers p.root).own j + (workers p.root).collector.total j))).anchor =
      projectBall p p.x0 p.R (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) := by
  rw [median_root_values p hp codes workers network h 1 hs (by omega) (warmWidth_pos p) hfull]
  exact median_final_anchor p hp codes p.root (workers p.root) hs (h.states p.root)

lemma median_received_anchor (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (hs : (workers v).phase = .median 1)
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent v) v = some (finish, bits)) :
    (update p v (workers v) (.received ⟨p.parent v, bits⟩)).anchor =
      projectBall p p.x0 p.R (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) := by
  have he : epochIndex p (workers v).phase < warmWidth p (localDepth p) := by
    simp only [hs, epochIndex]
    have hw := warmWidth_pos p
    omega
  have hd := medianContent_decode_down p codes workers network h v hv finish bits hpending he
  simp only [update]
  rw [ite_eq_left (show v ≠ p.root ∧ True from ⟨hv, trivial⟩)]
  change (finishBroadcast p (workers v)
    (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
      (downWidth p (workers v).phase) bits)).anchor = _
  rw [show downWidth p (workers v).phase = 1 by simp [downWidth, hs], hd]
  exact median_final_anchor p hp codes v (workers v) hs (h.states v)

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianAnchor
