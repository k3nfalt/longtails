import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementRelay
import LongTails.Proofs.DistributedJacobianStrongGrowthMedianAnchor

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementMedian

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayload
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianRelay
open DistributedJacobianStrongGrowthMedianAnchor
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementRelay

lemma refinementContent_median_root (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hm : MedianContent p codes workers network)
    (hcenter : projectBall p p.x0 p.R
      (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) = refinementPoint p g samples 0)
    (remaining : ℕ) (hs : (workers p.root).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (hfull : children p p.root ⊆ (workers p.root).collector.seen) :
    RefinementContent p g samples (Function.update workers p.root (relay p p.root (workers p.root)
      (broadcastValues p (workers p.root).phase
        (fun j => (workers p.root).own j + (workers p.root).collector.total j)))) network := by
  rw [median_root_values p hp codes workers network hm remaining hs hpos hle hfull]
  apply refinementContent_relay_median p g samples workers network h p.root remaining hs hpos hle
  · intro he
    subst remaining
    exact (median_final_center p hp codes p.root (workers p.root) hs (hm.states p.root)).trans hcenter
  · intro hn
    exact False.elim (hn rfl)

lemma refinementContent_median_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hm : MedianContent p codes workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (hcenter : projectBall p p.x0 p.R
      (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes)) = refinementPoint p g samples 0)
    (v : Fin p.n) (hv : v ≠ p.root) (remaining : ℕ)
    (hs : (workers v).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p))
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent v) v = some (finish, bits)) :
    RefinementContent p g samples (Function.update workers v
      (update p v (workers v) (.received ⟨p.parent v, bits⟩)))
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩ := by
  classical
  have he : epochIndex p (workers v).phase < warmWidth p (localDepth p) := by
    simp only [hs, epochIndex]
    omega
  have hd := medianContent_decode_down p codes workers network hm v hv finish bits hpending he
  have hu : network.messages v (p.parent v) = none := by
    cases hstored : network.messages v (p.parent v) with
    | none => rfl
    | some packet =>
        have hedge := hh v hv
        unfold DistributedJacobianStrongGrowthHandshake.edgeLoad at hedge
        rw [hpending, hstored] at hedge
        cases hsent : (workers v).sent <;>
          simp only [Option.isSome_some, Bool.toNat_true, hsent, Bool.toNat_false] at hedge <;> omega
  let nextNetwork : CommunicationState p :=
    ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩
  have hn := DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv
  have herase := refinementContent_erase p g samples workers network h (p.parent v) v
  have hfinal : remaining = 1 → (finishBroadcast p (workers v)
      (medianDecision p codes (epochIndex p (workers v).phase))).current = refinementPoint p g samples 0 := by
    intro hr
    subst remaining
    exact (median_final_center p hp codes v (workers v) hs (hm.states v)).trans hcenter
  have hrelay := refinementContent_relay_median p g samples workers nextNetwork herase v remaining hs hpos hle
    _ hfinal (by intro _; simp [nextNetwork, Function.update, Ne.symm hn, hu])
  simp only [update]
  rw [ite_eq_left (show v ≠ p.root ∧ True from ⟨hv, trivial⟩)]
  rw [show downWidth p (workers v).phase = 1 by simp [downWidth, hs], hd]
  exact hrelay

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementMedian
