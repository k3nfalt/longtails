import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementContent
import LongTails.Proofs.DistributedJacobianStrongGrowthMedianRelay

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementRelay

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementState
open DistributedJacobianStrongGrowthRefinementBroadcast
open DistributedJacobianStrongGrowthRefinementContent

lemma refinementContent_replace (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (next : State p)
    (hclear : v ≠ p.root → network.messages v (p.parent v) = none ∧ network.messages (p.parent v) v = none)
    (hstate : RefinementState p g samples v next)
    (hcollector : ∀ epoch, next.phase = .refinement epoch →
      CollectorCorrect p v (refinementValues p g samples epoch) next.collector)
    (hqueue : ∀ child bits, (child, bits) ∈ next.queue →
      warmWidth p (localDepth p) < epochIndex p next.phase →
      bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p p.root (refinementValues p g samples
          (epochIndex p next.phase - warmWidth p (localDepth p) - 1)))) :
    RefinementContent p g samples (Function.update workers v next) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hstate
    · simpa [Function.update, hi] using h.states i
  · intro i epoch hs
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hcollector epoch (by simpa [Function.update] using hs)
    · simpa [Function.update, hi] using h.collectors i epoch (by simpa [Function.update, hi] using hs)
  · intro child hc finish bits hpending epoch hs
    by_cases hv : child = v
    · subst child
      rw [(hclear hc).1] at hpending
      cases hpending
    · exact h.upward child hc finish bits hpending epoch (by simpa [Function.update, hv] using hs)
  · intro child hc finish bits hpending epoch hs
    by_cases hv : child = v
    · subst child
      rw [(hclear hc).2] at hpending
      cases hpending
    · exact h.downward child hc finish bits hpending epoch (by simpa [Function.update, hv] using hs)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hqueue child bits (by simpa [Function.update] using hmem)
        (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

lemma refinementContent_relay (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (epoch : ℕ)
    (hs : (workers v).phase = .refinement epoch) (hb : epoch < refinementCount p (localDepth p))
    (ha : (workers v).anchor = warmCenter p (warmCount p (localDepth p)) (warmWidth p (localDepth p))
      (warmSpacing p (localDepth p)) g samples)
    (hclear : v ≠ p.root → network.messages v (p.parent v) = none ∧ network.messages (p.parent v) v = none) :
    RefinementContent p g samples (Function.update workers v (relay p v (workers v)
      (subtreeValues p p.root (refinementValues p g samples epoch)))) network := by
  let values := subtreeValues p p.root (refinementValues p g samples epoch)
  have hactive : DistributedJacobianStrongGrowthPhases.Active (workers v).phase := by
    simp [hs, DistributedJacobianStrongGrowthPhases.Active]
  have hepoch := epochIndex_finishBroadcast p (workers v) values
    (by simpa only [hs, PhaseBounds] using hb) hactive
  apply refinementContent_replace p g samples workers network h v _ hclear
  · change RefinementState p g samples v (finishBroadcast p (workers v) values)
    dsimp only [values]
    rw [refinement_root_total p hp]
    exact refinementState_broadcast p g samples v (workers v) epoch hs hb (h.states v) ha
  · intro e _
    change CollectorCorrect p v _ (finishBroadcast p (workers v) values).collector
    rw [DistributedJacobianStrongGrowthMedianRelay.finishBroadcast_collector p (workers v) values hactive]
    exact collectorCorrect_empty p v _
  · intro child bits hmem _
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hmem
    have hbits : bits = naturalMessage (downWidth p (workers v).phase) values := (Prod.mk.inj hu).2.symm
    change bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
      (subtreeValues p p.root (refinementValues p g samples
        (epochIndex p (finishBroadcast p (workers v) values).phase - warmWidth p (localDepth p) - 1)))
    have hi : epochIndex p (finishBroadcast p (workers v) values).phase - warmWidth p (localDepth p) - 1 = epoch := by
      rw [hepoch, hs]
      simp only [epochIndex]
      omega
    rw [hi]
    simpa only [downWidth, hs, values] using hbits

lemma refinementContent_relay_median (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (remaining : ℕ)
    (hs : (workers v).phase = .median remaining)
    (hpos : 0 < remaining) (hle : remaining ≤ warmWidth p (localDepth p)) (values : Fin p.d → ℕ)
    (hfinal : remaining = 1 → (finishBroadcast p (workers v) values).current = refinementPoint p g samples 0)
    (hclear : v ≠ p.root → network.messages v (p.parent v) = none ∧ network.messages (p.parent v) v = none) :
    RefinementContent p g samples (Function.update workers v (relay p v (workers v) values)) network := by
  have hactive : DistributedJacobianStrongGrowthPhases.Active (workers v).phase := by
    simp [hs, DistributedJacobianStrongGrowthPhases.Active]
  have hb : PhaseBounds p (workers v).phase := by simp [PhaseBounds, hs]; omega
  have hepoch := epochIndex_finishBroadcast p (workers v) values hb hactive
  apply refinementContent_replace p g samples workers network h v _ hclear
  · change RefinementState p g samples v (finishBroadcast p (workers v) values)
    by_cases hr : 1 < remaining
    · simp [RefinementState, finishBroadcast, hs, hr, startMedian]
    · have he : remaining = 1 := by omega
      subst remaining
      exact refinementState_final_median p g samples v (workers v) values hs (hfinal rfl)
  · intro epoch _
    change CollectorCorrect p v _ (finishBroadcast p (workers v) values).collector
    rw [DistributedJacobianStrongGrowthMedianRelay.finishBroadcast_collector p (workers v) values hactive]
    exact collectorCorrect_empty p v _
  · intro child bits _ he
    change warmWidth p (localDepth p) < epochIndex p (finishBroadcast p (workers v) values).phase at he
    rw [hepoch, hs] at he
    simp only [epochIndex] at he
    omega

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementRelay
