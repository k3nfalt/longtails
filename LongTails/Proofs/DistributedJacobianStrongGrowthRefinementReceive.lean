import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementContent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReceive

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementState
open DistributedJacobianStrongGrowthRefinementContent

lemma refinement_of_epoch (p : Params) (phase : Phase) (epoch : ℕ)
    (ha : DistributedJacobianStrongGrowthPhases.Active phase) (hb : PhaseBounds p phase)
    (he : epochIndex p phase = warmWidth p (localDepth p) + epoch) : phase = .refinement epoch := by
  cases phase <;> simp_all [DistributedJacobianStrongGrowthPhases.Active, PhaseBounds, epochIndex]
  omega

lemma refinementContent_set_collector (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (collector : Collector p.n p.d)
    (hc : ∀ epoch, (workers v).phase = .refinement epoch →
      CollectorCorrect p v (refinementValues p g samples epoch) collector) :
    RefinementContent p g samples (Function.update workers v { workers v with collector := collector }) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update, RefinementState] using h.states v
    · simpa [Function.update, hi] using h.states i
  · intro i epoch hs
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hc epoch (by simpa [Function.update] using hs)
    · simpa [Function.update, hi] using h.collectors i epoch (by simpa [Function.update, hi] using hs)
  · intro child hchild finish bits hpending epoch hs
    by_cases hv : child = v
    · subst child
      exact h.upward v hchild finish bits hpending epoch (by simpa [Function.update] using hs)
    · exact h.upward child hchild finish bits hpending epoch (by simpa [Function.update, hv] using hs)
  · intro child hchild finish bits hpending epoch hs
    by_cases hv : child = v
    · subst child
      exact h.downward v hchild finish bits hpending epoch (by simpa [Function.update] using hs)
    · exact h.downward child hchild finish bits hpending epoch (by simpa [Function.update, hv] using hs)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using h.queued v child bits (by simpa [Function.update] using hmem)
        (by simpa [Function.update] using he)
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

lemma refinementContent_accept (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v child : Fin p.n) (values : Fin p.d → ℕ)
    (hvalues : ∀ epoch, (workers v).phase = .refinement epoch →
      values = subtreeValues p child (refinementValues p g samples epoch)) :
    RefinementContent p g samples (Function.update workers v
      { workers v with collector := accept (children p v) (workers v).collector child values }) network := by
  apply refinementContent_set_collector p g samples workers network h v
  intro epoch hs
  rw [hvalues epoch hs]
  exact collectorCorrect_accept p v _ _ (h.collectors v epoch hs) child

lemma refinementContent_receive_up (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (hb : ∀ v, PhaseBounds p (workers v).phase)
    (ha : ∀ v, DistributedJacobianStrongGrowthPhases.ActiveShape p (workers v))
    (child : Fin p.n) (hc : child ≠ p.root) (finish : Time) (bits : List Bool)
    (hpending : network.messages child (p.parent child) = some (finish, bits)) :
    RefinementContent p g samples (Function.update workers (p.parent child)
      (update p (p.parent child) (workers (p.parent child)) (.received ⟨child, bits⟩)))
      ⟨Function.update network.messages child (Function.update (network.messages child) (p.parent child) none)⟩ := by
  classical
  have hreverse : ¬ (p.parent child ≠ p.root ∧ child = p.parent (p.parent child)) := by
    intro hr
    exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child (p.parent child)
      hc hr.1 rfl hr.2.symm
  have hepoch := DistributedJacobianStrongGrowthEpochOrdering.epoch_eq_of_up p workers network hh ho
    child hc (finish, bits) hpending
  have hactive := ha child (Or.inr (DistributedJacobianStrongGrowthPayload.up_pending_sent p workers network
    hh child hc (finish, bits) hpending))
  have haccept := refinementContent_accept p g samples workers network h (p.parent child) child
    (receiveNaturals p.d (upWidth p (workers (p.parent child)).phase) bits) (by
      intro epoch hs
      have hsender := refinement_of_epoch p (workers child).phase epoch hactive (hb child)
        (by rw [← hepoch, hs]; rfl)
      rw [show upWidth p (workers (p.parent child)).phase =
        refinementWidth p (localDepth p) + LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countWidth p.n by
          simp [upWidth, hs]]
      exact refinementContent_decode_up p g samples workers network h child hc finish bits hpending epoch hsender)
  have herase := refinementContent_erase p g samples _ network haccept child (p.parent child)
  simpa only [update, ite_eq_right hreverse] using herase

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReceive
