import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementLocal

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementSend

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementLocal

lemma refinementContent_insert_up (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (finish : Time) (payload : List Bool)
    (hpayload : ∀ epoch, (workers v).phase = .refinement epoch →
      payload = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p v (refinementValues p g samples epoch)) ++
          List.replicate 64 false) :
    RefinementContent p g samples workers
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v)
        (some (finish, payload)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending epoch hs
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm.trans (hpayload epoch hs)
    · exact h.upward child hc time bits (by simpa [Function.update, hcv] using hpending) epoch hs
  · intro child hc time bits hpending epoch hs
    by_cases hpc : p.parent child = v
    · have hcv : child ≠ p.parent v := by
        intro heq
        exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child v hc hv hpc heq.symm
      exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) epoch hs
    · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) epoch hs
  · exact h.queued

lemma refinementContent_insert_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (finish : Time) (payload : List Bool)
    (hpayload : ∀ epoch, (workers v).phase = .refinement epoch →
      payload = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p p.root (refinementValues p g samples epoch)) ++
        List.replicate 64 false) :
    RefinementContent p g samples workers
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v
        (some (finish, payload)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending epoch hs
    by_cases hcp : child = p.parent v
    · have hpc : p.parent (p.parent v) ≠ v := by
        simpa only [hcp] using
          (DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp v child hv hc hcp.symm)
      exact h.upward child hc time bits (by simpa [Function.update, hcp, hpc] using hpending) epoch hs
    · exact h.upward child hc time bits (by simpa [Function.update, hcp] using hpending) epoch hs
  · intro child hc time bits hpending epoch hs
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm.trans (hpayload epoch hs)
    · by_cases hpc : p.parent child = p.parent v
      · exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) epoch hs
      · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) epoch hs
  · exact h.queued

lemma refinementContent_submit_up (p : Params) (hp : valid p) (S : Sampling p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (bits : List Bool)
    (hbits : ∀ epoch, (workers v).phase = .refinement epoch →
      bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p v (refinementValues p g samples epoch))) :
    RefinementContent p g samples workers ((communication p S).submit network time v
      (p.parent v, bits ++ List.replicate 64 false)) := by
  have hadj := DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl
  cases hstored : network.messages v (p.parent v) with
  | none =>
      rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time v (p.parent v)
        _ hadj hstored]
      apply refinementContent_insert_up p hp g samples workers network h v hv
      intro epoch hs
      rw [hbits epoch hs]
  | some packet => simpa [communication, hadj, hstored] using h

lemma refinementContent_submit_down (p : Params) (hp : valid p) (S : Sampling p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (bits : List Bool)
    (hbits : ∀ epoch, (workers v).phase = .refinement epoch →
      bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p p.root (refinementValues p g samples epoch))) :
    RefinementContent p g samples workers ((communication p S).submit network time (p.parent v)
      (v, bits ++ List.replicate 64 false)) := by
  have hadj := DistributedJacobianStrongGrowthOracle.adjacent_symm p v (p.parent v)
    (DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl)
  cases hstored : network.messages (p.parent v) v with
  | none =>
      rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time (p.parent v) v
        _ hadj hstored]
      apply refinementContent_insert_down p hp g samples workers network h v hv
      intro epoch hs
      rw [hbits epoch hs]
  | some packet => simpa [communication, hadj, hstored] using h

lemma refinement_up_payload (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (epoch : ℕ)
    (hs : (workers v).phase = .refinement epoch) (hw : (workers v).work = none)
    (hfull : children p v ⊆ (workers v).collector.seen) :
    naturalMessage (upWidth p (workers v).phase)
      (fun j => (workers v).own j + (workers v).collector.total j) =
      naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
        (subtreeValues p v (refinementValues p g samples epoch)) := by
  have hown : (workers v).own = refinementValues p g samples epoch v := by
    simpa only [hw] using ((h.states v).1 epoch hs).2
  simp only [upWidth, hs]
  congr 1
  funext j
  rw [hown]
  exact collectorCorrect_complete p hp v _ _ (h.collectors v epoch hs) hfull j

lemma refinementContent_queued_epoch (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool) (rest : List (Fin p.n × List Bool))
    (hq : (workers (p.parent v)).queue = (v, bits) :: rest)
    (epoch : ℕ) (hs : (workers v).phase = .refinement epoch) :
    bits = naturalMessage (refinementWidth p (localDepth p) + countWidth p.n)
      (subtreeValues p p.root (refinementValues p g samples epoch)) := by
  have hpos : 0 < (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) := by
    simp [hq]
  have hf := DistributedJacobianStrongGrowthHandshake.down_free_of_queued p workers network hh v hv hpos
  have hb := hh v hv
  unfold DistributedJacobianStrongGrowthHandshake.edgeLoad at hb
  have hcount : (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) = 1 := by
    cases hsent : (workers v).sent <;> simp only [hsent, Bool.toNat_false, Bool.toNat_true] at hb <;> omega
  have ho' := ho v hv
  simp only [DistributedJacobianStrongGrowthEpochOrdering.downLoad, hcount, hf,
    Option.isSome_none, Bool.toNat_false, Nat.add_zero] at ho'
  rw [hs] at ho'
  change epochIndex p (workers (p.parent v)).phase = warmWidth p (localDepth p) + epoch + 1 at ho'
  have hbits := h.queued (p.parent v) v bits (by simp [hq]) (by omega)
  have he : epochIndex p (workers (p.parent v)).phase - warmWidth p (localDepth p) - 1 = epoch := by omega
  simpa only [he] using hbits

lemma refinementContent_send_totals (p : Params) (hp : valid p) (S : Sampling p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (hw : (workers v).work = none)
    (hfull : children p v ⊆ (workers v).collector.seen) :
    RefinementContent p g samples (Function.update workers v { workers v with sent := true })
      ((communication p S).submit network time v (p.parent v,
        naturalMessage (upWidth p (workers v).phase)
          (fun j => (workers v).own j + (workers v).collector.total j) ++ List.replicate 64 false)) := by
  classical
  apply refinementContent_submit_up p hp S g samples _ network (refinementContent_sent p g samples workers network h v) v hv
  intro epoch hs
  simpa only [Function.update_self] using refinement_up_payload p hp g samples workers network h v epoch
    (by simpa only [Function.update_self] using hs) hw hfull

lemma refinementContent_send_queued (p : Params) (hp : valid p) (S : Sampling p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (time : Time) (bits : List Bool)
    (rest : List (Fin p.n × List Bool)) (hq : (workers (p.parent v)).queue = (v, bits) :: rest) :
    RefinementContent p g samples
      (Function.update workers (p.parent v) { workers (p.parent v) with queue := rest })
      ((communication p S).submit network time (p.parent v) (v, bits ++ List.replicate 64 false)) := by
  classical
  have hn := Ne.symm (DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv)
  apply refinementContent_submit_down p hp S g samples _ network
    (refinementContent_queue_tail p g samples workers network h (p.parent v) (v, bits) rest hq) v hv
  intro epoch hs
  simpa only [Function.update_of_ne hn] using
    refinementContent_queued_epoch p g samples workers network h hh ho v hv bits rest hq epoch
      (by simpa only [Function.update_of_ne hn] using hs)

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementSend
