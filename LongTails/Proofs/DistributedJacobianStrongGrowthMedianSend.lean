import LongTails.Proofs.DistributedJacobianStrongGrowthMedianLocal

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianSend

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPayloadAggregation
open DistributedJacobianStrongGrowthMedianReference
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianLocal

lemma medianContent_insert_up (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (finish : Time) (payload : List Bool)
    (hpayload : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      payload = naturalMessage (countWidth p.n)
        (subtreeValues p v (medianValues p codes (epochIndex p (workers v).phase))) ++
          List.replicate 64 false) :
    MedianContent p codes workers
      ⟨Function.update network.messages v (Function.update (network.messages v) (p.parent v)
        (some (finish, payload)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending he
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm.trans (hpayload he)
    · exact h.upward child hc time bits (by simpa [Function.update, hcv] using hpending) he
  · intro child hc time bits hpending he
    by_cases hpc : p.parent child = v
    · have hcv : child ≠ p.parent v := by
        intro heq
        exact DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp child v hc hv hpc heq.symm
      exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) he
    · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) he
  · exact h.queued

lemma medianContent_insert_down (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (finish : Time) (payload : List Bool)
    (hpayload : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      payload = naturalMessage 1 (medianDecision p codes (epochIndex p (workers v).phase)) ++
        List.replicate 64 false) :
    MedianContent p codes workers
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v
        (some (finish, payload)))⟩ := by
  classical
  constructor
  · exact h.states
  · exact h.collectors
  · intro child hc time bits hpending he
    by_cases hcp : child = p.parent v
    · have hpc : p.parent (p.parent v) ≠ v := by
        simpa only [hcp] using
          (DistributedJacobianStrongGrowthConservation.no_reverse_edge p hp v child hv hc hcp.symm)
      exact h.upward child hc time bits (by simpa [Function.update, hcp, hpc] using hpending) he
    · exact h.upward child hc time bits (by simpa [Function.update, hcp] using hpending) he
  · intro child hc time bits hpending he
    by_cases hcv : child = v
    · subst child
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hpending
      exact hpending.2.symm.trans (hpayload he)
    · by_cases hpc : p.parent child = p.parent v
      · exact h.downward child hc time bits (by simpa [Function.update, hpc, hcv] using hpending) he
      · exact h.downward child hc time bits (by simpa [Function.update, hpc] using hpending) he
  · exact h.queued

lemma median_up_payload (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n)
    (ha : DistributedJacobianStrongGrowthPhases.Active (workers v).phase)
    (hfull : children p v ⊆ (workers v).collector.seen)
    (he : epochIndex p (workers v).phase < warmWidth p (localDepth p)) :
    naturalMessage (upWidth p (workers v).phase)
      (fun j => (workers v).own j + (workers v).collector.total j) =
        naturalMessage (countWidth p.n)
          (subtreeValues p v (medianValues p codes (epochIndex p (workers v).phase))) := by
  have hown : (workers v).own = medianValues p codes (epochIndex p (workers v).phase) v := by
    cases hs : (workers v).phase <;> simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
    · simpa only [hs, epochIndex] using (h.states v _ hs).2
    · simp only [hs, epochIndex] at he
      omega
  have hn : (workers v).phase ≠ .baseline := by
    intro hb
    simp [hb, DistributedJacobianStrongGrowthPhases.Active] at ha
  rw [upWidth_of_early_epoch p _ hn he]
  congr 1
  funext j
  rw [hown]
  exact collectorCorrect_complete p hp v _ _ (h.collectors v he) hfull j

lemma medianContent_submit_up (p : Params) (hp : valid p) (S : Sampling p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (bits : List Bool)
    (hbits : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      bits = naturalMessage (countWidth p.n)
        (subtreeValues p v (medianValues p codes (epochIndex p (workers v).phase)))) :
    MedianContent p codes workers ((communication p S).submit network time v
      (p.parent v, bits ++ List.replicate 64 false)) := by
  have hadj := DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl
  cases hstored : network.messages v (p.parent v) with
  | none =>
      rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time v (p.parent v)
        _ hadj hstored]
      apply medianContent_insert_up p hp codes workers network h v hv
      intro he
      rw [hbits he]
  | some packet => simpa [communication, hadj, hstored] using h

lemma medianContent_submit_down (p : Params) (hp : valid p) (S : Sampling p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (bits : List Bool)
    (hbits : epochIndex p (workers v).phase < warmWidth p (localDepth p) →
      bits = naturalMessage 1 (medianDecision p codes (epochIndex p (workers v).phase))) :
    MedianContent p codes workers ((communication p S).submit network time (p.parent v)
      (v, bits ++ List.replicate 64 false)) := by
  have hadj := DistributedJacobianStrongGrowthOracle.adjacent_symm p v (p.parent v)
    (DistributedJacobianStrongGrowthOracle.child_adjacent p hp v (p.parent v) hv rfl)
  cases hstored : network.messages (p.parent v) v with
  | none =>
      rw [DistributedJacobianStrongGrowthOracle.communication_submit_free p S network time (p.parent v) v
        _ hadj hstored]
      apply medianContent_insert_down p hp codes workers network h v hv
      intro he
      rw [hbits he]
  | some packet => simpa [communication, hadj, hstored] using h

lemma medianContent_send_totals (p : Params) (hp : valid p) (S : Sampling p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (hv : v ≠ p.root)
    (time : Time) (ha : DistributedJacobianStrongGrowthPhases.Active (workers v).phase)
    (hfull : children p v ⊆ (workers v).collector.seen) :
    MedianContent p codes (Function.update workers v { workers v with sent := true })
      ((communication p S).submit network time v (p.parent v,
        naturalMessage (upWidth p (workers v).phase)
          (fun j => (workers v).own j + (workers v).collector.total j) ++ List.replicate 64 false)) := by
  classical
  apply medianContent_submit_up p hp S codes _ network (medianContent_sent p codes workers network h v) v hv
  intro he
  simpa only [Function.update_self] using median_up_payload p hp codes workers network h v ha hfull
    (by simpa only [Function.update_self] using he)

lemma medianContent_send_queued (p : Params) (hp : valid p) (S : Sampling p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (ho : DistributedJacobianStrongGrowthEpochOrdering.EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (time : Time) (bits : List Bool)
    (rest : List (Fin p.n × List Bool)) (hq : (workers (p.parent v)).queue = (v, bits) :: rest) :
    MedianContent p codes
      (Function.update workers (p.parent v) { workers (p.parent v) with queue := rest })
      ((communication p S).submit network time (p.parent v) (v, bits ++ List.replicate 64 false)) := by
  classical
  have hn := Ne.symm (DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv)
  apply medianContent_submit_down p hp S codes _ network
    (medianContent_queue_tail p codes workers network h (p.parent v) (v, bits) rest hq) v hv
  intro he
  simpa only [Function.update_of_ne hn] using
    medianContent_queued_epoch p codes workers network h hh ho v hv bits rest hq
      (by simpa only [Function.update_of_ne hn] using he)

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianSend
