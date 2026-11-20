import LongTails.Proofs.DistributedJacobianStrongGrowthMedianContent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianLocal

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianState
open DistributedJacobianStrongGrowthMedianContent

lemma medianContent_local (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (next : State p)
    (hepoch : epochIndex p next.phase = epochIndex p (workers v).phase)
    (hstate : MedianState p codes v next)
    (hcollector : next.collector = (workers v).collector)
    (hqueue : next.queue ⊆ (workers v).queue) :
    MedianContent p codes (Function.update workers v next) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using hstate
    · simpa [Function.update, hi] using h.states i
  · intro i he
    by_cases hi : i = v
    · subst i
      simpa [Function.update, hepoch, hcollector] using h.collectors v
        (by simpa [Function.update, hepoch] using he)
    · simpa [Function.update, hi] using h.collectors i (by simpa [Function.update, hi] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      simpa [Function.update, hepoch] using h.upward v hc finish bits hpending
        (by simpa [Function.update, hepoch] using he)
    · simpa [Function.update, hv] using h.upward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      simpa [Function.update, hepoch] using h.downward v hc finish bits hpending
        (by simpa [Function.update, hepoch] using he)
    · simpa [Function.update, hv] using h.downward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simpa [Function.update, hepoch] using h.queued v child bits
        (hqueue (by simpa [Function.update] using hmem)) (by simpa [Function.update, hepoch] using he)
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

lemma medianContent_finishLocal (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (x : Point p)
    (hn : (workers v).phase ≠ .baseline)
    (hcodes : (workers v).phase = .warming →
      (finishLocal p (workers v) x).warmCodes = fun j => (codes v j).val) :
    MedianContent p codes (Function.update workers v (finishLocal p (workers v) x)) network := by
  apply medianContent_local p codes workers network h v _ (epochIndex_finishLocal p (workers v) x hn)
  · cases hs : (workers v).phase with
    | baseline => exact False.elim (hn hs)
    | warming => exact medianState_finishLocal_warming p codes v (workers v) x hs (hcodes hs)
    | median remaining => simpa [MedianState, finishLocal, hs] using h.states v
    | refinement epoch => simp [MedianState, finishLocal, hs]
    | done => simp [MedianState, finishLocal, hs]
  · cases hs : (workers v).phase <;> simp [finishLocal, hs]
  · cases hs : (workers v).phase <;> simp [finishLocal, hs, startMedian]

lemma medianState_of_late (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (v : Fin p.n) (s : State p)
    (he : warmWidth p (localDepth p) < epochIndex p s.phase) : MedianState p codes v s := by
  intro remaining hs
  simp only [hs, epochIndex] at he
  omega

lemma medianContent_late (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (next : State p)
    (hepoch : warmWidth p (localDepth p) < epochIndex p next.phase) :
    MedianContent p codes (Function.update workers v next) network := by
  classical
  constructor
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using medianState_of_late p codes v next hepoch
    · simpa [Function.update, hi] using h.states i
  · intro i he
    by_cases hi : i = v
    · subst i
      simp only [Function.update_self] at he
      omega
    · simpa [Function.update, hi] using h.collectors i (by simpa [Function.update, hi] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      simp only [Function.update_self] at he
      omega
    · simpa [Function.update, hv] using h.upward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro child hc finish bits hpending he
    by_cases hv : child = v
    · subst child
      simp only [Function.update_self] at he
      omega
    · simpa [Function.update, hv] using h.downward child hc finish bits hpending
        (by simpa [Function.update, hv] using he)
  · intro i child bits hmem he
    by_cases hi : i = v
    · subst i
      simp only [Function.update_self] at he
      omega
    · simpa [Function.update, hi] using h.queued i child bits (by simpa [Function.update, hi] using hmem)
        (by simpa [Function.update, hi] using he)

lemma medianContent_relay_refinement (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (epoch : ℕ)
    (hs : (workers v).phase = .refinement epoch)
    (hb : epoch < refinementCount p (localDepth p)) (values : Fin p.d → ℕ) :
    MedianContent p codes (Function.update workers v (relay p v (workers v) values)) network := by
  apply medianContent_late p codes workers network h v
  change warmWidth p (localDepth p) < epochIndex p (finishBroadcast p (workers v) values).phase
  rw [epochIndex_finishBroadcast p (workers v) values
    (by simpa only [hs, PhaseBounds] using hb)
    (by simp [hs, DistributedJacobianStrongGrowthPhases.Active]), hs]
  simp only [epochIndex]
  omega

lemma medianContent_bookkeeping (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) (next : State p)
    (hphase : next.phase = (workers v).phase)
    (hlower : next.lower = (workers v).lower) (hown : next.own = (workers v).own)
    (hcollector : next.collector = (workers v).collector)
    (hqueue : next.queue ⊆ (workers v).queue) :
    MedianContent p codes (Function.update workers v next) network :=
  medianContent_local p codes workers network h v next (congrArg (epochIndex p) hphase)
    (medianState_congr p codes v _ _ hphase hlower hown (h.states v)) hcollector hqueue

lemma medianContent_queue_tail (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n)
    (packet : Fin p.n × List Bool) (rest : List (Fin p.n × List Bool))
    (hq : (workers v).queue = packet :: rest) :
    MedianContent p codes (Function.update workers v { workers v with queue := rest }) network := by
  apply medianContent_bookkeeping p codes workers network h v { workers v with queue := rest } rfl rfl rfl rfl
  intro item hitem
  rw [hq]
  exact List.mem_cons_of_mem packet hitem

lemma medianContent_busy (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) :
    MedianContent p codes (Function.update workers v { workers v with busy := true }) network :=
  medianContent_bookkeeping p codes workers network h v _ rfl rfl rfl rfl (fun _ hi => hi)

lemma medianContent_sent (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : MedianContent p codes workers network) (v : Fin p.n) :
    MedianContent p codes (Function.update workers v { workers v with sent := true }) network :=
  medianContent_bookkeeping p codes workers network h v _ rfl rfl rfl rfl (fun _ hi => hi)

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianLocal
