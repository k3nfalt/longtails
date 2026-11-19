import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementContent

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementLocal

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthRefinementState
open DistributedJacobianStrongGrowthRefinementContent

lemma refinementContent_bookkeeping (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) (next : State p)
    (hphase : next.phase = (workers v).phase)
    (hx : next.current = (workers v).current) (hw : next.work = (workers v).work)
    (hown : next.own = (workers v).own) (hc : next.collector = (workers v).collector)
    (hq : next.queue ⊆ (workers v).queue) :
    RefinementContent p g samples (Function.update workers v next) network := by
  classical
  apply refinementContent_congr p g samples workers _ network h
  · intro i
    by_cases hi : i = v
    · subst i
      simpa [Function.update] using refinementState_congr p g samples v (workers v) next
        hphase hx hw hown (h.states v)
    · simpa [Function.update, hi] using h.states i
  · intro i epoch hs
    by_cases hi : i = v
    · subst i
      simpa [Function.update, hphase] using hs
    · simpa [Function.update, hi] using hs
  · intro i
    by_cases hi : i = v
    · subst i
      simp [Function.update, hphase]
    · simp [Function.update, hi]
  · intro i
    by_cases hi : i = v
    · subst i
      simp [Function.update, hc]
    · simp [Function.update, hi]
  · intro i packet hmem
    by_cases hi : i = v
    · subst i
      exact hq (by simpa [Function.update] using hmem)
    · simpa [Function.update, hi] using hmem

lemma refinementContent_queue_tail (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n)
    (packet : Fin p.n × List Bool) (rest : List (Fin p.n × List Bool))
    (hq : (workers v).queue = packet :: rest) :
    RefinementContent p g samples (Function.update workers v { workers v with queue := rest }) network := by
  apply refinementContent_bookkeeping p g samples workers network h v
    { workers v with queue := rest } rfl rfl rfl rfl rfl
  intro item hitem
  rw [hq]
  exact List.mem_cons_of_mem packet hitem

lemma refinementContent_busy (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) :
    RefinementContent p g samples (Function.update workers v { workers v with busy := true }) network :=
  refinementContent_bookkeeping p g samples workers network h v _ rfl rfl rfl rfl rfl (fun _ hi => hi)

lemma refinementContent_sent (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (v : Fin p.n) :
    RefinementContent p g samples (Function.update workers v { workers v with sent := true }) network :=
  refinementContent_bookkeeping p g samples workers network h v _ rfl rfl rfl rfl rfl (fun _ hi => hi)

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementLocal
