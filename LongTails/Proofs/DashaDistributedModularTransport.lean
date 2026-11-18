import LongTails.Proofs.DashaDistributedExecution

namespace LongTails.Proofs.DashaDistributedModularTransport

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution

variable {p : Params}

lemma modular_initial (cfg : Config p) (k : ℕ) (hm : modularAt p cfg k = true) :
    cfg.initializer = none ∧ k = 0 := by
  cases hi : cfg.initializer <;> simp_all [modularAt]

lemma transportExact_of_packets (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (hw : ∀ k < (cfg.iterations : ℕ), ∀ i suffix,
      uplinkReceive p cfg seed k i (workerMessage cfg f seed k i ++ suffix) = wireIncrement cfg f seed k i)
    (hb : ∀ k < (cfg.iterations : ℕ), ∀ suffix,
      LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth
        (broadcastMessage cfg f seed k ++ suffix) =
        (fun j => ∑ i, (idealTrajectory p cfg f seed k).localCode i j))
    (hlo : modularAt p cfg 0 = true → ∀ j,
      -(LongTails.Algorithms.DashaQuantization.center cfg.initialWidth : ℤ) ≤
        ∑ i, (idealTrajectory p cfg f seed 0).localCode i j)
    (hhi : modularAt p cfg 0 = true → ∀ j,
      (∑ i, (idealTrajectory p cfg f seed 0).localCode i j) +
        LongTails.Algorithms.DashaQuantization.center cfg.initialWidth <
        LongTails.Algorithms.DashaModular.modulus cfg.initialWidth) :
    TransportExact cfg f seed := by
  refine ⟨hw, ?_, ?_, hb⟩
  · intro k hk i s hiter hseed
    by_cases hm : modularAt p cfg k = true
    · obtain ⟨hi, hk0⟩ := modular_initial cfg k hm
      have hzero : s.iteration = 0 := hiter.trans hk0
      have hmzero : modularAt p cfg 0 = true := by simpa only [hk0] using hm
      simp only [localIncrement, hzero, hseed, hmzero, ite_true, hk0, increment, previousCode,
        idealTrajectory, idealInitial, hi, initialIterate, sub_zero]
    · simpa only [localIncrement, hiter, hseed, ite_eq_right hm, wireIncrement,
        List.append_nil] using hw k hk i []
  · intro k hk
    by_cases hm : modularAt p cfg k = true
    · obtain ⟨hi, hk0⟩ := modular_initial cfg k hm
      subst k
      funext j
      simpa only [finishTotal, hm, ite_true, Pi.add_apply, previousCode, Finset.sum_const_zero,
        zero_add, wireIncrement, increment, Pi.sub_apply, Pi.zero_apply, sub_zero] using
        DashaModular.restore_sum_residues Finset.univ cfg.initialWidth
          (fun i => (idealTrajectory p cfg f seed 0).localCode i j) (hlo hm j) (hhi hm j)
    · simp only [finishTotal, wireIncrement, ite_eq_right hm]
      funext j
      simp only [Pi.add_apply, increment, Pi.sub_apply, Finset.sum_sub_distrib]
      ring

end LongTails.Proofs.DashaDistributedModularTransport
