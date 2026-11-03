import LongTails.Proofs.TailObliviousExecution
import LongTails.Proofs.TailObliviousAccuracy
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.TailObliviousLaw

open LongTails.Algorithms.TailObliviousExtragradient
open TailObliviousExecution TailObliviousAccuracy

lemma epoch_blocks_law {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) p P) (k off : ℕ) :
    MeasurePreserving (fun ξ => blocks k (2 * off) ξ) P
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps k) =>
        Measure.pi fun _ : Fin 2 => p) := by
  let Q2 : Measure (Fin 2 → Ω) := Measure.pi fun _ : Fin 2 => p
  have h1 := OracleTemplate.FiniteVariance.infinite_block_law p P hIID.independent
    hIID.marginal 2
  have h2 : MeasurePreserving (fun ζ : ℕ → Fin 2 → Ω => fun m => ζ (off + m))
      (Measure.infinitePi fun _ : ℕ => Q2) (Measure.infinitePi fun _ : ℕ => Q2) :=
    measurePreserving_snd.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving Q2 off)
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid Q2
  have h3 := OracleTemplate.FiniteVariance.infinite_block_law Q2
    (Measure.infinitePi fun _ : ℕ => Q2) hiid.independent hiid.marginal (innerSteps k)
  have hc := h3.comp (h2.comp h1)
  have heq : ((fun ζ : ℕ → Fin 2 → Ω => fun j : ℕ => fun i : Fin (innerSteps k) =>
      ζ (j * innerSteps k + i.val)) ∘ (fun ζ : ℕ → Fin 2 → Ω => fun m => ζ (off + m)) ∘
      (fun ξ : ℕ → Ω => fun m : ℕ => fun i : Fin 2 => ξ (m * 2 + i.val))) =
      fun ξ => blocks k (2 * off) ξ := by
    funext ξ j i h
    simp only [Function.comp_apply, blocks]
    congr 1
    ring
  rw [heq] at hc
  exact hc

end LongTails.Proofs.TailObliviousLaw
