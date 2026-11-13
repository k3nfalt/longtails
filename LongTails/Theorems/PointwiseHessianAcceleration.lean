import LongTails.Setups.PointwiseHessianConvex
import LongTails.Algorithms.PointwiseHessianAccelerated
import LongTails.Proofs.PointwiseHessianCost

namespace LongTails.Theorems.PointwiseHessianAcceleration

open OracleTemplate MeasureTheory
open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈35184372088832 * (1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + (Real.sqrt p.M₁ * p.R) ^ 3) * (1 + Real.log (2 + (p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 + p.M₁ ^ 2 * p.R ^ 4 * p.Δ) / p.ε + p.M₁ * p.R ^ 2)) ^ 4⌉₊

theorem result : Convergence LongTails.Setups.PointwiseHessianConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hv f O had
  have hadmissible := had
  obtain ⟨hf,hc,hT,hH0,⟨xs,hmin,hx,hgap⟩,hg,hH⟩ := hadmissible
  have hvalid := hv
  obtain ⟨hM₀,hM₁,hR,hΔ,hH₀,hε⟩ := hvalid
  refine ⟨xs,hmin,Filter.Eventually.of_forall ?_⟩
  intro seed
  have hfinished := LongTails.Proofs.PointwiseHessianCost.trace_finished p hv f O had seed.1 seed.2 (budget p 0)
    (Nat.le_ceil _)
  have hi := LongTails.Proofs.PointwiseHessianExecution.trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
    (fun x => hmin (Set.mem_univ x)) hx hgap O hg hH seed.1 seed.2 (budget p 0)
  have he := LongTails.Proofs.PointwiseHessianExecution.execute_of_finished O seed.1 seed.2 (budget p 0) hfinished
  change f (execute O (algorithm p.toPublic) (budget p) seed.1 seed.2) - f xs ≤ p.ε
  rw [show budget p = (fun _ => budget p 0) by rfl, he]
  have hh := hi.phase
  simpa only [LongTails.Proofs.PointwiseHessianExecution.PhaseInvariant, hfinished] using hh

end LongTails.Theorems.PointwiseHessianAcceleration
