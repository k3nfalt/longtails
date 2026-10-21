import LongTails.Setups.RelativeDiscrepancyPL
import LongTails.Proofs.Execution
import LongTails.Proofs.DiscrepancyBatchedGD

namespace OracleTemplate.RelativeDiscrepancyPL

open LongTails.Setups.RelativeDiscrepancyPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(4 * p.L / (3 * p.μ)) * Real.log (1 + p.Δ / p.ε)⌉₊ * max 1 ⌈2 * p.D⌉₊

theorem result : Convergence LongTails.Setups.RelativeDiscrepancyPL.spec budget := by
  have hbudget : budget = fun p _ => (max 1 ⌈2 * p.D⌉₊) * (⌈(4 * p.L / (3 * p.μ)) * Real.log (1 + p.Δ / p.ε)⌉₊) := by
    funext p i
    exact Nat.mul_comm _ _
  rw [hbudget]
  apply convergence_of_block_budget (S := spec) (fun p => ⌈(4 * p.L / (3 * p.μ)) * Real.log (1 + p.Δ / p.ε)⌉₊)
    (fun p => max 1 ⌈2 * p.D⌉₊)
  refine ⟨batchedGD, ?_, fun _ _ => trivial⟩
  intro p hp K hK f O ho
  obtain ⟨xstar, hmin, hgap, hpl⟩ := ho.2.2.2
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    obtain ⟨y, hy, hacc⟩ := (execute_accuracy p f O hp ho ξ K (by simpa only [show p.L / (3 * p.μ / 4) = 4 * p.L / (3 * p.μ) by ring] using hK))
    have he : f y = f xstar := le_antisymm (hy (Set.mem_univ _)) (hmin (Set.mem_univ _))
    simpa only [execute, Nat.mul_comm, budget, he, show p.L / (3 * p.μ / 4) = 4 * p.L / (3 * p.μ) by ring] using hacc

end OracleTemplate.RelativeDiscrepancyPL
