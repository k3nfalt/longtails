import LongTails.Setups.UncalibratedSharp
import LongTails.Proofs.Execution
import LongTails.Proofs.RobustPolyak

namespace OracleTemplate.UncalibratedSharp

open LongTails.Setups.UncalibratedSharp

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈((p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2 / (4 * (p.μ - p.ρ) ^ 2 * p.α * p.β)) * Real.log (1 + p.G ^ 2 * p.R ^ 2 / p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.UncalibratedSharp.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => robustPolyak (2 * (1 - p.ρ / p.μ) / (p.α + p.β)) p.x0, ?_, fun _ _ => trivial⟩
  intro p hp K hK f O ho
  obtain ⟨u, hmin, hdist, hsharp, hans⟩ := ho.2
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    obtain ⟨v, hv, hacc⟩ := (execute_accuracy p f O hp ho ξ K (by simpa only [budget, one_div, inv_div] using hK))
    have he : f v = f u := le_antisymm (hv (Set.mem_univ _)) (hmin (Set.mem_univ _))
    simpa only [execute, budget, he, one_div, inv_div] using hacc

end OracleTemplate.UncalibratedSharp
