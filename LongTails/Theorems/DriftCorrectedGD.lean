import LongTails.Setups.AffineDriftPL
import LongTails.Proofs.Execution
import LongTails.Proofs.DriftCorrectedGD

namespace OracleTemplate.AffineDriftPL

open LongTails.Setups.AffineDriftPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(p.L / p.μ) * Real.log (1 + 2 * p.Δ / p.ε)⌉₊ * (p.d + 2)

theorem result : Convergence LongTails.Setups.AffineDriftPL.spec budget := by
  have hbudget : budget = fun p _ => (p.d + 2) * (⌈(p.L / p.μ) * Real.log (1 + 2 * p.Δ / p.ε)⌉₊) := by
    funext p i
    exact Nat.mul_comm _ _
  rw [hbudget]
  apply convergence_of_block_budget (S := spec) (fun p => ⌈(p.L / p.μ) * Real.log (1 + 2 * p.Δ / p.ε)⌉₊)
    (fun p => p.d + 2)
  refine ⟨driftCorrectedGD, ?_, fun _ _ => trivial⟩
  intro p hp K hK f O ho
  obtain ⟨u, hmin, hgap, hpl⟩ := ho.2.2.2
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    obtain ⟨v, hv, hacc⟩ := (execute_accuracy p f O hp ho ξ K (by simpa only [show p.Δ / (p.ε / 2) = 2 * p.Δ / p.ε by ring] using hK))
    have he : f v = f u := le_antisymm (hv (Set.mem_univ _)) (hmin (Set.mem_univ _))
    simpa only [Nat.mul_comm, budget, he, show p.Δ / (p.ε / 2) = 2 * p.Δ / p.ε by ring] using hacc

end OracleTemplate.AffineDriftPL
