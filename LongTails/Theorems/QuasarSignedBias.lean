import LongTails.Setups.QuasarSignedBias
import LongTails.Proofs.Execution
import LongTails.Proofs.QuasarSignedBias

namespace OracleTemplate.QuasarSignedBias

open LongTails.Setups.QuasarSignedBias

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈p.R ^ 2 * (p.M ^ 2 + 2 * p.M * p.B) / (p.τ ^ 2 * p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.QuasarSignedBias.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => bestValueDescent (p.τ * p.ε / (p.M ^ 2 + 2 * p.M * p.B)) p.x0, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  obtain ⟨u, hmin, hdist, hsupport⟩ := ho.2.2.2
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    obtain ⟨v, hv, hacc⟩ := (execute_accuracy p f O hp ho ξ)
    have he : f v = f u := le_antisymm (hv (Set.mem_univ _)) (hmin (Set.mem_univ _))
    simpa only [budget, he] using hacc

end OracleTemplate.QuasarSignedBias
