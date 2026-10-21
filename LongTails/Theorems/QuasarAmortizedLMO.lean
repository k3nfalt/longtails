import LongTails.Setups.QuasarAmortizedLMO
import LongTails.Proofs.Execution
import LongTails.Proofs.QuasarAmortizedLMO

namespace OracleTemplate.QuasarAmortizedLMO

open LongTails.Setups.QuasarAmortizedLMO

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * max 1 ⌈(6 * p.L * p.D ^ 2 / p.τ ^ 2 + 2 * p.Γ / p.τ) / p.ε⌉₊

theorem result : Convergence LongTails.Setups.QuasarAmortizedLMO.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun p => max 1 ⌈(6 * p.L * p.D ^ 2 / p.τ ^ 2 + 2 * p.Γ / p.τ) / p.ε⌉₊)
    (fun p => 2)
  refine ⟨fun p => twoCallFrankWolfe p.τ p.x0, ?_, fun _ _ => trivial⟩
  intro p hp K hK f O ho
  obtain ⟨u, hu, hmin, hquasar⟩ := ho.2.2.2.2
  refine ⟨u, hu, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, ξ⟩
    obtain ⟨v, hv, hvmin, hfeas, hacc⟩ := (execute_accuracy p f O hp ho ξ K hK)
    have he : f v = f u := le_antisymm (hvmin hu) (hmin hv)
    exact ⟨hfeas, by simpa only [execute, Nat.mul_comm, budget, he] using hacc⟩

end OracleTemplate.QuasarAmortizedLMO
