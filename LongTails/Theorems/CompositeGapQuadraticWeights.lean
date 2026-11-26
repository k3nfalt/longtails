import LongTails.Setups.CompositeGapSmooth
import LongTails.Proofs.CompositeGapQuadraticWeights

namespace OracleTemplate.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth
open LongTails.Proofs.CompositeGapQuadraticWeights

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  ⌈32 * (2 + Real.sqrt 2) * p.R * Real.sqrt (p.H0 / p.ε) +
    85 * (1 + p.R * Real.sqrt p.H1) * Real.log (2 + p.Δ / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.CompositeGapSmooth.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨h0, h1, hR, hΔ, hε⟩ K hK I O ⟨hgrad, hprox, s, h⟩
  refine ⟨s, h.minimizer_feasible, h.minimizer, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ξ⟩
  apply execute_accuracy h h0 h1 hR hΔ hε O _ K ((budget_bound p h0 h1 hR hΔ hε).trans hK) ξ
  intro k query seed
  cases query with
  | gradient x => exact hgrad k seed x
  | prox a z v => exact hprox k seed a z v

end OracleTemplate.CompositeGapQuadraticWeights
