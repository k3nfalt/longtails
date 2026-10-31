import LongTails.Setups.CompositeGapSmooth
import LongTails.Proofs.CompositeGapRun
import LongTails.Proofs.CompositeGapBudget

namespace OracleTemplate.CompositeGapAccelerated

open LongTails.Setups.CompositeGapSmooth
open LongTails.Proofs.CompositeGapRun LongTails.Proofs.CompositeGapBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈8192 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) * Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) * Real.log (2 + p.Δ / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.CompositeGapSmooth.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨h0, h1, hR, hΔ, hε⟩ K hK I O ⟨hgrad, hprox, s, h⟩
  have hcalls : calls p ≤ K := (calls_bound p h0 h1 hR hΔ hε).trans hK
  have hans : ∀ k query seed, O.answer k (0, query) seed =
      CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox query := by
    intro k query seed
    cases query with
    | gradient x => exact hgrad k seed x
    | prox a z v => exact hprox k seed a z v
  refine ⟨s, h.minimizer_feasible, h.minimizer, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ξ⟩
  exact execute_accuracy h h0 h1 hR hΔ hε O hans K hcalls ξ

end OracleTemplate.CompositeGapAccelerated
