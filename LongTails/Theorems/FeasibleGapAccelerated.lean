import LongTails.Setups.FeasibleHessianGapComposite
import LongTails.Proofs.FeasibleGapRun
import LongTails.Proofs.FeasibleGapBudget

namespace OracleTemplate.FeasibleGapAccelerated

open LongTails.Setups.FeasibleHessianGapComposite
open LongTails.Proofs.FeasibleGapRun LongTails.Proofs.FeasibleGapBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈16777216 * (1 + p.R * Real.sqrt (p.H0 / p.ε + p.H1)) * Real.log (4 + p.R ^ 2 * (p.H0 / p.ε + p.H1)) ^ 2 * Real.log (2 + p.Δ / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.FeasibleHessianGapComposite.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨h0, h1, hR, hΔ, hε⟩ K hK I O ⟨hgrad, hprox, s, h⟩
  have hcalls : calls p ≤ K := (calls_bound p h0 h1 hR hΔ hε).trans hK
  refine ⟨s, h.minimizer_feasible, h.minimizer, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, ξ⟩
  exact execute_accuracy h h0 h1 hR hΔ hε O hgrad hprox K hcalls ξ

end OracleTemplate.FeasibleGapAccelerated
