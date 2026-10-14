import LongTails.Setups.QuadraticTemporalDiscrepancy
import LongTails.Proofs.Execution
import LongTails.Proofs.TemporalAcceleratedConvergence

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * max 1 ⌈Real.sqrt (p.L / p.μ) * Real.log (1 + 8 * p.Δ / p.ε) + 8 * p.D / Real.sqrt (p.μ * p.ε)⌉₊

theorem result : Convergence LongTails.Setups.QuadraticTemporalDiscrepancy.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun p => max 1 ⌈Real.sqrt (p.L / p.μ) * Real.log (1 + 8 * p.Δ / p.ε) + 8 * p.D / Real.sqrt (p.μ * p.ε)⌉₊) (fun _ => 2)
  refine ⟨fun p => tailAccelerated (Real.sqrt (p.μ / p.L)) p.μ p.x0, ?_, fun _ _ => trivial⟩
  intro p hp K hK I O ho
  refine Filter.Eventually.of_forall ?_
  · rintro ⟨⟨⟩, ξ⟩
    simpa only [budget, one_div, ← Real.sqrt_inv, inv_div] using (execute_accuracy p I O hp ho ξ K (by simpa only [one_div, ← Real.sqrt_inv, inv_div] using hK))

end OracleTemplate.TemporalDiscrepancy
