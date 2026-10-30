import LongTails.Setups.CappedHessianSimilarConvex
import LongTails.Proofs.CappedProximalOuter
import LongTails.Proofs.CappedProximalBudget

namespace LongTails.Theorems.CappedHessianSimilarAccelerated

open OracleTemplate LongTails.Setups.CappedHessianSimilarConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 40 * (1 + (p.m : ℝ) / p.s + (1 + Real.sqrt ((p.m : ℝ) * Real.sqrt p.m) / p.s) * Real.sqrt (p.δ / p.μ)) * (1 + Real.log (2 + (p.m : ℝ) + p.δ / p.μ)) * (1 + Real.log (2 + p.Δ / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.CappedHessianSimilarConvex.spec budget := by
  refine ⟨LongTails.Algorithms.CappedProximal.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp inst oracle hadm
  obtain ⟨hs, hsm, hd, hm, hD, he⟩ := hp
  exact LongTails.Proofs.CappedProximalOuter.successful_execution hadm.1 hs hm hd hD he
    oracle hadm.2 (budget p 0)
    (LongTails.Proofs.CappedProximalBudget.total_cost_upper hs hsm hm hd hD he)

end LongTails.Theorems.CappedHessianSimilarAccelerated
