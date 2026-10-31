import LongTails.Setups.GeneralizedSmoothFiniteSum
import LongTails.Proofs.GeneralizedFiniteSumGuarantee

namespace OracleTemplate.GeneralizedFiniteSum.LocalFiniteSumAcceleration

open LongTails.Setups.GeneralizedSmoothFiniteSum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈16777216 * ((p.n : ℝ) * (1 + p.L1 * p.R) * Real.log (2 + p.Δ / p.ε) ^ 2 + Real.sqrt ((p.n : ℝ) * (p.L0 + p.L1 * p.G) * p.R ^ 2 / p.ε) * Real.log (2 + p.Δ / p.ε))⌉₊

theorem result : Convergence LongTails.Setups.GeneralizedSmoothFiniteSum.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨localAcceleration, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  apply localAcceleration_success p hp f O hO
  exact oracleCost_le p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2

end OracleTemplate.GeneralizedFiniteSum.LocalFiniteSumAcceleration
