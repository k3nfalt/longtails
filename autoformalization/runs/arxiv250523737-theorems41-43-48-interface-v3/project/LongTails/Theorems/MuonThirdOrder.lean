import LongTails.Setups.MuonThirdOrder
import LongTails.Proofs.MuonThirdOrder

namespace OracleTemplate.MuonThirdOrder

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.MuonThirdOrder.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈8 * p.J * p.Δ / p.ε ^ 2 + 2 * p.s * (((min p.m p.n : ℕ) : ℝ) * Real.sqrt ((min p.m p.n : ℕ) : ℝ)) * p.Δ / (3 * p.J * p.ε)⌉₊ + 1

attribute [local simp] budget

theorem result : Convergence LongTails.Setups.MuonThirdOrder.spec budget := by
  refine ⟨OracleTemplate.MuonBest.algorithm, ?_, ?_⟩
  · intro p hp f O hO
    exact OracleTemplate.MuonThirdOrder.execution_accuracy p hp f O hO
  · intro p _
    rfl

end OracleTemplate.MuonThirdOrder
