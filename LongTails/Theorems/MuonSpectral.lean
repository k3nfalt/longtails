import LongTails.Setups.MuonSpectral
import LongTails.Proofs.MuonGuarantees

namespace OracleTemplate.MuonSpectral

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.MuonSpectral.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈18 ^ 4 * ((min p.m p.n : ℕ) : ℝ) * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4 + 18 ^ 2 * p.L * p.Δ / p.ε ^ 2 + 18 ^ 2 * ((min p.m p.n : ℕ) : ℝ) ^ 2 * p.σ ^ 4 / (p.L * p.Δ * p.ε ^ 2)⌉₊ + 1

attribute [local simp] budget

theorem result : Convergence LongTails.Setups.MuonSpectral.spec budget := by
  refine ⟨OracleTemplate.MuonTuning.spectral, ?_, ?_⟩
  · intro p hp f O hO
    exact OracleTemplate.MuonSpectral.execution_accuracy p hp f O hO
  · intro p _
    rfl

end OracleTemplate.MuonSpectral
