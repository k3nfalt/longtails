import LongTails.Setups.MomentumSpectralSmooth
import LongTails.Proofs.MomentumMuonRate
import LongTails.Proofs.MomentumSeparationBounds

namespace LongTails.Theorems.MuonMomentumSeparation

open OracleTemplate
open LongTails.Setups.MomentumSpectralSmooth LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.MomentumDirection LongTails.Proofs.MomentumDirectionExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌈128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2⌉₊ + 1) * (⌈(32 * p.L * p.Δ / p.ε ^ 2 + 16) / (1 - p.β)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.MomentumSpectralSmooth.spec budget := by
  refine ⟨fun p => muonMomentum p.β ((1 - p.β) * p.ε / (8 * p.L))
    (⌈128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2⌉₊ + 1)
    ⌈(32 * p.L * p.Δ / p.ε ^ 2 + 16) / (1 - p.β)⌉₊ p.x0, ?_, ?_⟩
  · intro p hp f O hadm
    exact ⟨LongTails.Proofs.MomentumMuonRate.muon_momentum_accuracy p hp f O hadm,
      LongTails.Proofs.MomentumSeparationBounds.sgd_momentum_lower hp,
      LongTails.Proofs.MomentumSeparationBounds.nsgd_momentum_lower hp⟩
  · intro p hp
    obtain ⟨hL, _, _, hε, _, hβ1⟩ := hp
    have hδ : 0 < 1 - p.β := by linarith
    exact ⟨(1 - p.β) * p.ε / (8 * p.L), _, _, by positivity, Nat.succ_pos _,
      momentum_follows polar _ _ (Nat.succ_pos _) _ _⟩

end LongTails.Theorems.MuonMomentumSeparation
