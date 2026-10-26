import LongTails.Setups.SpectralSmoothAdamComparison
import LongTails.Proofs.AdamComparisonUpper
import LongTails.Proofs.AdamSeparationLower

namespace LongTails.Theorems.MuonAdamSgdSeparation

open OracleTemplate
open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 65 * (⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ + 1)

theorem result : Convergence LongTails.Setups.SpectralSmoothAdamComparison.spec budget := by
  refine ⟨fun p => muon (p.ε / (2 * p.L)) 65 ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊ p.x0, ?_, ?_⟩
  · intro p hp f O hadm
    exact ⟨LongTails.Proofs.AdamComparisonUpper.muon_accuracy p hp f O hadm,
      LongTails.Proofs.AdamSeparationLower.adam_lower hp,
      LongTails.Proofs.AdamComparisonTuning.sgd_lower hp⟩
  · intro p hp
    refine ⟨p.ε / (2 * p.L), 65, ⌈8 * p.L * p.Δ / p.ε ^ 2⌉₊, ?_, by norm_num, ?_⟩
    · exact div_pos hp.2.2.2.1 (mul_pos (by norm_num) hp.2.1)
    · exact LongTails.Proofs.BatchedDirectionExecution.method_follows polar _ (by norm_num) _ _

end LongTails.Theorems.MuonAdamSgdSeparation
