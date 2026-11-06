import LongTails.Setups.OptimumGapGroupDro
import LongTails.Algorithms.SparseGroupSampling
import LongTails.Proofs.SparseGroupConvergence

open OracleTemplate
open scoped BigOperators

namespace LongTails.Theorems.SparseCertificateGroupDro

open LongTails.Setups.OptimumGapGroupDro

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => Nat.ceil (512 * (p.data.d + 1 : ℝ) ^ 2 * (Real.log (128 * p.data.K * (p.data.d + 1 : ℝ) / (p.data.ε * p.data.δ)) + p.data.d * Real.log (8 + 4096 * p.data.R * (p.data.d + 1 : ℝ) ^ 2 * (1 + p.data.G) / p.data.ε)) * ∑ i, 1 / max (p.gaps i) p.data.ε ^ 2)

theorem result : Convergence spec budget := by
  refine ⟨LongTails.Algorithms.SparseGroupSampling.algorithm, ?_, ?_⟩
  · intro p hp model O hadm
    obtain ⟨_, ⟨P, hIID, rfl⟩, xstar, hxstar, hmin, hgap⟩ := hadm
    exact LongTails.Proofs.SparseGroupConvergence.reservoir_successful p hp model P hIID
      xstar hxstar hmin hgap
  · intro p hp
    trivial

end LongTails.Theorems.SparseCertificateGroupDro
