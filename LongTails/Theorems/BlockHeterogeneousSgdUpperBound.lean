import LongTails.Setups.BlockHeterogeneousNonconvex
import LongTails.Proofs.BlockSgdConvergence

namespace LongTails.Theorems.BlockHeterogeneousSgdUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.BlockHeterogeneousNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈8 * (∑ j, q.L j) * q.Δ / q.ε ^ 2 + 20 * (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4⌉₊ + 1

theorem result : Convergence LongTails.Setups.BlockHeterogeneousNonconvex.spec budget :=
  LongTails.Proofs.BlockSgdConvergence.blockSgd_convergence

end LongTails.Theorems.BlockHeterogeneousSgdUpperBound
