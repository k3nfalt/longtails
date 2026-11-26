import LongTails.Setups.BiasedNoiseNonconvex
import LongTails.Proofs.BiasedSgdConvergence

namespace LongTails.Theorems.BiasedNoiseSgdUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.BiasedNoiseNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let r := (1 - q.m) * q.ε ^ 2
  ⌈16 * q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / r⌉₊ + 1

theorem result : Convergence LongTails.Setups.BiasedNoiseNonconvex.spec budget :=
  LongTails.Proofs.BiasedSgdConvergence.biased_sgd_convergence

end LongTails.Theorems.BiasedNoiseSgdUpperBound
