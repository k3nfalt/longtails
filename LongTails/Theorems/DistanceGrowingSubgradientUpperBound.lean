import LongTails.Setups.DistanceGrowingSubgradient
import LongTails.Proofs.LocalizedClippedConvergence

open OracleTemplate

namespace LongTails.Theorems.DistanceGrowingSubgradientUpperBound

noncomputable def budget : (let S := LongTails.Setups.DistanceGrowingSubgradient.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * (if p.G * p.R ≤ p.ε then 0 else ⌈1024 * p.R ^ 2 * (p.G ^ 2 + p.B ^ 2 * p.R ^ 2) * Real.log (8 / p.δ) / p.ε ^ 2⌉₊)

theorem result : Convergence LongTails.Setups.DistanceGrowingSubgradient.spec budget :=
  LongTails.Proofs.LocalizedClippedSubgradient.convergence

end LongTails.Theorems.DistanceGrowingSubgradientUpperBound
