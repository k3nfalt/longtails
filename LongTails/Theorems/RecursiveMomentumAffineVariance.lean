import LongTails.Setups.AffineVarianceMeanSquaredSmooth
import LongTails.Proofs.RecursiveMomentumConvergence

namespace OracleTemplate.RecursiveMomentum

open LongTails.Setups.AffineVarianceMeanSquaredSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈16 + 131 * q.Γ ^ 2 + 5 * q.Γ ^ 4 + 516 * q.Λ ^ 2 / q.ε ^ 2 + 64 * (q.L + q.Lbar) * (1 + 3 * q.Γ) * q.Δ / q.ε ^ 2 + 384 * (q.L + q.Lbar) * q.Λ * q.Δ / q.ε ^ 3⌉₊ + 2

theorem result : Convergence LongTails.Setups.AffineVarianceMeanSquaredSmooth.spec budget :=
  convergence

end OracleTemplate.RecursiveMomentum
