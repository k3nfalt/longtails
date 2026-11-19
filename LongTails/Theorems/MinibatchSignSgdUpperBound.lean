import LongTails.Setups.SeparableNoiseLinfSmooth
import LongTails.Proofs.SignSgdConvergence

namespace LongTails.Theorems.MinibatchSignSgdUpperBound

open OracleTemplate

noncomputable def budget : (let S := LongTails.Setups.SeparableNoiseLinfSmooth.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => (⌈8 * q.L * q.Δ / q.ε ^ 2⌉₊ + 1) * (⌈16 * q.S ^ 2 / q.ε ^ 2⌉₊ + 1)

theorem result : Convergence LongTails.Setups.SeparableNoiseLinfSmooth.spec budget :=
  LongTails.Proofs.SignSgdConvergence.sign_convergence

end LongTails.Theorems.MinibatchSignSgdUpperBound
