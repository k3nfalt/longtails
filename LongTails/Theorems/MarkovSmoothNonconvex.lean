import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.MarkovNormalizedRate

namespace LongTails.Theorems.MarkovSmoothNonconvex

open OracleTemplate Setups.MarkovSmoothNonconvex

noncomputable def budget : (let S := LongTails.Setups.MarkovSmoothNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌊2048 * p.L * p.Δ / p.ε ^ 2⌋₊ + 1) * ((⌊256 * p.σ ^ 2 / p.ε ^ 2⌋₊ + 1) * (⌊p.τ * Real.log (32 + 8192 * p.σ ^ 2 / p.ε ^ 2)⌋₊ + 1))

theorem result : Convergence LongTails.Setups.MarkovSmoothNonconvex.spec budget :=
  ⟨Proofs.MarkovNormalizedRate.algorithm, Proofs.MarkovNormalizedRate.accuracy, fun _ _ => trivial⟩

end LongTails.Theorems.MarkovSmoothNonconvex
